#!/usr/bin/env python3
"""One fixed full-Q search for R7 only, five shared seconds, streamed proofs."""
import argparse
import gzip
import hashlib
import importlib.util
import json
from pathlib import Path
import resource
import signal
import sys
import time

ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT))
from experiments.certified_power import PowerSimplifier,invert
from experiments.certified_completion import Budget
from experiments.counted_completion import CountedCompletion
from experiments.a4_structure import commuting_equations
from experiments.restricted_identity import map_record


class SharedDeadline(Exception):pass


def emit(event):print(json.dumps(event,separators=(',',':')),flush=True)


def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--input',type=Path,required=True);p.add_argument('--plan',type=Path,required=True);a=p.parse_args()
    raw=a.input.read_bytes();blueprint=json.loads(gzip.decompress(raw));plan=json.loads(a.plan.read_text())
    assert hashlib.sha256(raw).hexdigest()==plan['input_sha256']
    base=blueprint['quotient_relators'];target=blueprint['problem']['relators'][6]
    assert len(base)==236 and target==[5]*4 and base[198]==[5]*28 and plan['target']==7
    effective={name:list(resource.getrlimit(getattr(resource,name))) for name in ['RLIMIT_AS','RLIMIT_CPU','RLIMIT_FSIZE']}
    assert effective=={'RLIMIT_AS':[536870912]*2,'RLIMIT_CPU':[6]*2,'RLIMIT_FSIZE':[8388608]*2}
    spec=importlib.util.spec_from_file_location('independent_products',ROOT/'scripts/check-relation-span-certificate.py');checker=importlib.util.module_from_spec(spec);spec.loader.exec_module(checker)
    emit(dict(kind='header',target=7,target_word=target,input_sha256=hashlib.sha256(raw).hexdigest(),
              plan_sha256=hashlib.sha256(a.plan.read_bytes()).hexdigest(),effective_os_limits=effective))
    started=time.monotonic();deadline=started+5;engine=None;answer=dict(status='unresolved',reason='no_successful_certificate')
    phase='power';seeded=[];stop='';power_rules=[]
    def timeout(sig,frame):raise SharedDeadline()
    previous=signal.signal(signal.SIGALRM,timeout);signal.setitimer(signal.ITIMER_REAL,5)
    def check_target(proof):
        checker.check_product(target,base,json.loads(json.dumps(proof)),6)
        return dict(status='certified',factors=proof)
    try:
        core=plan['power_indices'];power=PowerSimplifier([base[i-1] for i in core],seconds=min(1,deadline-time.monotonic()))
        local=dict(method='power',rules=power.rules,targets=[power.prove(target)])
        mapped=map_record(local,core);power_rules=mapped['rules']
        for rule in power_rules:checker.check_product(list(rule['lhs']),base,json.loads(json.dumps(rule['factors'])),6)
        emit(dict(kind='power_result',local=local,mapped=mapped,metrics=dict(operations=power.operations,truncations=sorted(power.truncations)),elapsed=time.monotonic()-started))
        if mapped['targets'][0]['status']=='certified':answer=check_target(mapped['targets'][0]['factors']);stop='power_certified'
        else:
            phase='completion_initialization'
            class StreamingCompletion(CountedCompletion):
                def add_rule(self,lhs,rhs,proof,origin):
                    before=len(self.rules)
                    super().add_rule(lhs,rhs,proof,origin)
                    if len(self.rules)>before:emit(dict(kind='rule',rule=self.rules[-1]))
            engine=StreamingCompletion.__new__(StreamingCompletion)
            engine.__init__(6,[],seconds=max(.000001,min(5,deadline-time.monotonic())),max_rules=256,max_pairs=4000,max_word=512,max_factors=2000,max_steps=2000)
            engine.deadline=deadline
            def equation(lhs,rhs,proof,origin):
                checker.check_product(list(lhs)+checker.inv(rhs),base,json.loads(json.dumps(proof)),6)
                engine.equation(tuple(lhs),tuple(rhs),proof,origin)
                result=engine.prove(target)
                if result['status']=='certified':return check_target(result['factors'])
                return None
            phase='known_seeds'
            for j in plan['known_seed_targets']:
                word=blueprint['problem']['relators'][j-1];proof=blueprint['targets'][j-1]['factors']
                for sign in (1,-1):
                    lhs=word if sign==1 else checker.inv(word);pp=proof if sign==1 else invert(proof)
                    result=equation(lhs,(),pp,'known_quotient_certificate')
                    if result:answer=result;break
                if answer['status']=='certified':break
            if answer['status']!='certified':
                phase='central_square_seeds'
                for lemma in commuting_equations():
                    emit(dict(kind='auxiliary_equation',equation=lemma))
                    result=equation(lemma['lhs'],lemma['rhs'],lemma['factors'],lemma['origin'])
                    if result:answer=result;break
            if answer['status']!='certified':
                phase='derived_power_seeds'
                for rule in power_rules:
                    if rule['origin'] not in ['common_root_bezout','inversion_and_centrality']:continue
                    result=equation(rule['lhs'],(),rule['factors'],'checked_power_consequence')
                    if result:answer=result;break
            if answer['status']!='certified':
                phase='fixed_input_seeding'
                for i in plan['completion_input_order']:
                    result=equation(base[i-1],(),[((),i,1)],'original_Q_'+str(i));seeded.append(i)
                    if result:answer=result;break
            if answer['status']!='certified':
                phase='critical_pairs';engine.complete([target])
                result=engine.goal_answers[0] if engine.goal_answers else engine.prove(target)
                if result['status']=='certified':answer=check_target(result['factors'])
                else:answer=result
            stop='completion_certified' if answer['status']=='certified' else getattr(engine,'stop_reason','completion_unresolved')
    except SharedDeadline:
        stop='shared_search_time_limit'
        if answer['status']!='certified':answer=dict(status='unresolved',reason=stop)
    except Budget as error:stop=str(error);answer=dict(status='unresolved',reason=stop)
    finally:
        signal.setitimer(signal.ITIMER_REAL,0);signal.signal(signal.SIGALRM,previous)
    emit(dict(kind='target',target=7,answer=answer,elapsed=time.monotonic()-started))
    emit(dict(kind='summary',search_wall_seconds=time.monotonic()-started,stop_reason=stop,phase=phase,
              original_rows_seeded=seeded,original_rows_seeded_count=len(seeded),
              completion_rules=len(getattr(engine,'rules',[])) if engine else 0,
              accounting=engine.accounting() if engine and hasattr(engine,'pairs') else {},
              truncations=sorted(getattr(engine,'truncated',set())) if engine else [],
              max_equation_length=getattr(engine,'max_equation',0) if engine else 0,
              only_search_target=7))


if __name__=='__main__':main()
