#!/usr/bin/env python3
"""Only R12, only Q140/Q204/Q225, one shared second for BOTH methods."""
import argparse
import json
from pathlib import Path
import signal
import resource
import sys
import time

ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT))
from experiments.certified_power import PowerSimplifier
from experiments.certified_completion import Completion
from experiments.restricted_identity import map_record


class SharedTimeout(Exception):pass


def emit(record):print(json.dumps(record,separators=(',',':')),flush=True)


def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--input',type=Path,required=True);a=p.parse_args()
    source=json.loads(a.input.read_text());base=source['base_relators'];target=source['target']
    assert source['original_indices']==[225,140,204] and source['rank']==6 and target==[1]*7
    expected=[[1,5,1,-5],[-5]+[-1]*7+[5]+[1]*7,[1]*49]
    assert base==expected
    effective={name:list(resource.getrlimit(getattr(resource,name))) for name in ['RLIMIT_AS','RLIMIT_CPU','RLIMIT_FSIZE']}
    assert effective=={'RLIMIT_AS':[536870912]*2,'RLIMIT_CPU':[3]*2,'RLIMIT_FSIZE':[8388608]*2}
    emit(dict(kind='header',effective_os_limits=effective,original_indices=source['original_indices'],target=target,
              search_seconds=1,combined_rule_limit=128,critical_pair_limit=1000,
              word_limit=128,factor_limit=2000,reduction_steps_per_call=2000))
    def timeout(sig,frame):raise SharedTimeout()
    old=signal.signal(signal.SIGALRM,timeout)
    started=time.monotonic();deadline=started+1;used_rules=0;completed=[]
    signal.setitimer(signal.ITIMER_REAL,1)
    try:
        for method in ['power','completion']:
            emit(dict(kind='method_start',method=method,elapsed=time.monotonic()-started))
            remaining=deadline-time.monotonic()
            if remaining<=0: raise SharedTimeout()
            if method=='power':
                engine=PowerSimplifier(base,seconds=min(remaining,1),max_rules=32,max_word=128,max_factors=2000,max_steps=2000)
                answers=[engine.prove(target)]
                metrics=dict(operations=engine.operations,truncations=sorted(engine.truncations))
            else:
                engine=Completion(6,base,seconds=min(remaining,1),max_rules=128-used_rules,
                                  max_pairs=1000,max_word=128,max_factors=2000,max_steps=2000)
                initial=[engine.prove(target)]
                if initial[0]['status']!='certified': engine.complete([target])
                answers=engine.goal_answers or [initial[0] if initial[0]['status']=='certified' else engine.prove(target)]
                metrics=dict(critical_pairs=engine.pairs,queued_pairs=len(engine.queued),truncations=sorted(engine.truncated),
                             reduction_steps=engine.reductions,stop_reason=engine.stop_reason)
            raw=dict(method=method,rules=engine.rules,targets=answers,metrics=metrics,limits=engine.limits)
            mapped=map_record(raw,source['original_indices'])
            used_rules+=len(engine.rules)
            assert used_rules<=128
            emit(dict(kind='method_result',local=raw,mapped=mapped,elapsed=time.monotonic()-started))
            completed.append(method)
    except SharedTimeout:
        emit(dict(kind='shared_search_timeout',completed_methods=completed,elapsed=time.monotonic()-started))
    finally:
        signal.setitimer(signal.ITIMER_REAL,0);signal.signal(signal.SIGALRM,old)
    emit(dict(kind='summary',search_wall_seconds=time.monotonic()-started,completed_methods=completed,retained_rules=used_rules,
              no_other_targets=True))


if __name__=='__main__':main()
