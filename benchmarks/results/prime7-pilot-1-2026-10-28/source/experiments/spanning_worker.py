#!/usr/bin/env python3
"""One fixed-quotient search, emitting complete proof records incrementally."""
import argparse
import collections
import gzip
import hashlib
import json
from pathlib import Path
import resource
import signal
import sys
import time

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT))
from experiments.relation_span import FixedQuotient, inverse, quotient, reduce_word


class SearchBudgetExpired(Exception):
    pass


class PilotSearch(FixedQuotient):
    """Same indexed identities/BFS; enforce the state cap BEFORE insertion."""
    def prove(self,target):
        start=reduce_word(target)
        queue=collections.deque([(start,[])])
        seen={start}
        visited=0
        max_length=len(start)
        while queue and visited<self.max_states:
            if time.monotonic()>=self.deadline:
                raise SearchBudgetExpired()
            word,proof=queue.popleft();visited+=1
            if not word:
                return {'status':'certified','factors':proof,'states':len(seen),'visited':visited,'max_word_length':max_length}
            for pos in range(len(word)):
                for size in range(min(self.max_length,len(word)-pos),0,-1):
                    for right,index,sign,q in self.options.get(word[pos:pos+size],()):
                        if time.monotonic()>=self.deadline:
                            raise SearchBudgetExpired()
                        result=reduce_word(word[:pos]+right+word[pos+size:])
                        if len(result)>len(start)+6 or result in seen:
                            continue
                        if len(seen)>=self.max_states:
                            return {'status':'unresolved','reason':'state_limit','states':len(seen),'visited':visited,'max_word_length':max_length}
                        new=proof+[[list(reduce_word(word[:pos]+q)),index,sign]]
                        seen.add(result);max_length=max(max_length,len(result))
                        if not result:
                            return {'status':'certified','factors':new,'states':len(seen),'visited':visited,'max_word_length':max_length}
                        queue.append((result,new))
        return {'status':'unresolved','reason':'state_limit' if queue else 'finite_search_exhausted',
                'states':len(seen),'visited':visited,'max_word_length':max_length}


def emit(record):
    print(json.dumps(record,separators=(',',':')),flush=True)


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--input',type=Path,required=True)
    p.add_argument('--targets',required=True)
    p.add_argument('--tag',choices=['small-verification','prime7-authorized-pilot'],required=True)
    args=p.parse_args()
    raw=args.input.read_bytes()
    value=json.loads(gzip.decompress(raw) if args.input.suffix=='.gz' else raw)
    problem=value.get('problem',value)
    relations,labels=quotient(problem['rank'],problem['prime'],problem['relators'],problem['candidates'])
    if 'quotient_relators' in value:
        assert [list(r) for r in relations]==value['quotient_relators']
    targets=[int(x) for x in args.targets.split(',')]
    assert len(set(targets))==len(targets) and all(1<=x<=len(problem['relators']) for x in targets)
    expected={'RLIMIT_AS':[512*1024*1024]*2,'RLIMIT_CPU':[6]*2,'RLIMIT_FSIZE':[8*1024*1024]*2}
    effective={k:list(resource.getrlimit(getattr(resource,k))) for k in expected}
    assert effective==expected,'worker must be launched through the authorized OS limits'
    emit({'kind':'header','tag':args.tag,'input_sha256':hashlib.sha256(raw).hexdigest(),
          'selected_targets':targets,'effective_os_limits':effective,
          'search_limits':{'shared_seconds':5,'max_rules':20000,'max_states':1000,'word_growth':6},
          'quotient_relations':len(relations)})
    def expired(signum,frame):
        raise SearchBudgetExpired()
    signal.signal(signal.SIGALRM,expired)
    started=time.monotonic();deadline=started+5
    fixed=None;finished=set();expired_budget=False
    signal.setitimer(signal.ITIMER_REAL,5)
    try:
        fixed=PilotSearch(relations,seconds=5,max_rules=20000,max_states=1000)
        fixed.deadline=min(fixed.deadline,deadline)
        emit({'kind':'index','rule_instances':fixed.rule_count,'rule_budget_reached':fixed.build_limit,
              'elapsed_seconds':time.monotonic()-started})
        for target in targets:
            answer=fixed.prove(problem['relators'][target-1])
            emit({'kind':'target','target':target,'answer':answer,'elapsed_seconds':time.monotonic()-started})
            finished.add(target)
    except SearchBudgetExpired:
        expired_budget=True
    finally:
        signal.setitimer(signal.ITIMER_REAL,0)
    for target in targets:
        if target not in finished:
            emit({'kind':'target','target':target,'answer':{'status':'unresolved','reason':'shared_search_time_limit'},
                  'elapsed_seconds':time.monotonic()-started})
    emit({'kind':'summary','search_wall_seconds':time.monotonic()-started,
          'shared_time_limit_reached':expired_budget,'rule_instances':fixed.rule_count if fixed else None,
          'rule_budget_reached':fixed.build_limit if fixed else None,'index_builds':1})


if __name__=='__main__':
    main()
