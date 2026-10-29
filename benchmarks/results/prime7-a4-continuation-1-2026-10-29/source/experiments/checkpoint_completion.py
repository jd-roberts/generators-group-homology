"""Load checked rules verbatim; run ONLY a preselected immutable job list.

No input normalization or automatic job replenishment. The inherited equation
operations remain unchanged. A full job list consumes the cumulative queue
budget, so new equations may simplify later jobs but create no extra jobs.
"""
import heapq
from experiments.certified_completion import Budget
from experiments.counted_completion import CountedCompletion


class CheckpointCompletion(CountedCompletion):
    def __init__(self,rules,jobs,*,seconds=5,emit=lambda event:None):
        self.frozen_jobs=False
        self.emit=lambda event:None
        super().__init__(6,[],seconds=seconds,max_rules=256,max_pairs=4000,
                         max_word=512,max_factors=2000,max_steps=2000)
        if not len(rules)<=256 or not len(jobs)<=4000 or len(set(map(tuple,jobs)))!=len(jobs):
            raise ValueError('checkpoint exceeds limits or repeats jobs')
        loaded=[]
        for index,r in enumerate(rules):
            lhs,rhs=tuple(r['lhs']),tuple(r['rhs'])
            if r['id']!=index or not lhs or (len(lhs),lhs)<=(len(rhs),rhs):raise ValueError('invalid checkpoint orientation/index')
            if max(len(lhs),len(rhs))>512 or len(r['factors'])>2000:raise ValueError('oversize checkpoint')
            loaded.append(dict(r,lhs=lhs,rhs=rhs,factors=[(tuple(q),i,s) for q,i,s in r['factors']]))
        for i,j in jobs:
            if not 0<=i<=j<len(loaded):raise ValueError('invalid job')
        self.rules=loaded;self.equations={(r['lhs'],r['rhs']) for r in loaded}
        self.pending=[(0,k,tuple(pair)) for k,pair in enumerate(jobs)];heapq.heapify(self.pending)
        self.queued=set(map(tuple,jobs));self.serial=len(jobs);self.pairs=0
        self.max_queue=len(jobs);self.max_equation=0;self.reductions=0
        self.truncated=set();self.jobs_completed=0;self.initial_count=len(loaded)
        self.frozen_jobs=True
        self.truncated.add('fixed_job_selection')
        self.emit=emit

    def add_rule(self,lhs,rhs,proof,origin):
        if not self.frozen_jobs:
            return super().add_rule(lhs,rhs,proof,origin)
        key=(lhs,rhs)
        if key in self.equations:return
        if len(self.rules)>=self.limits['max_rules']:raise Budget('rule_limit')
        self.equations.add(key)
        rule=dict(id=len(self.rules),lhs=lhs,rhs=rhs,factors=proof,origin=origin)
        self.rules.append(rule)
        self.emit(dict(kind='new_rule',rule=rule))

    def overlaps(self,a,b):
        before=self.accounting();completed=False
        self.emit(dict(kind='job_start',ordinal=self.pairs-1,pair=[a['id'],b['id']]))
        try:
            super().overlaps(a,b);completed=True;self.jobs_completed+=1
        finally:
            after=self.accounting()
            delta={k:after[k]-before[k] for k in ['offset_tests','compatible_overlap_placements','submitted_overlap_equations','oversize_overlap_placements']}
            self.emit(dict(kind='job_end',ordinal=self.pairs-1,pair=[a['id'],b['id']],completed=completed,delta=delta))
