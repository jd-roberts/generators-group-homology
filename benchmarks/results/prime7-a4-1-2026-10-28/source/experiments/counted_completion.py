"""Experimental subclass: count overlap placements without editing old evidence.

The parent retains its proved equation/proof operations and queue strategy.
This copies ONLY overlap enumeration to expose finer accounting. Comparisons
on small fixtures require identical retained equations/proofs to the parent.
"""
from experiments.certified_completion import Completion, conjugate, invert


class CountedCompletion(Completion):
    def __init__(self,*args,**kwargs):
        self.offset_tests=0
        self.compatible_overlap_placements=0
        self.submitted_overlap_equations=0
        self.oversize_overlap_placements=0
        super().__init__(*args,**kwargs)

    def overlaps(self,a,b):
        u,v=a['lhs'],b['lhs']
        for offset in range(1-len(v),len(u)):
            self.tick();self.offset_tests+=1
            low,high=min(0,offset),max(len(u),offset+len(v))
            start,stop=max(0,offset),min(len(u),offset+len(v))
            if any(u[j]!=v[j-offset] for j in range(start,stop)):continue
            self.compatible_overlap_placements+=1
            common=tuple(u[j] if 0<=j<len(u) else v[j-offset] for j in range(low,high))
            if len(common)>self.limits['max_word']:
                self.oversize_overlap_placements+=1
                self.truncated.add('overlap_word_limit');continue
            pa,pb=-low,offset-low
            left=common[:pa]+a['rhs']+common[pa+len(u):]
            right=common[:pb]+b['rhs']+common[pb+len(v):]
            proof=invert(conjugate(common[:pa],a['factors']))+conjugate(common[:pb],b['factors'])
            self.submitted_overlap_equations+=1
            self.equation(left,right,proof,'critical_pair')

    def accounting(self):
        return dict(rule_pair_jobs_processed=self.pairs,rule_pair_jobs_queued=len(self.queued),
                    offset_tests=self.offset_tests,compatible_overlap_placements=self.compatible_overlap_placements,
                    submitted_overlap_equations=self.submitted_overlap_equations,
                    oversize_overlap_placements=self.oversize_overlap_placements,
                    compatible_placements_not_submitted=self.compatible_overlap_placements-self.submitted_overlap_equations-self.oversize_overlap_placements)
