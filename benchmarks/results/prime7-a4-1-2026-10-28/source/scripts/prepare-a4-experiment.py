#!/usr/bin/env python3
"""Static inspection and finite-field analysis ONLY; no arithmetic proof search."""
import argparse
import gzip
import hashlib
import importlib.util
import json
from pathlib import Path
import sys

ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT))
from experiments.certified_power import power_form
from experiments.relation_span import reduce_word


def module(name,path):
    spec=importlib.util.spec_from_file_location(name,ROOT/path);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);return m


def solve(rows,target,p=7):
    """Linear combination of arbitrary-width rows, or None."""
    basis={}
    for i,row in enumerate(rows):
        w=[x%p for x in row];c=[int(i==j) for j in range(len(rows))]
        for pivot,(r,d) in sorted(basis.items()):
            t=w[pivot];w=[(a-t*b)%p for a,b in zip(w,r)];c=[(a-t*b)%p for a,b in zip(c,d)]
        pivot=next((j for j,x in enumerate(w) if x),None)
        if pivot is not None:
            s=pow(w[pivot],-1,p);basis[pivot]=([x*s%p for x in w],[x*s%p for x in c])
    w=[x%p for x in target];c=[0]*len(rows)
    for pivot,(r,d) in sorted(basis.items()):
        t=w[pivot];w=[(a-t*b)%p for a,b in zip(w,r)];c=[(a+t*b)%p for a,b in zip(c,d)]
    return (None if any(w) else c),len(basis)


def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--output',type=Path,required=True);a=p.parse_args();a.output.mkdir(parents=True,exist_ok=False)
    frozen=(ROOT/'docs/evidence/prime7-spanning-preparation/fixed-quotient-blueprint.json.gz').read_bytes()
    source=json.loads(gzip.decompress(frozen));q=source['quotient_relators'];rs=source['problem']['relators'];ss=source['problem']['candidates']
    assert len(q)==236 and rs[6]==[5]*4 and q[198]==[5]*28
    original=module('independent','scripts/check-relation-span-certificate.py');assert original.verify(source)['certified_targets']==[3,5,9,12,15]
    inventory=json.loads((ROOT/'docs/evidence/prime7-spanning-preparation/inventory.json').read_text())
    M,Z=inventory['candidate_occurrence_matrix'],inventory['existing_zero_identity_matrix'];e7=[int(i==6) for i in range(32)]
    witness,rank=solve(M+Z,e7);assert witness is None and rank==17
    # Construct a dual functional annihilating the known rows, with value 1 on e7.
    equations=M+Z+[e7];rhs=[0]*(len(equations)-1)+[1]
    dual,_=solve([[r[j] for r in equations] for j in range(32)],rhs)
    assert dual is not None and all(sum(x*y for x,y in zip(row,dual))%7==0 for row in M+Z) and dual[6]==1
    exponents=lambda w:[sum(1 if x==j else -1 if x==-j else 0 for x in w) for j in range(1,7)]
    candidate_exponents=[exponents(w) for w in ss]
    necessary,eps_rank=solve(candidate_exponents,exponents(rs[6]));assert necessary is not None and eps_rank==6
    full=[];pure=[]
    for i,w in enumerate(q,1):
        root,e,c=power_form(w)
        if root==(-5,):pure.append(dict(index=i,exponent=e,conjugator=list(c)))
        full.append(dict(index=i,label=source['quotient_labels'][i-1],word=w,length=len(w),
                         a_occurrences=sum(abs(x)==5 for x in w),exponents=exponents(w),
                         canonical_cyclic_root=list(root),power_exponent=e,normalizing_conjugator=list(c)))
    assert [r['index'] for r in pure]==[199]
    core=[199]+list(range(225,237))+[7,39,71,103,167,132,139]
    # All fixed Q rows are input; power recognition uses a frozen 20-row view.
    order=list(range(225,237))+[199]+sorted([i for i in range(1,237) if i not in list(range(225,237))+[199]],key=lambda i:(len(q[i-1]),i))
    plan=dict(status='PREPARED_BEFORE_THE_ONE_SEARCH',target=7,target_word=rs[6],full_quotient_rows=236,
              input_sha256=hashlib.sha256(frozen).hexdigest(),power_indices=core,completion_input_order=order,
              known_seed_targets=[3,5,9,12,15],central_square_equations=20,
              method='power compiler on fixed 20-row view; then counted completion on all 236 rows with certified seeds; no BFS; no cyclic seed expansion',
              limits=dict(shared_search_seconds=5,power_seconds=1,memory_bytes=536870912,cpu_seconds=6,wall_seconds=10,
                          output_bytes=8388608,completion_rules=256,queued_rule_pair_jobs=4000,
                          word_overlap_length=512,proof_factors=2000,reduction_steps=2000),
              completion_inputs_include_target_as_relation=False,
              note='Only original Q rows and certificate-backed consequences may be seeded. a^4 is a target, not an input relation. All overlap placements are counted separately.')
    (a.output/'plan.json').write_text(json.dumps(plan,indent=2)+'\n')
    analysis=dict(kind='STATIC_WORD_INSPECTION_AND_F7_LINEAR_ALGEBRA_ONLY',quotient_inventory=full,pure_a_power_rows=pure,
                  candidate_exponents=candidate_exponents,necessary_exponent_witness=necessary,candidate_exponent_rank=eps_rank,
                  known_row_rank=rank,target_not_in_known_row_span=True,dual_functional_not_a_nonmembership_obstruction=dual)
    (a.output/'analysis.json').write_text(json.dumps(analysis,indent=2)+'\n')
    print('Static inspection: all 236 rows; only Q199 is conjugate to a pure a power. Candidate exponent rank 6; existing row rank 17, e7 not covered. No search run.')


if __name__=='__main__':main()
