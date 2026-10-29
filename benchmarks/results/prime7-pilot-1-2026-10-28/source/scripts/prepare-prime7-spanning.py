#!/usr/bin/env python3
"""Static inventory and linear consequences of existing certificates; NO search."""
import argparse
import gzip
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from experiments.relation_span import quotient


def counts(proof, n):
    result = [0] * n
    for _, index, sign in proof:
        result[index - 1] += sign
    return [x % 7 for x in result]


def representation(rows, target):
    """Return independently checkable row-combination coordinates, or None."""
    basis = {}
    for i, row in enumerate(rows):
        v, coefficients = row[:], [int(i == j) for j in range(len(rows))]
        for pivot, (b, c) in sorted(basis.items()):
            scale = v[pivot]
            v = [(a - scale * x) % 7 for a, x in zip(v, b)]
            coefficients = [(a - scale * x) % 7 for a, x in zip(coefficients, c)]
        pivot = next((j for j, x in enumerate(v) if x), None)
        if pivot is not None:
            scale = pow(v[pivot], -1, 7)
            basis[pivot] = ([x * scale % 7 for x in v], [x * scale % 7 for x in coefficients])
    v, result = target[:], [0] * len(rows)
    for pivot, (b, c) in sorted(basis.items()):
        scale = v[pivot]
        v = [(a - scale * x) % 7 for a, x in zip(v, b)]
        result = [(a + scale * x) % 7 for a, x in zip(result, c)]
    if any(v):
        return None, len(basis)
    assert [sum(c * row[j] for c, row in zip(result, rows)) % 7 for j in range(32)] == target
    return result, len(basis)


def named(word):
    names = ['z','u1','u2','u3','a','b1']
    result = []
    for x in word:
        if result and result[-1][0] == abs(x):
            result[-1][1] += 1 if x > 0 else -1
        else:
            result.append([abs(x), 1 if x > 0 else -1])
    return '*'.join(names[i-1] + (f'^{n}' if n != 1 else '') for i,n in result if n) or '1'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--gap', default='gap')
    parser.add_argument('--output', type=Path, required=True, help='new directory; never overwrite')
    args = parser.parse_args()
    started = time.monotonic()
    args.output.mkdir(parents=True, exist_ok=False)
    # Replay exact source identities/maps first, with its existing bounded tool.
    command = [sys.executable, str(ROOT/'scripts/verify-prime7-presentation.py'), '--gap', args.gap]
    check = subprocess.run(command, cwd=ROOT, text=True, capture_output=True, timeout=12)
    assert check.returncode == 0 and not check.stderr and 'PASS:' in check.stdout, (check.stdout,check.stderr)
    words = json.loads((ROOT/'docs/evidence/prime7-presentation-words.json').read_text())
    archive = json.loads(gzip.decompress((ROOT/'docs/evidence/prime7-normal-closure-certificates.json.gz').read_bytes()))
    groups = archive['groups']
    rs, ss = words['reduced_relators'], words['b0_twelve']
    M = [counts(groups['b0_twelve']['proofs'][str(i)],32) for i in range(1,13)]
    forward = [counts(groups['forward_relators']['proofs'][str(i)],32) for i in range(1,65)]
    identities = []
    for j in range(32):
        backward = counts(groups['backward_relators']['proofs'][str(j+1)],64)
        identities.append([(int(j==k)-sum(backward[i]*forward[i][k] for i in range(64)))%7 for k in range(32)])
    for j in range(14):
        composite = counts(groups['composites']['proofs'][str(j+1)],64)
        identities.append([sum(composite[i]*forward[i][k] for i in range(64))%7 for k in range(32)])
    covered, inventory = {}, []
    for j,r in enumerate(rs):
        e = [int(j==k) for k in range(32)]
        witness, combined_rank = representation(M+identities,e)
        if witness is not None:
            covered[str(j+1)] = {'candidate_coefficients': witness[:12], 'identity_coefficients': witness[12:]}
        inventory.append({'relator':j+1,'word':named(r),'length':len(r),
                          'existing_span_certificate':'direct candidate' if j+1 in [3,5,9] else 'verified linear consequence' if witness is not None else 'unresolved',
                          'recommended_search_priority':0 if witness is not None else len(r)})
    # Select a sufficient future target set; these extra unit rows are
    # HYPOTHESES until certified, not additional established relations.
    extended = M + identities
    complement = []
    for row in sorted(inventory,key=lambda r:(r['length'],r['relator'])):
        j=row['relator']-1
        e=[int(j==k) for k in range(32)]
        witness,_=representation(extended,e)
        if witness is None:
            complement.append(j+1);extended.append(e)
    completion_witnesses=[]
    for j in range(32):
        witness,full_rank=representation(extended,[int(j==k) for k in range(32)])
        assert witness is not None and full_rank==32
        completion_witnesses.append(witness)
    _, candidate_rank = representation(M,[0]*32)
    _, identity_rank = representation(identities,[0]*32)
    qrels, labels = quotient(6,7,rs,ss)
    memberships = [[[archive['conjugators'][q],i,s] for q,i,s in groups['b0_twelve']['proofs'][str(j)]] for j in range(1,13)]
    problem = {'name':'prime7_b0_FIXED_QUOTIENT_BLUEPRINT_ONLY','rank':6,'prime':7,
               'relators':rs,'candidates':ss,'candidate_membership':memberships}
    targets = [{'status':'unresolved','reason':'arithmetic search not authorized or launched'} for r in rs]
    for rj,si in [(3,2),(5,3),(9,1)]:
        targets[rj-1] = {'status':'certified','factors':[[[],224+si,1]],'states':0}
    # Elementary proof, no search: S1=R9=z*a*z*a^-1 makes a invert z.
    # K=[a,z^7] is Q140. Thus z^14 = (a*z^7 K^-1 (a*z^7)^-1)
    # times product_{j=1}^7 z^-j*S1*z^j. Then z^7=(z^14)^4*(z^49)^-1.
    square = [[[5]+[1]*7,140,-1]] + [[[-1]*j,225,1] for j in range(1,8)]
    targets[11] = {'status':'certified','factors':square*4+[[[],204,-1]],'states':0}
    # Isolate the single unconjugated R15 factor in the existing S4 identity.
    source = memberships[3]
    assert sum(index==15 for _,index,_ in source)==1
    position = next(i for i,(_,index,_) in enumerate(source) if index==15)
    assert source[position]==[[],15,1]
    def invert_proof(proof):
        return [[q,i,-sign] for q,i,sign in reversed(proof)]
    def expand_old(proof):
        result=[]
        for q,index,sign in proof:
            if index not in (9,12): raise ValueError('unexpected isolation premise')
            inner=targets[index-1]['factors']
            if sign<0: inner=invert_proof(inner)
            for v,i,t in inner:
                # Local free cancellation, not a search or word-problem call.
                stack=[]
                for x in q+v:
                    if stack and stack[-1]==-x: stack.pop()
                    else: stack.append(x)
                result.append([stack,i,t])
        return result
    targets[14] = {'status':'certified',
        'factors':invert_proof(expand_old(source[:position]))+[[[],228,1]]+invert_proof(expand_old(source[position+1:])),
        'states':0}
    blueprint = {'problem':problem,'quotient_relators':[list(r) for r in qrels],
                 'quotient_labels':labels,'targets':targets,
                 'notice':'STATIC ONLY. No arithmetic proof search or completion has run. Five targets have explicit products, compiled by elementary algebra and existing membership identities.'}
    import importlib.util
    spec=importlib.util.spec_from_file_location('independent_span_checker',ROOT/'scripts/check-relation-span-certificate.py')
    checker=importlib.util.module_from_spec(spec);spec.loader.exec_module(checker)
    status=checker.verify(blueprint)
    assert status['certified_targets']==[3,5,9,12,15] and status['spanning']=='unresolved'
    for row in inventory:
        if row['relator'] in [12,15]: row['existing_span_certificate']='explicit quotient product and linear consequence'
    (args.output/'fixed-quotient-blueprint.json.gz').write_bytes(gzip.compress((json.dumps(blueprint,separators=(',',':'))+'\n').encode(),mtime=0))
    source_paths = ['docs/evidence/prime7-presentation-words.json','docs/evidence/prime7-normal-closure-certificates.json.gz',
                    'tests/fixtures/roberts-v1-proposition32.g','tests/fixtures/roberts-v1-prime7-words.g',
                    'scripts/prepare-prime7-spanning.py','experiments/relation_span.py','scripts/check-relation-span-certificate.py']
    report = {'scope':'static free identities and F7 linear algebra only; no arithmetic search or KBMAG',
              'prior_certificate_replay_command':command,'prior_certificate_replay_stdout':check.stdout,
              'source_sha256':{p:hashlib.sha256((ROOT/p).read_bytes()).hexdigest() for p in source_paths},
              'quotient':{'stored_relations':len(qrels),'nonempty_relations':sum(bool(r) for r in qrels),
                          'commutators':192,'powers':32,'candidates':12,'total_length':sum(map(len,qrels)),
                          'maximum_length':max(map(len,qrels))},
              'candidate_occurrence_matrix':M,'existing_zero_identity_matrix':identities,
              'candidate_occurrence_rank':candidate_rank,'zero_identity_rank':identity_rank,
              'combined_rank':combined_rank,'formal_directions_unsettled':32-combined_rank,
              'covered_targets':covered,'inventory':inventory,
              'sufficient_future_targets':complement,'conditional_completion_witnesses':completion_witnesses,
              'completion_witness_notice':'Last columns are NOT established zero relations; they are the unit vectors of the future target list. These witnesses justify sufficiency only after those targets are certified.',
              'recommended_remaining_order':[r['relator'] for r in sorted(inventory,key=lambda r:(r['length'],r['relator'])) if r['existing_span_certificate']=='unresolved'],
              'wall_seconds':round(time.monotonic()-started,6),
              'not_proved':'Full spanning; formal residual dimension is not a lower bound on the true quotient.'}
    (args.output/'inventory.json').write_text(json.dumps(report,indent=2)+'\n')
    print('STATIC ONLY:',len(qrels),'quotient rows; targets with existing span proofs:',list(covered))
    print('Ranks: candidates',candidate_rank,'known zero identities',identity_rank,'combined',combined_rank,'remaining formal coordinates',32-combined_rank)
    print('No arithmetic search or completion executed.')


if __name__ == '__main__':
    main()
