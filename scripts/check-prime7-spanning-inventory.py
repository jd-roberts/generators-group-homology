#!/usr/bin/env python3
"""Replay source certificates and check static/conditional span witnesses only."""
import argparse
import gzip
import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]


def rank(rows):
    matrix = [r[:] for r in rows]
    count = 0
    for column in range(32):
        pivot = next((i for i in range(count,len(matrix)) if matrix[i][column] % 7),None)
        if pivot is None:
            continue
        matrix[count],matrix[pivot] = matrix[pivot],matrix[count]
        scale=pow(matrix[count][column],-1,7)
        matrix[count]=[x*scale%7 for x in matrix[count]]
        for i in range(count+1,len(matrix)):
            coefficient=matrix[i][column]
            matrix[i]=[(a-coefficient*b)%7 for a,b in zip(matrix[i],matrix[count])]
        count+=1
    return count


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--gap',default='gap')
    parser.add_argument('--directory',type=Path,default=ROOT/'docs/evidence/prime7-spanning-preparation')
    args=parser.parse_args()
    report=json.loads((args.directory/'inventory.json').read_text())
    for path,digest in report['source_sha256'].items():
        assert hashlib.sha256((ROOT/path).read_bytes()).hexdigest()==digest,path
    check=subprocess.run([sys.executable,str(ROOT/'scripts/verify-prime7-presentation.py'),'--gap',args.gap],cwd=ROOT,capture_output=True,text=True,timeout=12)
    assert check.returncode==0 and not check.stderr and 'PASS:' in check.stdout
    archive=json.loads(gzip.decompress((ROOT/'docs/evidence/prime7-normal-closure-certificates.json.gz').read_bytes()))['groups']
    def counts(proof,n):
        return [sum(sign for _,index,sign in proof if index==i+1)%7 for i in range(n)]
    M=[counts(archive['b0_twelve']['proofs'][str(i)],32) for i in range(1,13)]
    F=[counts(archive['forward_relators']['proofs'][str(i)],32) for i in range(1,65)]
    zero=[]
    for i in range(32):
        b=counts(archive['backward_relators']['proofs'][str(i+1)],64)
        zero.append([(int(i==j)-sum(b[k]*F[k][j] for k in range(64)))%7 for j in range(32)])
    for i in range(14):
        b=counts(archive['composites']['proofs'][str(i+1)],64)
        zero.append([sum(b[k]*F[k][j] for k in range(64))%7 for j in range(32)])
    assert M==report['candidate_occurrence_matrix'] and zero==report['existing_zero_identity_matrix']
    for key,w in report['covered_targets'].items():
        coefficients=w['candidate_coefficients']+w['identity_coefficients']
        assert len(coefficients)==58
        assert [sum(c*r[j] for c,r in zip(coefficients,M+zero))%7 for j in range(32)]==[int(j==int(key)-1) for j in range(32)]
    future=report['sufficient_future_targets']
    extra=[[int(j==i-1) for j in range(32)] for i in future]
    assert rank(M)==12 and rank(zero)==5 and rank(M+zero)==17
    assert len(future)==15 and rank(M+zero+extra)==32
    assert len(report['conditional_completion_witnesses'])==32
    for i,coefficients in enumerate(report['conditional_completion_witnesses']):
        assert len(coefficients)==73
        assert [sum(c*r[j] for c,r in zip(coefficients,M+zero+extra))%7 for j in range(32)]==[int(i==j) for j in range(32)]
    spec=importlib.util.spec_from_file_location('independent_checker',ROOT/'scripts/check-relation-span-certificate.py')
    checker=importlib.util.module_from_spec(spec);spec.loader.exec_module(checker)
    blueprint=json.loads(gzip.decompress((args.directory/'fixed-quotient-blueprint.json.gz').read_bytes()))
    status=checker.verify(blueprint)
    assert status['certified_targets']==[3,5,9,12,15] and status['spanning']=='unresolved'
    words=json.loads((ROOT/'docs/evidence/prime7-presentation-words.json').read_text())
    assert blueprint['problem']['relators']==words['reduced_relators']
    assert blueprint['problem']['candidates']==words['b0_twelve']
    print('PASS: source identities, five explicit quotient certificates, ranks 12/5/17, and conditional completion witnesses.')
    print('FUTURE TARGETS ONLY:',','.join(map(str,future)))
    print('Full spanning remains UNVERIFIED; none of these future targets was searched here.')


if __name__=='__main__':
    main()
