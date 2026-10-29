#!/usr/bin/env python3
"""Check a finite proof certificate, without importing any search code.

Unit equations are checked by clearing denominators and dividing INTEGER
polynomials by Phi_7. Coordinates are ascending monomial coefficients.
No enumeration, GAP, KBMAG, or floating-point arithmetic is used.
"""
import json
from collections import defaultdict
from fractions import Fraction
from itertools import combinations
from pathlib import Path


def trim(a):
    while len(a)>1 and not a[-1]: a.pop()
    return a


def add(a,b):
    return trim([(a[i] if i<len(a) else 0)+(b[i] if i<len(b) else 0)
                 for i in range(max(len(a),len(b)))])


def mul(a,b):
    c=[0]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b): c[i+j]+=x*y
    return trim(c)


def power(a,n):
    assert n>=0
    r=[1]
    for _ in range(n): r=mul(r,a)
    return r


def divide_phi(a):
    a=a[:]; q=[0]*max(1,len(a)-6)
    for k in range(len(a)-1,5,-1):
        c=a[k]; q[k-6]=c
        for j in range(7): a[k-j]-=c
    return trim(q),trim(a[:6])


def monomial(sign,k,exps,gens):
    r=[0]*k+[sign]
    for e,g in zip(exps,gens): r=mul(r,power(g,e))
    return r


def equation_certificate(pair,gens):
    x,y=pair['x'],pair['one_minus_x']
    ex,ey=x['coordinates'][1:],y['coordinates'][1:]
    assert len(ex)==len(ey)==len(gens)
    low=[min(0,a,b) for a,b in zip(ex,ey)]
    denom=monomial(1,0,[-a for a in low],gens)
    nx=monomial(x['sign'],x['coordinates'][0],[a-b for a,b in zip(ex,low)],gens)
    ny=monomial(y['sign'],y['coordinates'][0],[a-b for a,b in zip(ey,low)],gens)
    residual=add(add(denom,[-a for a in nx]),[-a for a in ny])
    q,r=divide_phi(residual)
    assert r==[0], 'not an exact unit equation'
    row=[(x['coordinates'][i]*y['coordinates'][j]-x['coordinates'][j]*y['coordinates'][i])%7
         for i,j in combinations(range(len(ex)+1),2)]
    return {'cleared_polynomial':residual,'phi7_quotient':q,'exterior_row':row}


def rank(a,p=7):
    a=[[x%p for x in row] for row in a]; r=0
    for j in range(len(a[0])):
        k=next((k for k in range(r,len(a)) if a[k][j]),None)
        if k is None: continue
        a[k],a[r]=a[r],a[k]
        c=pow(a[r][j],-1,p); a[r]=[c*x%p for x in a[r]]
        for k in range(r+1,len(a)):
            c=a[k][j]; a[k]=[(x-c*y)%p for x,y in zip(a[k],a[r])]
        r+=1
        if r==len(a): break
    return r


def det(a):
    a=[list(map(Fraction,row)) for row in a]; d=Fraction(1)
    for j in range(len(a)):
        k=next(k for k in range(j,len(a)) if a[k][j])
        if k!=j: a[k],a[j]=a[j],a[k]; d=-d
        t=a[j][j]; d*=t
        for k in range(j+1,len(a)):
            c=a[k][j]/t
            a[k]=[x-c*y for x,y in zip(a[k],a[j])]
    assert d.denominator==1
    return int(d)


def check_bar_additivity():
    # Work in a free abelian group on three generators, in additive notation.
    g,h,k=(1,0,0),(0,1,0),(0,0,1)
    plus=lambda a,b:tuple(x+y for x,y in zip(a,b))
    actual=defaultdict(int)
    for c,(a,b,z) in [(-1,(g,h,k)),(1,(g,k,h)),(-1,(k,g,h))]:
        for sign,pair in [(1,(b,z)),(-1,(plus(a,b),z)),(1,(a,plus(b,z))),(-1,(a,b))]:
            actual[pair]+=c*sign
    expected=defaultdict(int)
    for c,a,b in [(1,plus(g,h),k),(-1,g,k),(-1,h,k)]:
        expected[(a,b)]+=c; expected[(b,a)]-=c
    assert {x:c for x,c in actual.items() if c}=={x:c for x,c in expected.items() if c}


def main():
    root=Path(__file__).resolve().parent
    data=json.loads((root/'toral-certificates.json').read_text())
    eps=[[1,-1],[1,0,-1],[1,0,0,-1]]
    pi1,pi2=[1,1,0,1],[1,0,1,1]
    ca=[equation_certificate(x,eps) for x in data['equations_A']]
    cb=[equation_certificate(x,eps+[pi1,pi2]) for x in data['equations_B']]
    a=[x['exterior_row'] for x in ca]; b=[x['exterior_row'] for x in cb]
    assert rank(a)==6 and det(a)%7==1
    assert rank(b)==13
    witness=data['selected_cycle_witness_A']
    assert [sum(c*row[j] for c,row in zip(witness,a))%7 for j in range(6)]==[0,0,0,1,0,0]
    # Residue logs of (zeta,epsilon_1,epsilon_2,epsilon_3) relative to zeta.
    # These are checked in the two cubic F_2 quotients below.
    def f8mul(x,y,poly):
        out=0
        while y:
            if y&1: out^=x
            y>>=1; x<<=1
            if x&8: x^=poly
        return out
    logs=[]
    for poly in (0b1011,0b1101):
        powers=[1]
        for _ in range(6): powers.append(f8mul(powers[-1],2,poly))
        assert len(set(powers))==7 and f8mul(powers[-1],2,poly)==1
        log={x:i for i,x in enumerate(powers)}
        logs.append([1]+[log[1^powers[i]] for i in (1,2,3)])
        if poly==0b1011:
            assert 1^powers[1]^powers[3]==0
            assert log[1^powers[2]^powers[3]]==4
        else:
            assert 1^powers[2]^powers[3]==0
            assert log[1^powers[1]^powers[3]]==6
    # δ(t(a,b))=2*(v(a) log(b_unit)-v(b) log(a_unit)).
    columns=[]
    for i,j in combinations(range(6),2):
        v=[]
        for q in range(2):
            vals=[0,0,0,0,int(q==0),int(q==1)]
            unitlogs=logs[q]+([0,4] if q==0 else [6,0])
            v.append(2*(vals[i]*unitlogs[j]-vals[j]*unitlogs[i])%7)
        columns.append(v)
    tame=[list(x) for x in zip(*columns)]
    assert rank(tame)==2
    assert all(sum(x*y for x,y in zip(row,t))%7==0 for row in b for t in tame)
    # Product and Galois identities in the field, checked as integer polynomials.
    polynomials=[add(mul(pi1,pi2),[0,0,0,-2]),
                 add([1,0,0,1,0,0,0,0,0,1],[-x for x in pi2]),
                 add([1,0,1,0,0,0,1],[-x for x in mul([0]*6+[1],pi1)])]
    assert all(divide_phi(p)[1]==[0] for p in polynomials)
    check_bar_additivity()
    minkowski_bound=Fraction(4,3)**3*Fraction(720,6**6)*130
    assert minkowski_bound<5
    print(json.dumps({'verified':True,'A_rank':rank(a),'A_integer_determinant':det(a),
                      'A_selected_cycle_witness':witness,'B_rank':rank(b),
                      'B_tame_matrix':tame,'residue_unit_logs':logs,
                      'A_polynomial_certificates':ca,'B_polynomial_certificates':cb,
                      'bar_additivity_checked':True,
                      'minkowski_upper_bound':[minkowski_bound.numerator,minkowski_bound.denominator]},indent=2))


if __name__=='__main__': main()
