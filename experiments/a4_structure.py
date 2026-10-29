"""Fixed algebraic lemmas for a^2 centrality. No word search or completion.

All returned products use ORIGINAL Q indices. t=a^2, c=z^-3*b1*z^3,
b=c*a^-1. C(t,g)=t*g*t^-1*g^-1 is the standard commutator word.
"""
from experiments.relation_span import reduce_word as red, inverse as inv
from experiments.certified_power import conjugate, invert


def standard(t,g):return red(tuple(t)+tuple(g)+inv(t)+inv(g))


def central_square_proofs():
    a,z,c=(5,),(1,),(-1,)*3+(6,)+(1,)*3
    b=red(c+(-5,))
    # r=u*a*u*a^-1. When r=1: C(a^2,u)=r^-1*(u*a)r(u*a)^-1.
    proofs={1:[((),225,-1),((1,5),225,1)],
            2:[((),227,-1),((2,5),227,1)]}
    # When r is merely central: C(a^2,u)=u*[u,r]*u^-1 *
    # (u*a)*[a,r]*(u*a)^-1. No raw r is killed here.
    proofs[3]=[((3,),75,1),((3,5),139,1)]
    proofs[4]=[((4,),100,1),((4,5),132,1)]
    # S=Q228=b^3*a^2. C(a^2,c)=C(a^2,b)
    # = b^-3*S*b^3 * b^-2*S^-1*b^2.
    cp=[(inv(b)*3,228,1),(inv(b)*2,228,-1)]
    z3=[]
    for j in range(3):z3+=conjugate(z*j,proofs[1])
    zm3=conjugate(inv(z)*3,invert(z3))
    proofs[6]=z3+conjugate(z*3,cp)+conjugate(red(z*3+c),zm3)
    return proofs


def commuting_equations():
    """All four sign choices for each non-a generator; 20 equations total."""
    t=(5,5);result=[]
    for g,base in sorted(central_square_proofs().items()):
        for st in (1,-1):
            pt=base if st==1 else conjugate(inv(t),invert(base))
            tt=t if st==1 else inv(t)
            for sg in (1,-1):
                gg=(sg*g,)
                proof=pt if sg==1 else conjugate((-g,),invert(pt))
                result.append(dict(lhs=tt+gg,rhs=gg+tt,factors=proof,
                                   origin='certified_a2_centrality',generator=g,t_sign=st,g_sign=sg))
    return result
