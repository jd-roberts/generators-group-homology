#!/usr/bin/env python3
"""Exact finite arithmetic diagnostics; no group rewriting or homology oracle.

Run from any directory. Output is deterministic JSON on stdout.
The formal torus module is NOT asserted to surject onto arithmetic H_2.
"""
import itertools
import json


def mm(a, b, p=7):
    return [[sum(x*y for x, y in zip(row, col)) % p
             for col in zip(*b)] for row in a]


def eye(n):
    return [[int(i == j) for j in range(n)] for i in range(n)]


def rank(a, p=7):
    a = [list(row) for row in a]
    r = 0
    for j in range(len(a[0])):
        pivot = next((i for i in range(r, len(a)) if a[i][j] % p), None)
        if pivot is None:
            continue
        a[r], a[pivot] = a[pivot], a[r]
        c = pow(a[r][j] % p, -1, p)
        a[r] = [x*c % p for x in a[r]]
        for i in range(len(a)):
            if i != r:
                c = a[i][j] % p
                a[i] = [(x-c*y) % p for x, y in zip(a[i], a[r])]
        r += 1
        if r == len(a):
            break
    return r


def eigenspace_dimensions(a, p=7):
    n = len(a)
    return {str(t): n-rank([[a[i][j]-t*int(i == j)
                            for j in range(n)] for i in range(n)], p)
            for t in range(1, p)}


def torus_action(k):
    # Columns: zeta -> zeta^k, epsilon_i -> 1-zeta^(ki).
    # epsilon_(7-j) = -zeta^(-j) epsilon_j; -1 dies in H_1(-;F_7).
    a = [[0]*4 for _ in range(4)]
    a[0][0] = k
    for i in range(1, 4):
        j = (k*i) % 7
        if j > 3:
            j = 7-j
            a[0][i] = -j % 7
        a[j][i] = 1
    return a


def wedge2(a):
    pairs = list(itertools.combinations(range(len(a)), 2))
    return [[(a[i][k]*a[j][l]-a[i][l]*a[j][k]) % 7
             for k, l in pairs] for i, j in pairs]


def order_mod(a, p):
    for n in range(1, p):
        if pow(a, n, p) == 1:
            return n
    raise ValueError("not a unit")


def main():
    # Polynomial coefficients are in ascending degree order.
    f, g = [1, 1, 0, 1], [1, 0, 1, 1]
    product = [0]*7
    for i, x in enumerate(f):
        for j, y in enumerate(g):
            product[i+j] ^= x*y
    assert product == [1]*7
    assert all(sum(c*pow(x, i) for i, c in enumerate(h)) % 2
               for h in (f, g) for x in (0, 1))  # Cubics have no roots.
    actions = {k: torus_action(k) for k in range(1, 7)}
    assert actions[1] == eye(4)
    for k in actions:
        for l in actions:
            assert mm(actions[k], actions[l]) == actions[k*l % 7]
    a = actions[3]  # 3 generates (Z/7)^x.
    w = wedge2(a)
    assert sum(eigenspace_dimensions(a).values()) == 4
    assert sum(eigenspace_dimensions(w).values()) == 6
    tame = [[0, 3], [3, 0]]  # sigma_3 permutes the two primes over 2.
    assert mm(tame, tame) == [[2, 0], [0, 2]]
    splitting = []
    for p in (3, 5, 7, 11, 13):
        for ell in (2, 3, 5, 11, 13, 29):
            if p == ell:
                continue
            fdeg = order_mod(ell, p)
            assert (p-1) % fdeg == 0
            assert (ell**fdeg-1) % p == 0
            splitting.append({"cyclotomic_prime": p, "rational_prime": ell,
                              "residue_degree": fdeg,
                              "number_of_added_prime_ideals": (p-1)//fdeg,
                              "residue_field_order": ell**fdeg})
    print(json.dumps({
        "scope": "finite arithmetic and formal modules only; no arithmetic H2 computation",
        "phi7_mod2_factors_ascending": [f, g],
        "sigma3_on_torus_H1_columns": a,
        "torus_H1_eigenspace_dimensions": eigenspace_dimensions(a),
        "sigma3_on_formal_exterior_square": w,
        "formal_exterior_square_eigenspace_dimensions": eigenspace_dimensions(w),
        "sigma3_on_localization_residue_quotient": tame,
        "localization_residue_eigenspace_dimensions": eigenspace_dimensions(tame),
        "splitting": splitting,
        "checks": "factorization, cubic irreducibility, all 36 Galois products, eigen decompositions, residue orders passed"
    }, indent=2))


if __name__ == "__main__":
    main()
