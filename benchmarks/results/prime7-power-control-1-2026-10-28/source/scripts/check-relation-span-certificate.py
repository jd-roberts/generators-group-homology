#!/usr/bin/env python3
"""Independent free-cancellation checker, with no import of the producer."""
import argparse
import gzip
import json
from pathlib import Path


def inv(word):
    return [-x for x in reversed(word)]


def cancel(word):
    stack = []
    for x in word:
        if stack and stack[-1] == -x:
            stack.pop()
        else:
            stack.append(x)
    return stack


def check_product(word, base, factors, rank):
    stack = []
    for q, index, sign in factors:
        if sign not in (-1, 1) or not 1 <= index <= len(base) or any(not 1 <= abs(x) <= rank for x in q):
            raise ValueError("malformed conjugate factor")
        r = base[index - 1]
        for x in q + (r if sign == 1 else inv(r)) + inv(q):
            if stack and stack[-1] == -x:
                stack.pop()
            else:
                stack.append(x)
    if stack != cancel(word):
        raise ValueError("free-group product does not equal target")


def make_quotient(problem):
    # Independently construct the specified quotient, never adding the raw R.
    n, p, rs, ss = (problem[k] for k in ["rank", "prime", "relators", "candidates"])
    if n < 1 or p < 2 or any(p % k == 0 for k in range(2, int(p ** .5) + 1)):
        raise ValueError("invalid rank or prime")
    if any(not 1 <= abs(x) <= n for w in rs + ss for x in w):
        raise ValueError("word outside free generators")
    comms = [cancel([-i] + inv(r) + [i] + r) for i in range(1, n + 1) for r in rs]
    return comms + [cancel(r * p) for r in rs] + [cancel(s) for s in ss]


def compose(a, b):
    return [a[x] for x in b]


def permutation_word(word, images):
    degree = len(images[0])
    identity = list(range(degree))
    inverses = []
    for perm in images:
        if sorted(perm) != identity:
            raise ValueError("not a permutation")
        inverse = [0] * degree
        for i, value in enumerate(perm):
            inverse[value] = i
        inverses.append(inverse)
    result = identity
    for letter in word:
        result = compose(result, images[letter - 1] if letter > 0 else inverses[-letter - 1])
    return result


def verify(result):
    problem = result["problem"]
    rs, ss, n = problem["relators"], problem["candidates"], problem["rank"]
    memberships = problem["candidate_membership"]
    if len(ss) != len(memberships):
        raise ValueError("missing candidate membership hypotheses")
    for s, proof in zip(ss, memberships):
        check_product(s, rs, proof, n)
    qrels = make_quotient(problem)
    if qrels != result["quotient_relators"] or len(rs) != len(result["targets"]):
        raise ValueError("wrong fixed quotient or target inventory")
    positive = []
    for i, answer in enumerate(result["targets"]):
        if answer["status"] == "certified":
            check_product(rs[i], qrels, answer["factors"], n)
            positive.append(i + 1)
        elif answer["status"] != "unresolved":
            raise ValueError("producer may not declare nonmembership")
    negative = []
    obstruction = problem.get("obstruction")
    if obstruction:
        images = obstruction["generator_permutations"]
        if len(images) != n:
            raise ValueError("wrong number of permutation images")
        identity = list(range(len(images[0])))
        if any(permutation_word(r, images) != identity for r in qrels):
            raise ValueError("obstruction does not factor through the quotient")
        negative = [i + 1 for i, r in enumerate(rs) if permutation_word(r, images) != identity]
        if set(positive) & set(negative):
            raise ValueError("inconsistent certificates")
    return {"certified_targets": positive, "proved_nonmembers": negative,
            "spanning": "proved" if len(positive) == len(rs) else "disproved" if negative else "unresolved"}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("certificate", type=Path)
    args = parser.parse_args()
    raw = args.certificate.read_bytes()
    if args.certificate.suffix == ".gz":
        raw = gzip.decompress(raw)
    print(json.dumps(verify(json.loads(raw)), indent=2))
