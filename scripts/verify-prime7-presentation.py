#!/usr/bin/env python3
"""Replay finite certificates for Proposition 3.2; no proof search or KBMAG."""
import argparse
import gzip
import hashlib
import json
import os
from pathlib import Path
import subprocess
import time

ROOT = Path(__file__).resolve().parents[1]
WORDS = "docs/evidence/prime7-presentation-words.json"
CERTIFICATES = "docs/evidence/prime7-normal-closure-certificates.json.gz"


def append_reduced(stack, word):
    for letter in word:
        if stack and stack[-1] == -letter:
            stack.pop()
        else:
            stack.append(letter)


def reduced(word):
    stack = []
    append_reduced(stack, word)
    return stack


def inverse(word):
    return [-x for x in reversed(word)]


def substitute(word, images):
    stack = []
    for x in word:
        append_reduced(stack, images[x - 1] if x > 0 else inverse(images[-x - 1]))
    return stack


def matrix_multiply(a, b, prime=29):
    return [sum(a[2 * i + k] * b[2 * k + j] for k in range(2)) % prime
            for i in range(2) for j in range(2)]


def matrix_inverse(a, prime=29):
    assert (a[0] * a[3] - a[1] * a[2]) % prime == 1
    return [a[3], -a[1] % prime, -a[2] % prime, a[0]]


IDENTITY = [1, 0, 0, 1]


def matrix_power(a, n):
    if n < 0:
        a, n = matrix_inverse(a), -n
    result = IDENTITY
    while n:
        if n % 2:
            result = matrix_multiply(result, a)
        a, n = matrix_multiply(a, a), n // 2
    return result


def matrix_evaluate(word, images):
    result = IDENTITY
    for x in word:
        result = matrix_multiply(result, images[x - 1] if x > 0 else matrix_inverse(images[-x - 1]))
    return result


def named_word(word, rank):
    names = (["z", "u1", "u2", "u3", "a", "b1"] if rank == 6 else
             ["z", "u1", "u2", "u3", "a", "b", "b0", "b1", "b2", "b3", "b4", "b5", "b6", "w"])
    return "*".join(names[abs(x) - 1] + ("^-1" if x < 0 else "") for x in word) or "1"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--gap", default=os.environ.get("GAP", "gap"))
    parser.add_argument("--output", type=Path, help="optional evidence JSON")
    parser.add_argument("--show-certificate", metavar="GROUP:INDEX",
                        help="print a product of conjugates, e.g. twelve:6")
    args = parser.parse_args()
    started = time.monotonic()
    command = [args.gap, "-q", "-b", "--quitonbreak", "tests/prime7-presentation-export.g"]
    run = subprocess.run(command, cwd=ROOT, capture_output=True, text=True, timeout=5)
    assert run.returncode == 0 and not run.stderr, (run.stdout, run.stderr)
    exported = json.loads(run.stdout.split("BEGIN_PRIME7_PRESENTATION_JSON\n", 1)[1]
                          .split("\nEND_PRIME7_PRESENTATION_JSON", 1)[0])
    data = json.loads((ROOT / WORDS).read_text())
    assert exported == data, "committed free words differ from current source export"
    cert = json.loads(gzip.decompress((ROOT / CERTIFICATES).read_bytes()))
    assert cert["format"] == 1
    original, presentation = data["original_relators"], data["reduced_relators"]
    assert len(original) == 64 and len(presentation) == 32
    phi, psi = data["forward_generator_images"], data["backward_generator_images"]
    assert len(phi) == 14 and len(psi) == 6
    assert [substitute(r, phi) for r in original] == data["forward_relators"]
    assert [substitute(r, psi) for r in presentation] == data["backward_relators"]
    assert [reduced([i + 1] + inverse(substitute(w, psi))) for i, w in enumerate(phi)] == data["composites"]
    assert [reduced([i + 1] + inverse(substitute(w, phi))) for i, w in enumerate(psi)] == data["inverse_composites"] == [[]] * 6
    tau = [[1], [2], [3], [4], [5], [-1, -1, -1, 6, 1, 1, 1]]
    assert [substitute(w, tau) for w in data["twelve"]] == data["b0_twelve"]
    assert [substitute(w, tau) for w in data["corrected"]] == data["b0_corrected"]

    checked, factors = {}, 0
    for name, group in cert["groups"].items():
        base = data[group["base"]]
        rank = 14 if group["base"] == "original_relators" else 6
        checked[name] = []
        for key, proof in group["proofs"].items():
            target = data[name][int(key) - 1]
            stack = []
            for q_index, r_index, sign in proof:
                assert sign in (-1, 1) and 1 <= r_index <= len(base)
                assert 0 <= q_index < len(cert["conjugators"])
                q = cert["conjugators"][q_index]
                assert all(1 <= abs(x) <= rank for x in q)
                append_reduced(stack, q)
                append_reduced(stack, base[r_index - 1] if sign == 1 else inverse(base[r_index - 1]))
                append_reduced(stack, inverse(q))
            assert stack == reduced(target), (name, key)
            checked[name].append(int(key))
            factors += len(proof)
            if time.monotonic() - started > 10:
                raise TimeoutError("ten-second verification limit exceeded")
        checked[name].sort()
    for name, n in [("forward_relators", 64), ("backward_relators", 32),
                    ("composites", 14), ("b0_twelve", 12), ("b0_corrected", 6)]:
        assert checked[name] == list(range(1, n + 1))
    assert checked["twelve"] == [1, 2, 3, 5, 6, 7, 8, 9]

    # Exact, independently implemented SL(2,F29) witness. 7 has order seven.
    assert pow(7, 7, 29) == 1 and 7 != 1
    diagonal = lambda x: [pow(x, -1, 29), 0, 0, x]
    z = diagonal(7)
    units = [diagonal((1 - pow(7, i, 29)) % 29) for i in [1, 2, 3]]
    a, b = [0, 1, 28, 0], [1, 1, 28, 0]
    bs = [matrix_multiply(matrix_multiply(matrix_multiply(matrix_power(z, 3 * t), b),
                                            matrix_power(z, 3 * t)), a) for t in range(7)]
    w = matrix_power(z, 4)
    for u in units:
        w = matrix_multiply(w, u)
    original_images = [z] + units + [a, b] + bs + [w]
    images = [z] + units + [a, bs[1]]
    assert all(matrix_evaluate(r, original_images) == IDENTITY for r in original)
    assert all(matrix_evaluate(r, images) == IDENTITY for r in presentation)
    assert [matrix_evaluate(v, images) for v in phi] == original_images
    matrix_results = {name: [matrix_evaluate(r, images) for r in data[name]]
                      for name in ["twelve", "corrected", "b0_twelve", "b0_corrected"]}
    bad = lambda name: [i + 1 for i, value in enumerate(matrix_results[name]) if value != IDENTITY]
    assert bad("twelve") == [4, 10, 11, 12]
    assert bad("corrected") == [1, 3, 4, 5, 6]
    assert bad("b0_twelve") == bad("b0_corrected") == []
    for word in data["b0_corrected"]:
        assert all(sum(1 if x == i else -1 if x == -i else 0 for x in word) % 7 == 0
                   for i in range(1, 7))
        lifted = substitute(word, psi)
        assert all(sum(1 if x == i else -1 if x == -i else 0 for x in lifted) % 7 == 0
                   for i in range(1, 15))

    paths = [WORDS, CERTIFICATES, "tests/fixtures/roberts-v1-proposition32.g",
             "tests/fixtures/roberts-v1-prime7-words.g", "tests/prime7-presentation-export.g",
             "scripts/prime7-correction.g", "scripts/verify-prime7-presentation.py",
             "docs/evidence/prime7-b0-corrected-words.g",
             "Library-of-groups.g", "docs/evidence/paper-sources.json"]
    evidence = {"command": command, "gap_timeout_seconds": 5, "overall_limit_seconds": 10,
                "wall_seconds": round(time.monotonic() - started, 6),
                "scope": "Exact free-group certificate replay and finite matrices; no proof search, KBMAG, or relation-module spanning computation.",
                "source_sha256": {p: hashlib.sha256((ROOT / p).read_bytes()).hexdigest() for p in paths},
                "certified_products": checked, "conjugate_factors_checked": factors,
                "matrix_field": 29, "xi": 7, "original_generator_matrices": original_images,
                "reduced_generator_matrices": images, "matrix_results": matrix_results,
                "nonmembers": {name: bad(name) for name in ["twelve", "corrected"]},
                "unverified": "Spanning of A by the b0-interpreted twelve words; original arithmetic-group identification beyond the verified presentations."}
    if args.output:
        args.output.write_text(json.dumps(evidence, indent=2) + "\n")
    print(f"PASS: both presentation maps, 14 composites, 8 named memberships, 12 b0 memberships and 6 b0-corrected memberships ({evidence['wall_seconds']}s).")
    print(f"PASS: {factors} conjugate factors checked by free cancellation; all new corrected exponents vanish mod 7.")
    print("PROVED NONMEMBERS: named twelve 4,10,11,12; previous corrected words 1,3,4,5,6.")
    print("NOT VERIFIED: the twelve-word relation-module spanning certificate.")
    if args.show_certificate:
        name, key = args.show_certificate.split(":", 1)
        group = cert["groups"][name]
        rank = 14 if group["base"] == "original_relators" else 6
        proof = group["proofs"][key]
        print(f"Target {name}[{key}] = product below; R indexes {group['base']} in published/stored order.")
        for q_index, r_index, sign in proof:
            q = named_word(cert["conjugators"][q_index], rank)
            print(f"({q}) * R[{r_index}]^{sign} * ({q})^-1")


if __name__ == "__main__":
    main()
