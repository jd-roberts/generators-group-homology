#!/usr/bin/env python3
"""Verify/export the cheap source-word calculation; never load KBMAG."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import time

ROOT = Path(__file__).resolve().parents[1]
SOURCES = [
    "scripts/prime7-correction.g",
    "scripts/verify-prime7-corrections.py",
    "tests/prime7-corrected-representatives.g",
    "tests/fixtures/roberts-v1-prime7-words.g",
    "docs/evidence/prime7-corrected-words.g",
    "docs/evidence/paper-sources.json",
]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--gap", default=os.environ.get("GAP", "gap"))
    parser.add_argument("--output", type=Path, help="optional evidence JSON path")
    args = parser.parse_args()
    command = [args.gap, "-q", "-b", "tests/prime7-corrected-representatives.g"]
    started = time.monotonic()
    result = subprocess.run(command, cwd=ROOT, capture_output=True, text=True, timeout=5)
    elapsed = time.monotonic() - started
    if result.returncode or result.stderr or "PASS: matrices" not in result.stdout:
        raise RuntimeError(f"GAP verification failed:\n{result.stdout}\n{result.stderr}")
    calculation = json.loads(result.stdout.split("BEGIN_PRIME7_CORRECTION_JSON\n", 1)[1]
                             .split("\nEND_PRIME7_CORRECTION_JSON", 1)[0])
    coordinates = ["z", "u1", "u2", "u3", "a", "b1"]
    token = r"(z|u1|u2|u3|a|b1)(?:\^(-?\d+))?"
    for word, expected in zip(calculation["expanded_words"],
                              calculation["integer_exponent_sums"], strict=True):
        if not re.fullmatch(token + r"(?:\*" + token + r")*", word):
            raise RuntimeError("Exported word violates the explicit-word grammar")
        counts = dict.fromkeys(coordinates, 0)
        for match in re.finditer(token, word):
            counts[match[1]] += int(match[2] or 1)
        if [counts[x] for x in coordinates] != expected or any(v % 7 for v in counts.values()):
            raise RuntimeError("Independent integer exponent check failed")
    evidence = {
        "command": command, "timeout_seconds": 5, "wall_seconds": round(elapsed, 6),
        "exit_code": result.returncode,
        "scope": "Free words and matrices only; no KBMAG. Intended relation-module membership/spanning is not certified by this check.",
        "independent_check": "Python strict-token exponent counts agree with all six GAP integer exponent rows.",
        "source_sha256": {p: hashlib.sha256((ROOT / p).read_bytes()).hexdigest() for p in SOURCES},
        "calculation": calculation, "stdout": result.stdout, "stderr": result.stderr,
    }
    if args.output:
        args.output.write_text(json.dumps(evidence, indent=2) + "\n")
    print(f"PASS: corrected words, matrices, source comparison and 14-coordinate check ({elapsed:.6f}s; 5s limit).")
    print("PASS: independent Python integer exponent check of all six exported words.")
    print("NOT VERIFIED: the original twelve-word relation-module spanning certificate.")


if __name__ == "__main__":
    main()
