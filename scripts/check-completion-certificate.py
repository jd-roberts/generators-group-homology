#!/usr/bin/env python3
"""Independent checker: imports only the existing independent product checker.

Checks EVERY retained rule, not just target certificates. No completion/search
code is imported. Rule orientation is checked separately from group validity.
"""
import argparse
import importlib.util
import json
from pathlib import Path
import hashlib

spec = importlib.util.spec_from_file_location('products', Path(__file__).with_name('check-relation-span-certificate.py'))
products = importlib.util.module_from_spec(spec)
spec.loader.exec_module(products)


def verify(record):
    verdict = products.verify(record)
    base = products.make_quotient(record['problem'])
    rank = record['problem']['rank']
    for index, rule in enumerate(record['rules']):
        lhs, rhs = rule['lhs'], rule['rhs']
        if rule['id'] != index or not lhs or (len(lhs), tuple(lhs)) <= (len(rhs), tuple(rhs)):
            raise ValueError('invalid rule orientation or identifier')
        if any(type(x) is not int or not 1 <= abs(x) <= rank for x in lhs+rhs):
            raise ValueError('invalid rule letter')
        products.check_product(lhs + products.inv(rhs), base, rule['factors'], rank)
    return dict(**verdict, verified_rules=len(record['rules']),
                quotient_sha256=hashlib.sha256(json.dumps(base, separators=(',', ':')).encode()).hexdigest())


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('certificate', type=Path)
    args = parser.parse_args()
    print(json.dumps(verify(json.loads(args.certificate.read_text())), indent=2))
