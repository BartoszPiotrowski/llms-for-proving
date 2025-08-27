#!/usr/bin/env python3

import sys
import json
import concurrent.futures
import multiprocessing

from utils import lean_eval
from math import log, ceil, inf

#LEAN_DIR = "/Users/bpio/Research/Code/Bartosz/mathlib-4-20"
LEAN_DIR = "/Users/bpio/Research/Code/Public/Lean-Inequality-Benchmark"
PROCESSES = 12


def check(proofs):
    i, proofs = proofs
    print(f'Checking proofs for statement {i}...')
    proofs = proofs['proofs']
    for i, proof in enumerate(proofs):
        correct, msg, err = lean_eval(proof, LEAN_DIR)
        if correct:
            print(f'\033[32mProof {i + 1} correct!\033[0m')
            return i + 1
        print(f'Proof incorrect.\n{msg}\n{err}')
    print(f'\033[31mAll proofs incorrect.\033[0m')
    return 0

if __name__ == '__main__':
    proofs = [json.loads(l) for l in open(sys.argv[1])]
    with open(sys.argv[1]) as f:
        proofs = json.load(f)
    with multiprocessing.Pool(processes=PROCESSES) as pool:
        passed_indices = list(pool.map(check, enumerate(proofs)))
    max_pow = ceil(log(max(passed_indices), 2))
    for i in range(max_pow + 1):
        k = 2 ** i
        passed = [p and p <= k for p in passed_indices]
        print(f'Pass@{k:<2}: {(sum(passed) / len(passed)):.3f} = {sum(passed)} / {len(passed)}')
