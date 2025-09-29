#!/usr/bin/env python3

import sys
import os
import json
import concurrent.futures
import multiprocessing
import re

from utils import lean_eval, preprocess_proof
from math import log, ceil, inf

LEAN_DIR = "/Users/bpio/Research/Code/Bartosz/mathlib-4-11"
#LEAN_DIR = "/Users/bpio/Research/Code/Public/Lean-Inequality-Benchmark"
PROCESSES = 6


def check(proofs):
    n, proofs = proofs
    proofs = proofs['proofs']
    for i, proof in enumerate(proofs):
        proof = preprocess_proof(proof)
        if not proof:
            return -1, None
        correct, msg, err = lean_eval(proof, LEAN_DIR)
        if correct:
            print(f'\033[32mStatement {n}: proof {i} correct!\033[0m')
            return i, proof
        print(f'Proof incorrect.\n\n--- Proof ---{proof}\n\n--- Lean stdout ---\n{msg}\n\n--- Lean stderr ---\n{err}\n', file=sys.stderr)
    print(f'\033[31mStatement {n}: all proofs incorrect.\033[0m')
    return -1, None

if __name__ == '__main__':
    proofs_path = sys.argv[1]
    proofs = [json.loads(l) for l in open(proofs_path)]
    with open(sys.argv[1]) as f:
        proofs = json.load(f)
    with multiprocessing.Pool(processes=PROCESSES) as pool:
        passed_indices, correct_proofs = zip(*pool.map(check, enumerate(proofs)))
    max_pow = ceil(log(max(passed_indices), 2)) + 1
    print(f'max_pow {max_pow}')
    for i in range(max_pow + 1):
        k = 2 ** i
        passed = [-1 < p < k for p in passed_indices]
        print(f'Pass@{k:<2}: {(sum(passed) / len(passed)):.3f} = {sum(passed)} / {len(passed)}')
    correct_proofs = [p for p in correct_proofs if p]
    if correct_proofs:
        correct_proofs_path = os.path.join(LEAN_DIR, os.path.basename(
            proofs_path.replace('.json','') + '.lean'))
        imports = '\n'.join([l for l in correct_proofs[0].splitlines() if 'import ' in l])
        correct_proofs = [re.sub(r'^import .*\n', '', p, flags=re.M) for p in correct_proofs]
        with open(correct_proofs_path, 'w') as f:
            f.write('\n'.join([imports] + correct_proofs) + '\n')
        print(f'Correct proofs saved to {correct_proofs_path}')
    else:
        print(f'No correct proofs to save...')
