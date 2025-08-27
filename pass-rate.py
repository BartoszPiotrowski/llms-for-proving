#!/usr/bin/env python3

import sys
import json
import concurrent.futures
import multiprocessing

from utils import lean_eval, preprocess_proof
from math import log, ceil, inf

#LEAN_DIR = "/Users/bpio/Research/Code/Bartosz/mathlib-4-20"
LEAN_DIR = "/Users/bpio/Research/Code/Public/Lean-Inequality-Benchmark"
PROCESSES = 12


def check(proofs):
    n, proofs = proofs
    proofs = proofs['proofs']
    for i, proof in enumerate(proofs):
        proof = preprocess_proof(proof)
        if not proof:
            return 0, None
        correct, msg, err = lean_eval(proof, LEAN_DIR)
        if correct:
            print(f'\033[32mStatement {n}: proof {i + 1} correct!\033[0m')
            return i + 1, proof
        print(f'Proof incorrect.\n\n--- Proof ---{proof}\n\n--- Lean stdout ---\n{msg}\n\n--- Lean stderr ---\n{err}\n', file=sys.stderr)
    print(f'\033[31mStatement {n}: all proofs incorrect.\033[0m')
    return 0, None

if __name__ == '__main__':
    proofs_path = sys.argv[1]
    proofs = [json.loads(l) for l in open(proofs_path)]
    with open(sys.argv[1]) as f:
        proofs = json.load(f)
    with multiprocessing.Pool(processes=PROCESSES) as pool:
        passed_indices, correct_proofs = zip(*pool.map(check, enumerate(proofs)))
    max_pow = ceil(log(max(passed_indices), 2))
    for i in range(max_pow + 1):
        k = 2 ** i
        passed = [p and p <= k for p in passed_indices]
        print(f'Pass@{k:<2}: {(sum(passed) / len(passed)):.3f} = {sum(passed)} / {len(passed)}')
    correct_proofs_path = proofs_path.replace('.json','') + '-correct.lean'
    correct_proofs = [p for p in correct_proofs if p]
    with open(correct_proofs_path, 'w') as f:
        f.write('\n'.join(correct_proofs) + '\n')
    print(f'Correct proofs saved to {correct_proofs_path}')
