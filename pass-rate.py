#!/usr/bin/env python3

import sys
import json
import concurrent.futures
import multiprocessing

from utils import lean_eval

#LEAN_DIR = "/Users/bpio/Research/Code/Bartosz/mathlib-4-20"
LEAN_DIR = "/Users/bpio/Research/Code/Public/Lean-Inequality-Benchmark"
PROCESSES = 12


def check(proofs):
    proofs = proofs['proofs']
    for i, proof in enumerate(proofs):
        correct, msg, err = lean_eval(proof, LEAN_DIR)
        if correct:
            print(f'Proof {i} correct!')
            return 1
        #print(f'Proof incorrect.\n{msg}\n{err}')
    print('All proofs incorrect.')
    return 0

if __name__ == '__main__':
    proofs = [json.loads(l) for l in open(sys.argv[1])]
    with multiprocessing.Pool(processes=PROCESSES) as pool:
        passed = list(pool.map(check, proofs))
        print(f'Pass rate: {sum(passed) / len(passed)} = {sum(passed)} / {len(passed)}')
