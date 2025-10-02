#!/usr/bin/env python3

import sys
import json
from utils import lean_eval, extract_proof
from random import choice

log = sys.argv[1]
with open(log) as f:
    log = f.read()
log = log.split('INPUT STATEMENT: ')
for s in log[1:]:
    s = s.split('CANDIDATE PROOF: ')
    statement = s[0]
    proofs = []
    for r in s[1:]:
        p = extract_proof(r)
        p = 'import Mathlib\n\n' + p
        if p and not 'sorry' in p:
            proofs.append(p)
    print(len(proofs), file=sys.stderr)
    output = {'statement': statement, 'proofs': proofs}
    print(json.dumps(output))

