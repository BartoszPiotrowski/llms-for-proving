#!/usr/bin/env python3

import sys
import json

examples = [json.loads(l) for l in open(sys.argv[1])]
for e in examples:
    p = {'id': e['id'],
         'statement': e['lean4_src_header'] + e['lean4_formalization']}
    print(json.dumps(p))
