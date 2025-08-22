#!/usr/bin/env python3

import sys
import json
import re

lean_file = sys.argv[1]

with open(lean_file) as f:
    lean_file = f.read()

imports = re.findall(r"^import .*$", lean_file, re.MULTILINE)
theorems = re.findall(r"^theorem .*?:=", lean_file, re.MULTILINE|re.DOTALL)
imports = '\n'.join(imports) + '\n\n'
theorems = [imports + t for t in theorems]
print(json.dumps(theorems))
