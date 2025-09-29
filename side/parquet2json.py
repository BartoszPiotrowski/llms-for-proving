#!/usr/bin/env python3

import sys
import pandas as pd

df = pd.read_parquet(sys.argv[1])
for _, row in df.iterrows():
    print(row.to_json())
