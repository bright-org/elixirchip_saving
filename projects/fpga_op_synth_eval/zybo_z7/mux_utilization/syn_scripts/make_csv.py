#!/usr/bin/env python

import pandas as pd
import re

sels = []
luts = []

for sel in range(1, 10+1):
    name = f"sel{sel}"
    print(name)

    # LUT数チェック
    lut = 0
    with open(f"{name}/mux_utilization_tcl.runs/synth_1/mux_utilization_utilization_synth.rpt", 'r') as f:
        # 1行づつ読み込む
        for line in f:
            result =re.match(r"\| Slice LUTs\*             \|\s*([0-9]+)", line)
            if result:
                lut = result.group(1)

    print(f"{sel}, {lut}")
    sels.append(sel)
    luts.append(lut)

df = pd.DataFrame(data={"sel": sels, "LUT": luts})

df.to_csv("mux_result.csv", index=False)


