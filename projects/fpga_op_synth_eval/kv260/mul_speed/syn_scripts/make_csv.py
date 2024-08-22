#!/usr/bin/env python

import os
import sys
import shutil
import subprocess
import pandas as pd
import re

aws  = []
bws  = []
clks = []
oks  = []
luts = []

for clk in [333, 500, 585, 644, 725]:
    for w in range(3, 16+1):
        name = f"a{w}_b{w}_clk{clk}"
        print(name)

        # タイミングエラーチェック
        with open(f"{name}/output.txt", 'r') as f:
            content = f.read()
        ok = not ("CRITICAL WARNING: [Timing 38-282]" in content)

        # LUT数チェック
        lut = 0
        with open(f"{name}/mul_speed_tcl.runs/impl_1/mul_speed_utilization_placed.rpt", 'r') as f:
            # 1行づつ読み込む
            for line in f:
                result =re.match(r"\| CLB LUTs                \|\s*([0-9]+)", line)
                if result:
                    lut = result.group(1)

        aws.append(w)
        bws.append(w)
        clks.append(clk)
        oks.append(ok)
        luts.append(lut)

df = pd.DataFrame(data={"A": aws, "B": bws, "CLK": clks, "OK": oks, "LUTs": luts})

df.to_csv("mul_speed_result.csv", index=False)

