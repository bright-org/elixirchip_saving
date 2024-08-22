#!/usr/bin/env python

import os
import sys
import shutil
import subprocess
import pandas as pd
import re

pattern = [
    (18, 64, 64, 128, True,  True,  0, ""),
    (18, 64, 64,  64, True,  True,  0, "mul64"),  # mul
    (18, 64, 64,  64, True,  True, 64, "mulh64"),  # mulh
    (11, 48, 48,  96, True,  True,  0, ""),
    ( 6, 32, 32,  64, True,  True,  0, ""),
    ( 6, 32, 32,  64, True,  False, 0, ""),
    ( 6, 32, 32,  64, False, False, 0, ""),
    ( 6, 32, 32,  32, True,  True,  0, "mul32"),  # mul
    ( 6, 32, 32,  32, True,  True, 32, "mulh32"),  # mulh
    ( 3, 16, 16,  32, True,  True,  0, ""),
    ( 3,  8,  8,  16, True,  True,  0, ""),
    ( 3,  8,  8,  16, True,  False, 0, ""),
    ( 3,  8,  8,  16, False, False, 0, ""),
    ( 4, 23, 23,  46, False, False, 0, "FP32"),  # FP32
    (12, 53, 53, 106, False, False, 0, "FP64"),  # FP64
]

aws  = []
bws  = []
pws  = []
shifts = []
clks = []
oks  = []
luts = []
dsps = []
latencys = []
comments = []

for clk in [775]:
    for latency, a_bits, b_bits, p_bits, a_sign, b_sign, shift, comment in pattern:
#       p_bits = a_bits + b_bits - shift
        p_sign = a_sign or b_sign
        asin = "s" if a_sign else "u"
        bsin = "s" if b_sign else "u"
        psin = "s" if p_sign else "u"
        name = f"a{a_bits}{asin}_b{b_bits}{bsin}_p{p_bits}{psin}_latency{latency}_shift{shift}_clk{clk}"
        print(name)

        # タイミングエラーチェック
        with open(f"{name}/output.txt", 'r') as f:
            content = f.read()
        ok = not ("CRITICAL WARNING: [Timing 38-282]" in content)

        df_u = pd.read_csv(f"{name}/utilization_placed.csv")
        lut = int(df_u[df_u["Site Type"] == "CLB LUTs"]["Used"])
        dsp = int(df_u[df_u["Site Type"] == "DSPs"]["Used"])

#       # LUT数チェック
#       lut = 0
#       with open(f"{name}/dsp_mul_speed_tcl.runs/impl_1/dsp_mul_speed_utilization_placed.rpt", 'r') as f:
#           # 1行づつ読み込む
#           for line in f:
#               result =re.match(r"\| CLB LUTs                \|\s*([0-9]+)", line)
#               if result:
#                   lut = result.group(1)

        aws.append(f"{asin}{a_bits}")
        bws.append(f"{bsin}{b_bits}")
        pws.append(f"{psin}{p_bits}")
        shifts.append(shift)
        clks.append(clk)
        oks.append(ok)
        luts.append(lut)
        dsps.append(dsp)
        latencys.append(latency)
        comments.append(comment)


df = pd.DataFrame(data={"A bits": aws, "B bits": bws, "P bits": pws, "Latency": latencys, "LUTs": luts, "DSPs": dsps, "shift": shifts, "CLK": clks, "Timing Met": oks, "Comment": comments})

df.to_csv("mul_speed_result_zcu106.csv", index=False)

