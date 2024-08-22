#!/usr/bin/env python

#%% 
import os
import sys
import shutil
import subprocess
import numpy as np
import pandas as pd
import re


W_MAX = 16


for insert_ff in [True, False]:
    for sign in ["signed", "unsigned"]:

        aa = []
        bb = []
        clk = []
        oks = []
        luts = []
        tbl = np.zeros((W_MAX, W_MAX), dtype=np.int32)
        for aw in range(1, W_MAX+1):
            for bw in range(1, aw+1):
                name = f"{sign}_{aw}_{bw}"
                if insert_ff:
                    name += "_ff"
                print(name)

                # LUT数チェック
                lut = 0
                with open(f"{name}/mul_lut_tcl.runs/synth_1/mul_lut_utilization_synth.rpt", 'r') as f:
                    # 1行づつ読み込む
                    for line in f:
                        result =re.match(r"\| CLB LUTs\*               \|\s*([0-9]+)", line)
                        if result:
                            lut = result.group(1)

                print(f"{aw}, {bw}, {lut}")
                tbl[aw-1, bw-1] = lut
                tbl[bw-1, aw-1] = lut
                aa.append(aw)
                bb.append(bw)
                luts.append(lut)

        ff = "_ff" if insert_ff else ""

        df = pd.DataFrame(data={"A": aa, "B": bb, "LUTs": luts})

        df.to_csv(f"{sign}{ff}_mul_result.csv", index=False)

        np.savetxt(f"{sign}{ff}_mul_tbl.csv",tbl, delimiter=',',fmt='%d')

        with open(f"{sign}{ff}_mul_tbl.txt", "w") as f:
            for aw in range(1, W_MAX+1):
                for bw in range(1, W_MAX+1):
                    f.write(f"{tbl[aw-1, bw-1]:4d}\t")
                f.write("\n")

