#!/usr/bin/env python

#%% 
import os
import sys
import shutil
import subprocess
import pandas as pd


synth_list = [
    [64, 64, 725],
    [60, 60, 725],
    [56, 56, 725],
    [52, 52, 725],
    [48, 48, 725],
    [44, 44, 725],
    [40, 40, 725],
    [36, 36, 725],
    [32, 32, 725],
    [16, 16, 725],
    [ 8,  8, 725],
    [64, 64, 644],
    [60, 60, 644],
    [56, 56, 644],
    [52, 52, 644],
    [48, 48, 644],
    [64, 64, 500],
    [60, 60, 500],
    [56, 56, 500],
    [52, 52, 500],
    [48, 48, 500],
]

aa = []
bb = []
clks = []
oks = []
for clk in [500, 585, 644, 725]:
    for w in [8, 16, 32, 36, 40, 44, 48, 52, 56, 60, 64]:
        name = f"a{w}_b{w}_clk{clk}"
        with open(f"{name}/output.txt", 'r') as f:
            content = f.read()
        ok = not ("CRITICAL WARNING: [Timing 38-282]" in content)

        aa.append(w)
        bb.append(w)
        clks.append(clk)
        oks.append(ok)

df = pd.DataFrame(data={"A": aa, "B": bb, "CLK": clks, "OK": oks})

df.to_csv("add_result.csv", index=False)

