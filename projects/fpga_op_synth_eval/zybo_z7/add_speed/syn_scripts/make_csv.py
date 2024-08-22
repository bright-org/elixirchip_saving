#!/usr/bin/env python

#%% 
import os
import sys
import shutil
import subprocess
import pandas as pd


aa = []
bb = []
clks = []
oks = []
for clk in [464, 388, 333, 250]:
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

