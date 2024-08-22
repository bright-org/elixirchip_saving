#!/usr/bin/env python

#%% 
import os
import sys
import shutil
import subprocess
import pandas as pd


sels = []
clks = []
oks = []

for clk in [500, 585, 644, 725]:
    for sel in range(1, 11):
        name = f"sel{sel}_clk{clk}"
        print(name)

        with open(f"{name}/output.txt", 'r') as f:
            content = f.read()
        ok = not ("CRITICAL WARNING: [Timing 38-282]" in content)

        sels.append(sel)
        clks.append(clk)
        oks.append(ok)

df = pd.DataFrame(data={"sel": sels, "CLK": clks, "OK": oks})

df.to_csv("mux_result.csv", index=False)

