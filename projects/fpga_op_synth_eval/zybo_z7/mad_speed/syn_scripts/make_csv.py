#!/usr/bin/env python

#%% 
import os
import sys
import shutil
import subprocess
import pandas as pd


synth_list = [
    [  3,  3, 725],
    [  4,  4, 725],
    [  6,  6, 725],
    [  8,  8, 725],
    [ 10, 10, 725],
    [ 12, 12, 725],
    [ 16, 16, 725],
    [ 32, 32, 725],
    [ 64, 64, 725],

    [  3,  3, 644],
    [  4,  4, 644],
    [  6,  6, 644],
    [  8,  8, 644],
    [ 10, 10, 644],
    [ 12, 12, 644],
    [ 16, 16, 644],
    [ 32, 32, 644],
    [ 64, 64, 644],

    [  3,  3, 500],
    [  4,  4, 500],
    [  6,  6, 500],
    [  8,  8, 500],
    [ 10, 10, 500],
    [ 12, 12, 500],
    [ 16, 16, 500],
    [ 32, 32, 500],
    [ 64, 64, 500],
]


aa = []
bb = []
clk = []
oks = []
for s in synth_list:
    name = f"a{s[0]}_b{s[1]}_clk{s[2]}"
    with open(f"{name}/output.txt", 'r') as f:
        content = f.read()
    ok = not ("CRITICAL WARNING: [Timing 38-282]" in content)

    aa.append(s[0])
    bb.append(s[1])
    clk.append(s[2])
    oks.append(ok)

df = pd.DataFrame(data={"A": aa, "B": bb, "CLK": clk, "OK": oks})

df.to_csv("mad_result.csv", index=False)

