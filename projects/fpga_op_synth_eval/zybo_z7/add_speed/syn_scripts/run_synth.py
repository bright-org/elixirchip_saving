#!/usr/bin/env python

import os
import sys
import subprocess
import shutil


for clk in [464, 388, 333, 250]:
    for w in [8, 16, 32, 36, 40, 44, 48, 52, 56, 60, 64]:
        name = f"a{w}_b{w}_clk{clk}"
        print(name)
        os.makedirs(name, exist_ok=True)
        shutil.copy("../syn/tcl/Makefile", name)

        os.chdir(name)
        subprocess.run(f"make A_WIDTH={w} B_WIDTH={w} CLK_XDC=clk_{clk}.xdc > output.txt", shell=True)
        os.chdir("..")
