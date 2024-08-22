#!/usr/bin/env python

import os
import shutil
import subprocess


for clk in [464, 388, 333, 250]:
    for sel in range(1, 10+1):
        name = f"sel{sel}_clk{clk}"
        print(name)
        os.makedirs(name, exist_ok=True)
        shutil.copy("../syn/tcl/Makefile", name)

        os.chdir(name)
        subprocess.run(f"make SEL_WIDTH={sel} CLK_XDC=clk_{clk}.xdc > output.txt", shell=True)
        os.chdir("..")
