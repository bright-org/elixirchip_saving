#!/usr/bin/env python

import os
import shutil
import subprocess

for clk in [464, 388, 333, 200]:
    for w in range(3, 8+1):
        name = f"a{w}_b{w}_clk{clk}"
        print(name)
        os.makedirs(name, exist_ok=True)
        shutil.copy("../syn/tcl/Makefile", name)

        os.chdir(name)
        subprocess.run(f"make A_WIDTH={w} B_WIDTH={w} CLK_XDC=clk_{clk}.xdc > output.txt", shell=True)
        os.chdir("..")
