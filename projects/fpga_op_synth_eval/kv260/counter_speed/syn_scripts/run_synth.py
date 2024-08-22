#!/usr/bin/env python

import os
import sys
import shutil
import subprocess

for clk in [500, 585, 644, 725]:
    for w in range(8, 128+1, 8):
        name = f"w{w}_clk{clk}"
        print(name)
        os.makedirs(name, exist_ok=True)
        shutil.copy("../syn/tcl/Makefile", name)

        os.chdir(name)
        subprocess.run(f"make WIDTH={w} CLK_XDC=clk_{clk}.xdc > output.txt", shell=True)
        os.chdir("..")
