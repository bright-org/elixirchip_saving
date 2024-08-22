#!/usr/bin/env python

import os
import sys
import shutil
import subprocess

W_MAX = 16

#for insert_ff in [True, False]:
for insert_ff in [True]:
    for sign in ["unsigned", "signed"]:
        for aw in range(1, W_MAX+1):
            for bw in range(1, aw+1):
                name = f"{sign}_{aw}_{bw}"
                if insert_ff:
                    name += "_ff"
                print(name)
                os.makedirs(name, exist_ok=True)
                shutil.copy("../syn/tcl/Makefile", name)

                os.chdir(name)
                if insert_ff:
                    subprocess.run(f"make A_WIDTH={aw} B_WIDTH={bw} SIGN={sign} INS_FF=1 > output.txt", shell=True)
                else:
                    subprocess.run(f"make A_WIDTH={aw} B_WIDTH={bw} SIGN={sign} > output.txt", shell=True)
                os.chdir("..")

