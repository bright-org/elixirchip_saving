#!/usr/bin/env python

import os
import shutil
import subprocess

for sel in range(1, 10+1):
    name = f"sel{sel}"
    print(name)
    os.makedirs(name, exist_ok=True)
    shutil.copy("../syn/tcl/Makefile", name)

    os.chdir(name)
    subprocess.run(f"make SEL_WIDTH={sel} > output.txt", shell=True)
    os.chdir("..")
