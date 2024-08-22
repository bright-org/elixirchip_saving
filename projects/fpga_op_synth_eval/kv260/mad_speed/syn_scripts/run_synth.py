
#%% 
import os
import sys
import shutil
import subprocess


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


for s in synth_list:
    name = f"a{s[0]}_b{s[1]}_clk{s[2]}"
    print(name)
    os.makedirs(name, exist_ok=True)
    shutil.copy("../syn/tcl/Makefile", name)

    os.chdir(name)
#   subprocess.run(f["make", f"A_WIDTH={s[0]}", f"B_WIDTH={s[1]}", f"CLK_XDC=clk_{s[2]}.xdc", ">", "output.txt"], shell=True)
    subprocess.run(f"make A_WIDTH={s[0]} B_WIDTH={s[1]} CLK_XDC=clk_{s[2]}.xdc > output.txt", shell=True)
    os.chdir("..")


# %%
