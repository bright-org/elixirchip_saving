#!/usr/bin/env python

import os
import shutil
import subprocess

pattern = [
    (18, 64, 64, 128, True,  True,  0),
    (18, 64, 64,  64, True,  True,  0),  # mul
    (18, 64, 64,  64, True,  True, 64),  # mulh
    (11, 48, 48,  96, True,  True,  0),
    ( 6, 32, 32,  64, True,  True,  0),
    ( 6, 32, 32,  64, True,  False, 0),
    ( 6, 32, 32,  64, False, False, 0),
    ( 6, 32, 32,  32, True,  True,  0),  # mul
    ( 6, 32, 32,  32, True,  True, 32),  # mulh
    ( 3, 16, 16,  32, True,  True,  0),
    ( 3,  8,  8,  16, True,  True,  0),
    ( 3,  8,  8,  16, True,  False, 0),
    ( 3,  8,  8,  16, False, False, 0),
    ( 4, 23, 23,  46, False, False, 0),  # FP32
    (12, 53, 53, 106, False, False, 0),  # FP64
]


for clk in [543]:
    for latency, a_bits, b_bits, p_bits, a_sign, b_sign, shift in pattern:
#       p_bits = a_bits + b_bits - shift
        p_sign = a_sign or b_sign
        asin = "s" if a_sign else "u"
        bsin = "s" if b_sign else "u"
        psin = "s" if p_sign else "u"
        name = f"a{a_bits}{asin}_b{b_bits}{bsin}_p{p_bits}{psin}_latency{latency}_shift{shift}_clk{clk}"
        print(name)

        os.makedirs(name, exist_ok=True)
        shutil.copy("../syn/tcl/Makefile", name)

        asin = "signed" if a_sign else "unsigned"
        bsin = "signed" if b_sign else "unsigned"
        psin = "signed" if p_sign else "unsigned"

        os.chdir(name)
        subprocess.run(f"make LATENCY={latency} A_WIDTH={a_bits} B_WIDTH={b_bits} P_WIDTH={p_bits} A_SIGN={asin} B_SIGN={bsin} P_SIGN={psin} SHIFT={shift} CLK_XDC=clk_{clk}.xdc > output.txt", shell=True)
        os.chdir("..")
