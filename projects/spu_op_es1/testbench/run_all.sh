#! /bin/bash -eu

# 引数があればそれをなければxsimを SIMに設定
if [ $# -eq 1 ]; then
  SIM=$1
else
  SIM=xsim
fi

make -C    tb_elixirchip_es1_spu_ctl_valid/${SIM}   clean all
make -C tb_elixirchip_es1_spu_ctl_valid_en/${SIM}   clean all
make -C       tb_elixirchip_es1_spu_op_add/${SIM}   clean all
make -C       tb_elixirchip_es1_spu_op_sub/${SIM}   clean all
make -C       tb_elixirchip_es1_spu_op_mul/${SIM}   clean all
make -C      tb_elixirchip_es1_spu_op_mulu/${SIM}   clean all
make -C     tb_elixirchip_es1_spu_op_mulsu/${SIM}   clean all
make -C       tb_elixirchip_es1_spu_op_acc/${SIM}   clean all
make -C       tb_elixirchip_es1_spu_op_lut/${SIM}   clean all
make -C       tb_elixirchip_es1_spu_op_mac/${SIM}   clean all
make -C       tb_elixirchip_es1_spu_op_not/${SIM}   clean all
make -C       tb_elixirchip_es1_spu_op_and/${SIM}   clean all
make -C        tb_elixirchip_es1_spu_op_or/${SIM}   clean all
make -C       tb_elixirchip_es1_spu_op_xor/${SIM}   clean all
make -C      tb_elixirchip_es1_spu_op_nand/${SIM}   clean all
make -C       tb_elixirchip_es1_spu_op_nor/${SIM}   clean all
make -C      tb_elixirchip_es1_spu_op_xnor/${SIM}   clean all
make -C       tb_elixirchip_es1_spu_op_all/${SIM}   clean all
make -C       tb_elixirchip_es1_spu_op_any/${SIM}   clean all
make -C     tb_elixirchip_es1_spu_op_match/${SIM}   clean all
make -C       tb_elixirchip_es1_spu_op_sel/${SIM}   clean all
make -C    tb_elixirchip_es1_spu_op_sel_lt/${SIM}   clean all
make -C       tb_elixirchip_es1_spu_op_sll/${SIM}   clean all
make -C       tb_elixirchip_es1_spu_op_srl/${SIM}   clean all
make -C       tb_elixirchip_es1_spu_op_sra/${SIM}   clean all
make -C       tb_elixirchip_es1_spu_op_nop/${SIM}   clean all
make -C       tb_elixirchip_es1_spu_op_reg/${SIM}   clean all
make -C       tb_elixirchip_es1_spu_op_mem/${SIM}   clean all
make -C    tb_elixirchip_es1_spu_op_mem_sp/${SIM}   clean all
#make -C  tb_elixirchip_es1_spu_op_simd_add/${SIM}   clean all
#make -C  tb_elixirchip_es1_spu_op_simd_acc/${SIM}   clean all

echo "All tests passed!"
