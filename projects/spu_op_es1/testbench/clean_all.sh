#! /bin/bash -eu

# 引数があればそれをなければxsimを SIMに設定
if [ $# -eq 1 ]; then
  SIM=$1
else
  SIM=xsim
fi

make -C    tb_elixirchip_es1_spu_ctl_valid/${SIM}   distclean
make -C tb_elixirchip_es1_spu_ctl_valid_en/${SIM}   distclean
make -C       tb_elixirchip_es1_spu_op_add/${SIM}   distclean
make -C       tb_elixirchip_es1_spu_op_sub/${SIM}   distclean
make -C       tb_elixirchip_es1_spu_op_mul/${SIM}   distclean
make -C      tb_elixirchip_es1_spu_op_mulu/${SIM}   distclean
make -C     tb_elixirchip_es1_spu_op_mulsu/${SIM}   distclean
make -C       tb_elixirchip_es1_spu_op_acc/${SIM}   distclean
make -C       tb_elixirchip_es1_spu_op_mac/${SIM}   distclean
make -C       tb_elixirchip_es1_spu_op_not/${SIM}   distclean
make -C       tb_elixirchip_es1_spu_op_and/${SIM}   distclean
make -C        tb_elixirchip_es1_spu_op_or/${SIM}   distclean
make -C       tb_elixirchip_es1_spu_op_xor/${SIM}   distclean
make -C      tb_elixirchip_es1_spu_op_nand/${SIM}   distclean
make -C       tb_elixirchip_es1_spu_op_nor/${SIM}   distclean
make -C      tb_elixirchip_es1_spu_op_xnor/${SIM}   distclean
make -C       tb_elixirchip_es1_spu_op_all/${SIM}   distclean
make -C       tb_elixirchip_es1_spu_op_any/${SIM}   distclean
make -C     tb_elixirchip_es1_spu_op_match/${SIM}   distclean
make -C       tb_elixirchip_es1_spu_op_sel/${SIM}   distclean
make -C    tb_elixirchip_es1_spu_op_sel_lt/${SIM}   distclean
make -C       tb_elixirchip_es1_spu_op_sll/${SIM}   distclean
make -C       tb_elixirchip_es1_spu_op_srl/${SIM}   distclean
make -C       tb_elixirchip_es1_spu_op_sra/${SIM}   distclean
make -C       tb_elixirchip_es1_spu_op_nop/${SIM}   distclean
make -C       tb_elixirchip_es1_spu_op_reg/${SIM}   distclean
make -C       tb_elixirchip_es1_spu_op_mem/${SIM}   distclean
make -C    tb_elixirchip_es1_spu_op_mem_sp/${SIM}   distclean
#make -C  tb_elixirchip_es1_spu_op_simd_add/${SIM}  distclean
#make -C  tb_elixirchip_es1_spu_op_simd_acc/${SIM}  distclean


echo "All tests cleaned"
