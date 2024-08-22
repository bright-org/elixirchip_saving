

#ifndef __ELIXIRCHIP_ES1_SPU_OP_ADD_H__
#define __ELIXIRCHIP_ES1_SPU_OP_ADD_H__

#include <string>

#ifdef __cplusplus
extern "C" {
#endif

// 作成したライブラリの関数宣言
void* elixirchip_es1_spu_op_add_create(const char *name);
void  elixirchip_es1_spu_op_add_delete(void* handle);
void  elixirchip_es1_spu_op_add(void* handle, int s_carry, int s_data0, int s_data1, int s_clear, int s_valid, int& m_data, int& m_carry, int& m_msb_c);

#ifdef __cplusplus
}
#endif


#endif // __ELIXIRCHIP_ES1_SPU_OP_ADD_H__

