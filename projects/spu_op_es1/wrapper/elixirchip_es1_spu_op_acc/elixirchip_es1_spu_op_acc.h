

#ifndef __ELIXIRCHIP_ES1_SPU_OP_ACC__H__
#define __ELIXIRCHIP_ES1_SPU_OP_ACC__H__

#include <string>

#ifdef __cplusplus
extern "C" {
#endif

// 作成したライブラリの関数宣言
void* elixirchip_es1_spu_op_acc_create(const char *name);
void  elixirchip_es1_spu_op_acc_delete(void* handle);
void  elixirchip_es1_spu_op_acc(
            void* handle,
            int s_sub,
            int s_carry,
            int s_data,
            int s_clear,
            int s_valid,
            int& m_carry,
            int& m_data
        );

#ifdef __cplusplus
}
#endif


#endif // __ELIXIRCHIP_ES1_SPU_OP_ACC__H__

