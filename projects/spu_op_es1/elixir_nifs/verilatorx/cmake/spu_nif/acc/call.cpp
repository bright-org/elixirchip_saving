#include <erl_nif.h>
#include <string.h>

#include "wrapper.h"

ErlNifResourceType *SpuAccType;

void get_args(
    ErlNifEnv *env, const ERL_NIF_TERM argv[],
    int *s_sub,
    int *s_carry,
    int *s_data,
    int *s_clear,
    int *s_valid,
    int *m_carry,
    int *m_data)
{
    enif_get_int(env, argv[1], s_sub);
    enif_get_int(env, argv[2], s_carry);
    enif_get_int(env, argv[3], s_data);
    enif_get_int(env, argv[4], s_clear);
    enif_get_int(env, argv[5], s_valid);
    enif_get_int(env, argv[6], m_carry);
    enif_get_int(env, argv[7], m_data);
}

void destruct_spu_acc(ErlNifEnv *caller_env, void *obj)
{
    enif_fprintf(stdout, "destruct %p\n", obj);
    SpuAcc *spu_acc = (SpuAcc *)obj;
    elixirchip_es1_spu_op_acc_delete_#{bit}bit(spu_acc);
}

int load(ErlNifEnv *caller_env, void **priv_data, ERL_NIF_TERM load_info)
{
    SpuAccType = enif_open_resource_type(caller_env, "SpuAcc", "SpuAcc", destruct_spu_acc, ERL_NIF_RT_CREATE, nullptr);
    return 0;
}

ERL_NIF_TERM create(ErlNifEnv *env, int argc, const ERL_NIF_TERM argv[])
{
    // 文字列取り出し
    ErlNifBinary bin;
    if (!enif_inspect_binary(env, argv[0], &bin))
    {
        return enif_make_badarg(env);
    }
    char *str = (char *)malloc(bin.size + 1);
    memcpy(str, bin.data, bin.size);
    str[bin.size] = '\0';

    // 生成
    SpuAcc *resource = (SpuAcc *)enif_alloc_resource(SpuAccType, sizeof(SpuAcc));
    elixirchip_es1_spu_op_acc_create_#{bit}bit(resource, str);
    ERL_NIF_TERM handle = enif_make_resource(env, resource);

    // リソースオブジェクトを返す
    free(str);
    return enif_make_tuple2(env, enif_make_atom(env, "ok"), handle);
}

ERL_NIF_TERM acc_clk(ErlNifEnv *env, int argc, const ERL_NIF_TERM argv[])
{
    void *resource;
    enif_get_resource(env, argv[0], SpuAccType, &resource);
    SpuAcc *spu = (SpuAcc *)resource;

    int s_sub, s_carry, s_data, s_clear, s_valid, m_carry, m_data;
    get_args(env, argv, &s_sub, &s_carry, &s_data, &s_clear, &s_valid, &m_carry, &m_data);

    elixirchip_es1_spu_op_acc_#{bit}bit(spu, s_sub, s_carry, s_data, s_clear, s_valid, m_carry, m_data);
    // enif_fprintf(stdout, "test %p\n", m_data);

    return enif_make_tuple3(
        env, 
        enif_make_atom(env, "ok"),
        enif_make_int(env, m_carry),
        enif_make_int(env, m_data)
        );
}

static ErlNifFunc nif_funcs[] = {
    {"create", 1, create},
    {"acc_clk", 8, acc_clk}};

ERL_NIF_INIT(Elixir.SpuNif, nif_funcs, load, NULL, NULL, NULL)
