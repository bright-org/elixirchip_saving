#include <erl_nif.h>

static ERL_NIF_TERM
hello_nif(ErlNifEnv *env, int argc, const ERL_NIF_TERM argv[]) {
  return enif_make_int(env, 1);
}

// Let's define the array of ErlNifFunc beforehand:
static ErlNifFunc nif_funcs[] = {
  // {erl_function_name, erl_function_arity, c_function}
  {"hello_nif", 0, hello_nif}
};

ERL_NIF_INIT(Elixir.Hello, nif_funcs, NULL, NULL, NULL, NULL)