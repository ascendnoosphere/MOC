// Lean compiler output
// Module: MOC.TwoExceptions
// Imports: Init MOC.TwoFrame MOC.Weights Mathlib.LinearAlgebra.Matrix.SchurComplement Mathlib.Logic.Equiv.Fintype Mathlib.Topology.Algebra.Module.Cardinality Mathlib.Topology.Instances.Matrix
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
LEAN_EXPORT lean_object* l___private_MOC_TwoExceptions_0__MOC_pairEmbedding___elambda__1___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Matrix_vecEmpty___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_MOC_TwoExceptions_0__MOC_pairEmbedding___elambda__1(lean_object*);
LEAN_EXPORT lean_object* l___private_MOC_TwoExceptions_0__MOC_pairEmbedding___elambda__1___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_MOC_TwoExceptions_0__MOC_pairEmbedding___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Fin_cases(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_MOC_TwoExceptions_0__MOC_pairEmbedding(lean_object*);
static lean_object* l___private_MOC_TwoExceptions_0__MOC_pairEmbedding___rarg___closed__1;
lean_object* l_Matrix_vecCons___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_MOC_TwoExceptions_0__MOC_pairEmbedding___elambda__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_unsigned_to_nat(1u);
x_5 = l_Fin_cases(x_4, lean_box(0), x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_MOC_TwoExceptions_0__MOC_pairEmbedding___elambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_MOC_TwoExceptions_0__MOC_pairEmbedding___elambda__1___rarg___boxed), 3, 0);
return x_2;
}
}
static lean_object* _init_l___private_MOC_TwoExceptions_0__MOC_pairEmbedding___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Matrix_vecEmpty___boxed), 2, 1);
lean_closure_set(x_1, 0, lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_MOC_TwoExceptions_0__MOC_pairEmbedding___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = l___private_MOC_TwoExceptions_0__MOC_pairEmbedding___rarg___closed__1;
x_6 = lean_alloc_closure((void*)(l_Matrix_vecCons___rarg___boxed), 4, 3);
lean_closure_set(x_6, 0, x_4);
lean_closure_set(x_6, 1, x_2);
lean_closure_set(x_6, 2, x_5);
x_7 = lean_alloc_closure((void*)(l___private_MOC_TwoExceptions_0__MOC_pairEmbedding___elambda__1___rarg___boxed), 3, 2);
lean_closure_set(x_7, 0, x_1);
lean_closure_set(x_7, 1, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_MOC_TwoExceptions_0__MOC_pairEmbedding(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_MOC_TwoExceptions_0__MOC_pairEmbedding___rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_MOC_TwoExceptions_0__MOC_pairEmbedding___elambda__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_MOC_TwoExceptions_0__MOC_pairEmbedding___elambda__1___rarg(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_MOC_TwoFrame(uint8_t builtin, lean_object*);
lean_object* initialize_MOC_Weights(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_LinearAlgebra_Matrix_SchurComplement(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Logic_Equiv_Fintype(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Topology_Algebra_Module_Cardinality(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Topology_Instances_Matrix(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_MOC_TwoExceptions(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_MOC_TwoFrame(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_MOC_Weights(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_LinearAlgebra_Matrix_SchurComplement(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Logic_Equiv_Fintype(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Topology_Algebra_Module_Cardinality(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Topology_Instances_Matrix(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_MOC_TwoExceptions_0__MOC_pairEmbedding___rarg___closed__1 = _init_l___private_MOC_TwoExceptions_0__MOC_pairEmbedding___rarg___closed__1();
lean_mark_persistent(l___private_MOC_TwoExceptions_0__MOC_pairEmbedding___rarg___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
