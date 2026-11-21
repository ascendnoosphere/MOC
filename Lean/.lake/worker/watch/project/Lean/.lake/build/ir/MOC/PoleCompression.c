// Lean compiler output
// Module: MOC.PoleCompression
// Imports: Init MOC.Geometry Mathlib.Algebra.BigOperators.Fin Mathlib.LinearAlgebra.FreeModule.Finite.Matrix Mathlib.Tactic.LinearCombination
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
LEAN_EXPORT lean_object* l_MOC_poleFactor(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Finset_prod___at_MOC_poleFactor___spec__2___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Finset_prod___at_MOC_poleFactor___spec__1___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Finset_prod___at_MOC_poleFactor___spec__2___rarg(lean_object*, lean_object*);
static lean_object* l_MOC_poleFactor___closed__1;
lean_object* l_Multiset_map___rarg(lean_object*, lean_object*);
lean_object* l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_579_(lean_object*);
lean_object* l_Multiset_prod___at_MOC_matchingProduct___spec__2(lean_object*);
lean_object* l_Fin_succAbove___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MOC_poleFactor___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_664_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Finset_prod___at_MOC_poleFactor___spec__2(lean_object*);
lean_object* l_List_ofFn___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Finset_prod___at_MOC_poleFactor___spec__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Finset_prod___at_MOC_poleFactor___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_MOC_poleFactor___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_471_(lean_object*, lean_object*);
lean_object* l_List_finRange___lambda__1___boxed(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MOC_poleFactor___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Finset_prod___at_MOC_poleFactor___spec__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Multiset_map___rarg(x_2, x_1);
x_4 = l_Multiset_prod___at_MOC_matchingProduct___spec__2(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Finset_prod___at_MOC_poleFactor___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Finset_prod___at_MOC_poleFactor___spec__1___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Finset_prod___at_MOC_poleFactor___spec__2___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Multiset_map___rarg(x_2, x_1);
x_4 = l_Multiset_prod___at_MOC_matchingProduct___spec__2(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Finset_prod___at_MOC_poleFactor___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Finset_prod___at_MOC_poleFactor___spec__2___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_MOC_poleFactor___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_4 = l_Fin_succAbove___rarg(x_1, x_3);
lean_inc(x_2);
x_5 = lean_apply_1(x_2, x_4);
x_6 = lean_apply_1(x_2, x_1);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
x_9 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_579_(x_8);
x_10 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_471_(x_7, x_9);
x_11 = lean_ctor_get(x_5, 1);
lean_inc(x_11);
lean_dec(x_5);
x_12 = lean_ctor_get(x_6, 1);
lean_inc(x_12);
lean_dec(x_6);
x_13 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_579_(x_12);
x_14 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_471_(x_11, x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_10);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_MOC_poleFactor___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_5 = lean_apply_1(x_1, x_4);
x_6 = lean_apply_1(x_2, x_3);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
x_9 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_471_(x_7, x_8);
x_10 = lean_ctor_get(x_5, 1);
lean_inc(x_10);
lean_dec(x_5);
x_11 = lean_ctor_get(x_6, 1);
lean_inc(x_11);
lean_dec(x_6);
x_12 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_471_(x_10, x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
static lean_object* _init_l_MOC_poleFactor___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_List_finRange___lambda__1___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_MOC_poleFactor(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_5 = l_MOC_poleFactor___closed__1;
lean_inc(x_1);
x_6 = l_List_ofFn___rarg(x_1, x_5);
lean_inc(x_2);
lean_inc(x_4);
x_7 = lean_alloc_closure((void*)(l_MOC_poleFactor___lambda__1___boxed), 3, 2);
lean_closure_set(x_7, 0, x_4);
lean_closure_set(x_7, 1, x_2);
x_8 = l_Finset_prod___at_MOC_poleFactor___spec__1___rarg(x_6, x_7);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_1, x_9);
lean_dec(x_1);
x_11 = l_List_ofFn___rarg(x_10, x_5);
x_12 = lean_alloc_closure((void*)(l_MOC_poleFactor___lambda__2), 4, 3);
lean_closure_set(x_12, 0, x_3);
lean_closure_set(x_12, 1, x_2);
lean_closure_set(x_12, 2, x_4);
x_13 = l_Finset_prod___at_MOC_poleFactor___spec__2___rarg(x_11, x_12);
x_14 = lean_ctor_get(x_8, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_inc(x_15);
lean_inc(x_14);
x_16 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_664_(x_14, x_15);
x_17 = lean_ctor_get(x_8, 1);
lean_inc(x_17);
lean_dec(x_8);
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_dec(x_13);
lean_inc(x_18);
lean_inc(x_17);
x_19 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_664_(x_17, x_18);
x_20 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_579_(x_19);
x_21 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_471_(x_16, x_20);
x_22 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_664_(x_14, x_18);
x_23 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_664_(x_17, x_15);
x_24 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_471_(x_22, x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_21);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
LEAN_EXPORT lean_object* l_Finset_prod___at_MOC_poleFactor___spec__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Finset_prod___at_MOC_poleFactor___spec__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Finset_prod___at_MOC_poleFactor___spec__2___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Finset_prod___at_MOC_poleFactor___spec__2(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_MOC_poleFactor___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_MOC_poleFactor___lambda__1(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_MOC_Geometry(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Algebra_BigOperators_Fin(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_LinearAlgebra_FreeModule_Finite_Matrix(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Tactic_LinearCombination(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_MOC_PoleCompression(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_MOC_Geometry(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Algebra_BigOperators_Fin(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_LinearAlgebra_FreeModule_Finite_Matrix(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Tactic_LinearCombination(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_MOC_poleFactor___closed__1 = _init_l_MOC_poleFactor___closed__1();
lean_mark_persistent(l_MOC_poleFactor___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
