// Lean compiler output
// Module: MOC.SparseRow
// Imports: Init MOC.SupportBlocks Mathlib.Algebra.BigOperators.Fin
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
LEAN_EXPORT lean_object* l___private_MOC_SparseRow_0__MOC_weightedEntries___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_MOC_SparseRow_0__MOC_weightedEntries(lean_object*);
lean_object* l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_579_(lean_object*);
lean_object* l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_664_(lean_object*, lean_object*);
lean_object* l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_471_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_MOC_SparseRow_0__MOC_weightedEntries___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_inc(x_4);
x_6 = lean_apply_1(x_1, x_4);
lean_inc(x_5);
x_7 = lean_apply_1(x_2, x_5);
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
x_10 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_471_(x_8, x_9);
x_11 = lean_ctor_get(x_6, 1);
lean_inc(x_11);
lean_dec(x_6);
x_12 = lean_ctor_get(x_7, 1);
lean_inc(x_12);
lean_dec(x_7);
x_13 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_471_(x_11, x_12);
x_14 = lean_apply_2(x_3, x_4, x_5);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_inc(x_15);
lean_inc(x_10);
x_16 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_664_(x_10, x_15);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
lean_inc(x_17);
lean_inc(x_13);
x_18 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_664_(x_13, x_17);
x_19 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_579_(x_18);
x_20 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_471_(x_16, x_19);
x_21 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_664_(x_10, x_17);
x_22 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_664_(x_13, x_15);
x_23 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_471_(x_21, x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_20);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
LEAN_EXPORT lean_object* l___private_MOC_SparseRow_0__MOC_weightedEntries(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_MOC_SparseRow_0__MOC_weightedEntries___rarg), 5, 0);
return x_2;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_MOC_SupportBlocks(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Algebra_BigOperators_Fin(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_MOC_SparseRow(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_MOC_SupportBlocks(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Algebra_BigOperators_Fin(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
