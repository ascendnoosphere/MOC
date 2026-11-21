// Lean compiler output
// Module: MOC.AnchoredChart
// Imports: Init MOC.Source
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
extern lean_object* l___private_Mathlib_Data_Real_Basic_0__Real_zero;
LEAN_EXPORT lean_object* l_MOC_anchoredMatchingCoordinate___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Multiset_map___rarg(lean_object*, lean_object*);
extern lean_object* l___private_Mathlib_Data_Real_Basic_0__Real_one;
lean_object* l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_579_(lean_object*);
lean_object* l_Multiset_prod___at_MOC_matchingProduct___spec__2(lean_object*);
LEAN_EXPORT lean_object* l_MOC_anchoredMatchingCoordinate(lean_object*);
LEAN_EXPORT lean_object* l_MOC_anchoredMatchingCoordinate___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_664_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Finset_prod___at_MOC_anchoredMatchingCoordinate___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Finset_prod___at_MOC_anchoredMatchingCoordinate___spec__1___rarg(lean_object*, lean_object*);
lean_object* l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_471_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Finset_prod___at_MOC_anchoredMatchingCoordinate___spec__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Multiset_map___rarg(x_2, x_1);
x_4 = l_Multiset_prod___at_MOC_matchingProduct___spec__2(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Finset_prod___at_MOC_anchoredMatchingCoordinate___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Finset_prod___at_MOC_anchoredMatchingCoordinate___spec__1___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_MOC_anchoredMatchingCoordinate___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
lean_inc(x_4);
x_6 = lean_apply_1(x_5, x_4);
x_7 = lean_apply_1(x_2, x_6);
x_8 = lean_apply_1(x_3, x_4);
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_inc(x_10);
lean_inc(x_9);
x_11 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_664_(x_9, x_10);
x_12 = lean_ctor_get(x_7, 1);
lean_inc(x_12);
lean_dec(x_7);
x_13 = lean_ctor_get(x_8, 1);
lean_inc(x_13);
lean_dec(x_8);
lean_inc(x_13);
lean_inc(x_12);
x_14 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_664_(x_12, x_13);
x_15 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_579_(x_14);
x_16 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_471_(x_11, x_15);
x_17 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_664_(x_9, x_13);
x_18 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_664_(x_12, x_10);
x_19 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_471_(x_17, x_18);
x_20 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_579_(x_16);
x_21 = l___private_Mathlib_Data_Real_Basic_0__Real_one;
x_22 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_471_(x_21, x_20);
x_23 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_579_(x_19);
x_24 = l___private_Mathlib_Data_Real_Basic_0__Real_zero;
x_25 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_471_(x_24, x_23);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_22);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
LEAN_EXPORT lean_object* l_MOC_anchoredMatchingCoordinate___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_6 = lean_alloc_closure((void*)(l_MOC_anchoredMatchingCoordinate___rarg___lambda__1), 4, 3);
lean_closure_set(x_6, 0, x_5);
lean_closure_set(x_6, 1, x_3);
lean_closure_set(x_6, 2, x_4);
x_7 = l_Finset_prod___at_MOC_anchoredMatchingCoordinate___spec__1___rarg(x_1, x_6);
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_inc(x_9);
lean_inc(x_8);
x_10 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_664_(x_8, x_9);
x_11 = lean_ctor_get(x_2, 1);
lean_inc(x_11);
lean_dec(x_2);
x_12 = lean_ctor_get(x_7, 1);
lean_inc(x_12);
lean_dec(x_7);
lean_inc(x_12);
lean_inc(x_11);
x_13 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_664_(x_11, x_12);
x_14 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_579_(x_13);
x_15 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_471_(x_10, x_14);
x_16 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_664_(x_8, x_12);
x_17 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_664_(x_11, x_9);
x_18 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_471_(x_16, x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_15);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
LEAN_EXPORT lean_object* l_MOC_anchoredMatchingCoordinate(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_MOC_anchoredMatchingCoordinate___rarg), 5, 0);
return x_2;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_MOC_Source(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_MOC_AnchoredChart(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_MOC_Source(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
