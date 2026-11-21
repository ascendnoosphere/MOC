// Lean compiler output
// Module: MOC.Support
// Imports: Init MOC.Weights Mathlib.Analysis.Convex.Topology Mathlib.Analysis.NormedSpace.HahnBanach.Separation Mathlib.Analysis.SpecialFunctions.Pow.Complex Mathlib.Topology.Instances.Matrix
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
LEAN_EXPORT lean_object* l_MOC_matchingGap___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_579_(lean_object*);
lean_object* l_MOC_matchingProduct___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_664_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MOC_matchingGap(lean_object*);
lean_object* l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_471_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MOC_matchingGap___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_7 = l_MOC_matchingProduct___rarg(x_1, x_2, x_3, x_5);
x_8 = lean_ctor_get(x_4, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_inc(x_8);
x_10 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_664_(x_8, x_9);
x_11 = lean_ctor_get(x_4, 1);
lean_inc(x_11);
lean_dec(x_4);
x_12 = lean_ctor_get(x_7, 1);
lean_inc(x_12);
lean_dec(x_7);
lean_inc(x_11);
x_13 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_664_(x_11, x_12);
x_14 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_579_(x_13);
x_15 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_471_(x_10, x_14);
x_16 = l_MOC_matchingProduct___rarg(x_1, x_2, x_3, x_6);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_664_(x_8, x_17);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_664_(x_11, x_19);
x_21 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_579_(x_20);
x_22 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_471_(x_18, x_21);
x_23 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_579_(x_22);
x_24 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_471_(x_15, x_23);
return x_24;
}
}
LEAN_EXPORT lean_object* l_MOC_matchingGap(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_MOC_matchingGap___rarg), 6, 0);
return x_2;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_MOC_Weights(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Analysis_Convex_Topology(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Analysis_NormedSpace_HahnBanach_Separation(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Analysis_SpecialFunctions_Pow_Complex(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Topology_Instances_Matrix(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_MOC_Support(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_MOC_Weights(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Analysis_Convex_Topology(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Analysis_NormedSpace_HahnBanach_Separation(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Analysis_SpecialFunctions_Pow_Complex(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Topology_Instances_Matrix(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
