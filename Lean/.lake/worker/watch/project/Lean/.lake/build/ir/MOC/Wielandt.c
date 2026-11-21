// Lean compiler output
// Module: MOC.Wielandt
// Imports: Init MOC.Singular Mathlib.Analysis.Convex.Topology Mathlib.Analysis.NormedSpace.HahnBanach.Separation Mathlib.Tactic.Linarith
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
LEAN_EXPORT lean_object* l___private_MOC_Wielandt_0__MOC_circleLinePolynomial(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Complex_normSq(lean_object*);
lean_object* l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_664_(lean_object*, lean_object*);
lean_object* l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_471_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_MOC_Wielandt_0__MOC_circleLinePolynomial(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_664_(x_1, x_6);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
x_9 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_664_(x_2, x_8);
x_10 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_471_(x_7, x_9);
x_11 = l_Complex_normSq(x_5);
x_12 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_664_(x_3, x_11);
x_13 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_471_(x_10, x_12);
x_14 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_471_(x_13, x_4);
return x_14;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_MOC_Singular(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Analysis_Convex_Topology(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Analysis_NormedSpace_HahnBanach_Separation(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Tactic_Linarith(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_MOC_Wielandt(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_MOC_Singular(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Analysis_Convex_Topology(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Analysis_NormedSpace_HahnBanach_Separation(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Tactic_Linarith(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
