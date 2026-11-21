// Lean compiler output
// Module: MOC.SpectralPerturbation
// Imports: Init MOC.Support Mathlib.Algebra.Polynomial.Roots Mathlib.Topology.Baire.CompleteMetrizable Mathlib.Topology.Baire.Lemmas
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
LEAN_EXPORT lean_object* l___private_MOC_SpectralPerturbation_0__MOC_spectralLine(lean_object*);
LEAN_EXPORT lean_object* l___private_MOC_SpectralPerturbation_0__MOC_spectralLine___elambda__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_MOC_SpectralPerturbation_0__MOC_spectralLine___elambda__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_579_(lean_object*);
LEAN_EXPORT lean_object* l___private_MOC_SpectralPerturbation_0__MOC_spectralLine___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_MOC_SpectralPerturbation_0__MOC_spectralLine___elambda__1(lean_object*);
lean_object* l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_664_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_MOC_SpectralPerturbation_0__MOC_spectralLine___elambda__2(lean_object*);
lean_object* l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_471_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_MOC_SpectralPerturbation_0__MOC_spectralLine___elambda__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
lean_inc(x_4);
x_6 = lean_apply_1(x_5, x_4);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
lean_dec(x_2);
x_8 = lean_apply_1(x_7, x_4);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_6, 0);
lean_inc(x_10);
lean_inc(x_10);
x_11 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_579_(x_10);
x_12 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_471_(x_9, x_11);
x_13 = lean_ctor_get(x_8, 1);
lean_inc(x_13);
lean_dec(x_8);
x_14 = lean_ctor_get(x_6, 1);
lean_inc(x_14);
lean_dec(x_6);
lean_inc(x_14);
x_15 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_579_(x_14);
x_16 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_471_(x_13, x_15);
x_17 = lean_ctor_get(x_3, 0);
lean_inc(x_17);
lean_inc(x_12);
lean_inc(x_17);
x_18 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_664_(x_17, x_12);
x_19 = lean_ctor_get(x_3, 1);
lean_inc(x_19);
lean_dec(x_3);
lean_inc(x_16);
lean_inc(x_19);
x_20 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_664_(x_19, x_16);
x_21 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_579_(x_20);
x_22 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_471_(x_18, x_21);
x_23 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_664_(x_17, x_16);
x_24 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_664_(x_19, x_12);
x_25 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_471_(x_23, x_24);
x_26 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_471_(x_10, x_22);
x_27 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_471_(x_14, x_25);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
LEAN_EXPORT lean_object* l___private_MOC_SpectralPerturbation_0__MOC_spectralLine___elambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_MOC_SpectralPerturbation_0__MOC_spectralLine___elambda__1___rarg), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_MOC_SpectralPerturbation_0__MOC_spectralLine___elambda__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
lean_inc(x_4);
x_6 = lean_apply_1(x_5, x_4);
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
lean_dec(x_2);
x_8 = lean_apply_1(x_7, x_4);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_6, 0);
lean_inc(x_10);
lean_inc(x_10);
x_11 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_579_(x_10);
x_12 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_471_(x_9, x_11);
x_13 = lean_ctor_get(x_8, 1);
lean_inc(x_13);
lean_dec(x_8);
x_14 = lean_ctor_get(x_6, 1);
lean_inc(x_14);
lean_dec(x_6);
lean_inc(x_14);
x_15 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_579_(x_14);
x_16 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_471_(x_13, x_15);
x_17 = lean_ctor_get(x_3, 0);
lean_inc(x_17);
lean_inc(x_12);
lean_inc(x_17);
x_18 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_664_(x_17, x_12);
x_19 = lean_ctor_get(x_3, 1);
lean_inc(x_19);
lean_dec(x_3);
lean_inc(x_16);
lean_inc(x_19);
x_20 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_664_(x_19, x_16);
x_21 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_579_(x_20);
x_22 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_471_(x_18, x_21);
x_23 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_664_(x_17, x_16);
x_24 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_664_(x_19, x_12);
x_25 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_471_(x_23, x_24);
x_26 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_471_(x_10, x_22);
x_27 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_471_(x_14, x_25);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
LEAN_EXPORT lean_object* l___private_MOC_SpectralPerturbation_0__MOC_spectralLine___elambda__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_MOC_SpectralPerturbation_0__MOC_spectralLine___elambda__2___rarg), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_MOC_SpectralPerturbation_0__MOC_spectralLine___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_4 = lean_alloc_closure((void*)(l___private_MOC_SpectralPerturbation_0__MOC_spectralLine___elambda__2___rarg), 4, 3);
lean_closure_set(x_4, 0, x_1);
lean_closure_set(x_4, 1, x_2);
lean_closure_set(x_4, 2, x_3);
x_5 = lean_alloc_closure((void*)(l___private_MOC_SpectralPerturbation_0__MOC_spectralLine___elambda__1___rarg), 4, 3);
lean_closure_set(x_5, 0, x_1);
lean_closure_set(x_5, 1, x_2);
lean_closure_set(x_5, 2, x_3);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_MOC_SpectralPerturbation_0__MOC_spectralLine(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_MOC_SpectralPerturbation_0__MOC_spectralLine___rarg), 3, 0);
return x_2;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_MOC_Support(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Algebra_Polynomial_Roots(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Topology_Baire_CompleteMetrizable(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Topology_Baire_Lemmas(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_MOC_SpectralPerturbation(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_MOC_Support(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Algebra_Polynomial_Roots(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Topology_Baire_CompleteMetrizable(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Topology_Baire_Lemmas(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
