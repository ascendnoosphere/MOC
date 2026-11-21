// Lean compiler output
// Module: MOC.SpectralKKT
// Imports: Init MOC.SpectralGap Mathlib.Analysis.Calculus.Deriv.Inv Mathlib.Analysis.Calculus.Deriv.Pow Mathlib.Analysis.InnerProductSpace.PiL2
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
LEAN_EXPORT lean_object* l_Finset_prod___at_MOC_matchingCoordinateCoefficient___spec__1___rarg(lean_object*, lean_object*);
lean_object* l_Multiset_erase___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_MOC_SpectralKKT_0__MOC_matchingCoordinateCoefficient_match__1_splitter(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_MOC_SpectralKKT_0__MOC_matchingCoordinateCoefficient_match__1_splitter___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Multiset_map___rarg(lean_object*, lean_object*);
lean_object* l_Multiset_prod___at_MOC_matchingProduct___spec__2(lean_object*);
lean_object* l_Equiv_symm___elambda__2___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MOC_matchingCoordinateCoefficient(lean_object*);
LEAN_EXPORT lean_object* l_MOC_matchingCoordinateCoefficient___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_471_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MOC_matchingCoordinateCoefficient___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Finset_prod___at_MOC_matchingCoordinateCoefficient___spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Finset_prod___at_MOC_matchingCoordinateCoefficient___spec__2___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Finset_prod___at_MOC_matchingCoordinateCoefficient___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Finset_prod___at_MOC_matchingCoordinateCoefficient___spec__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Multiset_map___rarg(x_2, x_1);
x_4 = l_Multiset_prod___at_MOC_matchingProduct___spec__2(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Finset_prod___at_MOC_matchingCoordinateCoefficient___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Finset_prod___at_MOC_matchingCoordinateCoefficient___spec__1___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Finset_prod___at_MOC_matchingCoordinateCoefficient___spec__2___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Multiset_map___rarg(x_2, x_1);
x_4 = l_Multiset_prod___at_MOC_matchingProduct___spec__2(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Finset_prod___at_MOC_matchingCoordinateCoefficient___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Finset_prod___at_MOC_matchingCoordinateCoefficient___spec__2___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_MOC_matchingCoordinateCoefficient___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
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
x_11 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_471_(x_9, x_10);
x_12 = lean_ctor_get(x_7, 1);
lean_inc(x_12);
lean_dec(x_7);
x_13 = lean_ctor_get(x_8, 1);
lean_inc(x_13);
lean_dec(x_8);
x_14 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_471_(x_12, x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_11);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_MOC_matchingCoordinateCoefficient___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
lean_inc(x_5);
x_8 = l_Equiv_symm___elambda__2___rarg(x_5, x_7);
x_9 = l_Multiset_erase___rarg(x_2, x_1, x_8);
x_10 = lean_alloc_closure((void*)(l_MOC_matchingCoordinateCoefficient___rarg___lambda__1), 4, 3);
lean_closure_set(x_10, 0, x_5);
lean_closure_set(x_10, 1, x_3);
lean_closure_set(x_10, 2, x_4);
x_11 = l_Finset_prod___at_MOC_matchingCoordinateCoefficient___spec__1___rarg(x_9, x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_6, 0);
lean_inc(x_12);
lean_dec(x_6);
x_13 = l_Multiset_erase___rarg(x_2, x_1, x_12);
x_14 = lean_alloc_closure((void*)(l_MOC_matchingCoordinateCoefficient___rarg___lambda__1), 4, 3);
lean_closure_set(x_14, 0, x_5);
lean_closure_set(x_14, 1, x_3);
lean_closure_set(x_14, 2, x_4);
x_15 = l_Finset_prod___at_MOC_matchingCoordinateCoefficient___spec__2___rarg(x_13, x_14);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_MOC_matchingCoordinateCoefficient(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_MOC_matchingCoordinateCoefficient___rarg), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_MOC_SpectralKKT_0__MOC_matchingCoordinateCoefficient_match__1_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_3, x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l___private_MOC_SpectralKKT_0__MOC_matchingCoordinateCoefficient_match__1_splitter(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_MOC_SpectralKKT_0__MOC_matchingCoordinateCoefficient_match__1_splitter___rarg), 3, 0);
return x_3;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_MOC_SpectralGap(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Analysis_Calculus_Deriv_Inv(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Analysis_Calculus_Deriv_Pow(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Analysis_InnerProductSpace_PiL2(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_MOC_SpectralKKT(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_MOC_SpectralGap(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Analysis_Calculus_Deriv_Inv(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Analysis_Calculus_Deriv_Pow(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Analysis_InnerProductSpace_PiL2(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
