// Lean compiler output
// Module: MOC.Singular
// Imports: Init MOC.Small Mathlib.Algebra.Polynomial.Roots Mathlib.Analysis.Convex.Caratheodory Mathlib.Analysis.InnerProductSpace.Adjoint Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
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
LEAN_EXPORT lean_object* l___private_MOC_Singular_0__MOC_taggedLift___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_MOC_Singular_0__MOC_taggedLift___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_MOC_Singular_0__MOC_taggedLift___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Complex_normSq(lean_object*);
lean_object* l_Matrix_vecEmpty___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MOC_spectralMomentLift(lean_object*);
extern lean_object* l___private_Mathlib_Data_Real_Basic_0__Real_one;
static lean_object* l___private_MOC_Singular_0__MOC_taggedLift___rarg___lambda__2___closed__1;
lean_object* l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_579_(lean_object*);
lean_object* l_Sum_elim___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_MOC_Singular_0__MOC_taggedLift(lean_object*, lean_object*);
static lean_object* l___private_MOC_Singular_0__MOC_taggedLift___rarg___lambda__1___closed__2;
LEAN_EXPORT lean_object* l___private_MOC_Singular_0__MOC_taggedLift___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Fin_cases(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_MOC_Singular_0__MOC_taggedLift___rarg___lambda__1___closed__1;
LEAN_EXPORT lean_object* l___private_MOC_Singular_0__MOC_taggedLift___rarg___lambda__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Matrix_vecCons___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l___private_MOC_Singular_0__MOC_taggedLift___rarg___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Matrix_vecEmpty___boxed), 2, 1);
lean_closure_set(x_1, 0, lean_box(0));
return x_1;
}
}
static lean_object* _init_l___private_MOC_Singular_0__MOC_taggedLift___rarg___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l___private_Mathlib_Data_Real_Basic_0__Real_one;
x_3 = l___private_MOC_Singular_0__MOC_taggedLift___rarg___lambda__1___closed__1;
x_4 = lean_alloc_closure((void*)(l_Matrix_vecCons___rarg___boxed), 4, 3);
lean_closure_set(x_4, 0, x_1);
lean_closure_set(x_4, 1, x_2);
lean_closure_set(x_4, 2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_MOC_Singular_0__MOC_taggedLift___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_4 = lean_apply_1(x_1, x_2);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
x_7 = l_Complex_normSq(x_4);
x_8 = lean_unsigned_to_nat(1u);
x_9 = l___private_MOC_Singular_0__MOC_taggedLift___rarg___lambda__1___closed__2;
x_10 = lean_alloc_closure((void*)(l_Matrix_vecCons___rarg___boxed), 4, 3);
lean_closure_set(x_10, 0, x_8);
lean_closure_set(x_10, 1, x_7);
lean_closure_set(x_10, 2, x_9);
x_11 = lean_unsigned_to_nat(2u);
x_12 = lean_alloc_closure((void*)(l_Matrix_vecCons___rarg___boxed), 4, 3);
lean_closure_set(x_12, 0, x_11);
lean_closure_set(x_12, 1, x_6);
lean_closure_set(x_12, 2, x_10);
x_13 = lean_unsigned_to_nat(3u);
x_14 = l_Fin_cases(x_13, lean_box(0), x_5, x_12, x_3);
lean_dec(x_5);
return x_14;
}
}
static lean_object* _init_l___private_MOC_Singular_0__MOC_taggedLift___rarg___lambda__2___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l___private_Mathlib_Data_Real_Basic_0__Real_zero;
x_3 = l___private_MOC_Singular_0__MOC_taggedLift___rarg___lambda__1___closed__1;
x_4 = lean_alloc_closure((void*)(l_Matrix_vecCons___rarg___boxed), 4, 3);
lean_closure_set(x_4, 0, x_1);
lean_closure_set(x_4, 1, x_2);
lean_closure_set(x_4, 2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_MOC_Singular_0__MOC_taggedLift___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_4 = lean_apply_1(x_1, x_2);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_579_(x_5);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
x_8 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_579_(x_7);
x_9 = l_Complex_normSq(x_4);
x_10 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_579_(x_9);
x_11 = lean_unsigned_to_nat(1u);
x_12 = l___private_MOC_Singular_0__MOC_taggedLift___rarg___lambda__2___closed__1;
x_13 = lean_alloc_closure((void*)(l_Matrix_vecCons___rarg___boxed), 4, 3);
lean_closure_set(x_13, 0, x_11);
lean_closure_set(x_13, 1, x_10);
lean_closure_set(x_13, 2, x_12);
x_14 = lean_unsigned_to_nat(2u);
x_15 = lean_alloc_closure((void*)(l_Matrix_vecCons___rarg___boxed), 4, 3);
lean_closure_set(x_15, 0, x_14);
lean_closure_set(x_15, 1, x_8);
lean_closure_set(x_15, 2, x_13);
x_16 = lean_unsigned_to_nat(3u);
x_17 = l_Fin_cases(x_16, lean_box(0), x_6, x_15, x_3);
lean_dec(x_6);
return x_17;
}
}
LEAN_EXPORT lean_object* l___private_MOC_Singular_0__MOC_taggedLift___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_alloc_closure((void*)(l___private_MOC_Singular_0__MOC_taggedLift___rarg___lambda__1___boxed), 3, 1);
lean_closure_set(x_5, 0, x_1);
x_6 = lean_alloc_closure((void*)(l___private_MOC_Singular_0__MOC_taggedLift___rarg___lambda__2___boxed), 3, 1);
lean_closure_set(x_6, 0, x_2);
x_7 = l_Sum_elim___rarg(x_5, x_6, x_3);
x_8 = lean_apply_1(x_7, x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_MOC_Singular_0__MOC_taggedLift(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_MOC_Singular_0__MOC_taggedLift___rarg), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_MOC_Singular_0__MOC_taggedLift___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_MOC_Singular_0__MOC_taggedLift___rarg___lambda__1(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_MOC_Singular_0__MOC_taggedLift___rarg___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_MOC_Singular_0__MOC_taggedLift___rarg___lambda__2(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_MOC_spectralMomentLift(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
lean_inc(x_1);
x_2 = l_Complex_normSq(x_1);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_MOC_Small(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Algebra_Polynomial_Roots(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Analysis_Convex_Caratheodory(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Analysis_InnerProductSpace_Adjoint(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_LinearAlgebra_AffineSpace_FiniteDimensional(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_LinearAlgebra_Matrix_Charpoly_Coeff(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_LinearAlgebra_Matrix_ToLinearEquiv(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_MOC_Singular(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_MOC_Small(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Algebra_Polynomial_Roots(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Analysis_Convex_Caratheodory(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Analysis_InnerProductSpace_Adjoint(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_LinearAlgebra_AffineSpace_FiniteDimensional(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_LinearAlgebra_Matrix_Charpoly_Coeff(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_LinearAlgebra_Matrix_ToLinearEquiv(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_MOC_Singular_0__MOC_taggedLift___rarg___lambda__1___closed__1 = _init_l___private_MOC_Singular_0__MOC_taggedLift___rarg___lambda__1___closed__1();
lean_mark_persistent(l___private_MOC_Singular_0__MOC_taggedLift___rarg___lambda__1___closed__1);
l___private_MOC_Singular_0__MOC_taggedLift___rarg___lambda__1___closed__2 = _init_l___private_MOC_Singular_0__MOC_taggedLift___rarg___lambda__1___closed__2();
lean_mark_persistent(l___private_MOC_Singular_0__MOC_taggedLift___rarg___lambda__1___closed__2);
l___private_MOC_Singular_0__MOC_taggedLift___rarg___lambda__2___closed__1 = _init_l___private_MOC_Singular_0__MOC_taggedLift___rarg___lambda__2___closed__1();
lean_mark_persistent(l___private_MOC_Singular_0__MOC_taggedLift___rarg___lambda__2___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
