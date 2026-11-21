// Lean compiler output
// Module: MOC.ContactRectangle
// Imports: Init MOC.Obstruction Mathlib.Tactic.LinearCombination
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
lean_object* l_Equiv_swap___elambda__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_MOC_ContactRectangle_0__MOC_positiveMixedPerm___boxed(lean_object*);
lean_object* l_instDecidableEqFin___rarg___boxed(lean_object*, lean_object*);
lean_object* l_Matrix_vecEmpty___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_MOC_ContactRectangle_0__MOC_positiveMixedPerm(lean_object*);
lean_object* l_Equiv_trans___rarg(lean_object*, lean_object*);
static lean_object* l___private_MOC_ContactRectangle_0__MOC_positiveMixedPerm___closed__1;
static lean_object* l_Equiv_swap___at___private_MOC_ContactRectangle_0__MOC_positiveMixedPerm___spec__1___closed__1;
lean_object* l_Fin_cases(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Matrix_vecCons___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Equiv_swap___at___private_MOC_ContactRectangle_0__MOC_positiveMixedPerm___spec__1(lean_object*, lean_object*);
static lean_object* _init_l_Equiv_swap___at___private_MOC_ContactRectangle_0__MOC_positiveMixedPerm___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_instDecidableEqFin___rarg___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Equiv_swap___at___private_MOC_ContactRectangle_0__MOC_positiveMixedPerm___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_Equiv_swap___at___private_MOC_ContactRectangle_0__MOC_positiveMixedPerm___spec__1___closed__1;
x_4 = lean_alloc_closure((void*)(l_Equiv_swap___elambda__1___rarg), 4, 3);
lean_closure_set(x_4, 0, x_3);
lean_closure_set(x_4, 1, x_1);
lean_closure_set(x_4, 2, x_2);
lean_inc(x_4);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_4);
return x_5;
}
}
static lean_object* _init_l___private_MOC_ContactRectangle_0__MOC_positiveMixedPerm___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Matrix_vecEmpty___boxed), 2, 1);
lean_closure_set(x_1, 0, lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_MOC_ContactRectangle_0__MOC_positiveMixedPerm(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_unsigned_to_nat(2u);
x_4 = l_Equiv_swap___at___private_MOC_ContactRectangle_0__MOC_positiveMixedPerm___spec__1(x_2, x_3);
x_5 = lean_unsigned_to_nat(3u);
x_6 = l_Equiv_swap___at___private_MOC_ContactRectangle_0__MOC_positiveMixedPerm___spec__1(x_2, x_5);
lean_inc(x_4);
x_7 = l_Equiv_trans___rarg(x_6, x_4);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Equiv_swap___at___private_MOC_ContactRectangle_0__MOC_positiveMixedPerm___spec__1(x_8, x_2);
lean_inc(x_9);
x_10 = l_Equiv_trans___rarg(x_4, x_9);
x_11 = l_Equiv_swap___at___private_MOC_ContactRectangle_0__MOC_positiveMixedPerm___spec__1(x_8, x_3);
x_12 = l_Equiv_swap___at___private_MOC_ContactRectangle_0__MOC_positiveMixedPerm___spec__1(x_3, x_5);
x_13 = l_Equiv_trans___rarg(x_12, x_11);
x_14 = l_Equiv_swap___at___private_MOC_ContactRectangle_0__MOC_positiveMixedPerm___spec__1(x_8, x_5);
x_15 = l_Equiv_trans___rarg(x_14, x_9);
x_16 = l___private_MOC_ContactRectangle_0__MOC_positiveMixedPerm___closed__1;
x_17 = lean_alloc_closure((void*)(l_Matrix_vecCons___rarg___boxed), 4, 3);
lean_closure_set(x_17, 0, x_8);
lean_closure_set(x_17, 1, x_15);
lean_closure_set(x_17, 2, x_16);
x_18 = lean_alloc_closure((void*)(l_Matrix_vecCons___rarg___boxed), 4, 3);
lean_closure_set(x_18, 0, x_2);
lean_closure_set(x_18, 1, x_13);
lean_closure_set(x_18, 2, x_17);
x_19 = lean_alloc_closure((void*)(l_Matrix_vecCons___rarg___boxed), 4, 3);
lean_closure_set(x_19, 0, x_3);
lean_closure_set(x_19, 1, x_10);
lean_closure_set(x_19, 2, x_18);
x_20 = l_Fin_cases(x_5, lean_box(0), x_7, x_19, x_1);
lean_dec(x_7);
return x_20;
}
}
LEAN_EXPORT lean_object* l___private_MOC_ContactRectangle_0__MOC_positiveMixedPerm___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_MOC_ContactRectangle_0__MOC_positiveMixedPerm(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_MOC_Obstruction(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Tactic_LinearCombination(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_MOC_ContactRectangle(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_MOC_Obstruction(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Tactic_LinearCombination(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Equiv_swap___at___private_MOC_ContactRectangle_0__MOC_positiveMixedPerm___spec__1___closed__1 = _init_l_Equiv_swap___at___private_MOC_ContactRectangle_0__MOC_positiveMixedPerm___spec__1___closed__1();
lean_mark_persistent(l_Equiv_swap___at___private_MOC_ContactRectangle_0__MOC_positiveMixedPerm___spec__1___closed__1);
l___private_MOC_ContactRectangle_0__MOC_positiveMixedPerm___closed__1 = _init_l___private_MOC_ContactRectangle_0__MOC_positiveMixedPerm___closed__1();
lean_mark_persistent(l___private_MOC_ContactRectangle_0__MOC_positiveMixedPerm___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
