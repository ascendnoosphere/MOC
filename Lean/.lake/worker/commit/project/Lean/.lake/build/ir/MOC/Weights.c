// Lean compiler output
// Module: MOC.Weights
// Imports: Init MOC.Core Mathlib.Algebra.BigOperators.Field Mathlib.Data.Complex.BigOperators
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
lean_object* l_Multiset_sum___at_MOC_determinantValue___spec__5(lean_object*);
LEAN_EXPORT lean_object* l_Finset_prod___at_MOC_leibnizTerm___spec__2(lean_object*);
LEAN_EXPORT lean_object* l_MOC_marginal___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_cast___at_MOC_leibnizTerm___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Finset_prod___at_MOC_leibnizTerm___spec__2___rarg(lean_object*, lean_object*);
lean_object* l_Int_cast___at_Real_instIntCast___spec__2(lean_object*);
lean_object* l_Equiv_instFintype___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Finset_prod___at_MOC_exceptProduct___spec__1___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Finset_prod___at_MOC_exceptProduct___spec__1(lean_object*);
lean_object* l_Multiset_map___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MOC_leibnizTerm___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_MOC_exceptProduct___rarg___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_MOC_exceptProduct(lean_object*);
extern lean_object* l___private_Mathlib_Data_Real_Basic_0__Real_one;
LEAN_EXPORT lean_object* l_MOC_exceptProduct___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_579_(lean_object*);
lean_object* l_Multiset_prod___at_MOC_matchingProduct___spec__2(lean_object*);
static lean_object* l_MOC_marginal___rarg___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_MOC_leibnizTerm(lean_object*);
LEAN_EXPORT lean_object* l_MOC_exceptProduct___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_664_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Finset_sum___at_MOC_marginal___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_MOC_marginal___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Equiv_Perm_sign___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Finset_sum___at_MOC_marginal___spec__1___rarg(lean_object*, lean_object*);
lean_object* l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_471_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MOC_marginal(lean_object*);
LEAN_EXPORT lean_object* l_MOC_leibnizTerm___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_cast___at_MOC_leibnizTerm___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Int_cast___at_Real_instIntCast___spec__2(x_1);
x_3 = l___private_Mathlib_Data_Real_Basic_0__Real_zero;
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Finset_prod___at_MOC_leibnizTerm___spec__2___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Multiset_map___rarg(x_2, x_1);
x_4 = l_Multiset_prod___at_MOC_matchingProduct___spec__2(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Finset_prod___at_MOC_leibnizTerm___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Finset_prod___at_MOC_leibnizTerm___spec__2___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_MOC_leibnizTerm___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
lean_inc(x_3);
x_5 = lean_apply_1(x_4, x_3);
x_6 = lean_apply_2(x_2, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_MOC_leibnizTerm___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_inc(x_1);
x_5 = l_Equiv_Perm_sign___rarg(x_2, x_1);
lean_inc(x_4);
x_6 = lean_apply_1(x_5, x_4);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
x_8 = l_Int_cast___at_MOC_leibnizTerm___spec__1(x_7);
x_9 = lean_alloc_closure((void*)(l_MOC_leibnizTerm___rarg___lambda__1), 3, 2);
lean_closure_set(x_9, 0, x_4);
lean_closure_set(x_9, 1, x_3);
x_10 = l_Finset_prod___at_MOC_leibnizTerm___spec__2___rarg(x_1, x_9);
x_11 = lean_ctor_get(x_8, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_inc(x_12);
lean_inc(x_11);
x_13 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_664_(x_11, x_12);
x_14 = lean_ctor_get(x_8, 1);
lean_inc(x_14);
lean_dec(x_8);
x_15 = lean_ctor_get(x_10, 1);
lean_inc(x_15);
lean_dec(x_10);
lean_inc(x_15);
lean_inc(x_14);
x_16 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_664_(x_14, x_15);
x_17 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_579_(x_16);
x_18 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_471_(x_13, x_17);
x_19 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_664_(x_11, x_15);
x_20 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_664_(x_14, x_12);
x_21 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_471_(x_19, x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_18);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
LEAN_EXPORT lean_object* l_MOC_leibnizTerm(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_MOC_leibnizTerm___rarg), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Finset_sum___at_MOC_marginal___spec__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Multiset_map___rarg(x_2, x_1);
x_4 = l_Multiset_sum___at_MOC_determinantValue___spec__5(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Finset_sum___at_MOC_marginal___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Finset_sum___at_MOC_marginal___spec__1___rarg), 2, 0);
return x_2;
}
}
static lean_object* _init_l_MOC_marginal___rarg___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Mathlib_Data_Real_Basic_0__Real_zero;
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_MOC_marginal___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_apply_1(x_6, x_1);
x_8 = lean_apply_2(x_2, x_7, x_3);
x_9 = lean_unbox(x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_5);
lean_dec(x_4);
x_10 = l_MOC_marginal___rarg___lambda__1___closed__1;
return x_10;
}
else
{
lean_object* x_11; 
x_11 = lean_apply_1(x_4, x_5);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_MOC_marginal___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_inc(x_1);
lean_inc_n(x_2, 2);
x_6 = l_Equiv_instFintype___rarg(x_2, x_2, x_1, x_1);
x_7 = lean_alloc_closure((void*)(l_MOC_marginal___rarg___lambda__1), 5, 4);
lean_closure_set(x_7, 0, x_5);
lean_closure_set(x_7, 1, x_2);
lean_closure_set(x_7, 2, x_4);
lean_closure_set(x_7, 3, x_3);
x_8 = l_Finset_sum___at_MOC_marginal___spec__1___rarg(x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_MOC_marginal(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_MOC_marginal___rarg), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Finset_prod___at_MOC_exceptProduct___spec__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Multiset_map___rarg(x_2, x_1);
x_4 = l_Multiset_prod___at_MOC_matchingProduct___spec__2(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Finset_prod___at_MOC_exceptProduct___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Finset_prod___at_MOC_exceptProduct___spec__1___rarg), 2, 0);
return x_2;
}
}
static lean_object* _init_l_MOC_exceptProduct___rarg___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Mathlib_Data_Real_Basic_0__Real_one;
x_2 = l___private_Mathlib_Data_Real_Basic_0__Real_zero;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_MOC_exceptProduct___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
lean_inc(x_4);
x_5 = lean_apply_2(x_1, x_4, x_2);
x_6 = lean_unbox(x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = lean_apply_1(x_3, x_4);
return x_7;
}
else
{
lean_object* x_8; 
lean_dec(x_4);
lean_dec(x_3);
x_8 = l_MOC_exceptProduct___rarg___lambda__1___closed__1;
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_MOC_exceptProduct___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_closure((void*)(l_MOC_exceptProduct___rarg___lambda__1), 4, 3);
lean_closure_set(x_5, 0, x_2);
lean_closure_set(x_5, 1, x_4);
lean_closure_set(x_5, 2, x_3);
x_6 = l_Finset_prod___at_MOC_exceptProduct___spec__1___rarg(x_1, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_MOC_exceptProduct(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_MOC_exceptProduct___rarg), 4, 0);
return x_2;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_MOC_Core(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Algebra_BigOperators_Field(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Data_Complex_BigOperators(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_MOC_Weights(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_MOC_Core(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Algebra_BigOperators_Field(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Data_Complex_BigOperators(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_MOC_marginal___rarg___lambda__1___closed__1 = _init_l_MOC_marginal___rarg___lambda__1___closed__1();
lean_mark_persistent(l_MOC_marginal___rarg___lambda__1___closed__1);
l_MOC_exceptProduct___rarg___lambda__1___closed__1 = _init_l_MOC_exceptProduct___rarg___lambda__1___closed__1();
lean_mark_persistent(l_MOC_exceptProduct___rarg___lambda__1___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
