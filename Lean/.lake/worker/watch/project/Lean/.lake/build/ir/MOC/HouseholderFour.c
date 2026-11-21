// Lean compiler output
// Module: MOC.HouseholderFour
// Imports: Init MOC.Householder MOC.HouseholderPacking MOC.Small Mathlib.Tactic.FinCases
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
LEAN_EXPORT lean_object* l___private_MOC_HouseholderFour_0__MOC_fourTriangleEdges(lean_object*, lean_object*);
static lean_object* l___private_MOC_HouseholderFour_0__MOC_fourPair___closed__12;
static lean_object* l___private_MOC_HouseholderFour_0__MOC_fourTriangleEdges___closed__10;
static lean_object* l___private_MOC_HouseholderFour_0__MOC_fourPair___closed__5;
static lean_object* l___private_MOC_HouseholderFour_0__MOC_fourPair___closed__6;
lean_object* l_Equiv_swap___elambda__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_MOC_HouseholderFour_0__MOC_fourPair(lean_object*);
static lean_object* l___private_MOC_HouseholderFour_0__MOC_fourTriangleEdges___closed__2;
static lean_object* l___private_MOC_HouseholderFour_0__MOC_fourTriangleEdges___closed__14;
static lean_object* l___private_MOC_HouseholderFour_0__MOC_fourPair___closed__3;
static lean_object* l___private_MOC_HouseholderFour_0__MOC_fourTriangleEdges___closed__5;
static lean_object* l___private_MOC_HouseholderFour_0__MOC_fourEdgeMass___closed__1;
static lean_object* l___private_MOC_HouseholderFour_0__MOC_fourTriangleEdges___closed__1;
lean_object* l_Nat_cast___at_Real_instNatCast___spec__2(lean_object*);
static lean_object* l___private_MOC_HouseholderFour_0__MOC_fourPair___closed__2;
LEAN_EXPORT lean_object* l___private_MOC_HouseholderFour_0__MOC_fourEdgeMass(lean_object*, lean_object*);
static lean_object* l___private_MOC_HouseholderFour_0__MOC_fourTriangleEdges___closed__9;
static lean_object* l___private_MOC_HouseholderFour_0__MOC_fourTriangleEdges___closed__4;
lean_object* l_instDecidableEqFin___rarg___boxed(lean_object*, lean_object*);
static lean_object* l___private_MOC_HouseholderFour_0__MOC_fourPair___closed__10;
static lean_object* l___private_MOC_HouseholderFour_0__MOC_fourPair___closed__11;
static lean_object* l___private_MOC_HouseholderFour_0__MOC_fourPair___closed__7;
static lean_object* l___private_MOC_HouseholderFour_0__MOC_fourTriangleEdges___closed__8;
lean_object* l_Matrix_vecEmpty___boxed(lean_object*, lean_object*);
static lean_object* l___private_MOC_HouseholderFour_0__MOC_fourTriangleEdges___closed__7;
static lean_object* l___private_MOC_HouseholderFour_0__MOC_fourTriangleEdges___closed__12;
lean_object* l_Equiv_trans___rarg(lean_object*, lean_object*);
static lean_object* l___private_MOC_HouseholderFour_0__MOC_fourTriangleEdges___closed__11;
LEAN_EXPORT lean_object* l_Equiv_swap___at___private_MOC_HouseholderFour_0__MOC_fourSwap___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_MOC_HouseholderFour_0__MOC_fourTriangleEdges___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_MOC_HouseholderFour_0__MOC_fourSwap___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_MOC_HouseholderFour_0__MOC_fourEdgeMass___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_MOC_HouseholderFour_0__MOC_fourCycle___boxed(lean_object*, lean_object*);
lean_object* l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_664_(lean_object*, lean_object*);
static lean_object* l___private_MOC_HouseholderFour_0__MOC_fourTriangleEdges___closed__3;
lean_object* l_Fin_cases(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_MOC_HouseholderFour_0__MOC_fourPair___closed__9;
static lean_object* l___private_MOC_HouseholderFour_0__MOC_fourPair___closed__8;
static lean_object* l___private_MOC_HouseholderFour_0__MOC_fourPair___closed__1;
LEAN_EXPORT lean_object* l___private_MOC_HouseholderFour_0__MOC_fourSwap(lean_object*);
static lean_object* l___private_MOC_HouseholderFour_0__MOC_fourTriangleEdges___closed__13;
LEAN_EXPORT lean_object* l___private_MOC_HouseholderFour_0__MOC_fourPair___boxed(lean_object*);
static lean_object* l___private_MOC_HouseholderFour_0__MOC_fourPair___closed__4;
static lean_object* l___private_MOC_HouseholderFour_0__MOC_fourTriangleEdges___closed__6;
lean_object* l_Matrix_vecCons___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_MOC_HouseholderFour_0__MOC_fourCycle(lean_object*, uint8_t);
static lean_object* l_Equiv_swap___at___private_MOC_HouseholderFour_0__MOC_fourSwap___spec__1___closed__1;
static lean_object* _init_l___private_MOC_HouseholderFour_0__MOC_fourPair___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_MOC_HouseholderFour_0__MOC_fourPair___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_unsigned_to_nat(2u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_MOC_HouseholderFour_0__MOC_fourPair___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_unsigned_to_nat(3u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_MOC_HouseholderFour_0__MOC_fourPair___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_unsigned_to_nat(2u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_MOC_HouseholderFour_0__MOC_fourPair___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_unsigned_to_nat(3u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_MOC_HouseholderFour_0__MOC_fourPair___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_unsigned_to_nat(3u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_MOC_HouseholderFour_0__MOC_fourPair___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Matrix_vecEmpty___boxed), 2, 1);
lean_closure_set(x_1, 0, lean_box(0));
return x_1;
}
}
static lean_object* _init_l___private_MOC_HouseholderFour_0__MOC_fourPair___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l___private_MOC_HouseholderFour_0__MOC_fourPair___closed__6;
x_3 = l___private_MOC_HouseholderFour_0__MOC_fourPair___closed__7;
x_4 = lean_alloc_closure((void*)(l_Matrix_vecCons___rarg___boxed), 4, 3);
lean_closure_set(x_4, 0, x_1);
lean_closure_set(x_4, 1, x_2);
lean_closure_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l___private_MOC_HouseholderFour_0__MOC_fourPair___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = l___private_MOC_HouseholderFour_0__MOC_fourPair___closed__5;
x_3 = l___private_MOC_HouseholderFour_0__MOC_fourPair___closed__8;
x_4 = lean_alloc_closure((void*)(l_Matrix_vecCons___rarg___boxed), 4, 3);
lean_closure_set(x_4, 0, x_1);
lean_closure_set(x_4, 1, x_2);
lean_closure_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l___private_MOC_HouseholderFour_0__MOC_fourPair___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = l___private_MOC_HouseholderFour_0__MOC_fourPair___closed__4;
x_3 = l___private_MOC_HouseholderFour_0__MOC_fourPair___closed__9;
x_4 = lean_alloc_closure((void*)(l_Matrix_vecCons___rarg___boxed), 4, 3);
lean_closure_set(x_4, 0, x_1);
lean_closure_set(x_4, 1, x_2);
lean_closure_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l___private_MOC_HouseholderFour_0__MOC_fourPair___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_unsigned_to_nat(3u);
x_2 = l___private_MOC_HouseholderFour_0__MOC_fourPair___closed__3;
x_3 = l___private_MOC_HouseholderFour_0__MOC_fourPair___closed__10;
x_4 = lean_alloc_closure((void*)(l_Matrix_vecCons___rarg___boxed), 4, 3);
lean_closure_set(x_4, 0, x_1);
lean_closure_set(x_4, 1, x_2);
lean_closure_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l___private_MOC_HouseholderFour_0__MOC_fourPair___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = l___private_MOC_HouseholderFour_0__MOC_fourPair___closed__2;
x_3 = l___private_MOC_HouseholderFour_0__MOC_fourPair___closed__11;
x_4 = lean_alloc_closure((void*)(l_Matrix_vecCons___rarg___boxed), 4, 3);
lean_closure_set(x_4, 0, x_1);
lean_closure_set(x_4, 1, x_2);
lean_closure_set(x_4, 2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_MOC_HouseholderFour_0__MOC_fourPair(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_unsigned_to_nat(5u);
x_3 = l___private_MOC_HouseholderFour_0__MOC_fourPair___closed__1;
x_4 = l___private_MOC_HouseholderFour_0__MOC_fourPair___closed__12;
x_5 = l_Fin_cases(x_2, lean_box(0), x_3, x_4, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_MOC_HouseholderFour_0__MOC_fourPair___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_MOC_HouseholderFour_0__MOC_fourPair(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Equiv_swap___at___private_MOC_HouseholderFour_0__MOC_fourSwap___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_instDecidableEqFin___rarg___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Equiv_swap___at___private_MOC_HouseholderFour_0__MOC_fourSwap___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_Equiv_swap___at___private_MOC_HouseholderFour_0__MOC_fourSwap___spec__1___closed__1;
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
LEAN_EXPORT lean_object* l___private_MOC_HouseholderFour_0__MOC_fourSwap(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l___private_MOC_HouseholderFour_0__MOC_fourPair(x_1);
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec(x_2);
x_5 = l_Equiv_swap___at___private_MOC_HouseholderFour_0__MOC_fourSwap___spec__1(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_MOC_HouseholderFour_0__MOC_fourSwap___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_MOC_HouseholderFour_0__MOC_fourSwap(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l___private_MOC_HouseholderFour_0__MOC_fourEdgeMass___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = l_Nat_cast___at_Real_instNatCast___spec__2(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_MOC_HouseholderFour_0__MOC_fourEdgeMass(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_3 = l___private_MOC_HouseholderFour_0__MOC_fourPair(x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_inc(x_1);
x_5 = lean_apply_1(x_1, x_4);
x_6 = l___private_MOC_HouseholderFour_0__MOC_fourEdgeMass___closed__1;
x_7 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_664_(x_6, x_5);
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
lean_dec(x_3);
x_9 = lean_apply_1(x_1, x_8);
x_10 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_664_(x_7, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_MOC_HouseholderFour_0__MOC_fourEdgeMass___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_MOC_HouseholderFour_0__MOC_fourEdgeMass(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l___private_MOC_HouseholderFour_0__MOC_fourTriangleEdges___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_unsigned_to_nat(5u);
x_3 = l___private_MOC_HouseholderFour_0__MOC_fourPair___closed__7;
x_4 = lean_alloc_closure((void*)(l_Matrix_vecCons___rarg___boxed), 4, 3);
lean_closure_set(x_4, 0, x_1);
lean_closure_set(x_4, 1, x_2);
lean_closure_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l___private_MOC_HouseholderFour_0__MOC_fourTriangleEdges___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_unsigned_to_nat(4u);
x_3 = l___private_MOC_HouseholderFour_0__MOC_fourTriangleEdges___closed__1;
x_4 = lean_alloc_closure((void*)(l_Matrix_vecCons___rarg___boxed), 4, 3);
lean_closure_set(x_4, 0, x_1);
lean_closure_set(x_4, 1, x_2);
lean_closure_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l___private_MOC_HouseholderFour_0__MOC_fourTriangleEdges___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_unsigned_to_nat(3u);
x_3 = l___private_MOC_HouseholderFour_0__MOC_fourTriangleEdges___closed__2;
x_4 = lean_alloc_closure((void*)(l_Matrix_vecCons___rarg___boxed), 4, 3);
lean_closure_set(x_4, 0, x_1);
lean_closure_set(x_4, 1, x_2);
lean_closure_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l___private_MOC_HouseholderFour_0__MOC_fourTriangleEdges___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_unsigned_to_nat(2u);
x_3 = l___private_MOC_HouseholderFour_0__MOC_fourTriangleEdges___closed__1;
x_4 = lean_alloc_closure((void*)(l_Matrix_vecCons___rarg___boxed), 4, 3);
lean_closure_set(x_4, 0, x_1);
lean_closure_set(x_4, 1, x_2);
lean_closure_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l___private_MOC_HouseholderFour_0__MOC_fourTriangleEdges___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_unsigned_to_nat(1u);
x_3 = l___private_MOC_HouseholderFour_0__MOC_fourTriangleEdges___closed__4;
x_4 = lean_alloc_closure((void*)(l_Matrix_vecCons___rarg___boxed), 4, 3);
lean_closure_set(x_4, 0, x_1);
lean_closure_set(x_4, 1, x_2);
lean_closure_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l___private_MOC_HouseholderFour_0__MOC_fourTriangleEdges___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_unsigned_to_nat(4u);
x_3 = l___private_MOC_HouseholderFour_0__MOC_fourPair___closed__7;
x_4 = lean_alloc_closure((void*)(l_Matrix_vecCons___rarg___boxed), 4, 3);
lean_closure_set(x_4, 0, x_1);
lean_closure_set(x_4, 1, x_2);
lean_closure_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l___private_MOC_HouseholderFour_0__MOC_fourTriangleEdges___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_unsigned_to_nat(2u);
x_3 = l___private_MOC_HouseholderFour_0__MOC_fourTriangleEdges___closed__6;
x_4 = lean_alloc_closure((void*)(l_Matrix_vecCons___rarg___boxed), 4, 3);
lean_closure_set(x_4, 0, x_1);
lean_closure_set(x_4, 1, x_2);
lean_closure_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l___private_MOC_HouseholderFour_0__MOC_fourTriangleEdges___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___private_MOC_HouseholderFour_0__MOC_fourTriangleEdges___closed__7;
x_4 = lean_alloc_closure((void*)(l_Matrix_vecCons___rarg___boxed), 4, 3);
lean_closure_set(x_4, 0, x_1);
lean_closure_set(x_4, 1, x_2);
lean_closure_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l___private_MOC_HouseholderFour_0__MOC_fourTriangleEdges___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_unsigned_to_nat(3u);
x_3 = l___private_MOC_HouseholderFour_0__MOC_fourPair___closed__7;
x_4 = lean_alloc_closure((void*)(l_Matrix_vecCons___rarg___boxed), 4, 3);
lean_closure_set(x_4, 0, x_1);
lean_closure_set(x_4, 1, x_2);
lean_closure_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l___private_MOC_HouseholderFour_0__MOC_fourTriangleEdges___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = l___private_MOC_HouseholderFour_0__MOC_fourTriangleEdges___closed__9;
x_3 = lean_alloc_closure((void*)(l_Matrix_vecCons___rarg___boxed), 4, 3);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_1);
lean_closure_set(x_3, 2, x_2);
return x_3;
}
}
static lean_object* _init_l___private_MOC_HouseholderFour_0__MOC_fourTriangleEdges___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___private_MOC_HouseholderFour_0__MOC_fourTriangleEdges___closed__10;
x_4 = lean_alloc_closure((void*)(l_Matrix_vecCons___rarg___boxed), 4, 3);
lean_closure_set(x_4, 0, x_1);
lean_closure_set(x_4, 1, x_2);
lean_closure_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l___private_MOC_HouseholderFour_0__MOC_fourTriangleEdges___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l___private_MOC_HouseholderFour_0__MOC_fourTriangleEdges___closed__11;
x_3 = l___private_MOC_HouseholderFour_0__MOC_fourPair___closed__7;
x_4 = lean_alloc_closure((void*)(l_Matrix_vecCons___rarg___boxed), 4, 3);
lean_closure_set(x_4, 0, x_1);
lean_closure_set(x_4, 1, x_2);
lean_closure_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l___private_MOC_HouseholderFour_0__MOC_fourTriangleEdges___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = l___private_MOC_HouseholderFour_0__MOC_fourTriangleEdges___closed__8;
x_3 = l___private_MOC_HouseholderFour_0__MOC_fourTriangleEdges___closed__12;
x_4 = lean_alloc_closure((void*)(l_Matrix_vecCons___rarg___boxed), 4, 3);
lean_closure_set(x_4, 0, x_1);
lean_closure_set(x_4, 1, x_2);
lean_closure_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l___private_MOC_HouseholderFour_0__MOC_fourTriangleEdges___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = l___private_MOC_HouseholderFour_0__MOC_fourTriangleEdges___closed__5;
x_3 = l___private_MOC_HouseholderFour_0__MOC_fourTriangleEdges___closed__13;
x_4 = lean_alloc_closure((void*)(l_Matrix_vecCons___rarg___boxed), 4, 3);
lean_closure_set(x_4, 0, x_1);
lean_closure_set(x_4, 1, x_2);
lean_closure_set(x_4, 2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_MOC_HouseholderFour_0__MOC_fourTriangleEdges(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_unsigned_to_nat(3u);
x_4 = l___private_MOC_HouseholderFour_0__MOC_fourTriangleEdges___closed__3;
x_5 = l___private_MOC_HouseholderFour_0__MOC_fourTriangleEdges___closed__14;
x_6 = l_Fin_cases(x_3, lean_box(0), x_4, x_5, x_1);
x_7 = lean_apply_1(x_6, x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_MOC_HouseholderFour_0__MOC_fourTriangleEdges___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_MOC_HouseholderFour_0__MOC_fourTriangleEdges(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_MOC_HouseholderFour_0__MOC_fourCycle(lean_object* x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = l___private_MOC_HouseholderFour_0__MOC_fourTriangleEdges(x_1, x_3);
x_5 = l___private_MOC_HouseholderFour_0__MOC_fourSwap(x_4);
lean_dec(x_4);
x_6 = lean_unsigned_to_nat(2u);
x_7 = l___private_MOC_HouseholderFour_0__MOC_fourTriangleEdges(x_1, x_6);
x_8 = l___private_MOC_HouseholderFour_0__MOC_fourSwap(x_7);
lean_dec(x_7);
if (x_2 == 0)
{
lean_object* x_9; 
x_9 = l_Equiv_trans___rarg(x_8, x_5);
return x_9;
}
else
{
lean_object* x_10; 
x_10 = l_Equiv_trans___rarg(x_5, x_8);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l___private_MOC_HouseholderFour_0__MOC_fourCycle___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_2);
lean_dec(x_2);
x_4 = l___private_MOC_HouseholderFour_0__MOC_fourCycle(x_1, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_MOC_Householder(uint8_t builtin, lean_object*);
lean_object* initialize_MOC_HouseholderPacking(uint8_t builtin, lean_object*);
lean_object* initialize_MOC_Small(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Tactic_FinCases(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_MOC_HouseholderFour(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_MOC_Householder(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_MOC_HouseholderPacking(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_MOC_Small(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Tactic_FinCases(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_MOC_HouseholderFour_0__MOC_fourPair___closed__1 = _init_l___private_MOC_HouseholderFour_0__MOC_fourPair___closed__1();
lean_mark_persistent(l___private_MOC_HouseholderFour_0__MOC_fourPair___closed__1);
l___private_MOC_HouseholderFour_0__MOC_fourPair___closed__2 = _init_l___private_MOC_HouseholderFour_0__MOC_fourPair___closed__2();
lean_mark_persistent(l___private_MOC_HouseholderFour_0__MOC_fourPair___closed__2);
l___private_MOC_HouseholderFour_0__MOC_fourPair___closed__3 = _init_l___private_MOC_HouseholderFour_0__MOC_fourPair___closed__3();
lean_mark_persistent(l___private_MOC_HouseholderFour_0__MOC_fourPair___closed__3);
l___private_MOC_HouseholderFour_0__MOC_fourPair___closed__4 = _init_l___private_MOC_HouseholderFour_0__MOC_fourPair___closed__4();
lean_mark_persistent(l___private_MOC_HouseholderFour_0__MOC_fourPair___closed__4);
l___private_MOC_HouseholderFour_0__MOC_fourPair___closed__5 = _init_l___private_MOC_HouseholderFour_0__MOC_fourPair___closed__5();
lean_mark_persistent(l___private_MOC_HouseholderFour_0__MOC_fourPair___closed__5);
l___private_MOC_HouseholderFour_0__MOC_fourPair___closed__6 = _init_l___private_MOC_HouseholderFour_0__MOC_fourPair___closed__6();
lean_mark_persistent(l___private_MOC_HouseholderFour_0__MOC_fourPair___closed__6);
l___private_MOC_HouseholderFour_0__MOC_fourPair___closed__7 = _init_l___private_MOC_HouseholderFour_0__MOC_fourPair___closed__7();
lean_mark_persistent(l___private_MOC_HouseholderFour_0__MOC_fourPair___closed__7);
l___private_MOC_HouseholderFour_0__MOC_fourPair___closed__8 = _init_l___private_MOC_HouseholderFour_0__MOC_fourPair___closed__8();
lean_mark_persistent(l___private_MOC_HouseholderFour_0__MOC_fourPair___closed__8);
l___private_MOC_HouseholderFour_0__MOC_fourPair___closed__9 = _init_l___private_MOC_HouseholderFour_0__MOC_fourPair___closed__9();
lean_mark_persistent(l___private_MOC_HouseholderFour_0__MOC_fourPair___closed__9);
l___private_MOC_HouseholderFour_0__MOC_fourPair___closed__10 = _init_l___private_MOC_HouseholderFour_0__MOC_fourPair___closed__10();
lean_mark_persistent(l___private_MOC_HouseholderFour_0__MOC_fourPair___closed__10);
l___private_MOC_HouseholderFour_0__MOC_fourPair___closed__11 = _init_l___private_MOC_HouseholderFour_0__MOC_fourPair___closed__11();
lean_mark_persistent(l___private_MOC_HouseholderFour_0__MOC_fourPair___closed__11);
l___private_MOC_HouseholderFour_0__MOC_fourPair___closed__12 = _init_l___private_MOC_HouseholderFour_0__MOC_fourPair___closed__12();
lean_mark_persistent(l___private_MOC_HouseholderFour_0__MOC_fourPair___closed__12);
l_Equiv_swap___at___private_MOC_HouseholderFour_0__MOC_fourSwap___spec__1___closed__1 = _init_l_Equiv_swap___at___private_MOC_HouseholderFour_0__MOC_fourSwap___spec__1___closed__1();
lean_mark_persistent(l_Equiv_swap___at___private_MOC_HouseholderFour_0__MOC_fourSwap___spec__1___closed__1);
l___private_MOC_HouseholderFour_0__MOC_fourEdgeMass___closed__1 = _init_l___private_MOC_HouseholderFour_0__MOC_fourEdgeMass___closed__1();
lean_mark_persistent(l___private_MOC_HouseholderFour_0__MOC_fourEdgeMass___closed__1);
l___private_MOC_HouseholderFour_0__MOC_fourTriangleEdges___closed__1 = _init_l___private_MOC_HouseholderFour_0__MOC_fourTriangleEdges___closed__1();
lean_mark_persistent(l___private_MOC_HouseholderFour_0__MOC_fourTriangleEdges___closed__1);
l___private_MOC_HouseholderFour_0__MOC_fourTriangleEdges___closed__2 = _init_l___private_MOC_HouseholderFour_0__MOC_fourTriangleEdges___closed__2();
lean_mark_persistent(l___private_MOC_HouseholderFour_0__MOC_fourTriangleEdges___closed__2);
l___private_MOC_HouseholderFour_0__MOC_fourTriangleEdges___closed__3 = _init_l___private_MOC_HouseholderFour_0__MOC_fourTriangleEdges___closed__3();
lean_mark_persistent(l___private_MOC_HouseholderFour_0__MOC_fourTriangleEdges___closed__3);
l___private_MOC_HouseholderFour_0__MOC_fourTriangleEdges___closed__4 = _init_l___private_MOC_HouseholderFour_0__MOC_fourTriangleEdges___closed__4();
lean_mark_persistent(l___private_MOC_HouseholderFour_0__MOC_fourTriangleEdges___closed__4);
l___private_MOC_HouseholderFour_0__MOC_fourTriangleEdges___closed__5 = _init_l___private_MOC_HouseholderFour_0__MOC_fourTriangleEdges___closed__5();
lean_mark_persistent(l___private_MOC_HouseholderFour_0__MOC_fourTriangleEdges___closed__5);
l___private_MOC_HouseholderFour_0__MOC_fourTriangleEdges___closed__6 = _init_l___private_MOC_HouseholderFour_0__MOC_fourTriangleEdges___closed__6();
lean_mark_persistent(l___private_MOC_HouseholderFour_0__MOC_fourTriangleEdges___closed__6);
l___private_MOC_HouseholderFour_0__MOC_fourTriangleEdges___closed__7 = _init_l___private_MOC_HouseholderFour_0__MOC_fourTriangleEdges___closed__7();
lean_mark_persistent(l___private_MOC_HouseholderFour_0__MOC_fourTriangleEdges___closed__7);
l___private_MOC_HouseholderFour_0__MOC_fourTriangleEdges___closed__8 = _init_l___private_MOC_HouseholderFour_0__MOC_fourTriangleEdges___closed__8();
lean_mark_persistent(l___private_MOC_HouseholderFour_0__MOC_fourTriangleEdges___closed__8);
l___private_MOC_HouseholderFour_0__MOC_fourTriangleEdges___closed__9 = _init_l___private_MOC_HouseholderFour_0__MOC_fourTriangleEdges___closed__9();
lean_mark_persistent(l___private_MOC_HouseholderFour_0__MOC_fourTriangleEdges___closed__9);
l___private_MOC_HouseholderFour_0__MOC_fourTriangleEdges___closed__10 = _init_l___private_MOC_HouseholderFour_0__MOC_fourTriangleEdges___closed__10();
lean_mark_persistent(l___private_MOC_HouseholderFour_0__MOC_fourTriangleEdges___closed__10);
l___private_MOC_HouseholderFour_0__MOC_fourTriangleEdges___closed__11 = _init_l___private_MOC_HouseholderFour_0__MOC_fourTriangleEdges___closed__11();
lean_mark_persistent(l___private_MOC_HouseholderFour_0__MOC_fourTriangleEdges___closed__11);
l___private_MOC_HouseholderFour_0__MOC_fourTriangleEdges___closed__12 = _init_l___private_MOC_HouseholderFour_0__MOC_fourTriangleEdges___closed__12();
lean_mark_persistent(l___private_MOC_HouseholderFour_0__MOC_fourTriangleEdges___closed__12);
l___private_MOC_HouseholderFour_0__MOC_fourTriangleEdges___closed__13 = _init_l___private_MOC_HouseholderFour_0__MOC_fourTriangleEdges___closed__13();
lean_mark_persistent(l___private_MOC_HouseholderFour_0__MOC_fourTriangleEdges___closed__13);
l___private_MOC_HouseholderFour_0__MOC_fourTriangleEdges___closed__14 = _init_l___private_MOC_HouseholderFour_0__MOC_fourTriangleEdges___closed__14();
lean_mark_persistent(l___private_MOC_HouseholderFour_0__MOC_fourTriangleEdges___closed__14);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
