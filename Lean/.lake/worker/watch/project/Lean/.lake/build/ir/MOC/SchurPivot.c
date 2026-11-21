// Lean compiler output
// Module: MOC.SchurPivot
// Imports: Init MOC.PhaseMove MOC.SchurPhase Mathlib.LinearAlgebra.Matrix.SchurComplement
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
LEAN_EXPORT lean_object* l_MOC_schurPhaseSum___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_MOC_schurPhaseSum___rarg___closed__1;
static lean_object* l_MOC_schurPhaseSum___rarg___lambda__4___closed__2;
LEAN_EXPORT lean_object* l___private_Init_Data_Sum_Basic_0__Sum_decEqSum____x40_Init_Data_Sum_Basic___hyg_5____at_MOC_schurPivotPhase___spec__2___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Matrix_diagonal___at_MOC_schurPivotPhase___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MOC_schurPhaseSum(lean_object*);
LEAN_EXPORT lean_object* l_MOC_schurPhaseSum___rarg___lambda__3(lean_object*);
LEAN_EXPORT lean_object* l_MOC_schurPhaseSum___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_MOC_schurPhaseSum___rarg___closed__2;
static lean_object* l_MOC_schurPivotPhase___rarg___closed__1;
static lean_object* l_Matrix_diagonal___at_MOC_schurPivotPhase___spec__1___rarg___closed__1;
lean_object* l_Pi_instAdd___elambda__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MOC_schurPhaseSum___rarg___lambda__4___boxed(lean_object*);
LEAN_EXPORT lean_object* l_MOC_schurPhaseSum___rarg___lambda__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l_MOC_schurPivotPhase___rarg___lambda__2(lean_object*);
LEAN_EXPORT lean_object* l_MOC_schurPivotPhase(lean_object*);
extern lean_object* l___private_Mathlib_Data_Real_Basic_0__Real_one;
static lean_object* l_MOC_schurPhaseSum___rarg___closed__3;
lean_object* l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_579_(lean_object*);
LEAN_EXPORT lean_object* l_MOC_schurPhaseSum___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Sum_elim___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_MOC_schurPhaseSum___rarg___lambda__3___closed__1;
lean_object* l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_664_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MOC_schurPhaseSum___rarg___lambda__4(lean_object*);
lean_object* l_Matrix_fromBlocks___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Matrix_diagonal___at_MOC_schurPivotPhase___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_MOC_schurPivotPhase___rarg___lambda__2___boxed(lean_object*);
lean_object* l_Complex_instAdd(lean_object*, lean_object*);
static lean_object* l_MOC_schurPivotPhase___rarg___lambda__2___closed__1;
lean_object* l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_471_(lean_object*, lean_object*);
static lean_object* l_MOC_schurPhaseSum___rarg___lambda__4___closed__1;
LEAN_EXPORT lean_object* l_MOC_schurPivotPhase___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MOC_schurPivotPhase___rarg___lambda__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Sum_Basic_0__Sum_decEqSum____x40_Init_Data_Sum_Basic___hyg_5____at_MOC_schurPivotPhase___spec__2(lean_object*);
LEAN_EXPORT lean_object* l_MOC_schurPivotPhase___rarg___lambda__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MOC_schurPhaseSum___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Sum_Basic_0__Sum_decEqSum____x40_Init_Data_Sum_Basic___hyg_5____at_MOC_schurPivotPhase___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_dec(x_2);
lean_dec(x_1);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = 1;
x_5 = lean_box(x_4);
return x_5;
}
else
{
uint8_t x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = 0;
x_7 = lean_box(x_6);
return x_7;
}
}
else
{
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_8; lean_object* x_9; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_8 = 0;
x_9 = lean_box(x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
lean_dec(x_2);
x_11 = lean_ctor_get(x_3, 0);
lean_inc(x_11);
lean_dec(x_3);
x_12 = lean_apply_2(x_1, x_10, x_11);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Sum_Basic_0__Sum_decEqSum____x40_Init_Data_Sum_Basic___hyg_5____at_MOC_schurPivotPhase___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Init_Data_Sum_Basic_0__Sum_decEqSum____x40_Init_Data_Sum_Basic___hyg_5____at_MOC_schurPivotPhase___spec__2___rarg), 3, 0);
return x_2;
}
}
static lean_object* _init_l_Matrix_diagonal___at_MOC_schurPivotPhase___spec__1___rarg___closed__1() {
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
LEAN_EXPORT lean_object* l_Matrix_diagonal___at_MOC_schurPivotPhase___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
lean_inc(x_3);
x_5 = l___private_Init_Data_Sum_Basic_0__Sum_decEqSum____x40_Init_Data_Sum_Basic___hyg_5____at_MOC_schurPivotPhase___spec__2___rarg(x_1, x_3, x_4);
x_6 = lean_unbox(x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_3);
lean_dec(x_2);
x_7 = l_Matrix_diagonal___at_MOC_schurPivotPhase___spec__1___rarg___closed__1;
return x_7;
}
else
{
lean_object* x_8; 
x_8 = lean_apply_1(x_2, x_3);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Matrix_diagonal___at_MOC_schurPivotPhase___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Matrix_diagonal___at_MOC_schurPivotPhase___spec__1___rarg), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_MOC_schurPivotPhase___rarg___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
static lean_object* _init_l_MOC_schurPivotPhase___rarg___lambda__2___closed__1() {
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
LEAN_EXPORT lean_object* l_MOC_schurPivotPhase___rarg___lambda__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_MOC_schurPivotPhase___rarg___lambda__2___closed__1;
return x_2;
}
}
static lean_object* _init_l_MOC_schurPivotPhase___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_MOC_schurPivotPhase___rarg___lambda__2___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_MOC_schurPivotPhase___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_alloc_closure((void*)(l_MOC_schurPivotPhase___rarg___lambda__1___boxed), 2, 1);
lean_closure_set(x_5, 0, x_2);
x_6 = l_MOC_schurPivotPhase___rarg___closed__1;
x_7 = lean_alloc_closure((void*)(l_Sum_elim___rarg), 3, 2);
lean_closure_set(x_7, 0, x_5);
lean_closure_set(x_7, 1, x_6);
x_8 = l_Matrix_diagonal___at_MOC_schurPivotPhase___spec__1___rarg(x_1, x_7, x_3, x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_MOC_schurPivotPhase(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_MOC_schurPivotPhase___rarg), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_MOC_schurPivotPhase___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_MOC_schurPivotPhase___rarg___lambda__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_MOC_schurPivotPhase___rarg___lambda__2___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_MOC_schurPivotPhase___rarg___lambda__2(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_MOC_schurPhaseSum___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_MOC_schurPhaseSum___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_6 = lean_apply_2(x_1, x_4, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_inc(x_7);
lean_inc(x_2);
x_8 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_664_(x_2, x_7);
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_9);
lean_dec(x_6);
lean_inc(x_9);
lean_inc(x_3);
x_10 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_664_(x_3, x_9);
x_11 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_579_(x_10);
x_12 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_471_(x_8, x_11);
x_13 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_664_(x_2, x_9);
x_14 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_664_(x_3, x_7);
x_15 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_471_(x_13, x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_12);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
static lean_object* _init_l_MOC_schurPhaseSum___rarg___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Complex_instAdd), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_MOC_schurPhaseSum___rarg___lambda__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_MOC_schurPhaseSum___rarg___lambda__3___closed__1;
return x_2;
}
}
static lean_object* _init_l_MOC_schurPhaseSum___rarg___lambda__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_MOC_schurPhaseSum___rarg___lambda__3___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_MOC_schurPhaseSum___rarg___lambda__4___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_MOC_schurPhaseSum___rarg___lambda__4___closed__1;
x_2 = lean_alloc_closure((void*)(l_Pi_instAdd___elambda__1___rarg), 4, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_MOC_schurPhaseSum___rarg___lambda__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_MOC_schurPhaseSum___rarg___lambda__4___closed__2;
return x_2;
}
}
static lean_object* _init_l_MOC_schurPhaseSum___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Mathlib_Data_Real_Basic_0__Real_one;
x_2 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_579_(x_1);
return x_2;
}
}
static lean_object* _init_l_MOC_schurPhaseSum___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Mathlib_Data_Real_Basic_0__Real_zero;
x_2 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_579_(x_1);
return x_2;
}
}
static lean_object* _init_l_MOC_schurPhaseSum___rarg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_MOC_schurPhaseSum___rarg___lambda__4___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_MOC_schurPhaseSum___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_9 = lean_alloc_closure((void*)(l_MOC_schurPhaseSum___rarg___lambda__1___boxed), 3, 1);
lean_closure_set(x_9, 0, x_1);
x_10 = lean_ctor_get(x_6, 0);
lean_inc(x_10);
x_11 = l_MOC_schurPhaseSum___rarg___closed__1;
x_12 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_471_(x_10, x_11);
x_13 = lean_ctor_get(x_6, 1);
lean_inc(x_13);
lean_dec(x_6);
x_14 = l_MOC_schurPhaseSum___rarg___closed__2;
lean_inc(x_13);
x_15 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_471_(x_13, x_14);
lean_inc(x_12);
x_16 = lean_alloc_closure((void*)(l_MOC_schurPhaseSum___rarg___lambda__2), 5, 3);
lean_closure_set(x_16, 0, x_3);
lean_closure_set(x_16, 1, x_12);
lean_closure_set(x_16, 2, x_15);
x_17 = l_MOC_schurPhaseSum___rarg___closed__3;
x_18 = lean_alloc_closure((void*)(l_Pi_instAdd___elambda__1___rarg), 4, 3);
lean_closure_set(x_18, 0, x_17);
lean_closure_set(x_18, 1, x_2);
lean_closure_set(x_18, 2, x_16);
x_19 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_579_(x_13);
x_20 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_471_(x_19, x_14);
x_21 = lean_alloc_closure((void*)(l_MOC_schurPhaseSum___rarg___lambda__2), 5, 3);
lean_closure_set(x_21, 0, x_4);
lean_closure_set(x_21, 1, x_12);
lean_closure_set(x_21, 2, x_20);
x_22 = l_Matrix_fromBlocks___rarg(x_9, x_18, x_21, x_5, x_7, x_8);
return x_22;
}
}
LEAN_EXPORT lean_object* l_MOC_schurPhaseSum(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_MOC_schurPhaseSum___rarg), 8, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_MOC_schurPhaseSum___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_MOC_schurPhaseSum___rarg___lambda__1(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_MOC_schurPhaseSum___rarg___lambda__3___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_MOC_schurPhaseSum___rarg___lambda__3(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_MOC_schurPhaseSum___rarg___lambda__4___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_MOC_schurPhaseSum___rarg___lambda__4(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_MOC_PhaseMove(uint8_t builtin, lean_object*);
lean_object* initialize_MOC_SchurPhase(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_LinearAlgebra_Matrix_SchurComplement(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_MOC_SchurPivot(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_MOC_PhaseMove(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_MOC_SchurPhase(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_LinearAlgebra_Matrix_SchurComplement(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Matrix_diagonal___at_MOC_schurPivotPhase___spec__1___rarg___closed__1 = _init_l_Matrix_diagonal___at_MOC_schurPivotPhase___spec__1___rarg___closed__1();
lean_mark_persistent(l_Matrix_diagonal___at_MOC_schurPivotPhase___spec__1___rarg___closed__1);
l_MOC_schurPivotPhase___rarg___lambda__2___closed__1 = _init_l_MOC_schurPivotPhase___rarg___lambda__2___closed__1();
lean_mark_persistent(l_MOC_schurPivotPhase___rarg___lambda__2___closed__1);
l_MOC_schurPivotPhase___rarg___closed__1 = _init_l_MOC_schurPivotPhase___rarg___closed__1();
lean_mark_persistent(l_MOC_schurPivotPhase___rarg___closed__1);
l_MOC_schurPhaseSum___rarg___lambda__3___closed__1 = _init_l_MOC_schurPhaseSum___rarg___lambda__3___closed__1();
lean_mark_persistent(l_MOC_schurPhaseSum___rarg___lambda__3___closed__1);
l_MOC_schurPhaseSum___rarg___lambda__4___closed__1 = _init_l_MOC_schurPhaseSum___rarg___lambda__4___closed__1();
lean_mark_persistent(l_MOC_schurPhaseSum___rarg___lambda__4___closed__1);
l_MOC_schurPhaseSum___rarg___lambda__4___closed__2 = _init_l_MOC_schurPhaseSum___rarg___lambda__4___closed__2();
lean_mark_persistent(l_MOC_schurPhaseSum___rarg___lambda__4___closed__2);
l_MOC_schurPhaseSum___rarg___closed__1 = _init_l_MOC_schurPhaseSum___rarg___closed__1();
lean_mark_persistent(l_MOC_schurPhaseSum___rarg___closed__1);
l_MOC_schurPhaseSum___rarg___closed__2 = _init_l_MOC_schurPhaseSum___rarg___closed__2();
lean_mark_persistent(l_MOC_schurPhaseSum___rarg___closed__2);
l_MOC_schurPhaseSum___rarg___closed__3 = _init_l_MOC_schurPhaseSum___rarg___closed__3();
lean_mark_persistent(l_MOC_schurPhaseSum___rarg___closed__3);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
