// Lean compiler output
// Module: MOC.Householder
// Imports: Init MOC.Core Mathlib.Analysis.Complex.Basic Mathlib.LinearAlgebra.Matrix.SchurComplement Mathlib.Tactic.LinearCombination Mathlib.Topology.Algebra.Module.Cardinality Mathlib.Topology.Instances.Matrix
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
static lean_object* l_MOC_rankOnePhase___rarg___closed__5;
LEAN_EXPORT lean_object* l_Matrix_vecMulVec___at_MOC_rankOnePhase___spec__2(lean_object*);
static lean_object* l_MOC_rankOnePhase___rarg___closed__4;
LEAN_EXPORT lean_object* l_Matrix_vecMulVec___at_MOC_rankOnePhase___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Pi_instAdd___elambda__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Matrix_diagonal___at_MOC_rankOnePhase___spec__1(lean_object*);
static lean_object* l_Matrix_diagonal___at_MOC_rankOnePhase___spec__1___rarg___closed__1;
LEAN_EXPORT lean_object* l_MOC_rankOnePhase___rarg___lambda__5___boxed(lean_object*);
extern lean_object* l___private_Mathlib_Data_Real_Basic_0__Real_one;
static lean_object* l_MOC_rankOnePhase___rarg___lambda__5___closed__1;
static lean_object* l_MOC_rankOnePhase___rarg___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_MOC_rankOnePhase___rarg___lambda__2(lean_object*);
static lean_object* l_MOC_rankOnePhase___rarg___lambda__4___closed__1;
lean_object* l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_579_(lean_object*);
LEAN_EXPORT lean_object* l_MOC_rankOnePhase___rarg___lambda__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_MOC_rankOnePhase(lean_object*);
LEAN_EXPORT lean_object* l_MOC_rankOnePhase___rarg___lambda__1(lean_object*);
LEAN_EXPORT lean_object* l_MOC_rankOnePhase___rarg___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_MOC_rankOnePhase___rarg___lambda__5___closed__2;
lean_object* l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_664_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Matrix_diagonal___at_MOC_rankOnePhase___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MOC_rankOnePhase___rarg___lambda__5(lean_object*);
static lean_object* l_MOC_rankOnePhase___rarg___closed__1;
static lean_object* l_MOC_rankOnePhase___rarg___closed__3;
lean_object* l_Complex_instAdd(lean_object*, lean_object*);
lean_object* l_Function_comp___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MOC_rankOnePhase___rarg___lambda__4(lean_object*);
lean_object* l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_471_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MOC_rankOnePhase___rarg___lambda__4___boxed(lean_object*);
LEAN_EXPORT lean_object* l_MOC_rankOnePhase___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_MOC_rankOnePhase___rarg___closed__2;
static lean_object* _init_l_Matrix_diagonal___at_MOC_rankOnePhase___spec__1___rarg___closed__1() {
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
LEAN_EXPORT lean_object* l_Matrix_diagonal___at_MOC_rankOnePhase___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
lean_inc(x_3);
x_5 = lean_apply_2(x_1, x_3, x_4);
x_6 = lean_unbox(x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_3);
lean_dec(x_2);
x_7 = l_Matrix_diagonal___at_MOC_rankOnePhase___spec__1___rarg___closed__1;
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
LEAN_EXPORT lean_object* l_Matrix_diagonal___at_MOC_rankOnePhase___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Matrix_diagonal___at_MOC_rankOnePhase___spec__1___rarg), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Matrix_vecMulVec___at_MOC_rankOnePhase___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_5 = lean_apply_1(x_1, x_3);
x_6 = lean_apply_1(x_2, x_4);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_inc(x_8);
lean_inc(x_7);
x_9 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_664_(x_7, x_8);
x_10 = lean_ctor_get(x_5, 1);
lean_inc(x_10);
lean_dec(x_5);
x_11 = lean_ctor_get(x_6, 1);
lean_inc(x_11);
lean_dec(x_6);
lean_inc(x_11);
lean_inc(x_10);
x_12 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_664_(x_10, x_11);
x_13 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_579_(x_12);
x_14 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_471_(x_9, x_13);
x_15 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_664_(x_7, x_11);
x_16 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_664_(x_10, x_8);
x_17 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_471_(x_15, x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_14);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Matrix_vecMulVec___at_MOC_rankOnePhase___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Matrix_vecMulVec___at_MOC_rankOnePhase___spec__2___rarg), 4, 0);
return x_2;
}
}
static lean_object* _init_l_MOC_rankOnePhase___rarg___lambda__1___closed__1() {
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
LEAN_EXPORT lean_object* l_MOC_rankOnePhase___rarg___lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_MOC_rankOnePhase___rarg___lambda__1___closed__1;
return x_2;
}
}
LEAN_EXPORT lean_object* l_MOC_rankOnePhase___rarg___lambda__2(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_579_(x_3);
lean_ctor_set(x_1, 1, x_4);
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_1);
x_7 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_579_(x_6);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_MOC_rankOnePhase___rarg___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_7 = l_Matrix_vecMulVec___at_MOC_rankOnePhase___spec__2___rarg(x_1, x_2, x_5, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_inc(x_8);
lean_inc(x_3);
x_9 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_664_(x_3, x_8);
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
lean_dec(x_7);
lean_inc(x_10);
lean_inc(x_4);
x_11 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_664_(x_4, x_10);
x_12 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_579_(x_11);
x_13 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_471_(x_9, x_12);
x_14 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_664_(x_3, x_10);
x_15 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_664_(x_4, x_8);
x_16 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_471_(x_14, x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_13);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
static lean_object* _init_l_MOC_rankOnePhase___rarg___lambda__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Complex_instAdd), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_MOC_rankOnePhase___rarg___lambda__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_MOC_rankOnePhase___rarg___lambda__4___closed__1;
return x_2;
}
}
static lean_object* _init_l_MOC_rankOnePhase___rarg___lambda__5___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_MOC_rankOnePhase___rarg___lambda__4___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_MOC_rankOnePhase___rarg___lambda__5___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_MOC_rankOnePhase___rarg___lambda__5___closed__1;
x_2 = lean_alloc_closure((void*)(l_Pi_instAdd___elambda__1___rarg), 4, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_MOC_rankOnePhase___rarg___lambda__5(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_MOC_rankOnePhase___rarg___lambda__5___closed__2;
return x_2;
}
}
static lean_object* _init_l_MOC_rankOnePhase___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_MOC_rankOnePhase___rarg___lambda__1___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_MOC_rankOnePhase___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Mathlib_Data_Real_Basic_0__Real_one;
x_2 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_579_(x_1);
return x_2;
}
}
static lean_object* _init_l_MOC_rankOnePhase___rarg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Mathlib_Data_Real_Basic_0__Real_zero;
x_2 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_579_(x_1);
return x_2;
}
}
static lean_object* _init_l_MOC_rankOnePhase___rarg___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_MOC_rankOnePhase___rarg___lambda__2), 1, 0);
return x_1;
}
}
static lean_object* _init_l_MOC_rankOnePhase___rarg___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_MOC_rankOnePhase___rarg___lambda__5___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_MOC_rankOnePhase___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_6 = l_MOC_rankOnePhase___rarg___closed__1;
x_7 = lean_alloc_closure((void*)(l_Matrix_diagonal___at_MOC_rankOnePhase___spec__1___rarg), 4, 2);
lean_closure_set(x_7, 0, x_1);
lean_closure_set(x_7, 1, x_6);
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
x_9 = l_MOC_rankOnePhase___rarg___closed__2;
x_10 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_471_(x_8, x_9);
x_11 = lean_ctor_get(x_3, 1);
lean_inc(x_11);
lean_dec(x_3);
x_12 = l_MOC_rankOnePhase___rarg___closed__3;
x_13 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_471_(x_11, x_12);
x_14 = l_MOC_rankOnePhase___rarg___closed__4;
lean_inc(x_2);
x_15 = lean_alloc_closure((void*)(l_Function_comp___rarg), 3, 2);
lean_closure_set(x_15, 0, x_14);
lean_closure_set(x_15, 1, x_2);
x_16 = lean_alloc_closure((void*)(l_MOC_rankOnePhase___rarg___lambda__3), 6, 4);
lean_closure_set(x_16, 0, x_2);
lean_closure_set(x_16, 1, x_15);
lean_closure_set(x_16, 2, x_10);
lean_closure_set(x_16, 3, x_13);
x_17 = l_MOC_rankOnePhase___rarg___closed__5;
x_18 = l_Pi_instAdd___elambda__1___rarg(x_17, x_7, x_16, x_4);
x_19 = lean_apply_1(x_18, x_5);
return x_19;
}
}
LEAN_EXPORT lean_object* l_MOC_rankOnePhase(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_MOC_rankOnePhase___rarg), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_MOC_rankOnePhase___rarg___lambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_MOC_rankOnePhase___rarg___lambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_MOC_rankOnePhase___rarg___lambda__4___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_MOC_rankOnePhase___rarg___lambda__4(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_MOC_rankOnePhase___rarg___lambda__5___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_MOC_rankOnePhase___rarg___lambda__5(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_MOC_Core(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Analysis_Complex_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_LinearAlgebra_Matrix_SchurComplement(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Tactic_LinearCombination(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Topology_Algebra_Module_Cardinality(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Topology_Instances_Matrix(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_MOC_Householder(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_MOC_Core(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Analysis_Complex_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_LinearAlgebra_Matrix_SchurComplement(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Tactic_LinearCombination(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Topology_Algebra_Module_Cardinality(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Topology_Instances_Matrix(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Matrix_diagonal___at_MOC_rankOnePhase___spec__1___rarg___closed__1 = _init_l_Matrix_diagonal___at_MOC_rankOnePhase___spec__1___rarg___closed__1();
lean_mark_persistent(l_Matrix_diagonal___at_MOC_rankOnePhase___spec__1___rarg___closed__1);
l_MOC_rankOnePhase___rarg___lambda__1___closed__1 = _init_l_MOC_rankOnePhase___rarg___lambda__1___closed__1();
lean_mark_persistent(l_MOC_rankOnePhase___rarg___lambda__1___closed__1);
l_MOC_rankOnePhase___rarg___lambda__4___closed__1 = _init_l_MOC_rankOnePhase___rarg___lambda__4___closed__1();
lean_mark_persistent(l_MOC_rankOnePhase___rarg___lambda__4___closed__1);
l_MOC_rankOnePhase___rarg___lambda__5___closed__1 = _init_l_MOC_rankOnePhase___rarg___lambda__5___closed__1();
lean_mark_persistent(l_MOC_rankOnePhase___rarg___lambda__5___closed__1);
l_MOC_rankOnePhase___rarg___lambda__5___closed__2 = _init_l_MOC_rankOnePhase___rarg___lambda__5___closed__2();
lean_mark_persistent(l_MOC_rankOnePhase___rarg___lambda__5___closed__2);
l_MOC_rankOnePhase___rarg___closed__1 = _init_l_MOC_rankOnePhase___rarg___closed__1();
lean_mark_persistent(l_MOC_rankOnePhase___rarg___closed__1);
l_MOC_rankOnePhase___rarg___closed__2 = _init_l_MOC_rankOnePhase___rarg___closed__2();
lean_mark_persistent(l_MOC_rankOnePhase___rarg___closed__2);
l_MOC_rankOnePhase___rarg___closed__3 = _init_l_MOC_rankOnePhase___rarg___closed__3();
lean_mark_persistent(l_MOC_rankOnePhase___rarg___closed__3);
l_MOC_rankOnePhase___rarg___closed__4 = _init_l_MOC_rankOnePhase___rarg___closed__4();
lean_mark_persistent(l_MOC_rankOnePhase___rarg___closed__4);
l_MOC_rankOnePhase___rarg___closed__5 = _init_l_MOC_rankOnePhase___rarg___closed__5();
lean_mark_persistent(l_MOC_rankOnePhase___rarg___closed__5);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
