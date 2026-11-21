// Lean compiler output
// Module: MOC.NormalOrbit
// Imports: Init MOC.Jacobi MOC.Normal MOC.Singular MOC.Small MOC.Variational
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
LEAN_EXPORT lean_object* l_MOC_frobeniusSq(lean_object*);
LEAN_EXPORT lean_object* l_Finset_sum___at_MOC_frobeniusSq___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_MOC_frobeniusSq___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MOC_frobeniusSq___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Finset_sum___at_MOC_frobeniusSq___spec__3___rarg(lean_object*, lean_object*);
lean_object* l_Multiset_map___rarg(lean_object*, lean_object*);
lean_object* l_Complex_normSq(lean_object*);
LEAN_EXPORT lean_object* l_Multiset_sum___at_MOC_frobeniusSq___spec__2(lean_object*);
static lean_object* l_Multiset_sum___at_MOC_frobeniusSq___spec__2___closed__1;
LEAN_EXPORT lean_object* l_MOC_frobeniusSq___rarg___lambda__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Finset_sum___at_MOC_frobeniusSq___spec__3(lean_object*);
LEAN_EXPORT lean_object* l_Finset_sum___at_MOC_frobeniusSq___spec__1___rarg(lean_object*, lean_object*);
lean_object* l_List_foldrTR___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_471_(lean_object*, lean_object*);
static lean_object* _init_l_Multiset_sum___at_MOC_frobeniusSq___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_471_), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Multiset_sum___at_MOC_frobeniusSq___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Multiset_sum___at_MOC_frobeniusSq___spec__2___closed__1;
x_3 = l___private_Mathlib_Data_Real_Basic_0__Real_zero;
x_4 = l_List_foldrTR___rarg(x_2, x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Finset_sum___at_MOC_frobeniusSq___spec__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = l_Multiset_map___rarg(x_2, x_1);
x_4 = lean_alloc_closure((void*)(l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_471_), 2, 0);
x_5 = l___private_Mathlib_Data_Real_Basic_0__Real_zero;
x_6 = l_List_foldrTR___rarg(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Finset_sum___at_MOC_frobeniusSq___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Finset_sum___at_MOC_frobeniusSq___spec__1___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Finset_sum___at_MOC_frobeniusSq___spec__3___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = l_Multiset_map___rarg(x_2, x_1);
x_4 = lean_alloc_closure((void*)(l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_471_), 2, 0);
x_5 = l___private_Mathlib_Data_Real_Basic_0__Real_zero;
x_6 = l_List_foldrTR___rarg(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Finset_sum___at_MOC_frobeniusSq___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Finset_sum___at_MOC_frobeniusSq___spec__3___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_MOC_frobeniusSq___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_apply_2(x_1, x_2, x_3);
x_5 = l_Complex_normSq(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_MOC_frobeniusSq___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_closure((void*)(l_MOC_frobeniusSq___rarg___lambda__1), 3, 2);
lean_closure_set(x_4, 0, x_1);
lean_closure_set(x_4, 1, x_3);
x_5 = l_Finset_sum___at_MOC_frobeniusSq___spec__1___rarg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_MOC_frobeniusSq___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
lean_inc(x_1);
x_3 = lean_alloc_closure((void*)(l_MOC_frobeniusSq___rarg___lambda__2), 3, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
x_4 = l_Finset_sum___at_MOC_frobeniusSq___spec__3___rarg(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_MOC_frobeniusSq(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_MOC_frobeniusSq___rarg), 2, 0);
return x_2;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_MOC_Jacobi(uint8_t builtin, lean_object*);
lean_object* initialize_MOC_Normal(uint8_t builtin, lean_object*);
lean_object* initialize_MOC_Singular(uint8_t builtin, lean_object*);
lean_object* initialize_MOC_Small(uint8_t builtin, lean_object*);
lean_object* initialize_MOC_Variational(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_MOC_NormalOrbit(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_MOC_Jacobi(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_MOC_Normal(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_MOC_Singular(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_MOC_Small(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_MOC_Variational(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Multiset_sum___at_MOC_frobeniusSq___spec__2___closed__1 = _init_l_Multiset_sum___at_MOC_frobeniusSq___spec__2___closed__1();
lean_mark_persistent(l_Multiset_sum___at_MOC_frobeniusSq___spec__2___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
