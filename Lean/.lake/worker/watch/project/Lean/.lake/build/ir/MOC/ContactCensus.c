// Lean compiler output
// Module: MOC.ContactCensus
// Imports: Init MOC.Obstruction Mathlib.Data.Fintype.Perm
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
LEAN_EXPORT lean_object* l_MOC_fourPermIndex(lean_object*);
static lean_object* l_MOC_referenceNonminorFacetTwice___closed__1;
LEAN_EXPORT uint8_t l_List_elem___at_MOC_referenceNonminorFacetZeroIndices___spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Finset_sum___at_MOC_referenceNonminorFacetTwice___spec__1(lean_object*, lean_object*);
lean_object* l_Int_add___boxed(lean_object*, lean_object*);
static lean_object* l_MOC_fourPerm___closed__2;
LEAN_EXPORT lean_object* l_List_elem___at_MOC_referenceNonminorFacetZeroIndices___spec__2___boxed(lean_object*, lean_object*);
lean_object* l_Equiv_swap___elambda__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MOC_fourPerm___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Multiset_sum___at_MOC_referenceNonminorFacetTwice___spec__2(lean_object*);
static lean_object* l_MOC_fourPermEquiv___closed__3;
LEAN_EXPORT lean_object* l_MOC_fourPermEquiv;
LEAN_EXPORT lean_object* l___private_MOC_ContactCensus_0__MOC_mixedPermutationCostInt(lean_object*);
LEAN_EXPORT lean_object* l_MOC_referenceNonminorFacetTwice___lambda__1(lean_object*, lean_object*);
static lean_object* l_MOC_fourPermEquiv___closed__2;
lean_object* l_instDecidableEqFin___rarg___boxed(lean_object*, lean_object*);
static lean_object* l_MOC_fourPermEquiv___closed__1;
lean_object* l_Multiset_map___rarg(lean_object*, lean_object*);
static lean_object* l_MOC_referenceNonminorFacetZeroIndices___closed__1;
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Matrix_vecEmpty___boxed(lean_object*, lean_object*);
static lean_object* l_Multiset_sum___at_MOC_referenceNonminorFacetTwice___spec__2___closed__1;
LEAN_EXPORT lean_object* l_MOC_referenceNonminorFacetZeroIndices;
LEAN_EXPORT lean_object* l_MOC_fourPerm(lean_object*);
static lean_object* l_MOC_fourPerm___closed__1;
lean_object* l_Equiv_trans___rarg(lean_object*, lean_object*);
static lean_object* l_MOC_referenceNonminorFacetTwice___closed__2;
lean_object* lean_int_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Equiv_swap___at_MOC_fourPerm___spec__1(lean_object*, lean_object*);
static lean_object* l_MOC_referenceNonminorFacetTwice___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Multiset_ndinsert___at_MOC_referenceNonminorFacetZeroIndices___spec__1(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l_Equiv_swap___at_MOC_fourPerm___spec__1___closed__1;
lean_object* lean_nat_mod(lean_object*, lean_object*);
lean_object* l_List_ofFn___rarg(lean_object*, lean_object*);
lean_object* l_Fin_cases(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_List_foldrTR___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
lean_object* l_Equiv_refl(lean_object*);
LEAN_EXPORT lean_object* l_MOC_referenceNonminorFacetTwice(lean_object*);
lean_object* l_List_finRange___lambda__1___boxed(lean_object*);
static lean_object* l_Multiset_sum___at_MOC_referenceNonminorFacetTwice___spec__2___closed__2;
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Matrix_vecCons___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Equiv_swap___at_MOC_fourPerm___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_instDecidableEqFin___rarg___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Equiv_swap___at_MOC_fourPerm___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_Equiv_swap___at_MOC_fourPerm___spec__1___closed__1;
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
static lean_object* _init_l_MOC_fourPerm___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Equiv_refl(lean_box(0));
return x_1;
}
}
static lean_object* _init_l_MOC_fourPerm___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Matrix_vecEmpty___boxed), 2, 1);
lean_closure_set(x_1, 0, lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_MOC_fourPerm(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_2 = lean_unsigned_to_nat(2u);
x_3 = lean_unsigned_to_nat(3u);
x_4 = l_Equiv_swap___at_MOC_fourPerm___spec__1(x_2, x_3);
x_5 = lean_unsigned_to_nat(1u);
x_6 = l_Equiv_swap___at_MOC_fourPerm___spec__1(x_5, x_2);
x_7 = l_Equiv_swap___at_MOC_fourPerm___spec__1(x_5, x_3);
lean_inc(x_7);
lean_inc(x_6);
x_8 = l_Equiv_trans___rarg(x_6, x_7);
x_9 = l_Equiv_swap___at_MOC_fourPerm___spec__1(x_2, x_5);
lean_inc(x_9);
lean_inc(x_7);
x_10 = l_Equiv_trans___rarg(x_7, x_9);
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Equiv_swap___at_MOC_fourPerm___spec__1(x_11, x_5);
lean_inc(x_4);
lean_inc(x_12);
x_13 = l_Equiv_trans___rarg(x_12, x_4);
x_14 = l_Equiv_swap___at_MOC_fourPerm___spec__1(x_11, x_2);
lean_inc(x_14);
lean_inc(x_12);
x_15 = l_Equiv_trans___rarg(x_12, x_14);
x_16 = l_Equiv_swap___at_MOC_fourPerm___spec__1(x_11, x_3);
lean_inc(x_16);
lean_inc(x_14);
x_17 = l_Equiv_trans___rarg(x_14, x_16);
lean_inc(x_17);
lean_inc(x_12);
x_18 = l_Equiv_trans___rarg(x_12, x_17);
x_19 = l_Equiv_swap___at_MOC_fourPerm___spec__1(x_2, x_11);
lean_inc(x_16);
x_20 = l_Equiv_trans___rarg(x_16, x_19);
lean_inc(x_20);
lean_inc(x_12);
x_21 = l_Equiv_trans___rarg(x_12, x_20);
lean_inc(x_16);
lean_inc(x_12);
x_22 = l_Equiv_trans___rarg(x_12, x_16);
x_23 = l_Equiv_swap___at_MOC_fourPerm___spec__1(x_5, x_11);
lean_inc(x_23);
lean_inc(x_14);
x_24 = l_Equiv_trans___rarg(x_14, x_23);
lean_inc(x_7);
lean_inc(x_23);
x_25 = l_Equiv_trans___rarg(x_23, x_7);
lean_inc(x_14);
x_26 = l_Equiv_trans___rarg(x_14, x_25);
lean_inc(x_7);
lean_inc(x_14);
x_27 = l_Equiv_trans___rarg(x_14, x_7);
lean_inc(x_12);
lean_inc(x_7);
x_28 = l_Equiv_trans___rarg(x_7, x_12);
lean_inc(x_14);
x_29 = l_Equiv_trans___rarg(x_14, x_28);
lean_inc(x_23);
x_30 = l_Equiv_trans___rarg(x_23, x_9);
lean_inc(x_16);
x_31 = l_Equiv_trans___rarg(x_16, x_30);
lean_inc(x_23);
lean_inc(x_16);
x_32 = l_Equiv_trans___rarg(x_16, x_23);
lean_inc(x_6);
x_33 = l_Equiv_trans___rarg(x_6, x_23);
lean_inc(x_16);
x_34 = l_Equiv_trans___rarg(x_16, x_33);
lean_inc(x_6);
lean_inc(x_16);
x_35 = l_Equiv_trans___rarg(x_16, x_6);
x_36 = l_MOC_fourPerm___closed__2;
x_37 = lean_alloc_closure((void*)(l_Matrix_vecCons___rarg___boxed), 4, 3);
lean_closure_set(x_37, 0, x_11);
lean_closure_set(x_37, 1, x_35);
lean_closure_set(x_37, 2, x_36);
x_38 = lean_alloc_closure((void*)(l_Matrix_vecCons___rarg___boxed), 4, 3);
lean_closure_set(x_38, 0, x_5);
lean_closure_set(x_38, 1, x_34);
lean_closure_set(x_38, 2, x_37);
x_39 = lean_alloc_closure((void*)(l_Matrix_vecCons___rarg___boxed), 4, 3);
lean_closure_set(x_39, 0, x_2);
lean_closure_set(x_39, 1, x_16);
lean_closure_set(x_39, 2, x_38);
x_40 = lean_alloc_closure((void*)(l_Matrix_vecCons___rarg___boxed), 4, 3);
lean_closure_set(x_40, 0, x_3);
lean_closure_set(x_40, 1, x_20);
lean_closure_set(x_40, 2, x_39);
x_41 = lean_unsigned_to_nat(4u);
x_42 = lean_alloc_closure((void*)(l_Matrix_vecCons___rarg___boxed), 4, 3);
lean_closure_set(x_42, 0, x_41);
lean_closure_set(x_42, 1, x_32);
lean_closure_set(x_42, 2, x_40);
x_43 = lean_unsigned_to_nat(5u);
x_44 = lean_alloc_closure((void*)(l_Matrix_vecCons___rarg___boxed), 4, 3);
lean_closure_set(x_44, 0, x_43);
lean_closure_set(x_44, 1, x_31);
lean_closure_set(x_44, 2, x_42);
x_45 = lean_unsigned_to_nat(6u);
x_46 = lean_alloc_closure((void*)(l_Matrix_vecCons___rarg___boxed), 4, 3);
lean_closure_set(x_46, 0, x_45);
lean_closure_set(x_46, 1, x_29);
lean_closure_set(x_46, 2, x_44);
x_47 = lean_unsigned_to_nat(7u);
x_48 = lean_alloc_closure((void*)(l_Matrix_vecCons___rarg___boxed), 4, 3);
lean_closure_set(x_48, 0, x_47);
lean_closure_set(x_48, 1, x_27);
lean_closure_set(x_48, 2, x_46);
x_49 = lean_unsigned_to_nat(8u);
x_50 = lean_alloc_closure((void*)(l_Matrix_vecCons___rarg___boxed), 4, 3);
lean_closure_set(x_50, 0, x_49);
lean_closure_set(x_50, 1, x_17);
lean_closure_set(x_50, 2, x_48);
x_51 = lean_unsigned_to_nat(9u);
x_52 = lean_alloc_closure((void*)(l_Matrix_vecCons___rarg___boxed), 4, 3);
lean_closure_set(x_52, 0, x_51);
lean_closure_set(x_52, 1, x_14);
lean_closure_set(x_52, 2, x_50);
x_53 = lean_unsigned_to_nat(10u);
x_54 = lean_alloc_closure((void*)(l_Matrix_vecCons___rarg___boxed), 4, 3);
lean_closure_set(x_54, 0, x_53);
lean_closure_set(x_54, 1, x_26);
lean_closure_set(x_54, 2, x_52);
x_55 = lean_unsigned_to_nat(11u);
x_56 = lean_alloc_closure((void*)(l_Matrix_vecCons___rarg___boxed), 4, 3);
lean_closure_set(x_56, 0, x_55);
lean_closure_set(x_56, 1, x_24);
lean_closure_set(x_56, 2, x_54);
x_57 = lean_unsigned_to_nat(12u);
x_58 = lean_alloc_closure((void*)(l_Matrix_vecCons___rarg___boxed), 4, 3);
lean_closure_set(x_58, 0, x_57);
lean_closure_set(x_58, 1, x_22);
lean_closure_set(x_58, 2, x_56);
x_59 = lean_unsigned_to_nat(13u);
x_60 = lean_alloc_closure((void*)(l_Matrix_vecCons___rarg___boxed), 4, 3);
lean_closure_set(x_60, 0, x_59);
lean_closure_set(x_60, 1, x_21);
lean_closure_set(x_60, 2, x_58);
x_61 = lean_unsigned_to_nat(14u);
x_62 = lean_alloc_closure((void*)(l_Matrix_vecCons___rarg___boxed), 4, 3);
lean_closure_set(x_62, 0, x_61);
lean_closure_set(x_62, 1, x_18);
lean_closure_set(x_62, 2, x_60);
x_63 = lean_unsigned_to_nat(15u);
x_64 = lean_alloc_closure((void*)(l_Matrix_vecCons___rarg___boxed), 4, 3);
lean_closure_set(x_64, 0, x_63);
lean_closure_set(x_64, 1, x_15);
lean_closure_set(x_64, 2, x_62);
x_65 = lean_unsigned_to_nat(16u);
x_66 = lean_alloc_closure((void*)(l_Matrix_vecCons___rarg___boxed), 4, 3);
lean_closure_set(x_66, 0, x_65);
lean_closure_set(x_66, 1, x_13);
lean_closure_set(x_66, 2, x_64);
x_67 = lean_unsigned_to_nat(17u);
x_68 = lean_alloc_closure((void*)(l_Matrix_vecCons___rarg___boxed), 4, 3);
lean_closure_set(x_68, 0, x_67);
lean_closure_set(x_68, 1, x_12);
lean_closure_set(x_68, 2, x_66);
x_69 = lean_unsigned_to_nat(18u);
x_70 = lean_alloc_closure((void*)(l_Matrix_vecCons___rarg___boxed), 4, 3);
lean_closure_set(x_70, 0, x_69);
lean_closure_set(x_70, 1, x_7);
lean_closure_set(x_70, 2, x_68);
x_71 = lean_unsigned_to_nat(19u);
x_72 = lean_alloc_closure((void*)(l_Matrix_vecCons___rarg___boxed), 4, 3);
lean_closure_set(x_72, 0, x_71);
lean_closure_set(x_72, 1, x_10);
lean_closure_set(x_72, 2, x_70);
x_73 = lean_unsigned_to_nat(20u);
x_74 = lean_alloc_closure((void*)(l_Matrix_vecCons___rarg___boxed), 4, 3);
lean_closure_set(x_74, 0, x_73);
lean_closure_set(x_74, 1, x_8);
lean_closure_set(x_74, 2, x_72);
x_75 = lean_unsigned_to_nat(21u);
x_76 = lean_alloc_closure((void*)(l_Matrix_vecCons___rarg___boxed), 4, 3);
lean_closure_set(x_76, 0, x_75);
lean_closure_set(x_76, 1, x_6);
lean_closure_set(x_76, 2, x_74);
x_77 = lean_unsigned_to_nat(22u);
x_78 = lean_alloc_closure((void*)(l_Matrix_vecCons___rarg___boxed), 4, 3);
lean_closure_set(x_78, 0, x_77);
lean_closure_set(x_78, 1, x_4);
lean_closure_set(x_78, 2, x_76);
x_79 = lean_unsigned_to_nat(23u);
x_80 = l_MOC_fourPerm___closed__1;
x_81 = l_Fin_cases(x_79, lean_box(0), x_80, x_78, x_1);
return x_81;
}
}
LEAN_EXPORT lean_object* l_MOC_fourPerm___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_MOC_fourPerm(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_MOC_fourPermIndex(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_12; uint8_t x_13; lean_object* x_14; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
lean_dec(x_1);
x_3 = lean_unsigned_to_nat(0u);
lean_inc(x_2);
x_4 = lean_apply_1(x_2, x_3);
x_5 = lean_unsigned_to_nat(1u);
lean_inc(x_2);
x_6 = lean_apply_1(x_2, x_5);
x_7 = lean_unsigned_to_nat(2u);
x_8 = lean_apply_1(x_2, x_7);
x_9 = lean_unsigned_to_nat(6u);
x_10 = lean_nat_mul(x_9, x_4);
x_11 = lean_nat_dec_lt(x_4, x_6);
x_12 = lean_nat_dec_lt(x_4, x_8);
lean_dec(x_4);
x_13 = lean_nat_dec_lt(x_6, x_8);
if (x_11 == 0)
{
x_14 = x_3;
goto block_36;
}
else
{
x_14 = x_5;
goto block_36;
}
block_36:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_nat_sub(x_6, x_14);
lean_dec(x_14);
lean_dec(x_6);
x_16 = lean_nat_mul(x_7, x_15);
lean_dec(x_15);
x_17 = lean_nat_add(x_10, x_16);
lean_dec(x_16);
lean_dec(x_10);
if (x_12 == 0)
{
lean_object* x_18; 
x_18 = lean_nat_sub(x_8, x_3);
lean_dec(x_8);
if (x_13 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_nat_sub(x_18, x_3);
lean_dec(x_18);
x_20 = lean_nat_add(x_17, x_19);
lean_dec(x_19);
lean_dec(x_17);
x_21 = lean_unsigned_to_nat(24u);
x_22 = lean_nat_mod(x_20, x_21);
lean_dec(x_20);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_nat_sub(x_18, x_5);
lean_dec(x_18);
x_24 = lean_nat_add(x_17, x_23);
lean_dec(x_23);
lean_dec(x_17);
x_25 = lean_unsigned_to_nat(24u);
x_26 = lean_nat_mod(x_24, x_25);
lean_dec(x_24);
return x_26;
}
}
else
{
lean_object* x_27; 
x_27 = lean_nat_sub(x_8, x_5);
lean_dec(x_8);
if (x_13 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_nat_sub(x_27, x_3);
lean_dec(x_27);
x_29 = lean_nat_add(x_17, x_28);
lean_dec(x_28);
lean_dec(x_17);
x_30 = lean_unsigned_to_nat(24u);
x_31 = lean_nat_mod(x_29, x_30);
lean_dec(x_29);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_nat_sub(x_27, x_5);
lean_dec(x_27);
x_33 = lean_nat_add(x_17, x_32);
lean_dec(x_32);
lean_dec(x_17);
x_34 = lean_unsigned_to_nat(24u);
x_35 = lean_nat_mod(x_33, x_34);
lean_dec(x_33);
return x_35;
}
}
}
}
}
static lean_object* _init_l_MOC_fourPermEquiv___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_MOC_fourPerm___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_MOC_fourPermEquiv___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_MOC_fourPermIndex), 1, 0);
return x_1;
}
}
static lean_object* _init_l_MOC_fourPermEquiv___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_MOC_fourPermEquiv___closed__1;
x_2 = l_MOC_fourPermEquiv___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_MOC_fourPermEquiv() {
_start:
{
lean_object* x_1; 
x_1 = l_MOC_fourPermEquiv___closed__3;
return x_1;
}
}
static lean_object* _init_l_Multiset_sum___at_MOC_referenceNonminorFacetTwice___spec__2___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Multiset_sum___at_MOC_referenceNonminorFacetTwice___spec__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Int_add___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Multiset_sum___at_MOC_referenceNonminorFacetTwice___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Multiset_sum___at_MOC_referenceNonminorFacetTwice___spec__2___closed__2;
x_3 = l_Multiset_sum___at_MOC_referenceNonminorFacetTwice___spec__2___closed__1;
x_4 = l_List_foldrTR___rarg(x_2, x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Finset_sum___at_MOC_referenceNonminorFacetTwice___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Multiset_map___rarg(x_2, x_1);
x_4 = l_Multiset_sum___at_MOC_referenceNonminorFacetTwice___spec__2(x_3);
return x_4;
}
}
static lean_object* _init_l_MOC_referenceNonminorFacetTwice___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_MOC_referenceNonminorFacetTwice___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
lean_inc(x_2);
x_4 = lean_apply_1(x_3, x_2);
x_5 = lean_nat_dec_eq(x_4, x_2);
lean_dec(x_2);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = l_Multiset_sum___at_MOC_referenceNonminorFacetTwice___spec__2___closed__1;
return x_6;
}
else
{
lean_object* x_7; 
x_7 = l_MOC_referenceNonminorFacetTwice___lambda__1___closed__1;
return x_7;
}
}
}
static lean_object* _init_l_MOC_referenceNonminorFacetTwice___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_List_finRange___lambda__1___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_MOC_referenceNonminorFacetTwice___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = l_MOC_referenceNonminorFacetTwice___closed__1;
x_3 = l_List_ofFn___rarg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_MOC_referenceNonminorFacetTwice(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_66; lean_object* x_86; 
lean_inc(x_1);
x_2 = lean_alloc_closure((void*)(l_MOC_referenceNonminorFacetTwice___lambda__1), 2, 1);
lean_closure_set(x_2, 0, x_1);
x_3 = l_MOC_referenceNonminorFacetTwice___closed__2;
x_4 = l_Finset_sum___at_MOC_referenceNonminorFacetTwice___spec__1(x_3, x_2);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_unsigned_to_nat(0u);
lean_inc(x_5);
x_7 = lean_apply_1(x_5, x_6);
x_8 = lean_nat_dec_eq(x_7, x_6);
if (x_8 == 0)
{
lean_object* x_96; 
x_96 = lean_box(0);
x_86 = x_96;
goto block_95;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; uint8_t x_100; 
x_97 = lean_unsigned_to_nat(1u);
lean_inc(x_5);
x_98 = lean_apply_1(x_5, x_97);
x_99 = lean_unsigned_to_nat(2u);
x_100 = lean_nat_dec_eq(x_98, x_99);
lean_dec(x_98);
if (x_100 == 0)
{
lean_object* x_101; 
x_101 = lean_box(0);
x_86 = x_101;
goto block_95;
}
else
{
lean_object* x_102; 
x_102 = l_MOC_referenceNonminorFacetTwice___lambda__1___closed__1;
x_9 = x_102;
goto block_65;
}
}
block_65:
{
lean_object* x_10; lean_object* x_44; 
if (x_8 == 0)
{
lean_object* x_56; 
x_56 = lean_box(0);
x_44 = x_56;
goto block_55;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_57 = lean_unsigned_to_nat(2u);
lean_inc(x_5);
x_58 = lean_apply_1(x_5, x_57);
x_59 = lean_unsigned_to_nat(1u);
x_60 = lean_nat_dec_eq(x_58, x_59);
lean_dec(x_58);
if (x_60 == 0)
{
lean_object* x_61; 
x_61 = lean_box(0);
x_44 = x_61;
goto block_55;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_dec(x_7);
lean_dec(x_5);
x_62 = l_MOC_referenceNonminorFacetTwice___lambda__1___closed__1;
x_63 = lean_int_sub(x_9, x_62);
lean_dec(x_9);
x_64 = lean_int_sub(x_4, x_63);
lean_dec(x_63);
lean_dec(x_4);
return x_64;
}
}
block_43:
{
lean_object* x_11; uint8_t x_12; 
lean_dec(x_10);
x_11 = lean_unsigned_to_nat(2u);
x_12 = lean_nat_dec_eq(x_7, x_11);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_unsigned_to_nat(3u);
x_14 = lean_nat_dec_eq(x_7, x_13);
lean_dec(x_7);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_5);
x_15 = l_Multiset_sum___at_MOC_referenceNonminorFacetTwice___spec__2___closed__1;
x_16 = lean_int_sub(x_9, x_15);
lean_dec(x_9);
x_17 = lean_int_sub(x_4, x_16);
lean_dec(x_16);
lean_dec(x_4);
return x_17;
}
else
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_apply_1(x_5, x_11);
x_19 = lean_nat_dec_eq(x_18, x_11);
lean_dec(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = l_Multiset_sum___at_MOC_referenceNonminorFacetTwice___spec__2___closed__1;
x_21 = lean_int_sub(x_9, x_20);
lean_dec(x_9);
x_22 = lean_int_sub(x_4, x_21);
lean_dec(x_21);
lean_dec(x_4);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = l_MOC_referenceNonminorFacetTwice___lambda__1___closed__1;
x_24 = lean_int_sub(x_9, x_23);
lean_dec(x_9);
x_25 = lean_int_sub(x_4, x_24);
lean_dec(x_24);
lean_dec(x_4);
return x_25;
}
}
}
else
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_apply_1(x_5, x_11);
x_27 = lean_unsigned_to_nat(3u);
x_28 = lean_nat_dec_eq(x_26, x_27);
if (x_28 == 0)
{
uint8_t x_29; 
x_29 = lean_nat_dec_eq(x_7, x_27);
lean_dec(x_7);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_26);
x_30 = l_Multiset_sum___at_MOC_referenceNonminorFacetTwice___spec__2___closed__1;
x_31 = lean_int_sub(x_9, x_30);
lean_dec(x_9);
x_32 = lean_int_sub(x_4, x_31);
lean_dec(x_31);
lean_dec(x_4);
return x_32;
}
else
{
uint8_t x_33; 
x_33 = lean_nat_dec_eq(x_26, x_11);
lean_dec(x_26);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = l_Multiset_sum___at_MOC_referenceNonminorFacetTwice___spec__2___closed__1;
x_35 = lean_int_sub(x_9, x_34);
lean_dec(x_9);
x_36 = lean_int_sub(x_4, x_35);
lean_dec(x_35);
lean_dec(x_4);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = l_MOC_referenceNonminorFacetTwice___lambda__1___closed__1;
x_38 = lean_int_sub(x_9, x_37);
lean_dec(x_9);
x_39 = lean_int_sub(x_4, x_38);
lean_dec(x_38);
lean_dec(x_4);
return x_39;
}
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_26);
lean_dec(x_7);
x_40 = l_MOC_referenceNonminorFacetTwice___lambda__1___closed__1;
x_41 = lean_int_sub(x_9, x_40);
lean_dec(x_9);
x_42 = lean_int_sub(x_4, x_41);
lean_dec(x_41);
lean_dec(x_4);
return x_42;
}
}
}
block_55:
{
lean_object* x_45; uint8_t x_46; 
lean_dec(x_44);
x_45 = lean_unsigned_to_nat(1u);
x_46 = lean_nat_dec_eq(x_7, x_45);
if (x_46 == 0)
{
lean_object* x_47; 
x_47 = lean_box(0);
x_10 = x_47;
goto block_43;
}
else
{
lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_48 = lean_unsigned_to_nat(2u);
lean_inc(x_5);
x_49 = lean_apply_1(x_5, x_48);
x_50 = lean_nat_dec_eq(x_49, x_6);
lean_dec(x_49);
if (x_50 == 0)
{
lean_object* x_51; 
x_51 = lean_box(0);
x_10 = x_51;
goto block_43;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
lean_dec(x_7);
lean_dec(x_5);
x_52 = l_MOC_referenceNonminorFacetTwice___lambda__1___closed__1;
x_53 = lean_int_sub(x_9, x_52);
lean_dec(x_9);
x_54 = lean_int_sub(x_4, x_53);
lean_dec(x_53);
lean_dec(x_4);
return x_54;
}
}
}
}
block_85:
{
lean_object* x_67; uint8_t x_68; 
lean_dec(x_66);
x_67 = lean_unsigned_to_nat(1u);
x_68 = lean_nat_dec_eq(x_7, x_67);
if (x_68 == 0)
{
lean_object* x_69; uint8_t x_70; 
x_69 = lean_unsigned_to_nat(3u);
x_70 = lean_nat_dec_eq(x_7, x_69);
if (x_70 == 0)
{
lean_object* x_71; 
x_71 = l_Multiset_sum___at_MOC_referenceNonminorFacetTwice___spec__2___closed__1;
x_9 = x_71;
goto block_65;
}
else
{
lean_object* x_72; uint8_t x_73; 
lean_inc(x_5);
x_72 = lean_apply_1(x_5, x_67);
x_73 = lean_nat_dec_eq(x_72, x_67);
lean_dec(x_72);
if (x_73 == 0)
{
lean_object* x_74; 
x_74 = l_Multiset_sum___at_MOC_referenceNonminorFacetTwice___spec__2___closed__1;
x_9 = x_74;
goto block_65;
}
else
{
lean_object* x_75; 
x_75 = l_MOC_referenceNonminorFacetTwice___lambda__1___closed__1;
x_9 = x_75;
goto block_65;
}
}
}
else
{
lean_object* x_76; lean_object* x_77; uint8_t x_78; 
lean_inc(x_5);
x_76 = lean_apply_1(x_5, x_67);
x_77 = lean_unsigned_to_nat(3u);
x_78 = lean_nat_dec_eq(x_76, x_77);
if (x_78 == 0)
{
uint8_t x_79; 
x_79 = lean_nat_dec_eq(x_7, x_77);
if (x_79 == 0)
{
lean_object* x_80; 
lean_dec(x_76);
x_80 = l_Multiset_sum___at_MOC_referenceNonminorFacetTwice___spec__2___closed__1;
x_9 = x_80;
goto block_65;
}
else
{
uint8_t x_81; 
x_81 = lean_nat_dec_eq(x_76, x_67);
lean_dec(x_76);
if (x_81 == 0)
{
lean_object* x_82; 
x_82 = l_Multiset_sum___at_MOC_referenceNonminorFacetTwice___spec__2___closed__1;
x_9 = x_82;
goto block_65;
}
else
{
lean_object* x_83; 
x_83 = l_MOC_referenceNonminorFacetTwice___lambda__1___closed__1;
x_9 = x_83;
goto block_65;
}
}
}
else
{
lean_object* x_84; 
lean_dec(x_76);
x_84 = l_MOC_referenceNonminorFacetTwice___lambda__1___closed__1;
x_9 = x_84;
goto block_65;
}
}
}
block_95:
{
lean_object* x_87; uint8_t x_88; 
lean_dec(x_86);
x_87 = lean_unsigned_to_nat(2u);
x_88 = lean_nat_dec_eq(x_7, x_87);
if (x_88 == 0)
{
lean_object* x_89; 
x_89 = lean_box(0);
x_66 = x_89;
goto block_85;
}
else
{
lean_object* x_90; lean_object* x_91; uint8_t x_92; 
x_90 = lean_unsigned_to_nat(1u);
lean_inc(x_5);
x_91 = lean_apply_1(x_5, x_90);
x_92 = lean_nat_dec_eq(x_91, x_6);
lean_dec(x_91);
if (x_92 == 0)
{
lean_object* x_93; 
x_93 = lean_box(0);
x_66 = x_93;
goto block_85;
}
else
{
lean_object* x_94; 
x_94 = l_MOC_referenceNonminorFacetTwice___lambda__1___closed__1;
x_9 = x_94;
goto block_65;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_MOC_ContactCensus_0__MOC_mixedPermutationCostInt(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
lean_dec(x_1);
x_3 = lean_unsigned_to_nat(1u);
lean_inc(x_2);
x_4 = lean_apply_1(x_2, x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_4, x_5);
x_7 = lean_unsigned_to_nat(3u);
lean_inc(x_2);
x_8 = lean_apply_1(x_2, x_7);
x_9 = lean_unsigned_to_nat(2u);
x_10 = lean_nat_dec_eq(x_8, x_9);
x_11 = lean_apply_1(x_2, x_9);
x_12 = lean_nat_dec_eq(x_11, x_5);
if (x_6 == 0)
{
lean_object* x_52; 
x_52 = l_Multiset_sum___at_MOC_referenceNonminorFacetTwice___spec__2___closed__1;
x_13 = x_52;
goto block_51;
}
else
{
lean_object* x_53; 
x_53 = l_MOC_referenceNonminorFacetTwice___lambda__1___closed__1;
x_13 = x_53;
goto block_51;
}
block_51:
{
lean_object* x_14; 
if (x_10 == 0)
{
lean_object* x_49; 
x_49 = l_Multiset_sum___at_MOC_referenceNonminorFacetTwice___spec__2___closed__1;
x_14 = x_49;
goto block_48;
}
else
{
lean_object* x_50; 
x_50 = l_MOC_referenceNonminorFacetTwice___lambda__1___closed__1;
x_14 = x_50;
goto block_48;
}
block_48:
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_int_add(x_13, x_14);
lean_dec(x_14);
lean_dec(x_13);
if (x_12 == 0)
{
uint8_t x_36; 
x_36 = lean_nat_dec_eq(x_11, x_7);
if (x_36 == 0)
{
lean_object* x_37; 
lean_dec(x_8);
x_37 = l_Multiset_sum___at_MOC_referenceNonminorFacetTwice___spec__2___closed__1;
x_16 = x_37;
goto block_35;
}
else
{
uint8_t x_38; 
x_38 = lean_nat_dec_eq(x_8, x_5);
lean_dec(x_8);
if (x_38 == 0)
{
lean_object* x_39; 
x_39 = l_Multiset_sum___at_MOC_referenceNonminorFacetTwice___spec__2___closed__1;
x_16 = x_39;
goto block_35;
}
else
{
lean_object* x_40; 
x_40 = l_MOC_referenceNonminorFacetTwice___lambda__1___closed__1;
x_16 = x_40;
goto block_35;
}
}
}
else
{
uint8_t x_41; 
x_41 = lean_nat_dec_eq(x_8, x_7);
if (x_41 == 0)
{
uint8_t x_42; 
x_42 = lean_nat_dec_eq(x_11, x_7);
if (x_42 == 0)
{
lean_object* x_43; 
lean_dec(x_8);
x_43 = l_Multiset_sum___at_MOC_referenceNonminorFacetTwice___spec__2___closed__1;
x_16 = x_43;
goto block_35;
}
else
{
uint8_t x_44; 
x_44 = lean_nat_dec_eq(x_8, x_5);
lean_dec(x_8);
if (x_44 == 0)
{
lean_object* x_45; 
x_45 = l_Multiset_sum___at_MOC_referenceNonminorFacetTwice___spec__2___closed__1;
x_16 = x_45;
goto block_35;
}
else
{
lean_object* x_46; 
x_46 = l_MOC_referenceNonminorFacetTwice___lambda__1___closed__1;
x_16 = x_46;
goto block_35;
}
}
}
else
{
lean_object* x_47; 
lean_dec(x_8);
x_47 = l_MOC_referenceNonminorFacetTwice___lambda__1___closed__1;
x_16 = x_47;
goto block_35;
}
}
block_35:
{
lean_object* x_17; 
x_17 = lean_int_add(x_15, x_16);
lean_dec(x_16);
lean_dec(x_15);
if (x_6 == 0)
{
uint8_t x_18; 
lean_dec(x_11);
x_18 = lean_nat_dec_eq(x_4, x_3);
lean_dec(x_4);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = l_Multiset_sum___at_MOC_referenceNonminorFacetTwice___spec__2___closed__1;
x_20 = lean_int_sub(x_17, x_19);
lean_dec(x_17);
return x_20;
}
else
{
if (x_12 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = l_Multiset_sum___at_MOC_referenceNonminorFacetTwice___spec__2___closed__1;
x_22 = lean_int_sub(x_17, x_21);
lean_dec(x_17);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = l_MOC_referenceNonminorFacetTwice___lambda__1___closed__1;
x_24 = lean_int_sub(x_17, x_23);
lean_dec(x_17);
return x_24;
}
}
}
else
{
uint8_t x_25; 
x_25 = lean_nat_dec_eq(x_11, x_3);
lean_dec(x_11);
if (x_25 == 0)
{
uint8_t x_26; 
x_26 = lean_nat_dec_eq(x_4, x_3);
lean_dec(x_4);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = l_Multiset_sum___at_MOC_referenceNonminorFacetTwice___spec__2___closed__1;
x_28 = lean_int_sub(x_17, x_27);
lean_dec(x_17);
return x_28;
}
else
{
if (x_12 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = l_Multiset_sum___at_MOC_referenceNonminorFacetTwice___spec__2___closed__1;
x_30 = lean_int_sub(x_17, x_29);
lean_dec(x_17);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = l_MOC_referenceNonminorFacetTwice___lambda__1___closed__1;
x_32 = lean_int_sub(x_17, x_31);
lean_dec(x_17);
return x_32;
}
}
}
else
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_4);
x_33 = l_MOC_referenceNonminorFacetTwice___lambda__1___closed__1;
x_34 = lean_int_sub(x_17, x_33);
lean_dec(x_17);
return x_34;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_List_elem___at_MOC_referenceNonminorFacetZeroIndices___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_nat_dec_eq(x_1, x_4);
if (x_6 == 0)
{
x_2 = x_5;
goto _start;
}
else
{
uint8_t x_8; 
x_8 = 1;
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_Multiset_ndinsert___at_MOC_referenceNonminorFacetZeroIndices___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_List_elem___at_MOC_referenceNonminorFacetZeroIndices___spec__2(x_1, x_2);
if (x_3 == 0)
{
lean_object* x_4; 
x_4 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
else
{
lean_dec(x_1);
return x_2;
}
}
}
static lean_object* _init_l_MOC_referenceNonminorFacetZeroIndices___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_unsigned_to_nat(23u);
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_MOC_referenceNonminorFacetZeroIndices() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_1 = lean_unsigned_to_nat(22u);
x_2 = l_MOC_referenceNonminorFacetZeroIndices___closed__1;
x_3 = l_Multiset_ndinsert___at_MOC_referenceNonminorFacetZeroIndices___spec__1(x_1, x_2);
x_4 = lean_unsigned_to_nat(20u);
x_5 = l_Multiset_ndinsert___at_MOC_referenceNonminorFacetZeroIndices___spec__1(x_4, x_3);
x_6 = lean_unsigned_to_nat(18u);
x_7 = l_Multiset_ndinsert___at_MOC_referenceNonminorFacetZeroIndices___spec__1(x_6, x_5);
x_8 = lean_unsigned_to_nat(17u);
x_9 = l_Multiset_ndinsert___at_MOC_referenceNonminorFacetZeroIndices___spec__1(x_8, x_7);
x_10 = lean_unsigned_to_nat(16u);
x_11 = l_Multiset_ndinsert___at_MOC_referenceNonminorFacetZeroIndices___spec__1(x_10, x_9);
x_12 = lean_unsigned_to_nat(13u);
x_13 = l_Multiset_ndinsert___at_MOC_referenceNonminorFacetZeroIndices___spec__1(x_12, x_11);
x_14 = lean_unsigned_to_nat(12u);
x_15 = l_Multiset_ndinsert___at_MOC_referenceNonminorFacetZeroIndices___spec__1(x_14, x_13);
x_16 = lean_unsigned_to_nat(11u);
x_17 = l_Multiset_ndinsert___at_MOC_referenceNonminorFacetZeroIndices___spec__1(x_16, x_15);
x_18 = lean_unsigned_to_nat(10u);
x_19 = l_Multiset_ndinsert___at_MOC_referenceNonminorFacetZeroIndices___spec__1(x_18, x_17);
x_20 = lean_unsigned_to_nat(9u);
x_21 = l_Multiset_ndinsert___at_MOC_referenceNonminorFacetZeroIndices___spec__1(x_20, x_19);
x_22 = lean_unsigned_to_nat(7u);
x_23 = l_Multiset_ndinsert___at_MOC_referenceNonminorFacetZeroIndices___spec__1(x_22, x_21);
x_24 = lean_unsigned_to_nat(3u);
x_25 = l_Multiset_ndinsert___at_MOC_referenceNonminorFacetZeroIndices___spec__1(x_24, x_23);
return x_25;
}
}
LEAN_EXPORT lean_object* l_List_elem___at_MOC_referenceNonminorFacetZeroIndices___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_List_elem___at_MOC_referenceNonminorFacetZeroIndices___spec__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_MOC_Obstruction(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Data_Fintype_Perm(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_MOC_ContactCensus(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_MOC_Obstruction(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Data_Fintype_Perm(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Equiv_swap___at_MOC_fourPerm___spec__1___closed__1 = _init_l_Equiv_swap___at_MOC_fourPerm___spec__1___closed__1();
lean_mark_persistent(l_Equiv_swap___at_MOC_fourPerm___spec__1___closed__1);
l_MOC_fourPerm___closed__1 = _init_l_MOC_fourPerm___closed__1();
lean_mark_persistent(l_MOC_fourPerm___closed__1);
l_MOC_fourPerm___closed__2 = _init_l_MOC_fourPerm___closed__2();
lean_mark_persistent(l_MOC_fourPerm___closed__2);
l_MOC_fourPermEquiv___closed__1 = _init_l_MOC_fourPermEquiv___closed__1();
lean_mark_persistent(l_MOC_fourPermEquiv___closed__1);
l_MOC_fourPermEquiv___closed__2 = _init_l_MOC_fourPermEquiv___closed__2();
lean_mark_persistent(l_MOC_fourPermEquiv___closed__2);
l_MOC_fourPermEquiv___closed__3 = _init_l_MOC_fourPermEquiv___closed__3();
lean_mark_persistent(l_MOC_fourPermEquiv___closed__3);
l_MOC_fourPermEquiv = _init_l_MOC_fourPermEquiv();
lean_mark_persistent(l_MOC_fourPermEquiv);
l_Multiset_sum___at_MOC_referenceNonminorFacetTwice___spec__2___closed__1 = _init_l_Multiset_sum___at_MOC_referenceNonminorFacetTwice___spec__2___closed__1();
lean_mark_persistent(l_Multiset_sum___at_MOC_referenceNonminorFacetTwice___spec__2___closed__1);
l_Multiset_sum___at_MOC_referenceNonminorFacetTwice___spec__2___closed__2 = _init_l_Multiset_sum___at_MOC_referenceNonminorFacetTwice___spec__2___closed__2();
lean_mark_persistent(l_Multiset_sum___at_MOC_referenceNonminorFacetTwice___spec__2___closed__2);
l_MOC_referenceNonminorFacetTwice___lambda__1___closed__1 = _init_l_MOC_referenceNonminorFacetTwice___lambda__1___closed__1();
lean_mark_persistent(l_MOC_referenceNonminorFacetTwice___lambda__1___closed__1);
l_MOC_referenceNonminorFacetTwice___closed__1 = _init_l_MOC_referenceNonminorFacetTwice___closed__1();
lean_mark_persistent(l_MOC_referenceNonminorFacetTwice___closed__1);
l_MOC_referenceNonminorFacetTwice___closed__2 = _init_l_MOC_referenceNonminorFacetTwice___closed__2();
lean_mark_persistent(l_MOC_referenceNonminorFacetTwice___closed__2);
l_MOC_referenceNonminorFacetZeroIndices___closed__1 = _init_l_MOC_referenceNonminorFacetZeroIndices___closed__1();
lean_mark_persistent(l_MOC_referenceNonminorFacetZeroIndices___closed__1);
l_MOC_referenceNonminorFacetZeroIndices = _init_l_MOC_referenceNonminorFacetZeroIndices();
lean_mark_persistent(l_MOC_referenceNonminorFacetZeroIndices);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
