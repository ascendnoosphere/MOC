// Lean compiler output
// Module: MOC.FourContactCertificate
// Imports: Init Mathlib.Data.Fin.VecNotation Mathlib.Data.Real.Basic Mathlib.Tactic.FieldSimp Mathlib.Tactic.Ring
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
lean_object* l_CommRing_toNonUnitalCommRing___rarg(lean_object*);
extern lean_object* l___private_Mathlib_Data_Real_Basic_0__Real_zero;
lean_object* l_AddGroupWithOne_toAddGroup___rarg(lean_object*);
lean_object* l_Ring_toAddGroupWithOne___rarg(lean_object*);
lean_object* l_NonUnitalNonAssocSemiring_toDistrib___rarg(lean_object*);
lean_object* l_NonUnitalNonAssocCommRing_toNonUnitalNonAssocCommSemiring___rarg(lean_object*);
LEAN_EXPORT lean_object* l_MOC_t21CanonicalLift(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Matrix_vecEmpty___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MOC_fourMatchingCubic(lean_object*);
LEAN_EXPORT lean_object* l_MOC_t21CanonicalLift___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_SubNegZeroMonoid_toNegZeroClass___rarg(lean_object*);
lean_object* l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_579_(lean_object*);
static lean_object* l_MOC_t21CanonicalLift___closed__1;
lean_object* l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_664_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MOC_fourMatchingCubic___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MOC_t34RadialQ(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Fin_cases(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MOC_t34HeightLift___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_471_(lean_object*, lean_object*);
lean_object* l_Matrix_vecCons___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MOC_t34HeightLift(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Ring_toAddCommGroup___rarg(lean_object*);
LEAN_EXPORT lean_object* l_MOC_t34RadialC(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MOC_fourMatchingCubic___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
lean_inc(x_1);
x_3 = l_CommRing_toNonUnitalCommRing___rarg(x_1);
x_4 = l_NonUnitalNonAssocCommRing_toNonUnitalNonAssocCommSemiring___rarg(x_3);
x_5 = l_NonUnitalNonAssocSemiring_toDistrib___rarg(x_4);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
lean_inc(x_1);
x_7 = l_Ring_toAddGroupWithOne___rarg(x_1);
x_8 = l_AddGroupWithOne_toAddGroup___rarg(x_7);
lean_dec(x_7);
x_9 = lean_ctor_get(x_8, 2);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_ctor_get(x_4, 1);
lean_inc(x_10);
lean_dec(x_4);
x_11 = lean_unsigned_to_nat(13u);
lean_inc(x_2);
x_12 = lean_apply_1(x_2, x_11);
x_13 = lean_unsigned_to_nat(0u);
lean_inc(x_2);
x_14 = lean_apply_1(x_2, x_13);
x_15 = lean_unsigned_to_nat(6u);
lean_inc(x_2);
x_16 = lean_apply_1(x_2, x_15);
lean_inc(x_10);
lean_inc(x_16);
lean_inc(x_14);
x_17 = lean_apply_2(x_10, x_14, x_16);
x_18 = lean_unsigned_to_nat(1u);
lean_inc(x_2);
x_19 = lean_apply_1(x_2, x_18);
x_20 = lean_unsigned_to_nat(5u);
lean_inc(x_2);
x_21 = lean_apply_1(x_2, x_20);
lean_inc(x_10);
lean_inc(x_21);
lean_inc(x_19);
x_22 = lean_apply_2(x_10, x_19, x_21);
lean_inc(x_9);
lean_inc(x_22);
x_23 = lean_apply_2(x_9, x_17, x_22);
lean_inc(x_10);
x_24 = lean_apply_2(x_10, x_12, x_23);
x_25 = lean_unsigned_to_nat(9u);
lean_inc(x_2);
x_26 = lean_apply_1(x_2, x_25);
lean_inc(x_10);
lean_inc(x_26);
lean_inc(x_14);
x_27 = lean_apply_2(x_10, x_14, x_26);
lean_inc(x_6);
lean_inc(x_19);
lean_inc(x_14);
x_28 = lean_apply_2(x_6, x_14, x_19);
x_29 = lean_unsigned_to_nat(2u);
lean_inc(x_2);
x_30 = lean_apply_1(x_2, x_29);
lean_inc(x_6);
lean_inc(x_30);
x_31 = lean_apply_2(x_6, x_28, x_30);
x_32 = lean_unsigned_to_nat(3u);
lean_inc(x_2);
x_33 = lean_apply_1(x_2, x_32);
lean_inc(x_6);
lean_inc(x_33);
x_34 = lean_apply_2(x_6, x_31, x_33);
lean_inc(x_6);
lean_inc(x_21);
x_35 = lean_apply_2(x_6, x_34, x_21);
x_36 = lean_unsigned_to_nat(7u);
lean_inc(x_2);
x_37 = lean_apply_1(x_2, x_36);
lean_inc(x_6);
lean_inc(x_37);
x_38 = lean_apply_2(x_6, x_35, x_37);
lean_inc(x_6);
lean_inc(x_26);
x_39 = lean_apply_2(x_6, x_38, x_26);
lean_inc(x_10);
lean_inc(x_27);
x_40 = lean_apply_2(x_10, x_27, x_39);
lean_inc(x_9);
x_41 = lean_apply_2(x_9, x_24, x_40);
lean_inc(x_10);
lean_inc(x_26);
x_42 = lean_apply_2(x_10, x_22, x_26);
lean_inc(x_9);
x_43 = lean_apply_2(x_9, x_41, x_42);
x_44 = lean_unsigned_to_nat(10u);
lean_inc(x_2);
x_45 = lean_apply_1(x_2, x_44);
x_46 = l_Ring_toAddCommGroup___rarg(x_1);
lean_dec(x_1);
x_47 = l_SubNegZeroMonoid_toNegZeroClass___rarg(x_46);
lean_dec(x_46);
x_48 = lean_ctor_get(x_47, 1);
lean_inc(x_48);
lean_dec(x_47);
x_49 = lean_apply_1(x_48, x_14);
lean_inc(x_10);
lean_inc(x_33);
lean_inc(x_49);
x_50 = lean_apply_2(x_10, x_49, x_33);
lean_inc(x_9);
lean_inc(x_27);
x_51 = lean_apply_2(x_9, x_50, x_27);
lean_inc(x_10);
lean_inc(x_30);
lean_inc(x_19);
x_52 = lean_apply_2(x_10, x_19, x_30);
lean_inc(x_6);
x_53 = lean_apply_2(x_6, x_51, x_52);
lean_inc(x_10);
lean_inc(x_37);
x_54 = lean_apply_2(x_10, x_19, x_37);
lean_inc(x_6);
lean_inc(x_54);
x_55 = lean_apply_2(x_6, x_53, x_54);
lean_inc(x_10);
lean_inc(x_45);
x_56 = lean_apply_2(x_10, x_45, x_55);
lean_inc(x_6);
x_57 = lean_apply_2(x_6, x_43, x_56);
x_58 = lean_unsigned_to_nat(11u);
lean_inc(x_2);
x_59 = lean_apply_1(x_2, x_58);
lean_inc(x_10);
lean_inc(x_37);
lean_inc(x_49);
x_60 = lean_apply_2(x_10, x_49, x_37);
lean_inc(x_9);
x_61 = lean_apply_2(x_9, x_60, x_27);
lean_inc(x_10);
lean_inc(x_21);
lean_inc(x_30);
x_62 = lean_apply_2(x_10, x_30, x_21);
lean_inc(x_6);
x_63 = lean_apply_2(x_6, x_61, x_62);
lean_inc(x_10);
lean_inc(x_33);
x_64 = lean_apply_2(x_10, x_33, x_21);
lean_inc(x_6);
lean_inc(x_64);
x_65 = lean_apply_2(x_6, x_63, x_64);
lean_inc(x_10);
lean_inc(x_59);
x_66 = lean_apply_2(x_10, x_59, x_65);
lean_inc(x_6);
x_67 = lean_apply_2(x_6, x_57, x_66);
x_68 = lean_unsigned_to_nat(12u);
lean_inc(x_2);
x_69 = lean_apply_1(x_2, x_68);
lean_inc(x_10);
lean_inc(x_26);
x_70 = lean_apply_2(x_10, x_49, x_26);
lean_inc(x_6);
x_71 = lean_apply_2(x_6, x_70, x_54);
lean_inc(x_10);
lean_inc(x_30);
x_72 = lean_apply_2(x_10, x_30, x_16);
lean_inc(x_9);
x_73 = lean_apply_2(x_9, x_71, x_72);
lean_inc(x_10);
lean_inc(x_26);
lean_inc(x_30);
x_74 = lean_apply_2(x_10, x_30, x_26);
lean_inc(x_9);
x_75 = lean_apply_2(x_9, x_73, x_74);
lean_inc(x_6);
x_76 = lean_apply_2(x_6, x_75, x_64);
lean_inc(x_10);
lean_inc(x_37);
lean_inc(x_33);
x_77 = lean_apply_2(x_10, x_33, x_37);
lean_inc(x_6);
x_78 = lean_apply_2(x_6, x_76, x_77);
lean_inc(x_10);
x_79 = lean_apply_2(x_10, x_69, x_78);
lean_inc(x_6);
x_80 = lean_apply_2(x_6, x_67, x_79);
lean_inc(x_10);
lean_inc(x_45);
x_81 = lean_apply_2(x_10, x_30, x_45);
lean_inc(x_10);
lean_inc(x_59);
x_82 = lean_apply_2(x_10, x_81, x_59);
lean_inc(x_6);
x_83 = lean_apply_2(x_6, x_80, x_82);
x_84 = lean_unsigned_to_nat(8u);
lean_inc(x_2);
x_85 = lean_apply_1(x_2, x_84);
lean_inc(x_10);
lean_inc(x_85);
x_86 = lean_apply_2(x_10, x_33, x_85);
lean_inc(x_10);
x_87 = lean_apply_2(x_10, x_86, x_45);
lean_inc(x_9);
x_88 = lean_apply_2(x_9, x_83, x_87);
x_89 = lean_unsigned_to_nat(4u);
x_90 = lean_apply_1(x_2, x_89);
lean_inc(x_10);
lean_inc(x_90);
x_91 = lean_apply_2(x_10, x_90, x_37);
lean_inc(x_10);
x_92 = lean_apply_2(x_10, x_91, x_59);
x_93 = lean_apply_2(x_9, x_88, x_92);
lean_inc(x_10);
x_94 = lean_apply_2(x_10, x_90, x_85);
x_95 = lean_apply_2(x_10, x_94, x_26);
x_96 = lean_apply_2(x_6, x_93, x_95);
return x_96;
}
}
LEAN_EXPORT lean_object* l_MOC_fourMatchingCubic(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_MOC_fourMatchingCubic___rarg), 2, 0);
return x_2;
}
}
static lean_object* _init_l_MOC_t21CanonicalLift___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Matrix_vecEmpty___boxed), 2, 1);
lean_closure_set(x_1, 0, lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_MOC_t21CanonicalLift(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
lean_inc(x_4);
x_10 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_579_(x_4);
lean_inc(x_7);
x_11 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_579_(x_7);
lean_inc(x_11);
lean_inc(x_10);
x_12 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_471_(x_10, x_11);
lean_inc(x_6);
x_13 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_579_(x_6);
lean_inc(x_13);
x_14 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_471_(x_12, x_13);
lean_inc(x_4);
lean_inc(x_2);
x_15 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_471_(x_2, x_4);
lean_inc(x_7);
x_16 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_471_(x_15, x_7);
lean_inc(x_5);
x_17 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_471_(x_16, x_5);
lean_inc(x_6);
x_18 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_471_(x_17, x_6);
lean_inc(x_1);
x_19 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_579_(x_1);
lean_inc(x_6);
x_20 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_471_(x_6, x_19);
lean_inc(x_2);
x_21 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_579_(x_2);
lean_inc(x_11);
lean_inc(x_21);
x_22 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_471_(x_21, x_11);
lean_inc(x_22);
x_23 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_471_(x_22, x_13);
lean_inc(x_7);
x_24 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_471_(x_7, x_6);
x_25 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_579_(x_5);
x_26 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_471_(x_22, x_25);
lean_inc(x_8);
x_27 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_579_(x_8);
lean_inc(x_4);
x_28 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_471_(x_4, x_27);
lean_inc(x_7);
x_29 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_471_(x_2, x_7);
lean_inc(x_3);
x_30 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_579_(x_3);
x_31 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_471_(x_30, x_11);
x_32 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_471_(x_21, x_10);
x_33 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_471_(x_32, x_8);
x_34 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_471_(x_3, x_4);
x_35 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_471_(x_34, x_7);
x_36 = lean_unsigned_to_nat(0u);
x_37 = l_MOC_t21CanonicalLift___closed__1;
x_38 = lean_alloc_closure((void*)(l_Matrix_vecCons___rarg___boxed), 4, 3);
lean_closure_set(x_38, 0, x_36);
lean_closure_set(x_38, 1, x_1);
lean_closure_set(x_38, 2, x_37);
x_39 = lean_unsigned_to_nat(1u);
x_40 = lean_alloc_closure((void*)(l_Matrix_vecCons___rarg___boxed), 4, 3);
lean_closure_set(x_40, 0, x_39);
lean_closure_set(x_40, 1, x_35);
lean_closure_set(x_40, 2, x_38);
x_41 = lean_unsigned_to_nat(2u);
x_42 = lean_alloc_closure((void*)(l_Matrix_vecCons___rarg___boxed), 4, 3);
lean_closure_set(x_42, 0, x_41);
lean_closure_set(x_42, 1, x_33);
lean_closure_set(x_42, 2, x_40);
x_43 = lean_unsigned_to_nat(3u);
x_44 = lean_alloc_closure((void*)(l_Matrix_vecCons___rarg___boxed), 4, 3);
lean_closure_set(x_44, 0, x_43);
lean_closure_set(x_44, 1, x_31);
lean_closure_set(x_44, 2, x_42);
x_45 = lean_unsigned_to_nat(4u);
x_46 = lean_alloc_closure((void*)(l_Matrix_vecCons___rarg___boxed), 4, 3);
lean_closure_set(x_46, 0, x_45);
lean_closure_set(x_46, 1, x_29);
lean_closure_set(x_46, 2, x_44);
x_47 = lean_unsigned_to_nat(5u);
x_48 = lean_alloc_closure((void*)(l_Matrix_vecCons___rarg___boxed), 4, 3);
lean_closure_set(x_48, 0, x_47);
lean_closure_set(x_48, 1, x_28);
lean_closure_set(x_48, 2, x_46);
x_49 = lean_unsigned_to_nat(6u);
x_50 = l___private_Mathlib_Data_Real_Basic_0__Real_zero;
x_51 = lean_alloc_closure((void*)(l_Matrix_vecCons___rarg___boxed), 4, 3);
lean_closure_set(x_51, 0, x_49);
lean_closure_set(x_51, 1, x_50);
lean_closure_set(x_51, 2, x_48);
x_52 = lean_unsigned_to_nat(7u);
x_53 = lean_alloc_closure((void*)(l_Matrix_vecCons___rarg___boxed), 4, 3);
lean_closure_set(x_53, 0, x_52);
lean_closure_set(x_53, 1, x_26);
lean_closure_set(x_53, 2, x_51);
x_54 = lean_unsigned_to_nat(8u);
x_55 = lean_alloc_closure((void*)(l_Matrix_vecCons___rarg___boxed), 4, 3);
lean_closure_set(x_55, 0, x_54);
lean_closure_set(x_55, 1, x_50);
lean_closure_set(x_55, 2, x_53);
x_56 = lean_unsigned_to_nat(9u);
x_57 = lean_alloc_closure((void*)(l_Matrix_vecCons___rarg___boxed), 4, 3);
lean_closure_set(x_57, 0, x_56);
lean_closure_set(x_57, 1, x_24);
lean_closure_set(x_57, 2, x_55);
x_58 = lean_unsigned_to_nat(10u);
x_59 = lean_alloc_closure((void*)(l_Matrix_vecCons___rarg___boxed), 4, 3);
lean_closure_set(x_59, 0, x_58);
lean_closure_set(x_59, 1, x_23);
lean_closure_set(x_59, 2, x_57);
x_60 = lean_unsigned_to_nat(11u);
x_61 = lean_alloc_closure((void*)(l_Matrix_vecCons___rarg___boxed), 4, 3);
lean_closure_set(x_61, 0, x_60);
lean_closure_set(x_61, 1, x_20);
lean_closure_set(x_61, 2, x_59);
x_62 = lean_unsigned_to_nat(12u);
x_63 = lean_alloc_closure((void*)(l_Matrix_vecCons___rarg___boxed), 4, 3);
lean_closure_set(x_63, 0, x_62);
lean_closure_set(x_63, 1, x_18);
lean_closure_set(x_63, 2, x_61);
x_64 = lean_unsigned_to_nat(13u);
x_65 = l_Fin_cases(x_64, lean_box(0), x_14, x_63, x_9);
lean_dec(x_14);
return x_65;
}
}
LEAN_EXPORT lean_object* l_MOC_t21CanonicalLift___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_MOC_t21CanonicalLift(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_MOC_t34RadialQ(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_inc(x_4);
x_7 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_471_(x_4, x_5);
x_8 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_471_(x_7, x_6);
lean_inc(x_8);
x_9 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_579_(x_8);
x_10 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_471_(x_1, x_9);
x_11 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_471_(x_2, x_3);
x_12 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_664_(x_10, x_11);
x_13 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_664_(x_4, x_8);
x_14 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_579_(x_13);
x_15 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_471_(x_12, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_MOC_t34RadialC(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_inc(x_5);
lean_inc(x_4);
x_9 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_664_(x_4, x_5);
lean_inc(x_2);
lean_inc(x_7);
x_10 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_471_(x_7, x_2);
lean_inc(x_8);
lean_inc(x_10);
x_11 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_471_(x_10, x_8);
x_12 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_579_(x_11);
x_13 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_471_(x_3, x_12);
x_14 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_664_(x_9, x_13);
x_15 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_664_(x_4, x_10);
lean_inc(x_7);
x_16 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_471_(x_7, x_6);
lean_inc(x_8);
x_17 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_471_(x_16, x_8);
lean_inc(x_17);
x_18 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_664_(x_15, x_17);
x_19 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_579_(x_18);
x_20 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_471_(x_14, x_19);
lean_inc(x_7);
x_21 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_471_(x_7, x_8);
x_22 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_664_(x_5, x_21);
lean_inc(x_7);
x_23 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_471_(x_7, x_1);
x_24 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_471_(x_23, x_2);
lean_inc(x_24);
x_25 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_664_(x_22, x_24);
x_26 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_579_(x_25);
x_27 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_471_(x_20, x_26);
x_28 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_664_(x_7, x_24);
x_29 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_664_(x_28, x_17);
x_30 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_579_(x_29);
x_31 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_471_(x_27, x_30);
return x_31;
}
}
LEAN_EXPORT lean_object* l_MOC_t34HeightLift(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
lean_inc(x_4);
x_11 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_579_(x_4);
lean_inc(x_5);
x_12 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_579_(x_5);
lean_inc(x_12);
lean_inc(x_11);
x_13 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_471_(x_11, x_12);
lean_inc(x_7);
x_14 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_579_(x_7);
lean_inc(x_14);
x_15 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_471_(x_13, x_14);
lean_inc(x_4);
lean_inc(x_3);
x_16 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_471_(x_3, x_4);
lean_inc(x_5);
x_17 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_471_(x_16, x_5);
lean_inc(x_7);
x_18 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_471_(x_17, x_7);
lean_inc(x_1);
x_19 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_579_(x_1);
lean_inc(x_5);
x_20 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_471_(x_5, x_19);
lean_inc(x_3);
x_21 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_579_(x_3);
lean_inc(x_21);
x_22 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_471_(x_21, x_12);
lean_inc(x_14);
x_23 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_471_(x_22, x_14);
lean_inc(x_6);
x_24 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_579_(x_6);
lean_inc(x_24);
x_25 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_471_(x_23, x_24);
lean_inc(x_7);
x_26 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_471_(x_5, x_7);
lean_inc(x_6);
x_27 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_471_(x_26, x_6);
lean_inc(x_2);
lean_inc(x_21);
x_28 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_471_(x_21, x_2);
x_29 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_471_(x_28, x_8);
lean_inc(x_7);
lean_inc(x_4);
x_30 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_471_(x_4, x_7);
lean_inc(x_7);
x_31 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_471_(x_3, x_7);
x_32 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_471_(x_31, x_6);
lean_inc(x_2);
x_33 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_579_(x_2);
x_34 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_471_(x_32, x_33);
lean_inc(x_14);
x_35 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_471_(x_14, x_24);
x_36 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_471_(x_21, x_11);
lean_inc(x_14);
x_37 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_471_(x_36, x_14);
lean_inc(x_7);
x_38 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_471_(x_7, x_1);
x_39 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_471_(x_38, x_2);
x_40 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_471_(x_39, x_9);
x_41 = lean_unsigned_to_nat(0u);
x_42 = l_MOC_t21CanonicalLift___closed__1;
x_43 = lean_alloc_closure((void*)(l_Matrix_vecCons___rarg___boxed), 4, 3);
lean_closure_set(x_43, 0, x_41);
lean_closure_set(x_43, 1, x_40);
lean_closure_set(x_43, 2, x_42);
x_44 = lean_unsigned_to_nat(1u);
x_45 = lean_alloc_closure((void*)(l_Matrix_vecCons___rarg___boxed), 4, 3);
lean_closure_set(x_45, 0, x_44);
lean_closure_set(x_45, 1, x_4);
lean_closure_set(x_45, 2, x_43);
x_46 = lean_unsigned_to_nat(2u);
x_47 = lean_alloc_closure((void*)(l_Matrix_vecCons___rarg___boxed), 4, 3);
lean_closure_set(x_47, 0, x_46);
lean_closure_set(x_47, 1, x_37);
lean_closure_set(x_47, 2, x_45);
x_48 = lean_unsigned_to_nat(3u);
x_49 = lean_alloc_closure((void*)(l_Matrix_vecCons___rarg___boxed), 4, 3);
lean_closure_set(x_49, 0, x_48);
lean_closure_set(x_49, 1, x_35);
lean_closure_set(x_49, 2, x_47);
x_50 = lean_unsigned_to_nat(4u);
x_51 = lean_alloc_closure((void*)(l_Matrix_vecCons___rarg___boxed), 4, 3);
lean_closure_set(x_51, 0, x_50);
lean_closure_set(x_51, 1, x_34);
lean_closure_set(x_51, 2, x_49);
x_52 = lean_unsigned_to_nat(5u);
x_53 = lean_alloc_closure((void*)(l_Matrix_vecCons___rarg___boxed), 4, 3);
lean_closure_set(x_53, 0, x_52);
lean_closure_set(x_53, 1, x_30);
lean_closure_set(x_53, 2, x_51);
x_54 = lean_unsigned_to_nat(6u);
x_55 = lean_alloc_closure((void*)(l_Matrix_vecCons___rarg___boxed), 4, 3);
lean_closure_set(x_55, 0, x_54);
lean_closure_set(x_55, 1, x_14);
lean_closure_set(x_55, 2, x_53);
x_56 = lean_unsigned_to_nat(7u);
x_57 = lean_alloc_closure((void*)(l_Matrix_vecCons___rarg___boxed), 4, 3);
lean_closure_set(x_57, 0, x_56);
lean_closure_set(x_57, 1, x_29);
lean_closure_set(x_57, 2, x_55);
x_58 = lean_unsigned_to_nat(8u);
x_59 = lean_alloc_closure((void*)(l_Matrix_vecCons___rarg___boxed), 4, 3);
lean_closure_set(x_59, 0, x_58);
lean_closure_set(x_59, 1, x_7);
lean_closure_set(x_59, 2, x_57);
x_60 = lean_unsigned_to_nat(9u);
x_61 = lean_alloc_closure((void*)(l_Matrix_vecCons___rarg___boxed), 4, 3);
lean_closure_set(x_61, 0, x_60);
lean_closure_set(x_61, 1, x_27);
lean_closure_set(x_61, 2, x_59);
x_62 = lean_unsigned_to_nat(10u);
x_63 = lean_alloc_closure((void*)(l_Matrix_vecCons___rarg___boxed), 4, 3);
lean_closure_set(x_63, 0, x_62);
lean_closure_set(x_63, 1, x_25);
lean_closure_set(x_63, 2, x_61);
x_64 = lean_unsigned_to_nat(11u);
x_65 = lean_alloc_closure((void*)(l_Matrix_vecCons___rarg___boxed), 4, 3);
lean_closure_set(x_65, 0, x_64);
lean_closure_set(x_65, 1, x_20);
lean_closure_set(x_65, 2, x_63);
x_66 = lean_unsigned_to_nat(12u);
x_67 = lean_alloc_closure((void*)(l_Matrix_vecCons___rarg___boxed), 4, 3);
lean_closure_set(x_67, 0, x_66);
lean_closure_set(x_67, 1, x_18);
lean_closure_set(x_67, 2, x_65);
x_68 = lean_unsigned_to_nat(13u);
x_69 = l_Fin_cases(x_68, lean_box(0), x_15, x_67, x_10);
lean_dec(x_15);
return x_69;
}
}
LEAN_EXPORT lean_object* l_MOC_t34HeightLift___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_MOC_t34HeightLift(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_10);
return x_11;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Data_Fin_VecNotation(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Data_Real_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Tactic_FieldSimp(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Tactic_Ring(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_MOC_FourContactCertificate(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Data_Fin_VecNotation(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Data_Real_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Tactic_FieldSimp(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Tactic_Ring(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_MOC_t21CanonicalLift___closed__1 = _init_l_MOC_t21CanonicalLift___closed__1();
lean_mark_persistent(l_MOC_t21CanonicalLift___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
