import MOC.PolynomialCoefficientClearing
import Mathlib.Algebra.GCDMonoid.IntegrallyClosed
import Mathlib.Data.Complex.Basic
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.Nullstellensatz

/-! An integral primitive element for the function field of an affine curve.
The other coordinates can be recovered by polynomial quotients in two variables. -/

open BigOperators Polynomial Set
open scoped nonZeroDivisors

namespace MOC

private theorem exists_base_multiple_of_nonzero {R B : Type*} [CommRing R]
    [CommRing B] [IsDomain B] [Algebra R B] [Algebra.IsAlgebraic R B]
    (v : B) (hv : v ≠ 0) : ∃ d : R, d ≠ 0 ∧ ∃ b : B, algebraMap R B d = v * b := by
  let I : Ideal B := Ideal.span {v}
  have hvI : v ∈ I := Ideal.subset_span (mem_singleton v)
  have h := Ideal.comap_ne_bot_of_algebraic_mem hv hvI
    (Algebra.IsAlgebraic.isAlgebraic (R := R) v)
  obtain ⟨d, hd, hd0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp (show algebraMap R B d ∈ I from hd)
  exact ⟨d, hd0, b, hb⟩

private theorem finiteDimensional_fractionRing_of_quotient {σ : Type*} [Fintype σ]
    (Q : Ideal (MvPolynomial σ ℂ)) [Q.IsPrime] {F : Type*} [Field F]
    [Algebra F (FractionRing (MvPolynomial σ ℂ ⧸ Q))]
    [Algebra.IsAlgebraic F (FractionRing (MvPolynomial σ ℂ ⧸ Q))]
    (hc : ∀ c : ℂ, algebraMap (MvPolynomial σ ℂ ⧸ Q) _
      (Ideal.Quotient.mk Q (MvPolynomial.C c)) ∈ Set.range
        (algebraMap F (FractionRing (MvPolynomial σ ℂ ⧸ Q)))) :
    FiniteDimensional F (FractionRing (MvPolynomial σ ℂ ⧸ Q)) := by
  let B := MvPolynomial σ ℂ ⧸ Q
  let E := FractionRing B
  let f (i : σ) : E := algebraMap B E (Ideal.Quotient.mk Q (MvPolynomial.X i))
  let S := IntermediateField.adjoin F (Set.range f)
  letI : Finite ↥(Set.range f) := Set.finite_range f |>.to_subtype
  have hS : FiniteDimensional F S := IntermediateField.finiteDimensional_adjoin
    fun u _ => (Algebra.IsAlgebraic.isAlgebraic (R := F) u).isIntegral
  have hmem (b : B) : algebraMap B E b ∈ S := by
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective b
    apply MvPolynomial.induction_on p
    · intro c
      obtain ⟨d, hd⟩ := hc c
      exact hd ▸ S.algebraMap_mem d
    · intro p q hp hq
      simpa only [map_add] using S.add_mem hp hq
    · intro p i hp
      have hi : f i ∈ S := IntermediateField.subset_adjoin F _ (mem_range_self i)
      simpa only [map_mul] using S.mul_mem hp hi
  have ht : S = ⊤ := by
    apply top_unique
    intro u _
    obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective (A := B) u
    exact S.div_mem (hmem a) (hmem b)
  letI : FiniteDimensional F (⊤ : IntermediateField F E) := ht ▸ hS
  exact FiniteDimensional.of_injective
    (IntermediateField.topEquiv (F := F) (E := E)).symm.toLinearMap
    (IntermediateField.topEquiv (F := F) (E := E)).symm.injective

/-- Reconstruct each affine coordinate from an integral primitive element and
the base parameter. The denominators depend on the base parameter alone. -/
theorem exists_integral_primitive_curve_coordinates {σ : Type*} [Fintype σ]
    (Q : Ideal (MvPolynomial σ ℂ)) [Q.IsPrime]
    (g : ℂ[X] →ₐ[ℂ] MvPolynomial σ ℂ ⧸ Q) (hgi : Function.Injective g)
    (hg : letI := g.toRingHom.toAlgebra; Algebra.IsAlgebraic ℂ[X] (MvPolynomial σ ℂ ⧸ Q)) :
    letI := g.toRingHom.toAlgebra
    ∃ y : MvPolynomial σ ℂ ⧸ Q, IsIntegral ℂ[X] y ∧
      ((minpoly ℂ[X] y).map (algebraMap ℂ[X] (FractionRing ℂ[X]))).Separable ∧
      ∃ (d : ℂ[X]) (N : σ → Polynomial ℂ[X]), d ≠ 0 ∧
        ∀ i, g d * Ideal.Quotient.mk Q (MvPolynomial.X i) = Polynomial.aeval y (N i) := by
  classical
  let R := ℂ[X]
  let B := MvPolynomial σ ℂ ⧸ Q
  let F := FractionRing R
  let E := FractionRing B
  let j := algebraMap B E
  have hj : Function.Injective j := IsFractionRing.injective B E
  letI : Algebra R B := g.toRingHom.toAlgebra
  letI : Algebra.IsAlgebraic R B := hg
  letI : Algebra R E := (j.comp g.toRingHom).toAlgebra
  letI : SMul B E := (inferInstance : Algebra B E).toSMul
  letI : SMul R E := (inferInstance : Algebra R E).toSMul
  letI : IsScalarTower R B E := IsScalarTower.of_algebraMap_eq fun _ => rfl
  letI : FaithfulSMul R E := (faithfulSMul_iff_algebraMap_injective _ _).mpr (hj.comp hgi)
  letI : NoZeroSMulDivisors R E := NoZeroSMulDivisors.iff_faithfulSMul.mpr inferInstance
  letI : Algebra F E := FractionRing.liftAlgebra R E
  letI : SMul R F := (inferInstance : Algebra R F).toSMul
  letI : SMul F E := (inferInstance : Algebra F E).toSMul
  letI : IsScalarTower R F E := FractionRing.isScalarTower_liftAlgebra _ _
  have hE := (IsFractionRing.isAlgebraic_iff' R B E).mp hg
  letI : Algebra.IsAlgebraic F E := ⟨fun u =>
    (IsFractionRing.isAlgebraic_iff R F E).mp (hE.isAlgebraic u)⟩
  have hc (c : ℂ) : j (Ideal.Quotient.mk Q (MvPolynomial.C c)) ∈
      Set.range (algebraMap F E) := by
    refine ⟨algebraMap R F (Polynomial.C c), ?_⟩
    rw [← IsScalarTower.algebraMap_apply R F E]
    change j (g (Polynomial.C c)) = _
    exact congrArg j (g.commutes c)
  letI : FiniteDimensional F E := finiteDimensional_fractionRing_of_quotient Q hc
  letI : CharZero F := charZero_of_injective_algebraMap (IsFractionRing.injective R F)
  letI : Algebra.IsSeparable F E := Algebra.IsSeparable.of_integral _ _
  obtain ⟨a, ha⟩ := Field.exists_primitive_element F E
  have hai : IsIntegral F a := (Algebra.IsAlgebraic.isAlgebraic a).isIntegral
  obtain ⟨δ, hδ⟩ := IsIntegral.exists_multiple_integral_of_isLocalization (R := R)
    (Rₘ := F) R⁰ a hai
  obtain ⟨b, v, hv, hav⟩ := IsFractionRing.div_surjective (A := B) a
  have hv0 : v ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hv
  obtain ⟨e, he0, w, he⟩ := exists_base_multiple_of_nonzero (R := R) v hv0
  let y : B := g δ.val * w * b
  have hy : j y = algebraMap R E (δ.val * e) * a := by
    have hvj : j v ≠ 0 := (map_ne_zero_iff j hj).2 hv0
    calc
      j y = j (g δ.val) * j w * j b := by simp only [y, map_mul]
      _ = (j (g δ.val) * j w) * ((j b / j v) * j v) := by rw [div_mul_cancel₀ _ hvj]
      _ = (j (g δ.val) * (j v * j w)) * (j b / j v) := by
        ac_rfl
      _ = algebraMap R E (δ.val * e) * a := by
        rw [hav, ← map_mul j v w, ← he]
        change j (g δ.val) * j (g e) * a = j (g (δ.val * e)) * a
        simp only [map_mul]
  have hyi : IsIntegral R y := by
    apply (isIntegral_algebraMap_iff hj).mp
    change IsIntegral R (j y)
    rw [hy, map_mul]
    change IsIntegral R (algebraMap R E δ.val * algebraMap R E e * a)
    rw [mul_assoc, mul_left_comm (algebraMap R E δ.val) (algebraMap R E e), ← mul_assoc]
    have hδ' : IsIntegral R (algebraMap R E δ.val * a) := by
      simpa only [Submonoid.smul_def, Algebra.smul_def] using hδ
    simpa only [mul_assoc] using (isIntegral_algebraMap (R := R) (A := E) (x := e)).mul hδ'
  have hprim : IntermediateField.adjoin F {j y} = ⊤ := by
    rw [← ha]
    apply le_antisymm
    · apply IntermediateField.adjoin_simple_le_iff.mpr
      rw [hy, IsScalarTower.algebraMap_apply R F E]
      exact (IntermediateField.adjoin F {a}).mul_mem
        ((IntermediateField.adjoin F {a}).algebraMap_mem _)
        (IntermediateField.mem_adjoin_simple_self F a)
    · apply IntermediateField.adjoin_simple_le_iff.mpr
      have hd : algebraMap R E (δ.val * e) ≠ 0 :=
        (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective R E)).2
          (mul_ne_zero (mem_nonZeroDivisors_iff_ne_zero.mp δ.property) he0)
      have hrecover : a = (algebraMap R E (δ.val * e))⁻¹ * j y := by
        rw [hy, ← mul_assoc, inv_mul_cancel₀ hd, one_mul]
      rw [hrecover, IsScalarTower.algebraMap_apply R F E]
      exact (IntermediateField.adjoin F {j y}).mul_mem
        ((IntermediateField.adjoin F {j y}).inv_mem
          ((IntermediateField.adjoin F {j y}).algebraMap_mem _))
        (IntermediateField.mem_adjoin_simple_self F (j y))
  have hyFi : IsIntegral F (j y) := (Algebra.IsAlgebraic.isAlgebraic (j y)).isIntegral
  have hsep : ((minpoly R y).map (algebraMap R F)).Separable := by
    rw [← minpoly.isIntegrallyClosed_eq_field_fractions F E hyi]
    exact Algebra.IsSeparable.isSeparable F (j y)
  have hsurj : Function.Surjective (Polynomial.aeval (j y) : F[X] →ₐ[F] E) := by
    intro u
    have hu : u ∈ (⊤ : IntermediateField F E).toSubalgebra := by simp
    rw [← hprim, IntermediateField.adjoin_simple_toSubalgebra_of_integral hyFi,
      Algebra.adjoin_singleton_eq_range_aeval] at hu
    exact hu
  have hcoord (i : σ) : ∃ d : R, d ≠ 0 ∧ ∃ N : R[X],
      g d * Ideal.Quotient.mk Q (MvPolynomial.X i) = Polynomial.aeval y N := by
    obtain ⟨q, hq⟩ := hsurj (j (Ideal.Quotient.mk Q (MvPolynomial.X i)))
    obtain ⟨d, hd, N, hN⟩ := clear_polynomial_coefficients (R := R) q
    refine ⟨d, hd, N, hj ?_⟩
    have h : Polynomial.aeval (j y) (N.map (algebraMap R F)) =
        Polynomial.aeval (j y) (Polynomial.C (algebraMap R F d) * q) :=
      congrArg (Polynomial.aeval (j y)) hN
    rw [map_mul (Polynomial.aeval (j y)) (Polynomial.C (algebraMap R F d)) q,
      Polynomial.aeval_C, hq, Polynomial.aeval_map_algebraMap,
      Polynomial.aeval_algebraMap_apply, ← IsScalarTower.algebraMap_apply R F E] at h
    simpa only [map_mul] using h.symm
  choose d hd N hN using hcoord
  let D := ∏ i, d i
  have hD (i : σ) : d i ∣ D := Finset.dvd_prod_of_mem d (Finset.mem_univ i)
  choose e he using hD
  refine ⟨y, hyi, hsep, D, fun i => Polynomial.C (e i) * N i,
    Finset.prod_ne_zero_iff.mpr (fun i _ => hd i), fun i => ?_⟩
  calc
    g D * Ideal.Quotient.mk Q (MvPolynomial.X i) =
        g (e i) * (g (d i) * Ideal.Quotient.mk Q (MvPolynomial.X i)) := by
          rw [he i, map_mul]
          ac_rfl
    _ = Polynomial.aeval y (Polynomial.C (e i) * N i) := by
      rw [hN i, map_mul, Polynomial.aeval_C] <;> rfl

end MOC
