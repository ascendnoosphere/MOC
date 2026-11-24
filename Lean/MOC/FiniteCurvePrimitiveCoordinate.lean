import MOC.FiniteCurveAffineConnected
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.RingTheory.Localization.Integral

/-! A primitive coordinate for a finite characteristic-zero domain extension. -/

open scoped nonZeroDivisors

namespace MOC

section Primitive

variable (A B : Type*) [CommRing A] [IsDomain A] [CharZero A]
  [CommRing B] [IsDomain B] [Algebra A B] [FaithfulSMul A B] [Module.Finite A B]

/-- A finite domain extension in characteristic zero has a single element
that recovers every ring element using polynomial expressions with
denominators in the base ring. -/
theorem exists_primitive_element_with_base_denominators :
    ∃ v : B, ∀ b : B, ∃ d : A, d ≠ 0 ∧ ∃ P : Polynomial A,
      algebraMap A B d * b = P.eval₂ (algebraMap A B) v := by
  classical
  let K := FractionRing A
  let L := FractionRing B
  letI : Algebra K L := FractionRing.liftAlgebra A L
  letI : IsScalarTower A K L := FractionRing.isScalarTower_liftAlgebra A L
  have hBL := IsFractionRing.injective B L
  have hAL := FaithfulSMul.algebraMap_injective A L
  have hrepr (x : L) : ∃ b : B, ∃ a : A, a ≠ 0 ∧
      algebraMap B L b = algebraMap A L a * x := by
    obtain ⟨b, c, hc, hbc⟩ := IsFractionRing.div_surjective (A := B) x
    let I : Ideal B := Ideal.span {c}
    have hI := Ideal.comap_ne_bot_of_algebraic_mem (mem_nonZeroDivisors_iff_ne_zero.mp hc)
      (show c ∈ I from Ideal.mem_span_singleton_self _) (Algebra.IsAlgebraic.isAlgebraic (R := A) c)
    obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
    obtain ⟨q, hq⟩ := Ideal.mem_span_singleton.mp (show algebraMap A B a ∈ I from ha)
    refine ⟨q * b, a, ha0, ?_⟩
    have hcn : algebraMap B L c ≠ 0 := by simpa only [map_zero] using hBL.ne (mem_nonZeroDivisors_iff_ne_zero.mp hc)
    have hq' : algebraMap A L a = algebraMap B L c * algebraMap B L q := by
      rw [IsScalarTower.algebraMap_apply A B L, hq, map_mul]
    rw [map_mul, hq', ← hbc]
    field_simp
    ring
  have hfinite : Module.Finite K L := by
    obtain ⟨s, hs⟩ := (inferInstance : Module.Finite A B)
    let j : B →ₗ[A] L := (IsScalarTower.toAlgHom A B L).toLinearMap
    refine ⟨s.image (algebraMap B L), eq_top_iff.mpr (fun x _ => ?_)⟩
    set V := Submodule.span K (↑(s.image (algebraMap B L)) : Set L)
    have hspan : Submodule.span A (↑s : Set B) ≤ (V.restrictScalars A).comap j := by
      apply Submodule.span_le.mpr
      intro y hy
      exact Submodule.subset_span (Finset.mem_image.mpr ⟨y, hy, rfl⟩)
    obtain ⟨b, a, ha, hab⟩ := hrepr x
    have hb : algebraMap B L b ∈ V := hspan (hs ▸ Submodule.mem_top)
    have hsmul := V.smul_mem (algebraMap A K a)⁻¹ hb
    have hn : algebraMap A L a ≠ 0 := by simpa only [map_zero] using hAL.ne ha
    simpa only [hab, Algebra.smul_def, map_inv₀, ← IsScalarTower.algebraMap_apply,
      ← mul_assoc, inv_mul_cancel₀ hn, one_mul] using hsmul
  letI : Module.Finite K L := hfinite
  letI : CharZero K := inferInstanceAs (CharZero (FractionRing A))
  obtain ⟨α, hα⟩ := Field.exists_primitive_element K L
  obtain ⟨v, a, ha, hv⟩ := hrepr α
  let β := algebraMap B L v
  have hαspan : Algebra.adjoin K ({α} : Set L) = ⊤ := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_integral (IsIntegral.of_finite K α), hα]
    rfl
  have hαβ : α ∈ Algebra.adjoin K ({β} : Set L) := by
    have hb : β ∈ Algebra.adjoin K ({β} : Set L) := Algebra.subset_adjoin (Set.mem_singleton β)
    have hs := (Algebra.adjoin K ({β} : Set L)).smul_mem hb (algebraMap A K a)⁻¹
    change β = _ at hv
    have hn : algebraMap A L a ≠ 0 := by simpa only [map_zero] using hAL.ne ha
    simpa only [hv, Algebra.smul_def, map_inv₀, ← IsScalarTower.algebraMap_apply,
      ← mul_assoc, inv_mul_cancel₀ hn, one_mul] using hs
  have hβspan : Algebra.adjoin K ({β} : Set L) = ⊤ :=
    top_le_iff.mp (hαspan ▸ (Algebra.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr hαβ)))
  refine ⟨v, fun b => ?_⟩
  have hb : algebraMap B L b ∈ Algebra.adjoin K ({β} : Set L) := hβspan ▸ Algebra.mem_top
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hb
  obtain ⟨p, hp⟩ := hb
  obtain ⟨d, hd⟩ := IsLocalization.integerNormalization_map_to_map A⁰ p
  let P : Polynomial A := IsLocalization.integerNormalization A⁰ p
  refine ⟨d, mem_nonZeroDivisors_iff_ne_zero.mp d.property, P, hBL ?_⟩
  change Polynomial.aeval β p = algebraMap B L b at hp
  rw [← algebraMap_smul K (d : A) p, Polynomial.smul_eq_C_mul] at hd
  have h := congrArg (Polynomial.aeval β : Polynomial K → L) hd
  rw [Polynomial.aeval_map_algebraMap, map_mul, Polynomial.aeval_C, hp,
    ← IsScalarTower.algebraMap_apply A K L] at h
  rw [map_mul]
  change algebraMap B L (algebraMap A B d) * algebraMap B L b =
    algebraMap B L (P.eval₂ (algebraMap A B) v)
  rw [← IsScalarTower.algebraMap_apply A B L, Polynomial.hom_eval₂,
    ← IsScalarTower.algebraMap_eq A B L]
  simpa only [Polynomial.aeval_def, smul_eq_mul, Algebra.smul_def] using h.symm

end Primitive

/-- The complex points of a prime affine curve with a finite injective
projection to the affine line form a connected topological space. No
plane-coordinate or regularity premise is needed. -/
theorem connectedSpace_prime_finite_affine_curve
    {σ : Type*} [Fintype σ]
    (Q : Ideal (MvPolynomial σ ℂ)) [Q.IsPrime]
    (f : Polynomial ℂ →ₐ[ℂ] (MvPolynomial σ ℂ ⧸ Q)) (hf : f.Finite)
    (hfi : Function.Injective f)
    (t : MvPolynomial σ ℂ) (ht : Ideal.Quotient.mk Q t = f Polynomial.X) :
    ConnectedSpace (MvPolynomial.zeroLocus Q) := by
  let A := Polynomial ℂ
  let B := MvPolynomial σ ℂ ⧸ Q
  letI : Algebra A B := f.toRingHom.toAlgebra
  letI : Module.Finite A B := hf
  letI : FaithfulSMul A B := (faithfulSMul_iff_algebraMap_injective A B).mpr hfi
  obtain ⟨v, hv⟩ := exists_primitive_element_with_base_denominators A B
  obtain ⟨u, rfl⟩ := Ideal.Quotient.mk_surjective v
  exact connectedSpace_affine_of_coordinate_recovery Q f hf hfi t u ht
    (fun i => hv (Ideal.Quotient.mk Q (MvPolynomial.X i)))

end MOC
