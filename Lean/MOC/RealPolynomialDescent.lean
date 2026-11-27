import MOC.DeterminantPreorderingCertificate
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RingTheory.Algebraic.Integral

/-! Descent of polynomial solutions whose coordinates are algebraic over the reals. -/

open Polynomial

namespace MOC

noncomputable section

universe u

/-- The real numbers have no new algebraic elements in a semireal field extension. -/
theorem integral_over_real_mem_range {K : Type*} [Field K] [Algebra ℝ K] [IsSemireal K]
    {x : K} (hx : IsIntegral ℝ x) : x ∈ (algebraMap ℝ K).range := by
  let p := minpoly ℝ x
  have hp : Irreducible p := minpoly.irreducible hx
  obtain ⟨z, hz⟩ : ∃ z : ℂ, aeval z p = 0 :=
    IsAlgClosed.exists_aeval_eq_zero _ p (degree_pos_of_irreducible hp).ne'
  by_cases hzi : z.im = 0
  · have hreal : z = algebraMap ℝ ℂ z.re := Complex.ext rfl hzi
    rw [hreal, aeval_algebraMap_apply_eq_algebraMap_eval] at hz
    have hr : p.IsRoot z.re := (algebraMap ℝ ℂ).injective (hz.trans (map_zero _).symm)
    exact minpoly.degree_eq_one_iff.mp (degree_eq_one_of_irreducible_of_root hp hr)
  · let q := (X : ℝ[X]) ^ 2 - C (2 * z.re) * X + C (‖z‖ ^ 2)
    obtain ⟨r, hr⟩ : q ∣ p := p.quadratic_dvd_of_aeval_eq_zero_im_ne_zero hz hzi
    have hqdegree : q.degree = 2 := by
      dsimp only [q]
      compute_degree!
    have hqnu : ¬ IsUnit q := by
      intro hu
      exact two_ne_zero (hqdegree.symm.trans (isUnit_iff_degree_eq_zero.mp hu))
    have hpqr : Irreducible (q * r) := hr ▸ hp
    have hrunit : IsUnit r := (of_irreducible_mul hpqr).resolve_left hqnu
    have he : aeval x q * aeval x r = 0 := by
      rw [← map_mul, ← hr]
      exact minpoly.aeval ℝ x
    have hqzero : aeval x q = 0 :=
      (mul_eq_zero.mp he).resolve_right (hrunit.map (aeval x)).ne_zero
    have hnorm : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply, pow_two, pow_two]
    have hcompleted : q = (X - C z.re) ^ 2 + C (z.im ^ 2) := by
      simp only [q, hnorm, map_add, map_mul, map_pow, map_ofNat]
      ring
    rw [hcompleted, map_add, map_pow, map_sub, aeval_X, aeval_C, aeval_C, map_pow] at hqzero
    let a := x - algebraMap ℝ K z.re
    let b := algebraMap ℝ K z.im
    have hb : b ≠ 0 := by
      intro h
      exact hzi ((algebraMap ℝ K).injective (h.trans (map_zero (algebraMap ℝ K)).symm))
    have hsum : a ^ 2 + b ^ 2 = 0 := hqzero
    have hneg : (a / b) ^ 2 = -1 := by
      rw [div_pow, div_eq_iff (pow_ne_zero _ hb)]
      linear_combination hsum
    have hsq := IsSumSq.mul_self (a / b)
    rw [← pow_two, hneg] at hsq
    exact (IsSemireal.not_isSumSq_neg_one hsq).elim

/-- Every common univariate zero over a semireal extension gives a real
common zero. If any defining polynomial is nonzero, the given zero itself
is in the coefficient field. -/
theorem real_univariate_common_zero {K E : Type*} [Field K] [IsSemireal K]
    (e : ℝ →+* K) (x : K) (p : E → ℝ[X]) (h : ∀ j, (p j).eval₂ e x = 0) :
    ∃ y : ℝ, ∀ j, (p j).eval y = 0 := by
  classical
  by_cases hp : ∃ j, p j ≠ 0
  · obtain ⟨j, hj⟩ := hp
    letI : Algebra ℝ K := e.toAlgebra
    have hx : IsAlgebraic ℝ x := ⟨p j, hj, h j⟩
    obtain ⟨y, hy⟩ := integral_over_real_mem_range hx.isIntegral
    refine ⟨y, fun j => e.injective ?_⟩
    have he : e ((p j).eval y) = 0 := by
      change algebraMap ℝ K ((p j).eval y) = 0
      rw [← aeval_algebraMap_apply_eq_algebraMap_eval, hy]
      exact h j
    exact he.trans e.map_zero.symm
  · push_neg at hp
    exact ⟨0, fun j => by rw [hp j, eval_zero]⟩

/-- A polynomial solution over a semireal extension descends if all its
coordinates are integral over the reals. -/
theorem real_polynomial_system_descends_of_integral_values {K V E : Type*} [Field K]
    [Algebra ℝ K] [IsSemireal K] (f : E → MvPolynomial V ℝ) (x : V → K)
    (hx : ∀ j, MvPolynomial.aeval x (f j) = 0) (hint : ∀ v, IsIntegral ℝ (x v)) :
    ∃ y : V → ℝ, ∀ j, MvPolynomial.eval y (f j) = 0 := by
  classical
  choose y hy using fun v => integral_over_real_mem_range (hint v)
  have hxy : (algebraMap ℝ K) ∘ y = x := funext hy
  refine ⟨y, fun j => (algebraMap ℝ K).injective ?_⟩
  rw [map_zero, MvPolynomial.eval₂_comp, hxy]
  exact hx j

/-- Nonzero elimination polynomials for the individual coordinates
give descent over a semireal field. The ideal membership statements can
be given by exact finite polynomial identities. -/
theorem real_polynomial_system_descends_of_coordinate_elimination {K V E : Type*} [Field K]
    [Algebra ℝ K] [IsSemireal K] (f : E → MvPolynomial V ℝ) (p : V → ℝ[X])
    (hp : ∀ v, p v ≠ 0)
    (hmem : ∀ v, aeval (MvPolynomial.X v : MvPolynomial V ℝ) (p v) ∈ Ideal.span (Set.range f))
    (x : V → K) (hx : ∀ j, MvPolynomial.aeval x (f j) = 0) :
    ∃ y : V → ℝ, ∀ j, MvPolynomial.eval y (f j) = 0 := by
  let g : MvPolynomial V ℝ →ₐ[ℝ] K := MvPolynomial.aeval x
  have hker : Ideal.span (Set.range f) ≤ RingHom.ker g.toRingHom := by
    apply Ideal.span_le.mpr
    rintro _ ⟨j, rfl⟩
    exact RingHom.mem_ker.mpr (hx j)
  apply real_polynomial_system_descends_of_integral_values f x hx
  intro v
  have hn : g (aeval (MvPolynomial.X v) (p v)) = 0 := RingHom.mem_ker.mp (hker (hmem v))
  have hz : aeval (x v) (p v) = 0 := by
    rw [← aeval_algHom_apply, show g (MvPolynomial.X v) = x v from MvPolynomial.aeval_X x v] at hn
    exact hn
  exact (show IsAlgebraic ℝ (x v) from ⟨p v, hp v, hz⟩).isIntegral

/-- A semireal real coordinate ring that is integral over its coefficient
field has a real point. This applies to finite-dimensional coordinate rings. -/
theorem real_polynomial_zero_of_semireal_integral_quotient {V : Type u} {E : Type*}
    (f : E → MvPolynomial V ℝ)
    [Algebra.IsIntegral ℝ (MvPolynomial V ℝ ⧸ Ideal.span (Set.range f))]
    (h : IsSemireal (MvPolynomial V ℝ ⧸ Ideal.span (Set.range f))) :
    ∃ y : V → ℝ, ∀ j, MvPolynomial.eval y (f j) = 0 := by
  obtain ⟨K, hK, hS, e, x, hx⟩ := (semireal_polynomial_quotient_iff_extension_point f).mp h
  letI := hK
  letI := hS
  letI : Algebra ℝ K := e.toAlgebra
  let I := Ideal.span (Set.range f)
  let g : MvPolynomial V ℝ →ₐ[ℝ] K := MvPolynomial.aeval x
  have hker : I ≤ RingHom.ker g.toRingHom := by
    apply Ideal.span_le.mpr
    rintro _ ⟨j, rfl⟩
    exact RingHom.mem_ker.mpr (hx j)
  let φ : MvPolynomial V ℝ ⧸ I →ₐ[ℝ] K :=
    Ideal.Quotient.liftₐ I g fun p hp => RingHom.mem_ker.mp (hker hp)
  apply real_polynomial_system_descends_of_integral_values f x hx
  intro i
  have hi : IsIntegral ℝ (Ideal.Quotient.mk I (MvPolynomial.X i)) := Algebra.IsIntegral.isIntegral _
  have him := IsIntegral.map φ hi
  simpa only [φ, Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk, AlgHom.coe_toRingHom,
    g, MvPolynomial.aeval_X] using him

/-- Integral real coordinate rings satisfy the finite sum-of-squares
infeasibility criterion without a general quantifier-elimination theorem. -/
theorem polynomial_certificate_iff_no_real_zeros_of_integral_quotient {V : Type u} {E : Type*}
    [Fintype E] (f : E → MvPolynomial V ℝ)
    [Algebra.IsIntegral ℝ (MvPolynomial V ℝ ⧸ Ideal.span (Set.range f))] :
    (∃ s : MvPolynomial V ℝ, IsSumSq s ∧ ∃ h : E → MvPolynomial V ℝ,
        (-1 : MvPolynomial V ℝ) = s + ∑ j, h j * f j) ↔
      ¬ ∃ y : V → ℝ, ∀ j, MvPolynomial.eval y (f j) = 0 := by
  classical
  constructor
  · intro h
    exact no_real_zeros_of_quotient_sumSq f ((polynomial_certificate_iff_quotient_sumSq f).mp h)
  · intro hn
    by_contra hc
    exact hn (real_polynomial_zero_of_semireal_integral_quotient f
      ((semireal_quotient_iff_no_polynomial_certificate f).mpr hc))

/-- Every finite system in one variable has a sum-of-squares equation
certificate exactly when it has no real solution. -/
theorem one_variable_certificate_iff_no_real_zeros {E : Type*} [Fintype E]
    (f : E → MvPolynomial PUnit ℝ) :
    (∃ s : MvPolynomial PUnit ℝ, IsSumSq s ∧ ∃ h : E → MvPolynomial PUnit ℝ,
        (-1 : MvPolynomial PUnit ℝ) = s + ∑ j, h j * f j) ↔
      ¬ ∃ y : PUnit → ℝ, ∀ j, MvPolynomial.eval y (f j) = 0 := by
  classical
  constructor
  · intro h
    exact no_real_zeros_of_quotient_sumSq f ((polynomial_certificate_iff_quotient_sumSq f).mp h)
  · intro hn
    by_contra hc
    have hs := (semireal_quotient_iff_no_polynomial_certificate f).mpr hc
    obtain ⟨K, hK, hS, e, x, hx⟩ := (semireal_polynomial_quotient_iff_extension_point f).mp hs
    letI := hK
    letI := hS
    let p (j : E) : ℝ[X] := MvPolynomial.pUnitAlgEquiv ℝ (f j)
    have hconst : (fun _ : PUnit => x PUnit.unit) = x := by
      funext i
      cases i
      rfl
    have hroot (j : E) : (p j).eval₂ e (x PUnit.unit) = 0 := by
      dsimp only [p]
      rw [MvPolynomial.eval₂_const_pUnitAlgEquiv, hconst]
      exact hx j
    obtain ⟨y, hy⟩ := real_univariate_common_zero e (x PUnit.unit) p hroot
    refine hn ⟨fun _ => y, fun j => ?_⟩
    change MvPolynomial.eval₂ (RingHom.id ℝ) (fun _ => y) (f j) = 0
    rw [← MvPolynomial.eval₂_const_pUnitAlgEquiv]
    exact hy j

end
end MOC
