import MOC.PlaneCurveCovering
import MOC.PolynomialCoefficientClearing
import Mathlib.Tactic.Ring

/-! A separable polynomial over the function field remains separable and
retains its degree outside a finite set of specializations. -/

open Set Polynomial

namespace MOC

section FractionField

variable {R K : Type*} [CommRing R] [IsDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K]

/-- A common denominator clears the Bézout identity of a separable
polynomial and its derivative in a fraction field. -/
theorem exists_bezout_multiple_of_fraction_separable (P : R[X])
    (h : (P.map (algebraMap R K)).Separable) :
    ∃ q : R, q ≠ 0 ∧ ∃ A B : R[X], A * P + B * P.derivative = Polynomial.C q := by
  let f : R →+* K := algebraMap R K
  obtain ⟨a, b, hab⟩ := h
  obtain ⟨d, hd, A, hA⟩ := clear_polynomial_coefficients (R := R) a
  obtain ⟨e, he, B, hB⟩ := clear_polynomial_coefficients (R := R) b
  refine ⟨d * e, mul_ne_zero hd he, Polynomial.C e * A, Polynomial.C d * B, ?_⟩
  apply Polynomial.map_injective f (IsFractionRing.injective R K)
  change (((Polynomial.C e * A) * P + (Polynomial.C d * B) * P.derivative).map f) =
    (Polynomial.C (d * e)).map f
  have hAf : A.map f = Polynomial.C (f d) * a := hA
  have hBf : B.map f = Polynomial.C (f e) * b := hB
  simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, hAf, hBf,
    ← Polynomial.derivative_map, map_mul]
  calc
    _ = (Polynomial.C (f d) * Polynomial.C (f e)) *
        (a * P.map f + b * (P.map f).derivative) := by ring
    _ = _ := by rw [hab, mul_one, ← map_mul]

end FractionField

/-- The exceptional values are the zeros of the leading coefficient and
the denominator in a cleared Bézout identity. Any additional finite set
can be deleted at the same time. -/
theorem exists_finite_planePolynomial_exceptional_set (P : Polynomial ℂ[X])
    (hdeg : 0 < P.natDegree)
    (hsep : (P.map (algebraMap ℂ[X] (FractionRing ℂ[X]))).Separable)
    {T : Set ℂ} (hT : T.Finite) :
    ∃ S : Set ℂ, S.Finite ∧ T ⊆ S ∧
      (∀ t : ↥Sᶜ, (planePolynomialSpecialize P t.val).natDegree = P.natDegree) ∧
      (∀ t : ↥Sᶜ, (planePolynomialSpecialize P t.val).Separable) := by
  obtain ⟨q, hq, A, B, hbez⟩ := exists_bezout_multiple_of_fraction_separable P hsep
  have hP : P ≠ 0 := by
    intro hzero
    rw [hzero, Polynomial.natDegree_zero] at hdeg
    exact (lt_irrefl _) hdeg
  have hpq : q * P.leadingCoeff ≠ 0 := mul_ne_zero hq (Polynomial.leadingCoeff_ne_zero.mpr hP)
  let S : Set ℂ := T ∪ {t | (q * P.leadingCoeff).IsRoot t}
  have hg (t : ↥Sᶜ) : q.eval t.val ≠ 0 ∧ P.leadingCoeff.eval t.val ≠ 0 := by
    have h : (q * P.leadingCoeff).eval t.val ≠ 0 := fun he => t.property (Or.inr he)
    rw [Polynomial.eval_mul, mul_ne_zero_iff] at h
    exact h
  refine ⟨S, hT.union (Polynomial.finite_setOf_isRoot hpq), subset_union_left, ?_, ?_⟩
  · intro t
    exact Polynomial.natDegree_map_of_leadingCoeff_ne_zero (Polynomial.evalRingHom t.val) (hg t).2
  · intro t
    let f := Polynomial.evalRingHom t.val
    let R := planePolynomialSpecialize P t.val
    have he := congrArg (Polynomial.map f) hbez
    simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C,
      ← Polynomial.derivative_map] at he
    have he' : A.map f * R + B.map f * R.derivative = Polynomial.C (f q) := he
    have hn : f q ≠ 0 := (hg t).1
    refine ⟨Polynomial.C ((f q)⁻¹) * A.map f, Polynomial.C ((f q)⁻¹) * B.map f, ?_⟩
    rw [mul_assoc, mul_assoc, ← mul_add, he', ← map_mul, inv_mul_cancel₀ hn, map_one]

/-- A nonconstant generically separable plane polynomial covers the line
after deleting finitely many values and any supplied finite exceptions. -/
theorem exists_planePolynomial_covering_off_finite (P : Polynomial ℂ[X])
    (hdeg : 0 < P.natDegree)
    (hsep : (P.map (algebraMap ℂ[X] (FractionRing ℂ[X]))).Separable)
    {T : Set ℂ} (hT : T.Finite) :
    ∃ S : Set ℂ, S.Finite ∧ T ⊆ S ∧
      IsCoveringMap (fun z : PlanePolynomialRoots P Sᶜ => z.val.1) := by
  obtain ⟨S, hS, hTS, hd, hs⟩ := exists_finite_planePolynomial_exceptional_set P hdeg hsep hT
  exact ⟨S, hS, hTS, isCoveringMap_planePolynomialRoots P Sᶜ hdeg hd hs⟩

end MOC
