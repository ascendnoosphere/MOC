import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Localization.Integer

/-! Clearing coefficients of a polynomial over a fraction field. -/

open BigOperators Polynomial
open scoped nonZeroDivisors

namespace MOC

variable {R K : Type*} [CommRing R] [IsDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K]

/-- A common nonzero scalar clears the coefficient denominators of a
polynomial over a fraction field. -/
theorem clear_polynomial_coefficients (A : K[X]) :
    ∃ d : R, d ≠ 0 ∧ ∃ a : R[X],
      a.map (algebraMap R K) = Polynomial.C (algebraMap R K d) * A := by
  classical
  let d : R⁰ := IsLocalization.commonDenom R⁰ A.support A.coeff
  let a : R[X] := ∑ i : ↥A.support,
    Polynomial.monomial i.val (IsLocalization.integerMultiple R⁰ A.support A.coeff i)
  have hd (i : ↥A.support) :
      algebraMap R K (IsLocalization.integerMultiple R⁰ A.support A.coeff i) =
        algebraMap R K (d : R) * A.coeff i.val := by
    rw [IsLocalization.map_integerMultiple]
    change (d : R) • A.coeff i.val = _
    exact Algebra.smul_def _ _
  refine ⟨d, nonZeroDivisors.coe_ne_zero d, a, ?_⟩
  simp only [a, Polynomial.map_sum, Polynomial.map_monomial, hd]
  simp_rw [← Polynomial.C_mul_monomial]
  rw [← Finset.mul_sum, Finset.sum_coe_sort A.support (fun i : ℕ => Polynomial.monomial i (A.coeff i))]
  congr 1
  exact Polynomial.sum_monomial_eq A

end MOC
