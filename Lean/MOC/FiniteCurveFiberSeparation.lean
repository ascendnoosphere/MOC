import MOC.FiniteCurveFibers
import Mathlib.Algebra.Polynomial.ofFn
import Mathlib.Analysis.Complex.Polynomial.Basic

/-! A linear polynomial separates a pinned point from every other point in a finite fiber. -/

open Set
open scoped BigOperators

namespace MOC

variable {σ : Type*} [Fintype σ]

/-- A finite complex affine set admits a linear coordinate that separates
one pinned point from every distinct point in the set. Choose the
coefficient vector along a power pencil and avoid finitely many roots. -/
theorem exists_polynomial_separating_pinned_finite_point
    (S : Set (σ → ℂ)) (hS : S.Finite) (x : σ → ℂ) :
    ∃ u : MvPolynomial σ ℂ, ∀ y ∈ S, MvPolynomial.eval y u = MvPolynomial.eval x u → y = x := by
  classical
  let e := Fintype.equivFin σ
  let F (y : σ → ℂ) := Polynomial.ofFn (Fintype.card σ) (fun i => y (e.symm i))
  have hF : Function.Injective F := by
    intro y z h
    funext i
    have hh := congrArg (fun p : Polynomial ℂ => p.coeff ((e i).val)) h
    simpa only [F, Polynomial.ofFn_coeff_eq_val_of_lt _ (e i).isLt, Fin.eta, Equiv.symm_apply_apply]
      using hh
  let bad : Set ℂ := ⋃ y ∈ S \ {x}, {t | (F y - F x).IsRoot t}
  have hbad : bad.Finite := by
    apply hS.diff.biUnion
    intro y hy
    exact Polynomial.finite_setOf_isRoot (sub_ne_zero.mpr (fun h => hy.2 (hF h)))
  obtain ⟨a, ha⟩ := hbad.exists_not_mem
  let u : MvPolynomial σ ℂ := ∑ i : Fin (Fintype.card σ),
    MvPolynomial.C (a ^ i.val) * MvPolynomial.X (e.symm i)
  have heval (y : σ → ℂ) : MvPolynomial.eval y u = (F y).eval a := by
    simp only [u, F, MvPolynomial.eval_sum, MvPolynomial.eval_mul, MvPolynomial.eval_C,
      MvPolynomial.eval_X, Polynomial.ofFn_eq_sum_monomial, Polynomial.eval_finset_sum,
      Polynomial.eval_monomial, mul_comm]
  refine ⟨u, fun y hy h => ?_⟩
  by_cases hx : y = x
  · exact hx
  · exfalso
    apply ha
    simp only [bad, Set.mem_iUnion, Set.mem_setOf_eq]
    refine ⟨y, ⟨hy, hx⟩, ?_⟩
    change (F y - F x).eval a = 0
    rw [Polynomial.eval_sub, ← heval y, ← heval x, h, sub_self]

/-- Any specified point of a fiber of a finite affine projection can be
pinned by a second polynomial coordinate on that fiber. -/
theorem exists_polynomial_separating_pinned_finite_fiber
    (Q : Ideal (MvPolynomial σ ℂ))
    (f : Polynomial ℂ →ₐ[ℂ] (MvPolynomial σ ℂ ⧸ Q)) (hf : f.Finite)
    (t : MvPolynomial σ ℂ) (ht : Ideal.Quotient.mk Q t = f Polynomial.X)
    (x : MvPolynomial.zeroLocus Q) :
    ∃ u : MvPolynomial σ ℂ, ∀ y : MvPolynomial.zeroLocus Q,
      MvPolynomial.eval y.val t = MvPolynomial.eval x.val t →
      MvPolynomial.eval y.val u = MvPolynomial.eval x.val u → y = x := by
  obtain ⟨u, hu⟩ := exists_polynomial_separating_pinned_finite_point _
    (finite_points_over_finite_projection Q f hf t ht (MvPolynomial.eval x.val t)) x.val
  exact ⟨u, fun y h₁ h₂ => Subtype.ext (hu y.val ⟨y.property, h₁⟩ h₂)⟩

end MOC
