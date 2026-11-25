import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Order.Interval.Set.Infinite

/-! Every open neighborhood along a real line contains a parameter that
avoids the roots of a fixed nonzero polynomial. -/

open Polynomial

namespace MOC

/-- An open neighborhood of the base point contains a point on the line
whose parameter is outside the finite root set of the polynomial. -/
theorem exists_polynomial_nonroot_on_line {ι : Type*} (U : Set (ι → ℂ)) (hU : IsOpen U)
    (b v : ι → ℂ) (hb : b ∈ U) (Q : ℝ[X]) (hQ : Q ≠ 0) :
    ∃ t : ℝ, (fun i => b i + (t : ℂ) * v i) ∈ U ∧ Q.eval t ≠ 0 := by
  let γ (t : ℝ) (i : ι) := b i + (t : ℂ) * v i
  have hγ : Continuous γ := continuous_pi fun i =>
    continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
  have hmem : (0 : ℝ) ∈ γ ⁻¹' U := by simpa [γ] using hb
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp (hU.preimage hγ) 0 hmem
  by_contra! h
  have hs : Metric.ball (0 : ℝ) ε ⊆ {t | Q.IsRoot t} :=
    fun t ht => h t (hball ht)
  have hfin := (finite_setOf_isRoot hQ).subset hs
  rw [Real.ball_eq_Ioo] at hfin
  exact Set.Ioo_infinite (show 0 - ε < 0 + ε by linarith) hfin

end MOC
