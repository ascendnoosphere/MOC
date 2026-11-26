import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! The trace bound for orientation-reversing orthogonal matrices. -/

open BigOperators Matrix

namespace MOC

/-- A real orthogonal matrix with determinant minus one has trace at
most its order minus two. The proof uses a vector that it negates. -/
theorem orthogonal_trace_le_of_det_neg_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Q : Matrix ι ι ℝ) (hQ : Q * Qᵀ = 1) (hd : Q.det = -1) :
    Q.trace ≤ (Fintype.card ι : ℝ) - 2 := by
  have hprod : Q * (Qᵀ + 1) = Q + 1 := by
    rw [Matrix.mul_add, hQ, Matrix.mul_one, add_comm]
  have ht : Qᵀ + 1 = (Q + 1)ᵀ := by
    rw [Matrix.transpose_add, Matrix.transpose_one]
  have hdet := congrArg Matrix.det hprod
  rw [Matrix.det_mul, hd, ht, Matrix.det_transpose] at hdet
  have hs : (Q + 1).det = 0 := by linarith only [hdet]
  obtain ⟨v, hv, hz⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hs
  rw [Matrix.add_mulVec, Matrix.one_mulVec] at hz
  let B := Q - 1
  let N := ∑ j, v j ^ 2
  have hN : 0 < N := by
    obtain ⟨j, hj⟩ : ∃ j, v j ≠ 0 := by
      by_contra! h
      exact hv (funext h)
    exact Finset.sum_pos' (fun i _ => sq_nonneg (v i)) ⟨j, Finset.mem_univ j, sq_pos_of_ne_zero hj⟩
  have hcomponent (i : ι) : (∑ j, B i j * v j) = -2 * v i := by
    have h := congrFun hz i
    change (Q *ᵥ v) i + v i = 0 at h
    change (B *ᵥ v) i = _
    simp only [B, Matrix.sub_mulVec, Matrix.one_mulVec, Pi.sub_apply]
    linarith only [h]
  have hrow (i : ι) : 4 * v i ^ 2 ≤ (∑ j, B i j ^ 2) * N := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => B i j) v
    rw [hcomponent] at h
    nlinarith only [h]
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset ι)) => hrow i)
  rw [← Finset.mul_sum, ← Finset.sum_mul] at hsum
  have hF : (4 : ℝ) ≤ ∑ i, ∑ j, B i j ^ 2 := (mul_le_mul_right hN).mp hsum
  have hF_eq : (∑ i, ∑ j, B i j ^ 2) = (B * Bᵀ).trace := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply, pow_two]
  have htrace : (B * Bᵀ).trace = 2 * (Fintype.card ι : ℝ) - 2 * Q.trace := by
    simp only [B, Matrix.transpose_sub, Matrix.transpose_one, Matrix.mul_sub, Matrix.sub_mul,
      hQ, Matrix.one_mul, Matrix.mul_one, Matrix.trace_sub, Matrix.trace_one, Matrix.trace_transpose]
    ring
  rw [hF_eq, htrace] at hF
  linarith only [hF]

end MOC
