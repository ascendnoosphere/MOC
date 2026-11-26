import MOC.Core
import Mathlib.Data.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-! Explicit failures of the three-summand, rank threshold, and nonunitary
compression versions of determinant inclusion. -/

open BigOperators Matrix Polynomial

namespace MOC

noncomputable section

def threeSummandA : Matrix (Fin 2) (Fin 2) ℝ :=
  !![3,0; 0,-3]

def threeSummandB : Matrix (Fin 2) (Fin 2) ℝ :=
  !![0,4; 4,0]

def threeSummandC : Matrix (Fin 2) (Fin 2) ℝ :=
  !![-3,-4; -4,3]

def threeSummandVertex (s t : Bool) : ℝ :=
  -(3 + (if s then 4 else -4) + (if t then 5 else -5)) ^ 2

private theorem charpoly_fin_two_explicit (A : Matrix (Fin 2) (Fin 2) ℝ) :
    A.charpoly = (X - C (A 0 0)) * (X - C (A 1 1)) -
      C (A 0 1) * C (A 1 0) := by
  rw [Matrix.charpoly, Matrix.det_fin_two, Matrix.charmatrix_apply_eq,
    Matrix.charmatrix_apply_eq, Matrix.charmatrix_apply_ne _ _ _ (by decide),
    Matrix.charmatrix_apply_ne _ _ _ (by decide)]
  ring

/-- The zero determinant of three Hermitian summands is strictly above all
vertices obtained from independent pairings of their eigenvalue lists. -/
theorem three_hermitian_summands_counterexample :
    threeSummandA.IsHermitian ∧ threeSummandB.IsHermitian ∧ threeSummandC.IsHermitian ∧
      threeSummandA.charpoly = (X - C 3) * (X + C 3) ∧
      threeSummandB.charpoly = (X - C 4) * (X + C 4) ∧
      threeSummandC.charpoly = (X - C 5) * (X + C 5) ∧
      (threeSummandA + threeSummandB + threeSummandC).det = 0 ∧
      Set.range (fun st : Bool × Bool => threeSummandVertex st.1 st.2) =
        {-144,-36,-16,-4} := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold Matrix.IsHermitian
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [threeSummandA, Matrix.conjTranspose_apply]
  · unfold Matrix.IsHermitian
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [threeSummandB, Matrix.conjTranspose_apply]
  · unfold Matrix.IsHermitian
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [threeSummandC, Matrix.conjTranspose_apply]
  · rw [charpoly_fin_two_explicit]
    norm_num [threeSummandA]
    <;> ring
  · rw [charpoly_fin_two_explicit]
    norm_num [threeSummandB]
    <;> ring
  · rw [charpoly_fin_two_explicit]
    norm_num [threeSummandC]
    <;> ring
  · norm_num [Matrix.det_fin_two, threeSummandA, threeSummandB, threeSummandC]
  · ext x
    constructor
    · rintro ⟨⟨s,t⟩, rfl⟩
      cases s <;> cases t <;> norm_num [threeSummandVertex]
    · intro hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact ⟨(true,true), by norm_num [threeSummandVertex]⟩
      · exact ⟨(false,false), by norm_num [threeSummandVertex]⟩
      · exact ⟨(false,true), by norm_num [threeSummandVertex]⟩
      · exact ⟨(true,false), by norm_num [threeSummandVertex]⟩

private def halfBlock4 : Matrix (Fin 4) (Fin 4) ℚ :=
  !![1/2,1/2,0,0; 1/2,1/2,0,0; 0,0,1/2,1/2; 0,0,1/2,1/2]

private def halfBlock5 : Matrix (Fin 5) (Fin 5) ℚ :=
  !![1/2,1/2,0,0,0; 1/2,1/2,0,0,0; 0,0,1/2,1/2,0;
    0,0,1/2,1/2,0; 0,0,0,0,1]

private theorem rank_of_retraction {n k : ℕ}
    (L : Matrix (Fin n) (Fin k) ℚ) (R : Matrix (Fin k) (Fin n) ℚ)
    (h : R * L = 1) : (L * R).rank = k := by
  have htop : (L * R).rank ≤ k :=
    (Matrix.rank_mul_le_left L R).trans (by simpa using Matrix.rank_le_card_width L)
  have hprod : R * (L * R) * L = 1 := by
    calc
      _ = (R * L) * (R * L) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [h, Matrix.one_mul]
  have hbottom : k ≤ (L * R).rank := by
    have hr := (Matrix.rank_mul_le_left (R * (L * R)) L).trans
      (Matrix.rank_mul_le_right R (L * R))
    rwa [hprod, Matrix.rank_one, Fintype.card_fin] at hr
  exact le_antisymm htop hbottom

private theorem halfBlock4_rank : halfBlock4.rank = 2 := by
  let L : Matrix (Fin 4) (Fin 2) ℚ := !![1,0;1,0;0,1;0,1]
  let R : Matrix (Fin 2) (Fin 4) ℚ := !![1/2,1/2,0,0;0,0,1/2,1/2]
  have h : R * L = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [L, R, Matrix.mul_apply,
      Matrix.one_apply, Fin.sum_univ_four]
  have h' : L * R = halfBlock4 := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [L, R, Matrix.mul_apply,
      halfBlock4, Fin.sum_univ_two]
  rw [← h']
  exact rank_of_retraction L R h

private theorem halfBlock5_rank : halfBlock5.rank = 3 := by
  let L : Matrix (Fin 5) (Fin 3) ℚ := !![1,0,0;1,0,0;0,1,0;0,1,0;0,0,1]
  let R : Matrix (Fin 3) (Fin 5) ℚ := !![1/2,1/2,0,0,0;0,0,1/2,1/2,0;0,0,0,0,1]
  have h : R * L = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [L, R, Matrix.mul_apply,
      Matrix.one_apply, Fin.sum_univ_succ]
  have h' : L * R = halfBlock5 := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [L, R, Matrix.mul_apply,
      halfBlock5, Fin.sum_univ_three]
  rw [← h']
  exact rank_of_retraction L R h

set_option maxRecDepth 8000 in
/-- The singular order-four threshold example has rank two and determinant
one-sixteenth after multiplication by the additive spectral factors. -/
theorem rank_threshold_order_four :
    halfBlock4.rank = 2 ∧ halfBlock4.det = 0 ∧
      (diagonal (![0,1,0,1] : Fin 4 → ℚ) * halfBlock4 +
        halfBlock4 * diagonal ![0,1,0,1]).det = 1 / 16 := by
  refine ⟨halfBlock4_rank, ?_, ?_⟩ <;>
    rw [Matrix.det_succ_column_zero] <;> simp only [Matrix.det_fin_three, Fin.sum_univ_four] <;>
    decide +kernel

set_option maxRecDepth 12000 in
/-- The singular order-five threshold example has rank three and the
same nonzero determinant after entrywise multiplication. -/
theorem rank_threshold_order_five :
    halfBlock5.rank = 3 ∧ halfBlock5.det = 0 ∧
      (diagonal (![0,1,0,1,0] : Fin 5 → ℚ) * halfBlock5 +
        halfBlock5 * diagonal ![0,1,0,1,1]).det = 1 / 16 := by
  refine ⟨halfBlock5_rank, ?_, ?_⟩ <;>
    rw [Matrix.det_succ_column_zero] <;>
    simp only [Matrix.det_succ_column_zero (n := 3), Matrix.det_fin_three, Fin.sum_univ_succ] <;>
    decide +kernel

private def reflector3 : Matrix (Fin 3) (Fin 3) ℂ :=
  !![1/3,-2/3,-2/3; -2/3,1/3,-2/3; -2/3,-2/3,1/3]

private def reflectorTopLeft : Matrix (Fin 2) (Fin 2) ℂ :=
  reflector3.submatrix Fin.castSucc Fin.castSucc

/-- The invertible leading block of a unitary matrix can violate the
normalized determinant enclosure for nonunitary compressions. -/
theorem compressed_reflector_counterexample :
    IsUnitary reflector3 ∧ reflectorTopLeft.det = -1 / 3 ∧
      (diagonal (![0,1] : Fin 2 → ℂ) * reflectorTopLeft +
        reflectorTopLeft * diagonal ![0,1]).det / reflectorTopLeft.det = 4 / 3 := by
  have hU : reflector3 * reflector3ᴴ = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [reflector3, Matrix.mul_apply, Matrix.conjTranspose_apply,
        Matrix.one_apply, Fin.sum_univ_three, star_div₀]
  refine ⟨⟨hU, Matrix.mul_eq_one_comm.mp hU⟩, ?_, ?_⟩ <;>
    norm_num [reflectorTopLeft, reflector3, Matrix.det_fin_two,
      Matrix.submatrix_apply, Matrix.diagonal_mul, Matrix.mul_diagonal]

end

end MOC
