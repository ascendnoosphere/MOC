import MOC.FourNegativeCopy
import MOC.Small
import Mathlib.Data.Matrix.Rank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! Determinant inclusion for a spectrum paired with its negative. -/

open BigOperators Matrix

namespace MOC

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem holds_negative_copy_of_zero [Nonempty ι] (a : ι → ℂ)
    (U : Matrix ι ι ℂ) (h : determinantValue a (fun i => -a i) U = 0) :
    Holds a (fun i => -a i) U := by
  have hz : matchingProduct a (fun i => -a i) (Equiv.refl ι) = 0 := by
    obtain ⟨i⟩ := ‹Nonempty ι›
    unfold matchingProduct
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)
  unfold Holds
  rw [h, ← hz]
  exact matchingProduct_mem_hull _ _ _

/-- In odd order, the determinant for a spectrum and its negative vanishes if
nonzero row factors make the mixer symmetric between unequal eigenvalues. -/
theorem determinantValue_negative_copy_eq_zero_of_odd_of_row_symmetry
    (a d : ι → ℂ) (U : Matrix ι ι ℂ) (hU : IsUnitary U)
    (hodd : Odd (Fintype.card ι)) (hd : ∀ i, d i ≠ 0)
    (hsym : ∀ i j, a i ≠ a j → d i * U i j = d j * U j i) :
    determinantValue a (fun i => -a i) U = 0 := by
  let K : Matrix ι ι ℂ := Matrix.of fun i j => (a i - a j) * U i j
  let L : Matrix ι ι ℂ := diagonal d * K
  have hL : Lᵀ = -L := by
    ext i j : 1
    simp only [L, K, Matrix.transpose_apply, Matrix.diagonal_mul, Matrix.of_apply, Matrix.neg_apply]
    by_cases h : a i = a j
    · simp only [h, sub_self, zero_mul, mul_zero, neg_zero]
    · calc
        _ = (a j - a i) * (d j * U j i) := by ring
        _ = (a j - a i) * (d i * U i j) := by rw [hsym i j h]
        _ = _ := by ring
  have hz : L.det = 0 := by
    have h := congrArg Matrix.det hL
    rw [Matrix.det_transpose, Matrix.det_neg, hodd.neg_one_pow, neg_one_mul] at h
    linear_combination h / 2
  have hd' : (diagonal d).det ≠ 0 := by
    rw [Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => hd i
  have hK : K.det = 0 := by
    apply (mul_eq_zero.mp ?_).resolve_left hd'
    rw [← Matrix.det_mul]
    exact hz
  rw [determinantValue_eq_weightedEntryDet_div a (fun i => -a i) U hU]
  change K.det / U.det = 0
  rw [hK, zero_div]

/-- The identity matching has value zero and thus gives the inclusion when
the odd-order determinant vanishes by row symmetry. -/
theorem holds_negative_copy_of_odd_of_row_symmetry
    (a d : ι → ℂ) (U : Matrix ι ι ℂ) (hU : IsUnitary U)
    (hodd : Odd (Fintype.card ι)) (hd : ∀ i, d i ≠ 0)
    (hsym : ∀ i j, a i ≠ a j → d i * U i j = d j * U j i) :
    Holds a (fun i => -a i) U := by
  have hn : 0 < Fintype.card ι := by obtain ⟨k, hk⟩ := hodd; omega
  letI : Nonempty ι := Fintype.card_pos_iff.mp hn
  exact holds_negative_copy_of_zero a U
    (determinantValue_negative_copy_eq_zero_of_odd_of_row_symmetry a d U hU hodd hd hsym)

omit [DecidableEq ι] in
private theorem rank_add_le_sum (A B : Matrix ι ι ℂ) : (A + B).rank ≤ A.rank + B.rank := by
  have h : LinearMap.range (A + B).mulVecLin ≤
      LinearMap.range A.mulVecLin ⊔ LinearMap.range B.mulVecLin := by
    rintro _ ⟨v, rfl⟩
    rw [Matrix.mulVecLin_add, LinearMap.add_apply]
    exact Submodule.add_mem_sup (LinearMap.mem_range_self A.mulVecLin v)
      (LinearMap.mem_range_self B.mulVecLin v)
  exact (Submodule.finrank_mono h).trans (Submodule.finrank_add_le_finrank_add_finrank _ _)

/-- A diagonal subtraction leaves the weighted difference kernel unchanged.
Its rank is at most twice the rank of the matrix after subtraction. -/
theorem determinantValue_negative_copy_eq_zero_of_diagonal_rank
    (a d : ι → ℂ) (U : Matrix ι ι ℂ) (hU : IsUnitary U)
    (hrank : 2 * (U - diagonal d).rank < Fintype.card ι) :
    determinantValue a (fun i => -a i) U = 0 := by
  let T := U - diagonal d
  let A := diagonal a
  let K := A * T + T * diagonal (fun i => -a i)
  have hkernel : K = Matrix.of (fun i j => (a i + -a j) * U i j) := by
    ext i j : 1
    simp only [K, A, T, Matrix.add_apply, Matrix.diagonal_mul, Matrix.mul_diagonal,
      Matrix.sub_apply, Matrix.of_apply]
    by_cases hij : i = j
    · subst j
      rw [Matrix.diagonal_apply_eq]
      ring
    · rw [Matrix.diagonal_apply_ne _ hij, sub_zero]
      ring
  have hK : K.rank < Fintype.card ι := by
    have hsum := rank_add_le_sum (A * T) (T * diagonal (fun i => -a i))
    have hleft := Matrix.rank_mul_le_right A T
    have hright := Matrix.rank_mul_le_left T (diagonal (fun i => -a i))
    change 2 * T.rank < Fintype.card ι at hrank
    change K.rank ≤ _ at hsum
    omega
  have hzero : K.det = 0 := by
    by_contra hne
    have hu := (Matrix.isUnit_iff_isUnit_det K).mpr (isUnit_iff_ne_zero.mpr hne)
    rw [Matrix.rank_of_isUnit K hu] at hK
    exact (lt_irrefl _) hK
  rw [determinantValue_eq_weightedEntryDet_div a (fun i => -a i) U hU,
    ← hkernel, hzero, zero_div]

/-- In every order the inclusion holds for a spectrum and its negative
if the mixer differs from a diagonal matrix by rank at most two. -/
theorem holds_negative_copy_of_diagonal_rank_le_two
    (a d : ι → ℂ) (U : Matrix ι ι ℂ) (hU : IsUnitary U)
    (hrank : (U - diagonal d).rank ≤ 2) : Holds a (fun i => -a i) U := by
  by_cases hsmall : Fintype.card ι ≤ 3
  · exact conjecture_of_card_le_three hsmall _ _ U hU
  by_cases hfour : Fintype.card ι = 4
  · let e : Fin 4 ≃ ι := Fintype.equivOfCardEq (by simpa using hfour.symm)
    exact (holds_reindex_iff e e a (fun i => -a i) U).mp
      (holds_four_negative_copy (a ∘ e) _ (unitary_reindex e e hU))
  letI : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
  exact holds_negative_copy_of_zero a U
    (determinantValue_negative_copy_eq_zero_of_diagonal_rank a d U hU (by omega))

end MOC
