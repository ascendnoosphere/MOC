import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Matrix.Rank

/-! Rank bounds for spectral coefficient blocks presented as sums of outer products. -/

open BigOperators Matrix

namespace MOC

section

variable {κ m n : Type*} [Fintype κ] [Fintype m] [Fintype n]

/-- A sum of one outer product per contributing level has rank at most
the number of levels. -/
theorem rank_sum_outer_products_le (x : κ → m → ℂ) (y : κ → n → ℂ) :
    (Matrix.of fun i j => ∑ k, x k i * y k j).rank ≤ Fintype.card κ := by
  let A : Matrix m κ ℂ := Matrix.of fun i k => x k i
  let B : Matrix κ n ℂ := Matrix.of fun k j => y k j
  have h : Matrix.of (fun i j => ∑ k, x k i * y k j) = A * B := by
    ext i j : 1
    rfl
  rw [h]
  exact (Matrix.rank_mul_le_left A B).trans (Matrix.rank_le_card_width A)

/-- Taking coordinatewise real parts uses at most two real outer products
for each complex outer product. -/
theorem rank_real_sum_outer_products_le (x : κ → m → ℂ) (y : κ → n → ℂ) :
    (Matrix.of fun i j => (∑ k, x k i * y k j).re).rank ≤ 2 * Fintype.card κ := by
  let A : Matrix m (κ ⊕ κ) ℝ :=
    Matrix.of fun i => Sum.elim (fun k => (x k i).re) (fun k => -(x k i).im)
  let B : Matrix (κ ⊕ κ) n ℝ :=
    Matrix.of fun k j => Sum.elim (fun l => (y l j).re) (fun l => (y l j).im) k
  have h : Matrix.of (fun i j => (∑ k, x k i * y k j).re) = A * B := by
    ext i j : 1
    simp only [Matrix.of_apply, Matrix.mul_apply, A, B, Complex.re_sum, Complex.mul_re,
      Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, neg_mul, Finset.sum_neg_distrib,
      Finset.sum_sub_distrib, Finset.sum_add_distrib, sub_eq_add_neg]
  rw [h]
  have h' := (Matrix.rank_mul_le_left A B).trans (Matrix.rank_le_card_width A)
  simpa only [Fintype.card_sum, two_mul] using h'

end

section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The raw coefficient matrix of each subset level is an outer product. -/
theorem rank_spectral_subset_level_le_one (a b : ι → ℂ) (k : ℕ) :
    (Matrix.of fun I J : {S : Finset ι // S.card = k} =>
      (∏ i ∈ I.valᶜ, a i) * ∏ j ∈ J.val, b j).rank ≤ 1 := by
  classical
  let x : Unit → {S : Finset ι // S.card = k} → ℂ := fun _ I => ∏ i ∈ I.valᶜ, a i
  let y : Unit → {S : Finset ι // S.card = k} → ℂ := fun _ J => ∏ j ∈ J.val, b j
  simpa [x, y] using rank_sum_outer_products_le x y

end

end MOC
