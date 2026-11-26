import MOC.SegreConvexity
import Mathlib.Combinatorics.Enumerative.Catalan
import Mathlib.Data.Matrix.Rank
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Data.Fintype.Powerset
import Mathlib.LinearAlgebra.Trace

/-! Subset permutation operators, their coefficient space, and the two-row dimension sum. -/

open Matrix Finset

namespace MOC

variable {ι K : Type*} [Fintype ι] [DecidableEq ι] [Field K]

/-- The columns are the permutation operators in the basis indexed by subsets. -/
def subsetPermutationIncidence (ι K : Type*) [Fintype ι] [DecidableEq ι] [Zero K] [One K] :
    Matrix (Finset ι × Finset ι) (Equiv.Perm ι) K :=
  Matrix.of fun s σ => subsetPermutationOperator (R := K) σ s.1 s.2

/-- The dimension of the operator span equals the rank of the subset incidence matrix. -/
theorem finrank_subsetPermutationSpan_eq_rank :
    Module.finrank K (Submodule.span K (Set.range (subsetPermutationOperator (ι := ι) (R := K)))) =
      (subsetPermutationIncidence ι K).rank := by
  classical
  let A := subsetPermutationIncidence ι K
  let e := LinearEquiv.curry K K (Finset ι) (Finset ι)
  have he : e.toLinearMap '' Set.range A.col =
      Set.range (subsetPermutationOperator (ι := ι) (R := K)) := by
    rw [← Set.range_comp]
    rfl
  rw [← he, ← Submodule.map_span, LinearEquiv.finrank_map_eq,
    Matrix.rank_eq_finrank_span_cols]

/-- Subset indicators as functions on permutations have the same dimension as the operators. -/
theorem finrank_subsetPermutationSpan_eq_indicatorSpan :
    Module.finrank K (Submodule.span K (Set.range (subsetPermutationOperator (ι := ι) (R := K)))) =
      Module.finrank K (Submodule.span K (Set.range (subsetPermutationIncidence ι K).row)) := by
  rw [finrank_subsetPermutationSpan_eq_rank, Matrix.rank_eq_finrank_span_row]

/-- On the lower half of Pascal's row this is the two-row ballot number.
The reflected binomial makes the zero term at index minus one explicit. -/
def twoRowBinomialDifference (n j : ℕ) : ℤ :=
  (n.choose j : ℤ) - n.choose (n + 1 - j)

private theorem choose_convolution (n k : ℕ) :
    (∑ j ∈ range (k + 1), (n.choose j : ℤ) * n.choose (k - j)) =
      (2 * n).choose k := by
  have hn := Nat.add_choose_eq n n k
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => n.choose i * n.choose j)] at hn
  rw [two_mul]
  exact_mod_cast hn.symm

private theorem choose_square_sum (n : ℕ) :
    (∑ j ∈ range (n + 2), (n.choose j : ℤ) ^ 2) = n.centralBinom := by
  rw [sum_range_succ, Nat.choose_eq_zero_of_lt (Nat.lt_succ_self n)]
  simp only [Nat.cast_zero, zero_pow (by decide : 2 ≠ 0), add_zero]
  rw [Nat.centralBinom_eq_two_mul_choose, ← choose_convolution n n]
  refine sum_congr rfl fun j hj => ?_
  have hle : j ≤ n := by have := mem_range.mp hj; omega
  rw [Nat.choose_symm hle, pow_two]

private theorem binomialDifference_reflect (n j : ℕ) (hj : j ≤ n + 1) :
    twoRowBinomialDifference n (n + 1 - j) = -twoRowBinomialDifference n j := by
  unfold twoRowBinomialDifference
  rw [show n + 1 - (n + 1 - j) = j by omega]
  ring

private theorem binomialDifference_full_square_sum (n : ℕ) :
    (∑ j ∈ range (n + 2), twoRowBinomialDifference n j ^ 2) =
      2 * ((n.centralBinom : ℤ) - (2 * n).choose (n + 1)) := by
  have href : (∑ j ∈ range (n + 2), (n.choose (n + 1 - j) : ℤ) ^ 2) =
      ∑ j ∈ range (n + 2), (n.choose j : ℤ) ^ 2 := by
    simpa using sum_range_reflect (fun j => (n.choose j : ℤ) ^ 2) (n + 2)
  have expand (j : ℕ) : twoRowBinomialDifference n j ^ 2 =
      (n.choose j : ℤ) ^ 2 + (n.choose (n + 1 - j) : ℤ) ^ 2 -
        2 * ((n.choose j : ℤ) * n.choose (n + 1 - j)) := by
    unfold twoRowBinomialDifference
    ring
  simp_rw [expand]
  rw [sum_sub_distrib, sum_add_distrib, ← mul_sum, href, choose_square_sum,
    choose_convolution]
  ring

private theorem centralBinom_sub_choose_succ (n : ℕ) :
    (n.centralBinom : ℤ) - (2 * n).choose (n + 1) = catalan n := by
  have hc : catalan n * (n + 1) = n.centralBinom := by
    rw [catalan_eq_centralBinom_div, Nat.div_mul_cancel (Nat.succ_dvd_centralBinom n)]
  have hn := Nat.choose_succ_right_eq (2 * n) n
  rw [← Nat.centralBinom_eq_two_mul_choose, show 2 * n - n = n by omega] at hn
  have hci : (catalan n : ℤ) * (n + 1) = n.centralBinom := by exact_mod_cast hc
  have hni : ((2 * n).choose (n + 1) : ℤ) * (n + 1) = n.centralBinom * (n : ℤ) := by
    exact_mod_cast hn
  apply mul_right_cancel₀ (by positivity : (n : ℤ) + 1 ≠ 0)
  linear_combination hni * (-1) + (-hci)

/-- The sum of the squares of the two-row ballot numbers is the Catalan number. -/
theorem sum_twoRowBinomialDifference_sq (n : ℕ) :
    (∑ j ∈ range (n / 2 + 1), twoRowBinomialDifference n j ^ 2) = catalan n := by
  let m := n / 2 + 1
  let f := fun j => twoRowBinomialDifference n j ^ 2
  have htail : (∑ j ∈ range m, f (n + 2 - m + j)) = ∑ j ∈ range m, f j := by
    rw [← sum_range_reflect f m]
    apply sum_congr rfl
    intro j hj
    have hj' := mem_range.mp hj
    have h : n + 2 - m + j = n + 1 - (m - 1 - j) := by dsimp [m] at *; omega
    dsimp [f]
    rw [h, binomialDifference_reflect _ _ (by dsimp [m]; omega), neg_sq]
  have hmid : (∑ j ∈ range (n + 2 - m), f j) = ∑ j ∈ range m, f j := by
    rcases (show n + 2 - m = m ∨ n + 2 - m = m + 1 by dsimp [m]; omega) with h | h
    · rw [h]
    · have hm : n + 1 - m = m := by dsimp [m] at *; omega
      rw [h, sum_range_succ]
      simp only [f, twoRowBinomialDifference, hm, sub_self, zero_pow (by decide : 2 ≠ 0), add_zero]
  have hall : (∑ j ∈ range (n + 2), f j) = 2 * (∑ j ∈ range m, f j) := by
    conv_lhs => rw [show n + 2 = (n + 2 - m) + m by dsimp [m]; omega, sum_range_add]
    rw [htail, hmid, two_mul]
  have h := binomialDifference_full_square_sum n
  rw [centralBinom_sub_choose_succ] at h
  change (∑ j ∈ range m, f j) = (catalan n : ℤ)
  linarith

/-- Coordinates for signed transversal vectors of perfect matchings on twice as many labels. -/
abbrev MiddleSubset (n : ℕ) := {S : Finset (Fin (2 * n)) // S.card = n}

/-- The normalized reciprocal-binomial kernel on the middle subset level. -/
def middleSubsetKernel (n : ℕ) : Matrix (MiddleSubset n) (MiddleSubset n) ℚ :=
  Matrix.of fun S T =>
    (-1 : ℚ) ^ (S.val \ T.val).card /
      ((n + 1 : ℚ) * n.choose (S.val \ T.val).card)

theorem middleSubsetKernel_trace (n : ℕ) :
    (middleSubsetKernel n).trace = (catalan n : ℚ) := by
  have hcard : Fintype.card (MiddleSubset n) = n.centralBinom := by
    rw [Fintype.card_finset_len, Fintype.card_fin, Nat.centralBinom_eq_two_mul_choose]
  have hdiv : catalan n * (n + 1) = n.centralBinom := by
    rw [catalan_eq_centralBinom_div, Nat.div_mul_cancel (Nat.succ_dvd_centralBinom n)]
  have hd (S : MiddleSubset n) : middleSubsetKernel n S S = 1 / (n + 1 : ℚ) := by
    simp [middleSubsetKernel]
  rw [Matrix.trace]
  change (∑ S, middleSubsetKernel n S S) = _
  simp only [hd, sum_const, card_univ, nsmul_eq_mul, hcard, ← hdiv, Nat.cast_mul,
    Nat.cast_add, Nat.cast_one]
  field_simp

/-- Expansion over all transversals of an oriented matching. A common scalar shift cancels
on every pair. Taking the two endpoint values in each pair to be zero or one gives the
signed transversal evaluation at each binary state. -/
theorem signed_transversal_shift_sum {R α : Type*} [CommRing R] [Fintype α] [DecidableEq α]
    (x y : α → R) (t : R) :
    (∑ J : Finset α, (∏ i ∈ J, (x i - t)) * ∏ i ∈ Jᶜ, (t - y i)) =
      ∏ i, (x i - y i) := by
  rw [← Fintype.prod_add]
  exact Finset.prod_congr rfl fun i _ => by ring

end MOC
