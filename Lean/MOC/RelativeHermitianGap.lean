import MOC.RelativeUnitaryGram
import Mathlib.Data.Complex.Norm

/-! The Hermitian and skew-Hermitian parts control the relative Gram defect. -/

open BigOperators Matrix
open scoped ComplexConjugate

namespace MOC

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem normSq_sub_eq_re_hermitian_product (u v : ℂ) :
    Complex.normSq u - Complex.normSq v =
      ((u - conj v) * conj (u + conj v)).re := by
  simp only [Complex.normSq_apply, Complex.mul_re, Complex.sub_re, Complex.sub_im,
    Complex.add_re, Complex.add_im, Complex.conj_re, Complex.conj_im]
  ring

/-- Each row and column squared-norm defect requires a product of off-diagonal
Hermitian and skew-Hermitian entries of the relative matrix. -/
theorem relative_energy_defect_le_hermitian_skew (W : Matrix ι ι ℂ) (i : ι) :
    |(∑ j, Complex.normSq (W j i)) - ∑ j, Complex.normSq (W i j)| ≤
      ∑ j ∈ Finset.univ.erase i,
        ‖W j i - conj (W i j)‖ * ‖W j i + conj (W i j)‖ := by
  rw [← Finset.sum_sub_distrib,
    ← Finset.sum_erase_add _ _ (Finset.mem_univ i), sub_self, add_zero]
  simp_rw [normSq_sub_eq_re_hermitian_product]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  simpa only [norm_mul, Complex.norm_conj] using
    (Complex.abs_re_le_norm ((W j i - conj (W i j)) *
      conj (W j i + conj (W i j))))

/-- A nonzero relative entry joining two unequal Gram levels forces a quantitative
contribution from the off-diagonal Hermitian and skew-Hermitian parts. The
weight can be centered at any `r` because the total row and column defect vanishes. -/
theorem relative_gram_edge_le_hermitian_skew (a : ι → ℂ) (W : Matrix ι ι ℂ) (r : ℝ)
    (hB : IsStarNormal (diagonal a * W)) (i j : ι) :
    Complex.normSq (W j i) * (Complex.normSq (a i) - Complex.normSq (a j)) ^ 2 ≤
      ∑ k, |(Complex.normSq (a k)) ^ 2 - r| *
        (∑ l ∈ Finset.univ.erase k,
          ‖W l k - conj (W k l)‖ * ‖W l k + conj (W k l)‖) := by
  let E (k l : ι) := Complex.normSq (W l k) *
    (Complex.normSq (a k) - Complex.normSq (a l)) ^ 2
  have hn (k l : ι) : 0 ≤ E k l := mul_nonneg (Complex.normSq_nonneg _) (sq_nonneg _)
  have he : E i j ≤ ∑ k, ∑ l, E k l :=
    (Finset.single_le_sum (fun l _ => hn i l) (Finset.mem_univ j)).trans
      (Finset.single_le_sum (fun k _ => Finset.sum_nonneg fun l _ => hn k l) (Finset.mem_univ i))
  dsimp only [E] at he
  rw [relative_modulus_energy_eq_row_column_defect a W hB] at he
  let e (k : ι) := (∑ l, Complex.normSq (W l k)) - ∑ l, Complex.normSq (W k l)
  have hsum : ∑ k, e k = 0 := by
    dsimp only [e]
    rw [Finset.sum_sub_distrib]
    exact sub_eq_zero.mpr (Finset.sum_comm (f := fun k l => Complex.normSq (W l k)))
  have hcenter : (∑ k, (Complex.normSq (a k)) ^ 2 * e k) =
      ∑ k, ((Complex.normSq (a k)) ^ 2 - r) * e k := by
    simp only [sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum, hsum, mul_zero, sub_zero]
  rw [hcenter] at he
  refine he.trans (Finset.sum_le_sum fun k _ => ?_)
  calc
    _ ≤ |((Complex.normSq (a k)) ^ 2 - r) * e k| := le_abs_self _
    _ = |(Complex.normSq (a k)) ^ 2 - r| * |e k| := abs_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left (relative_energy_defect_le_hermitian_skew W k) (abs_nonneg _)

omit [DecidableEq ι] in
/-- The Gram energy of a balanced real array is the pairing of its level
differences with its weighted row and column exchange. For a normal `B`,
take `m i j = ‖B i j‖²` and `q i = ‖a i‖²`. The exchange is then the
difference of squared moduli of opposite entries of `B * (diagonal a)ᴴ`. -/
theorem gram_energy_eq_weighted_entry_exchange (q : ι → ℝ) (m : ι → ι → ℝ)
    (hm : ∀ i, (∑ j, m i j) = ∑ j, m j i) :
    (∑ i, ∑ j, m i j * (q i - q j) ^ 2) =
      ∑ i, ∑ j, (q i - q j) * (q i * m j i - q j * m i j) := by
  have hbal : (∑ i, ∑ j, q i ^ 2 * m i j) = ∑ i, ∑ j, q i ^ 2 * m j i := by
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.mul_sum, ← Finset.mul_sum, hm i]
  have hswap : (∑ i, ∑ j, (q i * q j) * m j i) = ∑ i, ∑ j, (q i * q j) * m i j := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [mul_comm (q j) (q i)]
  calc
    _ = ∑ i, ∑ j, ((q i - q j) * (q i * m j i - q j * m i j) +
          (q i ^ 2 * m i j - q i ^ 2 * m j i) - ((q i * q j) * m i j - (q i * q j) * m j i)) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = _ := by
      simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, hbal, hswap, sub_self, add_zero, sub_zero]

end MOC
