import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import MOC.TwoValues

/-! The lattice part of the independent-threshold variance argument.
Projection-minor probability measures: R. Lyons,
DOI 10.1007/s10240-003-0016-0. The score/variance identifications for
a unitary are inputs to the last theorem, not consequences of it. -/

open Finset BigOperators

namespace MOC

noncomputable section

/-- Optimal variance lower bound at a mean on the integer lattice. -/
def latticeVariancePenalty (x : ℝ) : ℝ :=
  Int.fract x * (1 - Int.fract x)

theorem latticeVariancePenalty_periodic (x : ℝ) (k : ℤ) :
    latticeVariancePenalty (x + k) = latticeVariancePenalty x := by
  simp [latticeVariancePenalty, Int.fract_add_intCast]

/-- A sum of threshold variances dominates the lattice penalty of the
aggregate mean. There is no joint probability space in this statement. -/
theorem latticeVariancePenalty_add_le (x y : ℝ) :
    latticeVariancePenalty (x + y) ≤ latticeVariancePenalty x + latticeVariancePenalty y := by
  have hx := Int.fract_nonneg x
  have hy := Int.fract_nonneg y
  have hx' := (Int.fract_lt_one x).le
  have hy' := (Int.fract_lt_one y).le
  obtain ⟨z, hz⟩ := Int.fract_add x y
  have hlo : (-1 : ℝ) ≤ z := by
    have h := Int.fract_add_fract_le x y
    linarith
  have hhi : (z : ℝ) ≤ 0 := by
    have h := Int.fract_add_le x y
    linarith
  have hzlo : (-1 : ℤ) ≤ z := by exact_mod_cast hlo
  have hzhi : z ≤ 0 := by exact_mod_cast hhi
  have hz' : z = 0 ∨ z = -1 := by omega
  unfold latticeVariancePenalty
  rcases hz' with h | h
  · rw [h, Int.cast_zero] at hz
    have he : Int.fract (x + y) = Int.fract x + Int.fract y := by linarith
    rw [he]
    nlinarith only [mul_nonneg hx hy]
  · rw [h, Int.cast_neg, Int.cast_one] at hz
    have he : Int.fract (x + y) = Int.fract x + Int.fract y - 1 := by linarith
    rw [he]
    nlinarith only [mul_nonneg (sub_nonneg.mpr hx') (sub_nonneg.mpr hy')]

theorem latticeVariancePenalty_sum_le {ι : Type*} (S : Finset ι) (m : ι → ℝ) :
    latticeVariancePenalty (∑ j ∈ S, m j) ≤ ∑ j ∈ S, latticeVariancePenalty (m j) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [latticeVariancePenalty]
  | insert j S hj ih =>
    rw [sum_insert hj, sum_insert hj]
    exact (latticeVariancePenalty_add_le _ _).trans (add_le_add_left ih _)

/-- Finite positive weights on integer scores force the lattice
variance bound; neither score order nor adjacent-support enumeration
is needed. -/
theorem integer_variance_lower_bound {κ : Type*} [Fintype κ] (w : κ → ℝ) (s : κ → ℤ)
    (hw : ∀ i, 0 ≤ w i) (hs : ∑ i, w i = 1) :
    let m := ∑ i, w i * (s i : ℝ)
    latticeVariancePenalty m ≤ ∑ i, w i * ((s i : ℝ) - m)^2 := by
  intro m
  let k : ℤ := ⌊m⌋
  have hpoint (i : κ) : 0 ≤ ((s i : ℝ) - k) * ((s i : ℝ) - k - 1) := by
    have h : s i ≤ k ∨ k + 1 ≤ s i := by omega
    rcases h with h | h
    · have h' : (s i : ℝ) ≤ k := by exact_mod_cast h
      exact mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)
    · have h' : (k : ℝ) + 1 ≤ s i := by exact_mod_cast h
      exact mul_nonneg (by linarith) (by linarith)
  have hpos := Finset.sum_nonneg
    (s := univ) (fun i _ => mul_nonneg (hw i) (hpoint i))
  have hsum : ∑ i, w i * ((s i : ℝ) - m) = 0 := by
    simp only [mul_sub, sum_sub_distrib, ← sum_mul, hs, one_mul, m, sub_self]
  have hcalc (i : κ) :
      w i * (((s i : ℝ) - k) * ((s i : ℝ) - k - 1)) =
        w i * ((s i : ℝ) - m)^2 +
          (2*(m-k)-1)*(w i*((s i : ℝ)-m)) -
          w i * ((m-k)*(1-(m-k))) := by ring
  simp only [hcalc, sum_sub_distrib, sum_add_distrib, ← mul_sum, hsum, mul_zero, add_zero,
    ← sum_mul, hs, one_mul] at hpos
  exact sub_nonneg.mp hpos

/-- Squaring nonnegative threshold differences after adding them
dominates adding their squares. -/
theorem sum_threshold_sq_le_sq_sum {ι : Type*} (S : Finset ι) (d : ι → ℝ)
    (hd : ∀ j, 0 ≤ d j) :
    ∑ j ∈ S, (d j)^2 ≤ (∑ j ∈ S, d j)^2 := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert j S hj ih =>
    rw [sum_insert hj, sum_insert hj, add_sq]
    have hp : 0 ≤ 2 * d j * ∑ i ∈ S, d i :=
      mul_nonneg (mul_nonneg (by norm_num) (hd j)) (sum_nonneg fun i _ => hd i)
    linarith

/-- Main lattice implication. Each threshold has a normalized positive
minor-weight law, whose scaled integer statistic has the given variance
decomposition over edges. The full variance uses a squared sum over
the thresholds crossing an edge. -/
theorem independent_threshold_variance_lower_bound
    {J E κ : Type*} [Fintype J] [Fintype E] [Fintype κ] [DecidableEq J]
    (crossing : E → Finset J) (c : E → ℝ) (d : J → ℝ)
    (hc : ∀ e, 0 ≤ c e) (hd : ∀ j, 0 ≤ d j)
    (w : J → κ → ℝ) (s : J → κ → ℤ)
    (hw : ∀ j i, 0 ≤ w j i) (hs : ∀ j, ∑ i, w j i = 1)
    (m : J → ℝ) (hm : ∀ j, m j = ∑ i, w j i * (s j i : ℝ))
    (hvar : ∀ j, (∑ i, w j i * ((s j i : ℝ) - m j)^2) =
      ∑ e, if j ∈ crossing e then c e * (d j)^2 else 0)
    (k : ℤ) :
    latticeVariancePenalty ((∑ j, m j) + k) ≤
      ∑ e, c e * (∑ j ∈ crossing e, d j)^2 := by
  rw [latticeVariancePenalty_periodic]
  calc
    _ ≤ ∑ j, latticeVariancePenalty (m j) := latticeVariancePenalty_sum_le univ m
    _ ≤ ∑ j, ∑ e, if j ∈ crossing e then c e * (d j)^2 else 0 := by
      apply sum_le_sum
      intro j _
      rw [← hvar, hm]
      exact integer_variance_lower_bound (w j) (s j) (hw j) (hs j)
    _ = ∑ e, c e * ∑ j ∈ crossing e, (d j)^2 := by
      rw [sum_comm]
      apply sum_congr rfl
      intro e _
      rw [mul_sum]
      rw [← sum_filter]
      simp
    _ ≤ _ := sum_le_sum fun e _ =>
      mul_le_mul_of_nonneg_left (sum_threshold_sq_le_sq_sum _ d hd) (hc e)

private theorem weighted_quadratic_shift {κ : Type*} [Fintype κ]
    (w s : κ → ℝ) (hw : ∑ k, w k = 1) (m l h : ℝ)
    (hm : ∑ k, w k * s k = m) :
    (∑ k, w k * ((s k - l) * (s k - h))) =
      (∑ k, w k * (s k - m)^2) - (m - l) * (h - m) := by
  have hcenter : ∑ k, w k * (s k - m) = 0 := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hw, one_mul, hm, sub_self]
  have he (k : κ) :
      w k * ((s k - l) * (s k - h)) =
        w k * (s k - m)^2 + (2*m - l - h) * (w k * (s k - m)) -
          w k * ((m - l) * (h - m)) := by ring
  simp only [he, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    hcenter, mul_zero, add_zero, ← Finset.sum_mul, hw, one_mul]

/-- Nonnegative weights on finite scores force two variance bounds.
The open interval between `l` and `h` must contain no score, and every
score must lie between `L` and `H`. -/
theorem weighted_score_variance_bounds {κ : Type*} [Fintype κ]
    (w s : κ → ℝ) (hw : ∀ k, 0 ≤ w k) (hsum : ∑ k, w k = 1)
    (m l h L H : ℝ) (hm : ∑ k, w k * s k = m) (hlh : l ≤ h)
    (hgap : ∀ k, s k ≤ l ∨ h ≤ s k) (hrange : ∀ k, L ≤ s k ∧ s k ≤ H) :
    (m - l) * (h - m) ≤ (∑ k, w k * (s k - m)^2) ∧
      (∑ k, w k * (s k - m)^2) ≤ (m - L) * (H - m) := by
  constructor
  · have hnonneg : 0 ≤ ∑ k, w k * ((s k - l) * (s k - h)) := by
      apply Finset.sum_nonneg
      intro k _
      apply mul_nonneg (hw k)
      rcases hgap k with hk | hk
      · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr hk)
          (sub_nonpos.mpr (hk.trans hlh))
      · exact mul_nonneg (sub_nonneg.mpr (hlh.trans hk)) (sub_nonneg.mpr hk)
    rw [weighted_quadratic_shift w s hsum m l h hm] at hnonneg
    exact sub_nonneg.mp hnonneg
  · have hnonpos : (∑ k, w k * ((s k - L) * (s k - H))) ≤ 0 := by
      apply Finset.sum_nonpos
      intro k _
      exact mul_nonpos_of_nonneg_of_nonpos (hw k)
        (mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr (hrange k).1)
          (sub_nonpos.mpr (hrange k).2))
    rw [weighted_quadratic_shift w s hsum m L H hm] at hnonpos
    exact sub_nonpos.mp hnonpos

end
end MOC
