import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! A uniform positive floor on a finite probability law gives a quantitative
support margin in terms of the variation of the projected scores. -/

open BigOperators

namespace MOC

private theorem squared_support_margin_of_centered_scores
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (p w : ι → ℝ) (μ h : ℝ) (hμ : 0 ≤ μ)
    (hw : ∀ i, μ ≤ w i) (hs : ∑ i, w i = 1)
    (hh : ∀ i, p i ≤ h) (hp : ∑ i, p i = 0) :
    μ ^ 2 * (Fintype.card ι : ℝ) * (∑ i, p i ^ 2) ≤
      ((Fintype.card ι : ℝ) - 1) * (h - (∑ i, w i * p i)) ^ 2 := by
  let m : ℝ := Fintype.card ι
  have hm : 1 ≤ m := by
    change (1 : ℝ) ≤ (Fintype.card ι : ℝ)
    exact_mod_cast Nat.succ_le_of_lt (Fintype.card_pos : 0 < Fintype.card ι)
  have hm0 : 0 ≤ m := zero_le_one.trans hm
  have hz (i : ι) : 0 ≤ h - p i := sub_nonneg.mpr (hh i)
  have hsum : (∑ i, (h - p i)) = m * h := by
    simp [Finset.sum_sub_distrib, hp, m, nsmul_eq_mul]
  have hsplit : (∑ i, (h - p i) ^ 2) = m * h ^ 2 + ∑ i, p i ^ 2 := by
    calc
      _ = ∑ i, (h ^ 2 - (2 * h) * p i + p i ^ 2) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hp]
        simp [m, nsmul_eq_mul]
  have hvar : m * (∑ i, p i ^ 2) ≤ (m - 1) * (m * h) ^ 2 := by
    have hsq : (∑ i, (h - p i) ^ 2) ≤ (∑ i, (h - p i)) ^ 2 :=
      Finset.sum_sq_le_sq_sum_of_nonneg (fun i _ => hz i)
    rw [hsplit, hsum] at hsq
    have hmul := mul_le_mul_of_nonneg_left hsq hm0
    nlinarith only [hmul]
  have hgap : μ * (m * h) ≤ h - (∑ i, w i * p i) := by
    calc
      _ = ∑ i, μ * (h - p i) := by rw [← hsum, Finset.mul_sum]
      _ ≤ ∑ i, w i * (h - p i) :=
        Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right (hw i) (hz i))
      _ = _ := by rw [show (∑ i, w i * (h - p i)) = ∑ i, (w i * h - w i * p i) by
                       simp only [mul_sub],
                     Finset.sum_sub_distrib, ← Finset.sum_mul, hs, one_mul]
  have hfloor : 0 ≤ μ * (m * h) := by
    rw [← hsum]
    exact mul_nonneg hμ (Finset.sum_nonneg fun i _ => hz i)
  have hgapSq := (sq_le_sq₀ hfloor (hfloor.trans hgap)).2 hgap
  calc
    _ = μ ^ 2 * (m * (∑ i, p i ^ 2)) := by ring
    _ ≤ μ ^ 2 * ((m - 1) * (m * h) ^ 2) :=
      mul_le_mul_of_nonneg_left hvar (sq_nonneg _)
    _ = (m - 1) * (μ * (m * h)) ^ 2 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hgapSq (sub_nonneg.mpr hm)

/-- A probability floor `μ` yields a lower bound on the squared support
gap. The spread is the sum of squared deviations from the arithmetic mean. -/
theorem squared_support_margin_of_weight_floor
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (p w : ι → ℝ) (μ h : ℝ) (hμ : 0 ≤ μ)
    (hw : ∀ i, μ ≤ w i) (hs : ∑ i, w i = 1)
    (hh : ∀ i, p i ≤ h) :
    μ ^ 2 * (Fintype.card ι : ℝ) *
        (∑ i, (p i - (∑ j, p j) / (Fintype.card ι : ℝ)) ^ 2) ≤
      ((Fintype.card ι : ℝ) - 1) * (h - (∑ i, w i * p i)) ^ 2 := by
  let m : ℝ := Fintype.card ι
  let c : ℝ := (∑ j, p j) / m
  have hm : m ≠ 0 := by
    change (Fintype.card ι : ℝ) ≠ 0
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card ι ≠ 0)
  have hc : m * c = ∑ i, p i := by
    rw [show c = (∑ i, p i) / m from rfl, ← mul_div_assoc, mul_div_cancel_left₀ _ hm]
  have hp : (∑ i, (p i - c)) = 0 := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    change (∑ i, p i) - m * c = 0
    rw [hc, sub_self]
  have hweighted : h - c - (∑ i, w i * (p i - c)) = h - (∑ i, w i * p i) := by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hs, one_mul]
    ring
  simpa only [hweighted, c, m] using
    squared_support_margin_of_centered_scores (fun i => p i - c) w μ (h - c)
      hμ hw hs (fun i => sub_le_sub_right (hh i) c) hp

/-- The determinant of the planar score covariance gives a common squared
margin for all unit directions after dividing by its trace. The coordinates
`p` and `q` are centered at their arithmetic means. -/
theorem squared_support_margin_of_planar_covariance
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (p q w : ι → ℝ) (μ x y h : ℝ)
    (hμ : 0 ≤ μ) (hw : ∀ i, μ ≤ w i) (hs : ∑ i, w i = 1)
    (hh : ∀ i, x * p i + y * q i ≤ h) (hp : ∑ i, p i = 0) (hq : ∑ i, q i = 0) :
    let A := ∑ i, p i ^ 2
    let B := ∑ i, p i * q i
    let C := ∑ i, q i ^ 2
    μ ^ 2 * (Fintype.card ι : ℝ) * (A * C - B ^ 2) * (x ^ 2 + y ^ 2) ≤
      (A + C) * ((Fintype.card ι : ℝ) - 1) * (h - (∑ i, w i * (x * p i + y * q i))) ^ 2 := by
  dsimp only
  let A := ∑ i, p i ^ 2
  let B := ∑ i, p i * q i
  let C := ∑ i, q i ^ 2
  let t (i : ι) := x * p i + y * q i
  have ht : ∑ i, t i = 0 := by
    simp only [t, Finset.sum_add_distrib, ← Finset.mul_sum, hp, hq, mul_zero, add_zero]
  have hvar : (∑ i, t i ^ 2) = A * x ^ 2 + 2 * B * x * y + C * y ^ 2 := by
    calc
      _ = ∑ i, (x ^ 2 * p i ^ 2 + (2 * x * y) * (p i * q i) + y ^ 2 * q i ^ 2) := by
        apply Finset.sum_congr rfl
        intro i _
        dsimp only [t]
        ring
      _ = _ := by
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum, A, B, C]
        ring
  have htrace : 0 ≤ A + C :=
    add_nonneg (Finset.sum_nonneg fun i _ => sq_nonneg (p i))
      (Finset.sum_nonneg fun i _ => sq_nonneg (q i))
  have hdir : (A * C - B ^ 2) * (x ^ 2 + y ^ 2) ≤ (A + C) * (∑ i, t i ^ 2) := by
    rw [hvar]
    have hid : (A + C) * (A * x ^ 2 + 2 * B * x * y + C * y ^ 2) =
        (A * C - B ^ 2) * (x ^ 2 + y ^ 2) + (A * x + B * y) ^ 2 + (B * x + C * y) ^ 2 := by
      ring
    rw [hid]
    exact (le_add_of_nonneg_right (sq_nonneg _)).trans (le_add_of_nonneg_right (sq_nonneg _))
  have hmargin := squared_support_margin_of_centered_scores t w μ h hμ hw hs hh ht
  let m : ℝ := Fintype.card ι
  have hm : 0 ≤ μ ^ 2 * m := mul_nonneg (sq_nonneg _) (Nat.cast_nonneg _)
  change μ ^ 2 * m * (A * C - B ^ 2) * (x ^ 2 + y ^ 2) ≤
    (A + C) * (m - 1) * (h - (∑ i, w i * t i)) ^ 2
  calc
    _ = (μ ^ 2 * m) * ((A * C - B ^ 2) * (x ^ 2 + y ^ 2)) := by ring
    _ ≤ (μ ^ 2 * m) * ((A + C) * (∑ i, t i ^ 2)) := mul_le_mul_of_nonneg_left hdir hm
    _ = (A + C) * (μ ^ 2 * m * (∑ i, t i ^ 2)) := by ring
    _ ≤ (A + C) * ((m - 1) * (h - (∑ i, w i * t i)) ^ 2) :=
      mul_le_mul_of_nonneg_left hmargin htrace
    _ = _ := by ring

end MOC
