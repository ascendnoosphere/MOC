import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

/-! The scalar Hessian obstruction for an extremum of a sum of two scaled unitaries. -/

namespace MOC

private theorem phase_curvature_of_normSq (t : ℝ) (ht : 0 < t) (ht' : t < 1) (p : ℂ)
    (hp : Complex.normSq p = t ^ 2 * Complex.normSq (1 - p)) :
    let c : ℝ := -(t ^ 2) / (1 - t ^ 2)
    Complex.normSq (p - (c : ℂ)) = c * (c - 1) ∧
      p * (1 - p) = ((1 - 2 * p.re : ℝ) : ℂ) * (p - (c : ℂ)) ∧ 0 < 1 - 2 * p.re := by
  intro c
  have ht₂ : 0 < 1 - t ^ 2 := by nlinarith only [mul_pos (sub_pos.mpr ht') (show 0 < 1 + t by linarith)]
  have hc : c * (1 - t ^ 2) = -(t ^ 2) := by
    dsimp only [c]
    exact div_mul_cancel₀ _ ht₂.ne'
  have hp₀ : p ≠ 0 := by
    intro h
    have hzero : (0 : ℝ) = t ^ 2 := by simpa [h] using hp
    exact (pow_ne_zero 2 ht.ne') hzero.symm
  have hn : Complex.normSq p * (1 - t ^ 2) = t ^ 2 * (1 - 2 * p.re) := by
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.one_re,
      Complex.one_im] at hp ⊢
    linear_combination hp
  have hbalance : Complex.normSq p = c * (2 * p.re - 1) := by
    apply mul_right_cancel₀ ht₂.ne'
    rw [show c * (2 * p.re - 1) * (1 - t ^ 2) = c * (1 - t ^ 2) * (2 * p.re - 1) by ring,
      hc, hn]
    ring
  refine ⟨?_, ?_, (pos_of_mul_pos_right ?_ (sq_nonneg t))⟩
  · simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
      Complex.ofReal_im, sub_zero] at hbalance ⊢
    linear_combination hbalance
  · apply Complex.ext
    · simp only [Complex.mul_re, Complex.sub_re, Complex.sub_im, Complex.one_re,
        Complex.one_im, Complex.ofReal_re, Complex.ofReal_im, sub_zero, zero_mul,
        Complex.normSq_apply] at hbalance ⊢
      linear_combination hbalance
    · simp only [Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.one_re,
        Complex.one_im, Complex.ofReal_re, Complex.ofReal_im, sub_zero, zero_mul]
      ring
  · rw [← hn]
    exact mul_pos (Complex.normSq_pos.mpr hp₀) ht₂

private theorem phase_transfer_obstruction (p q ω : ℂ) (a m n : ℝ) (ha : 0 < a)
    (hm : 1 ≤ m) (hn : 1 ≤ n) (hsize : 2 < m + n)
    (hqpos : 0 < 1 - 2 * q.re) (hppos : 0 < 1 - 2 * p.re)
    (hΔ : ω * (p - q) = ((-2 * a : ℝ) : ℂ))
    (hp : (ω * (p * (1 - p))).re = -a * (1 - 2 * p.re))
    (hq : (ω * (q * (1 - q))).re = a * (1 - 2 * q.re))
    (hsplit : 1 < m → 0 ≤ (ω * (p * (1 - p))).re)
    (htransfer : 0 ≤ (ω * (p * (1 - p) / (m : ℂ) + q * (1 - q) / (n : ℂ) +
      (p - q) ^ 2)).re) : False := by
  have hmeq : m = 1 := by
    by_contra hne
    have hle := hsplit (lt_of_le_of_ne hm (Ne.symm hne))
    rw [hp] at hle
    linarith only [hle, mul_pos ha hppos]
  have hnone : 1 < n := by linarith only [hsize, hmeq]
  have hΔ₂ : (ω * (p - q) ^ 2).re = -(2 * a) * (p.re - q.re) := by
    rw [pow_two, ← mul_assoc, hΔ, Complex.re_ofReal_mul, Complex.sub_re]
    ring
  have hre (u : ℂ) : (ω * (u / (n : ℂ))).re = (ω * u).re / n := by
    rw [← mul_div_assoc, div_eq_mul_inv, ← Complex.ofReal_inv, Complex.re_mul_ofReal, div_eq_mul_inv]
  rw [hmeq, Complex.ofReal_one, div_one, mul_add, mul_add, Complex.add_re, Complex.add_re,
    hp, hre, hq, hΔ₂] at htransfer
  have hfactor : -a * (1 - 2 * p.re) + a * (1 - 2 * q.re) / n +
      -(2 * a) * (p.re - q.re) = a * (1 - 2 * q.re) * (n⁻¹ - 1) := by
    simp only [div_eq_mul_inv]
    ring
  rw [hfactor] at htransfer
  exact (not_lt_of_ge htransfer)
    (mul_neg_of_pos_of_neg (mul_pos ha hqpos) (sub_neg.mpr (inv_lt_one_of_one_lt₀ hnone)))

private theorem phase_pair_coefficients (t : ℝ) (ht : 0 < t) (ht' : t < 1)
    (p q ω : ℂ) (hpq : p ≠ q) (hω : ω ≠ 0)
    (hp : Complex.normSq p = t ^ 2 * Complex.normSq (1 - p))
    (hq : Complex.normSq q = t ^ 2 * Complex.normSq (1 - q))
    (hstationary : (ω * p).im = (ω * q).im) :
    ∃ a : ℝ, a ≠ 0 ∧ (0 < 1 - 2 * p.re) ∧ (0 < 1 - 2 * q.re) ∧
      ω * (p - q) = ((-2 * a : ℝ) : ℂ) ∧
      (ω * (p * (1 - p))).re = -a * (1 - 2 * p.re) ∧
      (ω * (q * (1 - q))).re = a * (1 - 2 * q.re) := by
  let c : ℝ := -(t ^ 2) / (1 - t ^ 2)
  obtain ⟨hpCircle, hpCurvature, hpPos⟩ := phase_curvature_of_normSq t ht ht' p hp
  obtain ⟨hqCircle, hqCurvature, hqPos⟩ := phase_curvature_of_normSq t ht ht' q hq
  let x := (ω * (p - (c : ℂ))).re
  let y := (ω * (q - (c : ℂ))).re
  have hIm : (ω * (p - (c : ℂ))).im = (ω * (q - (c : ℂ))).im := by
    simp only [mul_sub, Complex.sub_im, hstationary]
  have hnorm : Complex.normSq (ω * (p - (c : ℂ))) = Complex.normSq (ω * (q - (c : ℂ))) := by
    rw [Complex.normSq_mul, Complex.normSq_mul, hpCircle, hqCircle]
  have hxy : x ≠ y := by
    intro h
    have he := Complex.ext h hIm
    exact hpq (by linear_combination (mul_left_cancel₀ hω he))
  have hadd : x + y = 0 := by
    simp only [Complex.normSq_apply, hIm] at hnorm
    have hzero : (x - y) * (x + y) = 0 := by
      dsimp only [x, y]
      linear_combination hnorm
    exact (mul_eq_zero.mp hzero).resolve_left (sub_ne_zero.mpr hxy)
  have hx : x = -y := eq_neg_of_add_eq_zero_left hadd
  have hcurvP : (ω * (p * (1 - p))).re = x * (1 - 2 * p.re) := by
    rw [hpCurvature, mul_left_comm, Complex.re_ofReal_mul]
    exact mul_comm _ _
  have hcurvQ : (ω * (q * (1 - q))).re = y * (1 - 2 * q.re) := by
    rw [hqCurvature, mul_left_comm, Complex.re_ofReal_mul]
    exact mul_comm _ _
  have hΔ : ω * (p - q) = ((x - y : ℝ) : ℂ) := by
    have hsub : p - q = (p - (c : ℂ)) - (q - (c : ℂ)) := by ring
    rw [hsub, mul_sub]
    apply Complex.ext
    · simp only [Complex.sub_re, Complex.ofReal_re, x, y]
    · simp only [Complex.sub_im, Complex.ofReal_im, hIm, sub_self]
  refine ⟨y, fun h => hxy (by rw [hx, h, neg_zero]), hpPos, hqPos, ?_, ?_, hcurvQ⟩
  · rw [hΔ, hx]
    exact congrArg Complex.ofReal (by ring)
  · simpa only [hx] using hcurvP

/-- Between distinct relative eigenspaces at stationarity the projected
off-block coefficient in the trace Hessian vanishes. -/
theorem re_phase_cross_zero (t : ℝ) (ht : 0 < t) (hlt : t < 1)
    (p q ω : ℂ) (hpq : p ≠ q) (hω : ω ≠ 0)
    (hp : Complex.normSq p = t ^ 2 * Complex.normSq (1 - p))
    (hq : Complex.normSq q = t ^ 2 * Complex.normSq (1 - q))
    (hstationary : (ω * p).im = (ω * q).im) :
    (ω * (p + q - 2 * p * q)).re = 0 := by
  obtain ⟨a, _, _, _, hΔ, hcP, hcQ⟩ := phase_pair_coefficients t ht hlt p q ω hpq hω hp hq hstationary
  have hΔ₂ : (ω * (p - q) ^ 2).re = (-2 * a) * (p.re - q.re) := by
    rw [pow_two, ← mul_assoc, hΔ, Complex.re_ofReal_mul, Complex.sub_re]
  rw [show p + q - 2 * p * q = p * (1 - p) + q * (1 - q) + (p - q) ^ 2 by ring,
    mul_add, mul_add, Complex.add_re, Complex.add_re, hcP, hcQ, hΔ₂]
  ring

/-- Two distinct relative eigenphases cannot pass both types of second
variation in order greater than two. Intra-eigenspace splits give `hsplitP`
and `hsplitQ`. Opposite equal velocities within each eigenspace give `htransfer`. -/
theorem two_phase_quadratic_obstruction (t : ℝ) (ht : 0 < t) (ht' : t < 1)
    (p q ω : ℂ) (hpq : p ≠ q) (hω : ω ≠ 0)
    (hp : Complex.normSq p = t ^ 2 * Complex.normSq (1 - p))
    (hq : Complex.normSq q = t ^ 2 * Complex.normSq (1 - q))
    (hstationary : (ω * p).im = (ω * q).im)
    (m n : ℝ) (hm : 1 ≤ m) (hn : 1 ≤ n) (hsize : 2 < m + n)
    (hsplitP : 1 < m → 0 ≤ (ω * (p * (1 - p))).re)
    (hsplitQ : 1 < n → 0 ≤ (ω * (q * (1 - q))).re)
    (htransfer : 0 ≤ (ω * (p * (1 - p) / (m : ℂ) + q * (1 - q) / (n : ℂ) +
      (p - q) ^ 2)).re) : False := by
  obtain ⟨a, hane, hpPos, hqPos, hΔ, hcP, hcQ⟩ := phase_pair_coefficients t ht ht' p q ω hpq hω hp hq hstationary
  by_cases haPos : 0 < a
  · exact phase_transfer_obstruction p q ω a m n haPos hm hn hsize hqPos hpPos hΔ
      hcP hcQ hsplitP htransfer
  · have hapos' : 0 < -a := neg_pos.mpr (lt_of_le_of_ne (le_of_not_gt haPos) hane)
    have hΔ' : ω * (q - p) = ((-2 * (-a) : ℝ) : ℂ) := by
      rw [show q - p = -(p - q) by ring, mul_neg, hΔ, ← Complex.ofReal_neg]
      exact congrArg Complex.ofReal (by ring)
    have htransfer' : 0 ≤ (ω * (q * (1 - q) / (n : ℂ) + p * (1 - p) / (m : ℂ) +
        (q - p) ^ 2)).re := by
      rw [add_comm (q * (1 - q) / (n : ℂ)), show (q - p) ^ 2 = (p - q) ^ 2 by ring]
      exact htransfer
    exact phase_transfer_obstruction q p ω (-a) n m hapos' hn hm (by rwa [add_comm]) hpPos hqPos hΔ'
      (by simpa only [neg_neg] using hcQ) hcP hsplitQ htransfer'

end MOC
