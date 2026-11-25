import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import MOC.FourT18T20Minor

/-! A rational squared-norm certificate for the two T20 source ratios. -/

namespace MOC

noncomputable section

private def realQuadratic (a b c : ℝ) (q : ℂ) : ℂ :=
  (a : ℂ) * (q * q) + (b : ℂ) * q + (c : ℂ)

set_option maxHeartbeats 1000000 in
private theorem quadratic_ratio_certificate (a b c A B C : ℝ) (q : ℂ)
    (hn : realQuadratic a b c q ≠ 0) :
    let d := a * B - A * b
    let e := a * C - A * c
    (-a * d) * (-(realQuadratic A B C q / realQuadratic a b c q).im *
        Complex.normSq (realQuadratic a b c q)) =
      q.im * (-a * Complex.normSq ((d : ℂ) * q + (e : ℂ)) +
        (a * e ^ 2 - b * d * e + c * d ^ 2)) := by
  dsimp only
  have hden : Complex.normSq (realQuadratic a b c q) ≠ 0 :=
    (Complex.normSq_pos.mpr hn).ne'
  rw [Complex.div_im]
  field_simp [hden]
  simp only [realQuadratic, Complex.normSq_apply, Complex.mul_re, Complex.mul_im,
    Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
    Complex.ofReal_re, Complex.ofReal_im]
  ring

private theorem quadratic_ratio_pos (a b c A B C : ℝ) (q : ℂ) (μ : ℝ)
    (ha : a < 0) (hd : 0 < a * B - A * b)
    (hc : 0 < a * (a * C - A * c) ^ 2 - b * (a * B - A * b) * (a * C - A * c) +
      c * (a * B - A * b) ^ 2)
    (hn : realQuadratic a b c q ≠ 0) (hμ : 0 < μ * q.im) :
    0 < -μ * (realQuadratic A B C q / realQuadratic a b c q).im := by
  let d := a * B - A * b
  let e := a * C - A * c
  have h := quadratic_ratio_certificate a b c A B C q hn
  change (-a * d) * (-(realQuadratic A B C q / realQuadratic a b c q).im *
    Complex.normSq (realQuadratic a b c q)) = _ at h
  have ht : (-a * d) * ((-μ * (realQuadratic A B C q / realQuadratic a b c q).im) *
      Complex.normSq (realQuadratic a b c q)) =
      (μ * q.im) * (-a * Complex.normSq ((d : ℂ) * q + (e : ℂ)) +
        (a * e ^ 2 - b * d * e + c * d ^ 2)) := by
    linear_combination μ * h
  have hpos : 0 < (-a * d) * ((-μ * (realQuadratic A B C q / realQuadratic a b c q).im) *
      Complex.normSq (realQuadratic a b c q)) := by
    rw [ht]
    exact mul_pos hμ (add_pos_of_nonneg_of_pos
      (mul_nonneg (neg_nonneg.mpr ha.le) (Complex.normSq_nonneg _)) hc)
  exact pos_of_mul_pos_left
    (pos_of_mul_pos_right hpos (mul_nonneg (neg_nonneg.mpr ha.le) hd.le))
    (Complex.normSq_nonneg _)

/-- The common denominator of the two T20 obstruction ratios. -/
def fourT20QuadraticDenominator (h k l : ℝ) (q : ℂ) : ℂ :=
  realQuadratic (h - 1) (-h * k - h - k * l + k + l) (h * k) q

/-- In the supported T20 sign region the quadratic has no nonreal zero. -/
theorem fourT20QuadraticDenominator_ne_zero (h k l : ℝ) (q : ℂ)
    (hh : h < 1) (hk : k < 0) (hl : 1 < l) (hq : q.im ≠ 0) :
    fourT20QuadraticDenominator h k l q ≠ 0 := by
  let a := h - 1
  let b := -h * k - h - k * l + k + l
  let c := h * k
  let J := realQuadratic a b c q
  change J ≠ 0
  intro hz
  have hJi : J.im = (2 * a * q.re + b) * q.im := by
    simp only [J, realQuadratic, Complex.mul_re, Complex.mul_im, Complex.add_im,
      Complex.ofReal_re, Complex.ofReal_im]
    ring
  have hi := congrArg Complex.im hz
  rw [hJi, Complex.zero_im] at hi
  have hcrit : 2 * a * q.re + b = 0 := (mul_eq_zero.mp hi).resolve_right hq
  have hJr : J.re = -(k - 1) * (l - 1) - a * ((q.re - 1) ^ 2 + q.im ^ 2) := by
    simp only [J, realQuadratic, Complex.mul_re, Complex.mul_im, Complex.add_re,
      Complex.ofReal_re, Complex.ofReal_im]
    dsimp only [a, b, c] at hcrit ⊢
    linear_combination (q.re - 1) * hcrit
  have hpos : 0 < J.re := by
    rw [hJr, sub_eq_add_neg, ← neg_mul]
    exact add_pos_of_pos_of_nonneg
      (mul_pos (neg_pos.mpr (sub_neg.mpr (hk.trans zero_lt_one))) (sub_pos.mpr hl))
      (mul_nonneg (neg_nonneg.mpr (sub_nonpos.mpr hh.le)) (add_nonneg (sq_nonneg _) (sq_nonneg _)))
  simpa only [hz, Complex.zero_re, lt_irrefl] using hpos

set_option maxHeartbeats 1000000 in
/-- In the nonreal T20 sign region, both source ratios have positive support
projection. After clearing denominators, each is a sum of a squared norm and a
positive polynomial in the real parameters. -/
theorem fourT20_obstruction_ratios_pos (h k l : ℝ) (q : ℂ) (μ : ℝ)
    (hh : 0 < h) (hh1 : h < 1) (hk : k < 0) (hl : 1 < l)
    (hμ : 0 < μ * q.im) :
    let u := 1 + l * (k - 1)
    0 < -μ * ((((h * k + u - k : ℝ) : ℂ) * q - ((h * k : ℝ) : ℂ)) /
      fourT20QuadraticDenominator h k l q).im ∧
    0 < -μ * (((q - (k : ℂ)) * ((u : ℂ) * q - (k : ℂ))) /
      fourT20QuadraticDenominator h k l q).im := by
  let u := 1 + l * (k - 1)
  let a := h - 1
  let b := -h * k - h - k * l + k + l
  let c := h * k
  change 0 < -μ * ((((h * k + u - k : ℝ) : ℂ) * q - ((h * k : ℝ) : ℂ)) /
      realQuadratic a b c q).im ∧
    0 < -μ * (((q - (k : ℂ)) * ((u : ℂ) * q - (k : ℂ))) /
      realQuadratic a b c q).im
  have ha : a < 0 := sub_neg.mpr hh1
  have hH : 0 < 1 - h := sub_pos.mpr hh1
  have hK : 0 < -k := neg_pos.mpr hk
  have hK1 : 0 < 1 - k := sub_pos.mpr (hk.trans zero_lt_one)
  have hL : 0 < l - 1 := sub_pos.mpr hl
  have hL0 : 0 < l := zero_lt_one.trans hl
  have hq : q.im ≠ 0 := (mul_ne_zero_iff.mp hμ.ne').2
  have hJ := fourT20QuadraticDenominator_ne_zero h k l q hh1 hk hl hq
  constructor
  · have hNum : ((h * k + u - k : ℝ) : ℂ) * q - ((h * k : ℝ) : ℂ) =
        realQuadratic 0 (h * k + u - k) (-h * k) q := by
      unfold realQuadratic
      push_cast
      ring
    rw [hNum]
    apply quadratic_ratio_pos a b c 0 (h * k + u - k) (-h * k) q μ ha _ _ hJ hμ
    · have he : a * (h * k + u - k) - 0 * b =
          (1 - h) * (h * (-k) + (1 - k) * (l - 1)) := by dsimp only [a, u]; ring
      rw [he]
      exact mul_pos hH (add_pos (mul_pos hh hK) (mul_pos hK1 hL))
    · let d := a * (h * k + u - k) - 0 * b
      let e := a * (-h * k) - 0 * c
      change 0 < a * e ^ 2 - b * d * e + c * d ^ 2
      have he : a * e ^ 2 - b * d * e + c * d ^ 2 =
          h * (-k) * (1 - h) ^ 3 * (1 - k) * (l - 1) := by
        dsimp only [a, b, c, d, e, u]
        ring
      rw [he]
      exact mul_pos (mul_pos (mul_pos (mul_pos hh hK) (pow_pos hH 3)) hK1) hL
  · have hNum : (q - (k : ℂ)) * ((u : ℂ) * q - (k : ℂ)) =
        realQuadratic u (-k * (u + 1)) (k ^ 2) q := by
      unfold realQuadratic
      push_cast
      ring
    rw [hNum]
    apply quadratic_ratio_pos a b c u (-k * (u + 1)) (k ^ 2) q μ ha _ _ hJ hμ
    · have he : a * (-k * (u + 1)) - u * b =
          (1 - h) * (1 - k) * (l - 1) + (-k * l + l - 1) ^ 2 := by
        dsimp only [a, b, u]
        ring
      rw [he]
      exact add_pos_of_pos_of_nonneg (mul_pos (mul_pos hH hK1) hL) (sq_nonneg _)
    · let d := a * (-k * (u + 1)) - u * b
      let e := a * k ^ 2 - u * c
      change 0 < a * e ^ 2 - b * d * e + c * d ^ 2
      have he : a * e ^ 2 - b * d * e + c * d ^ 2 =
          k ^ 2 * l ^ 2 * (1 - h) ^ 2 * (1 - k) ^ 3 * (l - 1) := by
        dsimp only [a, b, c, d, e, u]
        ring
      rw [he]
      exact mul_pos (mul_pos (mul_pos (mul_pos (sq_pos_of_ne_zero hk.ne) (pow_pos hL0 2))
        (pow_pos hH 2)) (pow_pos hK1 3)) hL

/-- The rational T20 source identities and sign region certify the unitary
determinant support inequality. -/
theorem fourT20_support_of_quadratic_obstructions (a b : Fin 4 → ℂ) (η : ℂ) (H : ℝ)
    (hn : ∀ i, H ≤ (η * matchingProduct a b (fourPerm i).symm).re)
    (hc : ∀ i ∈ fourT20ContactIndices, (η * matchingProduct a b (fourPerm i).symm).re = H)
    (U : Matrix (Fin 4) (Fin 4) ℂ) (hU : IsUnitary U)
    (h k l x μ : ℝ) (q : ℂ) (hh : 0 < h) (hh1 : h < 1) (hk : k < 0) (hl : 1 < l)
    (hx : x < 0) (hμ : 0 < μ * q.im) :
    let u := 1 + l * (k - 1)
    let J := fourT20QuadraticDenominator h k l q
    let g (i : Fin 24) := (η * matchingProduct a b (fourPerm i).symm).re - H
    g 3 - g 2 + g 18 = (1 - x) * l *
      (-μ * ((((h * k + u - k : ℝ) : ℂ) * q - ((h * k : ℝ) : ℂ)) / J).im) →
    g 13 - g 3 = -(h * (1 - x)) / (k - 1) *
      (-μ * (((q - (k : ℂ)) * ((u : ℂ) * q - (k : ℂ))) / J).im) →
    H ≤ (η * determinantValue a b U).re := by
  dsimp only
  intro hA hB
  obtain ⟨hSA, hSB⟩ := fourT20_obstruction_ratios_pos h k l q μ hh hh1 hk hl hμ
  have hx1 : 0 < 1 - x := sub_pos.mpr (hx.trans zero_lt_one)
  have hl0 : 0 < l := zero_lt_one.trans hl
  have hk1 : k - 1 < 0 := sub_neg.mpr (hk.trans zero_lt_one)
  apply fourT20_support_of_two_inequalities a b η H hn hc U hU
  · dsimp only
    rw [hA]
    exact (mul_pos (mul_pos hx1 hl0) hSA).le
  · dsimp only
    rw [hB]
    exact (mul_pos (div_pos_of_neg_of_neg (neg_neg_of_pos (mul_pos hh hx1)) hk1) hSB).le

end

end MOC
