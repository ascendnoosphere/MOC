import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! The real sign argument for the mixed branch of Zheng's order-four quadratic-ratio pattern.
The two Hermitian polynomials are written in the chart coordinate shifted
by `x / t` and scaled by `t`, so the tested real vector is `(1, 0)`. -/

namespace MOC

private theorem hermitian_form_nonpos {a b c : ℝ} (ha : a < 0)
    (hdet : 0 ≤ a * c - b ^ 2) (s t : ℝ) :
    a + 2 * b * s + c * (s ^ 2 + t ^ 2) ≤ 0 := by
  have hid : a * (a + 2 * b * s + c * (s ^ 2 + t ^ 2)) =
      (a + b * s) ^ 2 + (a * c - b ^ 2) * s ^ 2 + (a * c - b ^ 2 + b ^ 2) * t ^ 2 := by
    ring
  have hnonneg : 0 ≤ a * (a + 2 * b * s + c * (s ^ 2 + t ^ 2)) := by
    rw [hid]
    exact add_nonneg (add_nonneg (sq_nonneg _) (mul_nonneg hdet (sq_nonneg _)))
      (mul_nonneg (add_nonneg hdet (sq_nonneg _)) (sq_nonneg _))
  by_contra! hpos
  exact (not_lt_of_ge hnonneg) (mul_neg_of_neg_of_pos ha hpos)

private theorem hermitian_form_pos {a b c : ℝ} (ha : 0 < a)
    (hdet : 0 < a * c - b ^ 2) (s t : ℝ) :
    0 < a + 2 * b * s + c * (s ^ 2 + t ^ 2) := by
  have hid : a * (a + 2 * b * s + c * (s ^ 2 + t ^ 2)) =
      (a + b * s) ^ 2 + (a * c - b ^ 2) * s ^ 2 + (a * c - b ^ 2 + b ^ 2) * t ^ 2 := by
    ring
  have hpos : 0 < (a + b * s) ^ 2 + (a * c - b ^ 2) * s ^ 2 := by
    by_cases hs : s = 0
    · simpa [hs] using sq_pos_of_pos ha
    · exact add_pos_of_nonneg_of_pos (sq_nonneg _) (mul_pos hdet (sq_pos_of_ne_zero hs))
  apply (mul_pos_iff_of_pos_left ha).mp
  rw [hid]
  exact add_pos_of_pos_of_nonneg hpos (mul_nonneg (add_nonneg hdet.le (sq_nonneg _)) (sq_nonneg _))

/-- The two source equations and two Hermitian identities of the distinct quadratic-ratio pattern
chart force the strict capacity bound for the four-coefficient Gram. -/
theorem fourQuadraticRatio_capacity_of_chart {x t r u a b c d e k : ℝ}
    (hx : 1 < x) (hrt : 0 < r * t) (htu : t * u < 0)
    (hb : 0 ≤ b) (hc : 0 < c) (hd : 0 < d) (he : 0 ≤ e) (hk : 0 ≤ k)
    (ha : a = (x - 1) * c - d) :
    let y := x - 1
    let h := 1 - t
    let H := h + u
    let E := H * (1 - t * x) - h * r * y
    let J := H * (1 - t * x) + h * y
    let L := y - r + u
    let K := t * y * b - x * h * d
    k = h * c - t * (b + d) → E * e = t * y * H * b - J * d →
    (E < 0 → ∃ D₀ D₁ D₂ P₀ P₁ P₂ s v Q : ℝ, 0 < Q ∧
      D₀ + 2 * D₁ * s + D₂ * (s ^ 2 + v ^ 2) = d * Q ∧
      D₀ * D₂ - D₁ ^ 2 = -(r ^ 3) * u * x * y * L * E ∧
      D₀ = r * u * x * y * (h * r - H * y) ∧
      P₀ + 2 * P₁ * s + P₂ * (s ^ 2 + v ^ 2) = K * Q ∧
      P₀ * P₂ - P₁ ^ 2 = -(r ^ 2) * u ^ 2 * x ^ 2 * h * y * L * E ∧
      P₀ = r * u ^ 2 * x ^ 2 * y * (y - h)) →
    d ^ 2 * (a + b + c + d) < a * b * (c - d) := by
  intro y h H E J L K hke hee hforms
  have hx₀ : 0 < x := zero_lt_one.trans hx
  have hy : 0 < y := sub_pos.mpr hx
  have hbd : 0 < b + d := add_pos_of_nonneg_of_pos hb hd
  have ht : 0 < t := by
    by_contra! ht'
    have hr' : r < 0 := by
      by_contra! hr'
      exact (not_lt_of_ge (mul_nonpos_of_nonneg_of_nonpos hr' ht')) hrt
    have hu' : 0 < u := by
      by_contra! hu'
      exact (not_lt_of_ge (mul_nonneg_of_nonpos_of_nonpos ht' hu')) htu
    have hh' : 0 < h := by dsimp only [h]; linarith only [ht']
    have hH' : 0 < H := add_pos hh' hu'
    have htx : 0 < 1 - t * x := by linarith only [mul_nonpos_of_nonpos_of_nonneg ht' hx₀.le]
    have hE' : 0 < E := sub_pos.mpr
      ((mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hh' hr') hy).trans (mul_pos hH' htx))
    have hJ' : 0 < J := add_pos (mul_pos hH' htx) (mul_pos hh' hy)
    have hn : t * y * H * b ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg ht' hy.le) hH'.le) hb
    linarith only [hee, mul_nonneg hE'.le he, hn, mul_pos hJ' hd]
  have hr : 0 < r := (mul_pos_iff_of_pos_right ht).mp hrt
  have hu : u < 0 := by
    by_contra! hu'
    exact (not_lt_of_ge (mul_nonneg ht.le hu')) htu
  have hbound : t * (b + d) ≤ h * c := by linarith only [hke, hk]
  have hh : 0 < h := (mul_pos_iff_of_pos_right hc).mp ((mul_pos ht hbd).trans_le hbound)
  have hK : 0 < K := by
    by_cases hE : 0 ≤ E
    · have hJE : J = E + h * y * (r + 1) := by dsimp only [J, E]; ring
      have hJ : 0 < J := by rw [hJE]; positivity
      have hleft : J * d ≤ t * y * H * b := by linarith only [hee, mul_nonneg hE he]
      have hH : 0 < H := by
        by_contra! hH'
        have hn := mul_nonpos_of_nonpos_of_nonneg
          (mul_nonpos_of_nonneg_of_nonpos (mul_nonneg ht.le hy.le) hH') hb
        linarith only [hleft, hn, mul_pos hJ hd]
      have hJE' : J - x * h * H = -u * y := by dsimp only [J, H, h, y]; ring
      have hJgt : x * h * H < J := by linarith only [hJE', mul_pos (neg_pos.mpr hu) hy]
      apply (mul_pos_iff_of_pos_right hH).mp
      dsimp only [K]
      nlinarith only [hleft, mul_lt_mul_of_pos_right hJgt hd]
    · have hE' : E < 0 := lt_of_not_ge hE
      obtain ⟨D₀, D₁, D₂, P₀, P₁, P₂, s, v, Q, hQ, hD, hdetD, hD₀, hP, hdetP, hP₀⟩ :=
        hforms hE'
      have hL : 0 < L := by
        by_contra! hL'
        have hR : 0 < h * r - H * y := by
          by_contra! hR'
          have hHy : 0 < H * y := by linarith only [hR', mul_pos hh hr]
          have hH := (mul_pos_iff_of_pos_right hy).mp hHy
          have hydiff : 0 ≤ H * y - h * r := by linarith only [hR']
          have hiden : E = H * (h - y) * (1 + y) + y * (H * y - h * r) := by
            dsimp only [E, y, h]
            ring
          have hyh : h < y := by
            by_contra! hyh'
            have hn := add_nonneg
              (mul_nonneg (mul_nonneg hH.le (sub_nonneg.mpr hyh')) (by positivity : 0 ≤ 1 + y))
              (mul_nonneg hy.le hydiff)
            have hEn : 0 ≤ E := hiden.symm ▸ hn
            exact (not_lt_of_ge hEn) hE'
          have hid : h * L = -u * (y - h) + (H * y - h * r) := by dsimp only [L, H]; ring
          have hpos : 0 < h * L := by
            rw [hid]
            exact add_pos_of_pos_of_nonneg (mul_pos (neg_pos.mpr hu) (sub_pos.mpr hyh)) hydiff
          exact (not_lt_of_ge (mul_nonpos_of_nonneg_of_nonpos hh.le hL')) hpos
        have hdn : D₀ < 0 := by
          rw [hD₀]
          exact mul_neg_of_neg_of_pos
            (mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hr hu) hx₀) hy) hR
        have hcoef : 0 ≤ -(r ^ 3) * u * x * y := by
          rw [show -(r ^ 3) * u * x * y = r ^ 3 * (-u) * x * y by ring]
          exact mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg hr.le 3) (neg_nonneg.mpr hu.le)) hx₀.le) hy.le
        have hdet : 0 ≤ D₀ * D₂ - D₁ ^ 2 := by
          rw [hdetD, mul_assoc (-(r ^ 3) * u * x * y)]
          exact mul_nonneg hcoef (mul_nonneg_of_nonpos_of_nonpos hL' hE'.le)
        have hn := hermitian_form_nonpos hdn hdet s v
        rw [hD] at hn
        exact (not_lt_of_ge hn) (mul_pos hd hQ)
      have hyh : h < y := by
        by_contra! hyh'
        have hH : 0 < H := by
          change 0 < h + u
          change 0 < y - r + u at hL
          linarith only [hL, hyh', hr]
        have hid : E = (h - y) * (H + h * y) + h * y * L := by
          dsimp only [E, h, y, H, L]
          ring
        rw [hid] at hE'
        exact (not_lt_of_ge (add_nonneg
          (mul_nonneg (sub_nonneg.mpr hyh') (add_nonneg hH.le (mul_nonneg hh.le hy.le)))
          (mul_nonneg (mul_nonneg hh.le hy.le) hL.le))) hE'
      have hPu := sq_pos_of_ne_zero hu.ne
      have hPpos : 0 < P₀ := by
        rw [hP₀]
        exact mul_pos (mul_pos (mul_pos (mul_pos hr hPu) (sq_pos_of_pos hx₀)) hy) (sub_pos.mpr hyh)
      have hPdet : 0 < P₀ * P₂ - P₁ ^ 2 := by
        rw [hdetP, show -(r ^ 2) * u ^ 2 * x ^ 2 * h * y * L * E =
          r ^ 2 * u ^ 2 * x ^ 2 * h * y * L * (-E) by ring]
        have hnegE := neg_pos.mpr hE'
        positivity
      have hPval := hermitian_form_pos hPpos hPdet s v
      rw [hP] at hPval
      exact (mul_pos_iff_of_pos_right hQ).mp hPval
  have hyden : 0 < y * b * c - x * d * (b + d) := by
    apply (mul_pos_iff_of_pos_left hh).mp
    have hweighted := mul_le_mul_of_nonneg_left hbound (mul_nonneg hy.le hb)
    have hgain := mul_pos hbd hK
    dsimp only [K] at hgain
    nlinarith only [hweighted, hgain]
  have hid : a * b * (c - d) - d ^ 2 * (a + b + c + d) =
      c * (y * b * c - x * d * (b + d)) := by rw [ha]; dsimp only [y]; ring
  apply sub_pos.mp
  rw [hid]
  exact mul_pos hc hyden

/-- A real quadratic evaluated at a complex point, with coefficients listed
in increasing degree. -/
def quadraticRatioQuadraticEval (p : ℝ × ℝ × ℝ) (v : ℂ) : ℂ :=
  (p.1 : ℂ) + (p.2.1 : ℂ) * v + (p.2.2 : ℂ) * v ^ 2

private def quadraticBezout (p q : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  (p.2.1 * q.1 - p.1 * q.2.1, p.2.2 * q.1 - p.1 * q.2.2,
    p.2.2 * q.2.1 - p.2.1 * q.2.2)

theorem quadratic_quotient_im (p q : ℝ × ℝ × ℝ) (v : ℂ)
    (hv : v.im ≠ 0) (hq : quadraticRatioQuadraticEval q v ≠ 0) :
    ((quadraticRatioQuadraticEval p v / quadraticRatioQuadraticEval q v).im / v.im) *
      Complex.normSq (quadraticRatioQuadraticEval q v) =
      let M := quadraticBezout p q
      M.1 + 2 * M.2.1 * v.re + M.2.2 * (v.re ^ 2 + v.im ^ 2) := by
  rw [Complex.div_im]
  have hQ : Complex.normSq (quadraticRatioQuadraticEval q v) ≠ 0 :=
    ne_of_gt (Complex.normSq_pos.mpr hq)
  field_simp [hv, hQ]
  simp only [quadraticBezout, quadraticRatioQuadraticEval, Complex.normSq_apply, pow_two,
    Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, mul_zero, sub_zero, zero_add, add_zero]
  ring

/-- The common quadratic denominator after translating to `t*v - x` and
clearing the factor `t`. -/
def quadraticRatioShiftedDen (x t r u : ℝ) : ℝ × ℝ × ℝ :=
  let y := x - 1
  (u * x * y, u * y + (u - r) * x + t * (r - y), u - r - t)

/-- The quadratic numerator for the difference of quadratic-ratio pattern matching ratios at
indices 2 and 13. -/
def quadraticRatioShiftedNumD (x t r u : ℝ) : ℝ × ℝ × ℝ :=
  let y := x - 1
  let h := 1 - t
  (u * y * h * x * (y - r),
    u * y * (h * y - r) + (u - r) * h * x * (y - r) + t * (r - y) * h * y,
    (u - r) * (h * y - r) - t * h * y)

/-- The quadratic numerator for the quadratic-ratio pattern matching ratio at index 19. -/
def quadraticRatioShiftedNumB (x t r u : ℝ) : ℝ × ℝ × ℝ :=
  let y := x - 1
  let h := 1 - t
  let s₀ := h * u * x ^ 2
  let s₁ := -h * x * (r + t - u) + u * x
  let s₂ := -(r + t - u)
  let Q := quadraticRatioShiftedDen x t r u
  ((r - y) * s₀, (r - y) * s₁ - s₀ + Q.1, (r - y) * s₂ - s₁ + Q.2.1)

set_option maxHeartbeats 4000000 in
/-- Exact determinants and evaluations of the two shifted Hermitian forms.
This supplies the Hermitian witnesses required by the real sign argument. -/
theorem fourQuadraticRatio_capacity_of_quadratic_ratios {x t r u a b c d e k : ℝ} (v : ℂ)
    (hx : 1 < x) (hrt : 0 < r * t) (htu : t * u < 0)
    (hb : 0 ≤ b) (hc : 0 < c) (hd : 0 < d) (he : 0 ≤ e) (hk : 0 ≤ k)
    (ha : a = (x - 1) * c - d) (hv : v.im ≠ 0) :
    let Q := quadraticRatioQuadraticEval (quadraticRatioShiftedDen x t r u) v
    let B := quadraticRatioQuadraticEval (quadraticRatioShiftedNumB x t r u) v
    let D := quadraticRatioQuadraticEval (quadraticRatioShiftedNumD x t r u) v
    let y := x - 1
    let h := 1 - t
    let H := h + u
    let E := H * (1 - t * x) - h * r * y
    let J := H * (1 - t * x) + h * y
    Q ≠ 0 → b = t * ((B / Q).im / v.im) → d = t * ((D / Q).im / v.im) →
    k = h * c - t * (b + d) → E * e = t * y * H * b - J * d →
    d ^ 2 * (a + b + c + d) < a * b * (c - d) := by
  intro Q B D y h H E J hQ hb' hd' hk' he'
  have ht : t ≠ 0 := right_ne_zero_of_mul hrt.ne'
  apply fourQuadraticRatio_capacity_of_chart hx hrt htu hb hc hd he hk ha hk' he'
  intro _
  let p := quadraticBezout (quadraticRatioShiftedNumD x t r u) (quadraticRatioShiftedDen x t r u)
  let q := quadraticBezout (quadraticRatioShiftedNumB x t r u) (quadraticRatioShiftedDen x t r u)
  let P : ℝ × ℝ × ℝ :=
    (t * y * q.1 - x * h * p.1, t * y * q.2.1 - x * h * p.2.1,
      t * y * q.2.2 - x * h * p.2.2)
  let S := Complex.normSq Q / t ^ 2
  have hS : 0 < S := div_pos (Complex.normSq_pos.mpr hQ) (sq_pos_of_ne_zero ht)
  refine ⟨p.1 / t, p.2.1 / t, p.2.2 / t, P.1 / t, P.2.1 / t, P.2.2 / t,
    v.re, v.im, S, hS, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hdform : ((D / Q).im / v.im) * Complex.normSq Q =
        p.1 + 2 * p.2.1 * v.re + p.2.2 * (v.re ^ 2 + v.im ^ 2) :=
      quadratic_quotient_im _ _ v hv hQ
    calc
      _ = (p.1 + 2 * p.2.1 * v.re + p.2.2 * (v.re ^ 2 + v.im ^ 2)) / t := by ring
      _ = (((D / Q).im / v.im) * Complex.normSq Q) / t := by rw [hdform]
      _ = d * S := by dsimp only [S]; rw [hd']; field_simp [ht, hv] <;> ring
  · change _ = -(r ^ 3) * u * x * y * (y - r + u) * E
    dsimp only [p, quadraticBezout, quadraticRatioShiftedDen, quadraticRatioShiftedNumD, y, h, H, E]
    field_simp [ht]
    ring
  · change _ = r * u * x * y * (h * r - H * y)
    dsimp only [p, quadraticBezout, quadraticRatioShiftedDen, quadraticRatioShiftedNumD, y, h, H]
    field_simp [ht]
    ring
  · have hdform : ((D / Q).im / v.im) * Complex.normSq Q =
        p.1 + 2 * p.2.1 * v.re + p.2.2 * (v.re ^ 2 + v.im ^ 2) :=
      quadratic_quotient_im _ _ v hv hQ
    have hbform : ((B / Q).im / v.im) * Complex.normSq Q =
        q.1 + 2 * q.2.1 * v.re + q.2.2 * (v.re ^ 2 + v.im ^ 2) :=
      quadratic_quotient_im _ _ v hv hQ
    have hform : (t * y * ((B / Q).im / v.im) - x * h * ((D / Q).im / v.im)) *
        Complex.normSq Q = P.1 + 2 * P.2.1 * v.re + P.2.2 * (v.re ^ 2 + v.im ^ 2) := by
      dsimp only [P]
      linear_combination (t * y) * hbform - (x * h) * hdform
    calc
      _ = (P.1 + 2 * P.2.1 * v.re + P.2.2 * (v.re ^ 2 + v.im ^ 2)) / t := by ring
      _ = ((t * y * ((B / Q).im / v.im) - x * h * ((D / Q).im / v.im)) *
          Complex.normSq Q) / t := by rw [hform]
      _ = _ := by dsimp only [S]; rw [hb', hd']; field_simp [ht, hv] <;> ring
  · change _ = -(r ^ 2) * u ^ 2 * x ^ 2 * h * y * (y - r + u) * E
    dsimp only [P, p, q, quadraticBezout, quadraticRatioShiftedDen, quadraticRatioShiftedNumD, quadraticRatioShiftedNumB, y, h, H, E]
    field_simp [ht]
    ring
  · change _ = r * u ^ 2 * x ^ 2 * y * (y - h)
    dsimp only [P, p, q, quadraticBezout, quadraticRatioShiftedDen, quadraticRatioShiftedNumD, quadraticRatioShiftedNumB, y, h]
    field_simp [ht]
    ring

end MOC
