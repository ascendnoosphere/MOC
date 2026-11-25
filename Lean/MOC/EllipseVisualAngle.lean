import MOC.MobiusCircleDefect
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity

/-! Bounds on the visual angle of a subinterval of the focal segment of a
confocal ellipse, using dot products instead of an inverse trigonometric
parameter. -/

namespace MOC

private theorem chordDot_re (Z : ℂ) (s t : ℝ) :
    ((Z - (s : ℂ)) * star (Z - (t : ℂ))).re =
      (Z.re - s) * (Z.re - t) + Z.im ^ 2 := by
  simp only [Complex.star_def, Complex.mul_re, Complex.sub_re, Complex.sub_im,
    Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im, sub_zero]
  ring

private theorem chordDot_im (Z : ℂ) (s t : ℝ) :
    ((Z - (s : ℂ)) * star (Z - (t : ℂ))).im = Z.im * (s - t) := by
  simp only [Complex.star_def, Complex.mul_im, Complex.sub_re, Complex.sub_im,
    Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im, sub_zero]
  ring

private theorem sq_norm_coordinates (z : ℂ) : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
  rw [Complex.sq_norm]
  simp only [Complex.normSq_apply, pow_two]

/- For two complex numbers with the same imaginary part, the cosine of
their angle to the real axis increases with their real part. -/
private theorem normalized_re_le_of_im_eq (P Q : ℂ)
    (him : P.im = Q.im) (hre : P.re ≤ Q.re) :
    P.re * ‖Q‖ ≤ Q.re * ‖P‖ := by
  have hdiff : (Q.re * ‖P‖) ^ 2 - (P.re * ‖Q‖) ^ 2 =
      (Q.re ^ 2 - P.re ^ 2) * P.im ^ 2 := by
    rw [mul_pow, mul_pow, sq_norm_coordinates P, sq_norm_coordinates Q, ← him]
    ring
  by_cases hp : 0 ≤ P.re
  · have hq := hp.trans hre
    apply (sq_le_sq₀ (mul_nonneg hp (norm_nonneg Q)) (mul_nonneg hq (norm_nonneg P))).mp
    linarith only [hdiff, mul_nonneg
      (sub_nonneg.mpr ((sq_le_sq₀ hp hq).mpr hre)) (sq_nonneg P.im)]
  by_cases hq : 0 ≤ Q.re
  · exact (mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hp) (norm_nonneg Q)).trans
      (mul_nonneg hq (norm_nonneg P))
  have hpn := le_of_not_ge hp
  have hqn := le_of_not_ge hq
  have hneg := (sq_le_sq₀
    (neg_nonneg.mpr (mul_nonpos_of_nonpos_of_nonneg hqn (norm_nonneg P)))
    (neg_nonneg.mpr (mul_nonpos_of_nonpos_of_nonneg hpn (norm_nonneg Q)))).mp
  have hsq : (- (Q.re * ‖P‖)) ^ 2 ≤ (- (P.re * ‖Q‖)) ^ 2 := by
    rw [neg_sq, neg_sq]
    linarith only [hdiff, mul_nonpos_of_nonpos_of_nonneg
      (sub_nonpos.mpr (by simpa only [neg_sq] using
        (sq_le_sq₀ (neg_nonneg.mpr hqn) (neg_nonneg.mpr hpn)).mpr (neg_le_neg hre)))
      (sq_nonneg P.im)]
  exact neg_le_neg_iff.mp (hneg hsq)

private theorem focal_distance (A B : ℝ) (Z : ℂ) (e : ℝ)
    (hA : 0 < A) (hB : 0 < B) (hfocus : A ^ 2 = B ^ 2 + 4)
    (hellipse : (Z.re / A) ^ 2 + (Z.im / B) ^ 2 = 1) (he : e ^ 2 = 4) :
    ‖Z - (e : ℂ)‖ = A - e * (Z.re / A) := by
  let x := Z.re / A
  let y := Z.im / B
  have hre : Z.re = A * x := by dsimp only [x]; field_simp [hA.ne'] <;> ring
  have him : Z.im = B * y := by dsimp only [y]; field_simp [hB.ne'] <;> ring
  have hxy : x ^ 2 + y ^ 2 = 1 := hellipse
  have hprod : (e * x) ^ 2 ≤ 4 := by
    rw [mul_pow, he]
    linarith only [hxy, sq_nonneg y]
  have hpos : 0 ≤ A - e * x := by
    have hlt : (e * x) ^ 2 < A ^ 2 := by linarith only [hprod, hfocus, sq_pos_of_pos hB]
    by_contra hn
    have hh := (sq_le_sq₀ hA.le (by linarith : 0 ≤ e * x)).mpr
      (by linarith : A ≤ e * x)
    exact (not_lt_of_ge hh) hlt
  have hsq : ‖Z - (e : ℂ)‖ ^ 2 = (A - e * x) ^ 2 := by
    rw [sq_norm_coordinates, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
      Complex.ofReal_im, sub_zero, hre, him]
    linear_combination B ^ 2 * hxy + (x ^ 2 - 1) * hfocus + (1 - x ^ 2) * he
  exact le_antisymm
    ((sq_le_sq₀ (norm_nonneg _) hpos).mp hsq.le)
    ((sq_le_sq₀ hpos (norm_nonneg _)).mp hsq.ge)

/-- The cosine of the angle subtended by any subinterval of the focal
segment is at least the minimum cosine for the entire focal segment. -/
theorem confocal_chord_cosine_bound (A B : ℝ) (Z : ℂ) (s t : ℝ)
    (hA : 0 < A) (hB : 0 < B) (hfocus : A ^ 2 = B ^ 2 + 4)
    (hellipse : (Z.re / A) ^ 2 + (Z.im / B) ^ 2 = 1)
    (hs₀ : -2 ≤ s) (hs₁ : s ≤ 2) (ht₀ : -2 ≤ t) (ht₁ : t ≤ 2) :
    let V := (Z - (s : ℂ)) * star (Z - (t : ℂ))
    (B ^ 2 - 4) * ‖V‖ ≤ A ^ 2 * V.re := by
  let F := (Z - ((-2 : ℝ) : ℂ)) * star (Z - ((2 : ℝ) : ℂ))
  let x := Z.re / A
  let y := Z.im / B
  have hre : Z.re = A * x := by dsimp only [x]; field_simp [hA.ne'] <;> ring
  have him : Z.im = B * y := by dsimp only [y]; field_simp [hB.ne'] <;> ring
  have hxy : x ^ 2 + y ^ 2 = 1 := hellipse
  have hF : ‖F‖ = A ^ 2 - 4 * x ^ 2 := by
    change ‖(Z - ((-2 : ℝ) : ℂ)) * star (Z - ((2 : ℝ) : ℂ))‖ = _
    rw [Complex.norm_mul, Complex.star_def, Complex.norm_conj,
      focal_distance A B Z (-2) hA hB hfocus hellipse (by norm_num),
      focal_distance A B Z 2 hA hB hfocus hellipse (by norm_num)]
    change (A - (-2) * x) * (A - 2 * x) = _
    ring
  have hFre : F.re = 2 * B ^ 2 - ‖F‖ := by
    change ((Z - ((-2 : ℝ) : ℂ)) * star (Z - ((2 : ℝ) : ℂ))).re = _
    rw [chordDot_re, hF, hre, him]
    linear_combination B ^ 2 * hxy + (x ^ 2 + 1) * hfocus
  have hFpos : 0 < ‖F‖ := by
    rw [hF]
    linarith only [hfocus, hxy, sq_nonneg y, sq_pos_of_pos hB]
  have hFbound : (B ^ 2 - 4) * ‖F‖ ≤ A ^ 2 * F.re := by
    rw [hFre]
    have hh := mul_le_mul_of_nonneg_left
      (show ‖F‖ ≤ A ^ 2 by rw [hF]; linarith only [sq_nonneg x]) (sq_nonneg B)
    nlinarith only [hh, congrArg (fun z : ℝ => z * ‖F‖) hfocus]
  suffices hordered : ∀ u v : ℝ, -2 ≤ u → u ≤ v → v ≤ 2 →
      (B ^ 2 - 4) * ‖(Z - (u : ℂ)) * star (Z - (v : ℂ))‖ ≤
        A ^ 2 * ((Z - (u : ℂ)) * star (Z - (v : ℂ))).re by
    by_cases hst : s ≤ t
    · exact hordered s t hs₀ hst ht₁
    · have h := hordered t s ht₀ (le_of_not_ge hst) hs₁
      dsimp only
      rw [chordDot_re, Complex.norm_mul, Complex.star_def, Complex.norm_conj]
      rw [chordDot_re, Complex.norm_mul, Complex.star_def, Complex.norm_conj,
        mul_comm ‖Z - (t : ℂ)‖,
        mul_comm (Z.re - t) (Z.re - s)] at h
      exact h
  intro u v hu huv hv
  let V := (Z - (u : ℂ)) * star (Z - (v : ℂ))
  let C := (Z - ((-2 : ℝ) : ℂ)) * star (Z - (v : ℂ))
  have hVr : V.re = (Z.re - u) * (Z.re - v) + Z.im ^ 2 := chordDot_re Z u v
  have hCr : C.re = (Z.re - (-2)) * (Z.re - v) + Z.im ^ 2 := chordDot_re Z (-2) v
  have hFr : F.re = (Z.re - (-2)) * (Z.re - 2) + Z.im ^ 2 := chordDot_re Z (-2) 2
  have h₁ : 0 ≤ (v + 2) * V.re - (v - u) * C.re := by
    rw [hVr, hCr]
    have he : (v + 2) * ((Z.re - u) * (Z.re - v) + Z.im ^ 2) -
        (v - u) * ((Z.re - (-2)) * (Z.re - v) + Z.im ^ 2) =
      (u + 2) * ((Z.re - v) ^ 2 + Z.im ^ 2) := by ring
    rw [he]
    exact mul_nonneg (by linarith) (add_nonneg (sq_nonneg _) (sq_nonneg _))
  have h₂ : 0 ≤ 4 * C.re - (v + 2) * F.re := by
    rw [hCr, hFr]
    have he : 4 * ((Z.re - (-2)) * (Z.re - v) + Z.im ^ 2) -
        (v + 2) * ((Z.re - (-2)) * (Z.re - 2) + Z.im ^ 2) =
      (2 - v) * ((Z.re + 2) ^ 2 + Z.im ^ 2) := by ring
    rw [he]
    exact mul_nonneg (sub_nonneg.mpr hv) (add_nonneg (sq_nonneg _) (sq_nonneg _))
  by_cases he : u = v
  · subst v
    have hreal : ((Z - (u : ℂ)) * star (Z - (u : ℂ))) =
        (Complex.normSq (Z - (u : ℂ)) : ℂ) := by
      rw [Complex.normSq_eq_conj_mul_self, ← Complex.star_def, mul_comm]
    rw [hreal, Complex.ofReal_re, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Complex.normSq_nonneg _), hfocus]
    exact mul_le_mul_of_nonneg_right (by linarith) (Complex.normSq_nonneg _)
  let k := (v - u) / 4
  have hk : 0 < k := div_pos (sub_pos.mpr (lt_of_le_of_ne huv he)) (by norm_num)
  have hVre : k * F.re ≤ V.re := by
    apply (mul_le_mul_right (show 0 < v + 2 by
      linarith only [hu, lt_of_le_of_ne huv he])).mp
    have hfirst := mul_nonneg (by norm_num : 0 ≤ (4 : ℝ)) h₁
    have hsecond := mul_nonneg (sub_nonneg.mpr huv) h₂
    dsimp only [k]
    nlinarith only [hfirst, hsecond]
  have hVim : ((k : ℂ) * F).im = V.im := by
    rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
    change k * ((Z - ((-2 : ℝ) : ℂ)) * star (Z - ((2 : ℝ) : ℂ))).im =
      ((Z - (u : ℂ)) * star (Z - (v : ℂ))).im
    rw [chordDot_im, chordDot_im]
    dsimp only [k]
    ring
  have hscale : F.re * ‖V‖ ≤ V.re * ‖F‖ := by
    have hh := normalized_re_le_of_im_eq ((k : ℂ) * F) V hVim
      (by simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] using hVre)
    rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
      Complex.norm_mul (k : ℂ) F, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hk] at hh
    apply (mul_le_mul_left hk).mp
    nlinarith only [hh]
  change (B ^ 2 - 4) * ‖V‖ ≤ A ^ 2 * V.re
  apply (mul_le_mul_right hFpos).mp
  have hfirst := mul_le_mul_of_nonneg_right hFbound (norm_nonneg V)
  have hsecond := mul_le_mul_of_nonneg_left hscale (sq_nonneg A)
  nlinarith only [hfirst, hsecond]

/-- The real and imaginary axes of the confocal ellipse associated
with the chord factorization. -/
noncomputable def confocalPoint (q p : ℂ) : ℂ := p / q + q / p

/-- The map of the unit circle used for the ellipse factorization.
The real homothety relating this map to the given ellipse cancels
from its cross ratios. -/
noncomputable def ellipseCircleImage (q w : ℂ) : ℂ := w + q / w

private theorem ellipseCircleImage_sub (q w z : ℂ) (hw : w ≠ 0) (hz : z ≠ 0) :
    ellipseCircleImage q w - ellipseCircleImage q z =
      (w - z) * (1 - q / (w * z)) := by
  unfold ellipseCircleImage
  field_simp [hw, hz] <;> ring

private theorem ellipse_pair_factor (q p x y : ℂ)
    (hq : q ≠ 0) (hp : p ≠ 0) (hx : x ≠ 0) (hy : y ≠ 0)
    (hprod : p ^ 2 = x * y) :
    (1 - q / x) * (1 - q / y) = (q / p) * (confocalPoint q p - (x + y) / p) := by
  have hadd : x⁻¹ + y⁻¹ = (x + y) / p ^ 2 := by
    rw [hprod]
    field_simp [hx, hy] <;> ring
  have hmul : x⁻¹ * y⁻¹ = (p ^ 2)⁻¹ := by
    rw [hprod]
    field_simp [hx, hy] <;> ring
  calc
    _ = 1 - q * (x⁻¹ + y⁻¹) + q ^ 2 * (x⁻¹ * y⁻¹) := by
      simp only [div_eq_mul_inv]
      ring
    _ = _ := by
      rw [hadd, hmul]
      unfold confocalPoint
      field_simp [hq, hp] <;> ring

/-- Factor the ratio of the ellipse and circle cross ratios through two
real focal-segment parameters when the original four points are unit
points. The identity itself holds for arbitrary nonzero points. -/
theorem ellipse_crossRatio_factorization (q p a b c d : ℂ)
    (hq : q ≠ 0) (hp : p ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0)
    (hc : c ≠ 0) (hd : d ≠ 0) (hprod : p ^ 2 = a * b * c * d)
    (hsource : (a - d) * (b - c) ≠ 0)
    (himage : (ellipseCircleImage q a - ellipseCircleImage q d) *
      (ellipseCircleImage q b - ellipseCircleImage q c) ≠ 0) :
    spectralCrossRatio (ellipseCircleImage q a) (ellipseCircleImage q b)
      (ellipseCircleImage q c) (ellipseCircleImage q d) =
    spectralCrossRatio a b c d *
      ((confocalPoint q p - (a * c + b * d) / p) /
        (confocalPoint q p - (a * d + b * c) / p)) := by
  have hn : (ellipseCircleImage q a - ellipseCircleImage q c) *
      (ellipseCircleImage q b - ellipseCircleImage q d) =
      ((a - c) * (b - d)) * (q / p) * (confocalPoint q p - (a * c + b * d) / p) := by
    rw [ellipseCircleImage_sub q a c ha hc, ellipseCircleImage_sub q b d hb hd, mul_mul_mul_comm,
      ellipse_pair_factor q p (a * c) (b * d) hq hp (mul_ne_zero ha hc) (mul_ne_zero hb hd)
        (by rw [hprod]; ring)]
    ring
  have hden : (ellipseCircleImage q a - ellipseCircleImage q d) *
      (ellipseCircleImage q b - ellipseCircleImage q c) =
      ((a - d) * (b - c)) * (q / p) * (confocalPoint q p - (a * d + b * c) / p) := by
    rw [ellipseCircleImage_sub q a d ha hd, ellipseCircleImage_sub q b c hb hc, mul_mul_mul_comm,
      ellipse_pair_factor q p (a * d) (b * c) hq hp (mul_ne_zero ha hd) (mul_ne_zero hb hc)
        (by rw [hprod]; ring)]
    ring
  have hseg : confocalPoint q p - (a * d + b * c) / p ≠ 0 := by
    intro he
    exact himage (by rw [hden, he, mul_zero])
  unfold spectralCrossRatio
  rw [hn, hden, mul_div_mul_comm, mul_div_mul_right _ _ (div_ne_zero hq hp)]

/-- A cross ratio of four unit points has zero imaginary part. -/
theorem unit_circle_crossRatio_im_zero (a b c d : ℂ)
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hc : ‖c‖ = 1) (hd : ‖d‖ = 1)
    (hden : (a - d) * (b - c) ≠ 0) :
    (spectralCrossRatio a b c d).im = 0 := by
  let N := (a - c) * (b - d)
  let D := (a - d) * (b - c)
  have hD : Complex.normSq D ≠ 0 := (Complex.normSq_pos.mpr hden).ne'
  have hunit (z : ℂ) (hz : ‖z‖ = 1) : Complex.normSq z = 1 := by
    rw [← Complex.sq_norm, hz, one_pow]
  have him : (N * star D).im = 0 := by
    change (((a - c) * (b - d)) * star ((a - d) * (b - c))).im = 0
    rw [Complex.star_def, circle_defect_eq_modulus_differences]
    simp only [hunit a ha, hunit b hb, hunit c hc, hunit d hd, sub_self, zero_mul, zero_add]
  change (N / D).im = 0
  have he : (N / D).im * Complex.normSq D = (N * star D).im := by
    rw [Complex.div_im, ← sub_div, div_mul_cancel₀ _ hD]
    simp only [Complex.star_def, Complex.mul_im, Complex.conj_re, Complex.conj_im]
    ring
  exact (mul_eq_zero.mp (he.trans him)).resolve_right hD

private theorem unit_pair_sum (x y p : ℂ)
    (hx : ‖x‖ = 1) (hp : ‖p‖ = 1) (hxy : p ^ 2 = x * y) :
    ∃ s : ℝ, -2 ≤ s ∧ s ≤ 2 ∧ (x + y) / p = (s : ℂ) := by
  have hpn : p ≠ 0 := by intro h; simp [h] at hp
  have hxn : x ≠ 0 := by intro h; simp [h] at hx
  let E := x / p
  have hE : ‖E‖ = 1 := by simp only [E, norm_div, hx, hp, div_one]
  have hey : y / p = E⁻¹ := by
    dsimp only [E]
    field_simp [hpn, hxn]
    linear_combination -hxy
  have hbar : E⁻¹ = star E := Complex.inv_eq_conj hE
  have hreal : E + star E = ((2 * E.re : ℝ) : ℂ) := by
    apply Complex.ext
    · simp only [Complex.add_re, Complex.star_def, Complex.conj_re, Complex.ofReal_re]
      ring
    · simp only [Complex.add_im, Complex.star_def, Complex.conj_im, Complex.ofReal_im, add_neg_cancel]
  have hbound := Complex.abs_re_le_norm E
  rw [hE] at hbound
  obtain ⟨hl, hu⟩ := abs_le.mp hbound
  refine ⟨2 * E.re, by linarith, by linarith, ?_⟩
  rw [add_div, hey, hbar]
  exact hreal

private theorem confocal_condition (q : ℝ) (p : ℂ)
    (hq : 0 < q) (hq₁ : q < 1) (hp : ‖p‖ = 1) :
    let A := q⁻¹ + q
    let B := q⁻¹ - q
    let Z := confocalPoint (q : ℂ) p
    0 < A ∧ 0 < B ∧ A ^ 2 = B ^ 2 + 4 ∧
      (Z.re / A) ^ 2 + (Z.im / B) ^ 2 = 1 := by
  dsimp only
  let A := q⁻¹ + q
  let B := q⁻¹ - q
  let Z := confocalPoint (q : ℂ) p
  have hA : 0 < A := add_pos (inv_pos.mpr hq) hq
  have hB : 0 < B := by
    apply sub_pos.mpr
    have hh : q ^ 2 < 1 := by simpa only [one_pow] using
      (sq_lt_sq₀ hq.le zero_le_one).mpr hq₁
    rw [← one_div]
    exact (lt_div_iff₀ hq).mpr (by simpa only [pow_two] using hh)
  refine ⟨hA, hB, ?_, ?_⟩
  · change A ^ 2 = B ^ 2 + 4
    dsimp only [A, B]
    field_simp [hq.ne'] <;> ring
  · have he : Z = (q⁻¹ : ℝ) * p + (q : ℂ) * star p := by
      simp only [Z, confocalPoint, div_eq_mul_inv, ← Complex.ofReal_inv, Complex.inv_eq_conj hp,
        Complex.star_def]
      ring
    have hr : Z.re = A * p.re := by
      rw [he]
      simp only [A, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.star_def, Complex.conj_re, zero_mul, sub_zero]
      ring
    have hi : Z.im = B * p.im := by
      rw [he]
      simp only [B, Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.star_def, Complex.conj_im, zero_mul, add_zero]
      ring
    have hn : p.re ^ 2 + p.im ^ 2 = 1 := by
      rw [← sq_norm_coordinates, hp, one_pow]
    change (Z.re / A) ^ 2 + (Z.im / B) ^ 2 = 1
    rw [hr, hi, mul_div_cancel_left₀ _ hA.ne', mul_div_cancel_left₀ _ hB.ne']
    exact hn

/-- For a negative real ordering of the circle cross ratio, the
normalized real part of its ellipse cross ratio has the sharp upper
bound determined by the focal visual angle. -/
theorem ellipse_crossRatio_re_bound (q : ℝ) (a b c d : ℂ)
    (hq : 0 < q) (hq₁ : q < 1)
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hc : ‖c‖ = 1) (hd : ‖d‖ = 1)
    (hsource : (a - d) * (b - c) ≠ 0)
    (himage : (ellipseCircleImage (q : ℂ) a - ellipseCircleImage (q : ℂ) d) *
      (ellipseCircleImage (q : ℂ) b - ellipseCircleImage (q : ℂ) c) ≠ 0)
    (hneg : (spectralCrossRatio a b c d).re < 0) :
    let e := ellipseCircleImage (q : ℂ)
    let ratio := spectralCrossRatio (e a) (e b) (e c) (e d)
    (q⁻¹ + q) ^ 2 * ratio.re ≤ (4 - (q⁻¹ - q) ^ 2) * ‖ratio‖ := by
  have hNorm (u : ℂ) (hu : ‖u‖ = 1) : u ≠ 0 := by intro h; simp [h] at hu
  obtain ⟨p, hprod⟩ := IsAlgClosed.exists_pow_nat_eq (a * b * c * d) (n := 2) two_pos
  have hp : ‖p‖ = 1 := by
    have hn : ‖p‖ ^ 2 = 1 := by
      rw [← norm_pow, hprod]
      simp only [Complex.norm_mul, ha, hb, hc, hd, one_mul]
    exact le_antisymm
      ((sq_le_sq₀ (norm_nonneg p) zero_le_one).mp (by simpa only [one_pow] using hn.le))
      ((sq_le_sq₀ zero_le_one (norm_nonneg p)).mp (by simpa only [one_pow] using hn.ge))
  have hpair (u v : ℂ) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) : ‖u * v‖ = 1 := by
    rw [Complex.norm_mul, hu, hv, one_mul]
  obtain ⟨s, hs₀, hs₁, hs⟩ := unit_pair_sum (a * c) (b * d) p (hpair a c ha hc) hp
    (by rw [hprod]; ring)
  obtain ⟨t, ht₀, ht₁, ht⟩ := unit_pair_sum (a * d) (b * c) p (hpair a d ha hd) hp
    (by rw [hprod]; ring)
  let Z := confocalPoint (q : ℂ) p
  obtain ⟨hA, hB, hfocus, hellipse⟩ := confocal_condition q p hq hq₁ hp
  let V := (Z - (s : ℂ)) * star (Z - (t : ℂ))
  have hVisual : ((q⁻¹ - q) ^ 2 - 4) * ‖V‖ ≤ (q⁻¹ + q) ^ 2 * V.re :=
    confocal_chord_cosine_bound _ _ Z s t hA hB hfocus hellipse hs₀ hs₁ ht₀ ht₁
  have hzn : Z - (t : ℂ) ≠ 0 := by
    intro he
    let A := q⁻¹ + q
    let B := q⁻¹ - q
    have hz : Z = (t : ℂ) := sub_eq_zero.mp he
    change (Z.re / A) ^ 2 + (Z.im / B) ^ 2 = 1 at hellipse
    rw [hz, Complex.ofReal_re, Complex.ofReal_im, zero_div, zero_pow two_ne_zero, add_zero] at hellipse
    have htSq : t ^ 2 = A ^ 2 := by
      calc
        _ = (t / A) ^ 2 * A ^ 2 := by field_simp [show A ≠ 0 from hA.ne'] <;> ring
        _ = _ := by rw [hellipse, one_mul]
    have htBound : t ^ 2 ≤ 4 := by
      nlinarith only [mul_nonneg (by linarith : 0 ≤ t + 2) (sub_nonneg.mpr ht₁)]
    change A ^ 2 = B ^ 2 + 4 at hfocus
    have hBsq : 0 < B ^ 2 := sq_pos_of_pos hB
    linarith only [htSq, htBound, hfocus, hBsq]
  let R := (Z - (s : ℂ)) / (Z - (t : ℂ))
  let N := Complex.normSq (Z - (t : ℂ))
  have hN : 0 < N := Complex.normSq_pos.mpr hzn
  have hm : V = (N : ℂ) * R := by
    dsimp only [V, N, R]
    rw [Complex.normSq_eq_conj_mul_self, ← Complex.star_def]
    field_simp [hzn] <;> ring
  have hR : ((q⁻¹ - q) ^ 2 - 4) * ‖R‖ ≤ (q⁻¹ + q) ^ 2 * R.re := by
    rw [hm, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
      Complex.norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hN] at hVisual
    apply (mul_le_mul_left hN).mp
    nlinarith only [hVisual]
  have hEq := ellipse_crossRatio_factorization (q : ℂ) p a b c d
    (Complex.ofReal_ne_zero.mpr hq.ne') (hNorm p hp) (hNorm a ha) (hNorm b hb) (hNorm c hc)
    (hNorm d hd) hprod hsource himage
  rw [hs, ht] at hEq
  change spectralCrossRatio _ _ _ _ = spectralCrossRatio a b c d * R at hEq
  let L := spectralCrossRatio a b c d
  have hi : L.im = 0 := unit_circle_crossRatio_im_zero a b c d ha hb hc hd hsource
  have hn : ‖L‖ = -L.re := by
    have hreal : L = (L.re : ℂ) :=
      Complex.ext (Complex.ofReal_re _).symm (hi.trans (Complex.ofReal_im _).symm)
    calc
      _ = ‖(L.re : ℂ)‖ := congrArg norm hreal
      _ = _ := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_neg hneg]
  dsimp only
  rw [hEq]
  change (q⁻¹ + q) ^ 2 * (L * R).re ≤ (4 - (q⁻¹ - q) ^ 2) * ‖L * R‖
  rw [Complex.mul_re, hi, zero_mul, sub_zero, Complex.norm_mul, hn]
  nlinarith only [mul_le_mul_of_nonneg_left hR (neg_nonneg.mpr hneg.le)]

end MOC
