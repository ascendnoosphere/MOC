import MOC.FourT7Source
import MOC.FourCoincidence
import MOC.Support
import Mathlib.Tactic.Lift
import MOC.TwoExceptions

/-! Exact positive kernels for the supporting face with precisely the six T7 contacts. -/

namespace MOC

noncomputable section

private theorem t7_chord_factors (z w v r c : ℂ) :
    let F := fourT7ProjectiveProduct z ![w, v, r, c]
    F 0 - F 1 = v * (r - c) * (z - 1) ∧
    F 2 - F 0 = (z - c) * (v - r) ∧
    F 7 - F 1 = (1 - c) * (z - r) * (v - w) ∧
    F 8 - F 2 = r * (z - c) * (w - v) ∧
    F 3 - F 1 = z * (1 - c) * (v - r) ∧
    F 6 - F 8 = (z - c) * (r - w) ∧
    F 9 - F 7 = z * (1 - c) * (w - r) ∧
    F 10 - F 8 = z * (c - r) * (w - 1) ∧
    F 14 - F 8 = (z - c) * (v - r) * (w - 1) ∧
    F 18 - F 4 = (v - 1) * (F 10 - F 7) ∧
    F 14 - F 0 = -v * (F 6 - F 8) := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change -v * (1 - r) * (z - c) - -v * (1 - c) * (z - r) = _
    ring
  · change -r * (1 - v) * (z - c) - -v * (1 - r) * (z - c) = _
    ring
  · change -w * (1 - c) * (z - r) - -v * (1 - c) * (z - r) = _
    ring
  · change -r * (1 - w) * (z - c) - -r * (1 - v) * (z - c) = _
    ring
  · change -r * (1 - c) * (z - v) - -v * (1 - c) * (z - r) = _
    ring
  · change -w * (1 - r) * (z - c) - -r * (1 - w) * (z - c) = _
    ring
  · change -r * (1 - c) * (z - w) - -w * (1 - c) * (z - r) = _
    ring
  · change -c * (1 - w) * (z - r) - -r * (1 - w) * (z - c) = _
    ring
  · change -v * (1 - w) * (z - c) - -r * (1 - w) * (z - c) = _
    ring
  · change -w * (1 - v) * (z - r) - -c * (1 - v) * (z - r) =
      (v - 1) * (-c * (1 - w) * (z - r) - -w * (1 - c) * (z - r))
    ring
  · change -v * (1 - w) * (z - c) - -v * (1 - r) * (z - c) =
      -v * (-w * (1 - r) * (z - c) - -r * (1 - w) * (z - c))
    ring

private theorem t7_chord_kernels (z w v r c h t k l s : ℂ)
    (hv1 : v ≠ 1) (hvz : v ≠ z) (hr : r ≠ 0) (hzr : z ≠ r)
    (hzc : z ≠ c) (hvr : v ≠ r) (hcr : c ≠ r)
    (ht : t ≠ 0) (hk : k - 1 ≠ 0) (hkt : k - 1 = t * (h - 1))
    (hw : w = v + s * (v - r) / r)
    (hzv : v - z = (h - 1) * v * (z - 1))
    (hB : (z - c) * (v - r) = t * (c - r) * (z - v))
    (he : (1 - c) * (z - r) / (r * (z - c)) = l / (k - 1) - 1) :
    let F := fourT7ProjectiveProduct z ![w, v, r, c]
    let Q (i j : Fin 24) := (F i - F j) / ((z - c) * (v - r))
    Q 3 1 = (l / (k - 1) - 1) * (z * r / (z - r)) ∧
    Q 6 8 = -(1 + s / r) ∧
    Q 9 7 = (1 + s / r) * Q 3 1 ∧
    Q 10 8 = -h / (k - 1) * ((w - 1) / (v - 1)) ∧
    Q 14 8 = w - 1 ∧
    Q 14 0 = -v * Q 6 8 ∧
    Q 18 4 = (-h * (w - 1) + (k + l * s) * (v - 1)) / (k - 1) := by
  let F := fourT7ProjectiveProduct z ![w, v, r, c]
  let B := (z - c) * (v - r)
  let Q (i j : Fin 24) := (F i - F j) / B
  change Q 3 1 = _ ∧ Q 6 8 = _ ∧ Q 9 7 = _ ∧ Q 10 8 = _ ∧ Q 14 8 = _ ∧
    Q 14 0 = _ ∧ Q 18 4 = _
  obtain ⟨h01, h20, h71, h82, h31, h68, h97, h108, h148, h184, h140⟩ := t7_chord_factors z w v r c
  change F 0 - F 1 = _ at h01
  change F 2 - F 0 = B at h20
  change F 7 - F 1 = _ at h71
  change F 8 - F 2 = _ at h82
  change F 3 - F 1 = _ at h31
  change F 6 - F 8 = _ at h68
  change F 9 - F 7 = _ at h97
  change F 10 - F 8 = _ at h108
  change F 14 - F 8 = B * (w - 1) at h148
  change F 18 - F 4 = (v - 1) * (F 10 - F 7) at h184
  change F 14 - F 0 = -v * (F 6 - F 8) at h140
  have hbn : B ≠ 0 := mul_ne_zero (sub_ne_zero.mpr hzc) (sub_ne_zero.mpr hvr)
  have heq3 : Q 3 1 = (l / (k - 1) - 1) * (z * r / (z - r)) := by
    dsimp only [Q, B]
    rw [h31, ← he]
    field_simp [hr, sub_ne_zero.mpr hzr, sub_ne_zero.mpr hzc, sub_ne_zero.mpr hvr] <;> ring
  have heq6 : Q 6 8 = -(1 + s / r) := by
    dsimp only [Q, B]
    rw [h68, hw]
    field_simp [hr, sub_ne_zero.mpr hzc, sub_ne_zero.mpr hvr] <;> ring
  have heq9 : Q 9 7 = (1 + s / r) * Q 3 1 := by
    dsimp only [Q, B]
    rw [h97, h31, hw]
    field_simp [hr, sub_ne_zero.mpr hzc, sub_ne_zero.mpr hvr] <;> ring
  have hhz : z * (v - 1) = h * v * (z - 1) := by linear_combination hzv
  have hzdiv : z / (t * (z - v)) = -h / ((k - 1) * (v - 1)) := by
    apply (div_eq_div_iff (mul_ne_zero ht (sub_ne_zero.mpr hvz.symm))
      (mul_ne_zero hk (sub_ne_zero.mpr hv1))).mpr
    rw [hkt]
    linear_combination t * (h - 1) * hhz - h * t * hzv
  have heq10 : Q 10 8 = -h / (k - 1) * ((w - 1) / (v - 1)) := by
    calc
      Q 10 8 = z / (t * (z - v)) * (w - 1) := by
        dsimp only [Q, B]
        rw [h108, hB]
        field_simp [ht, sub_ne_zero.mpr hvz.symm, sub_ne_zero.mpr hcr] <;> ring
      _ = _ := by rw [hzdiv]; ring
  have hB1 : B = (k - 1) * (F 0 - F 1) := by
    change (z - c) * (v - r) = _
    rw [hB, h01, hkt]
    linear_combination -(t * (c - r)) * hzv
  have heq1 : Q 1 0 = -1 / (k - 1) := by
    apply (div_eq_iff hbn).mpr
    rw [hB1]
    field_simp [hk] <;> ring
  have heq8 : Q 8 0 = 1 + s := by
    change (F 8 - F 0) / ((z - c) * (v - r)) = _
    rw [show F 8 - F 0 = (F 8 - F 2) + (F 2 - F 0) by ring, h82, h20, hw]
    dsimp only [B]
    field_simp [hr, sub_ne_zero.mpr hzc, sub_ne_zero.mpr hvr] <;> ring
  have heq7 : Q 7 1 = -s * (l / (k - 1) - 1) := by
    dsimp only [Q, B]
    rw [h71, hw, ← he]
    field_simp [hr, sub_ne_zero.mpr hzc, sub_ne_zero.mpr hvr] <;> ring
  have h87 : Q 8 7 = (k + l * s) / (k - 1) := by
    calc
      Q 8 7 = Q 8 0 - Q 7 1 - Q 1 0 := by dsimp only [Q]; ring
      _ = _ := by rw [heq8, heq7, heq1]; field_simp [hk] <;> ring
  have heq14 : Q 14 8 = w - 1 := by
    change (F 14 - F 8) / B = _
    rw [h148]
    field_simp [hbn] <;> ring
  have heq14' : Q 14 0 = -v * Q 6 8 := by
    dsimp only [Q]
    rw [h140]
    ring
  refine ⟨heq3, heq6, heq9, heq10, heq14, heq14', ?_⟩
  calc
    Q 18 4 = (v - 1) * (Q 10 8 + Q 8 7) := by
      change (F 18 - F 4) / B = _
      rw [h184]
      dsimp only [Q]
      ring
    _ = _ := by rw [heq10, h87]; field_simp [hk, sub_ne_zero.mpr hv1] <;> ring

set_option maxHeartbeats 2500000 in
private theorem t7_projected_kernels (z w v r c : ℂ) (h t k l s L : ℝ) (g : Fin 24 → ℝ)
    (hz : z ≠ 0) (hv : v ≠ 0) (hv1 : v ≠ 1) (hvz : v ≠ z) (hr : r ≠ 0)
    (hzr : z ≠ r) (hzc : z ≠ c) (hvr : v ≠ r) (hcr : c ≠ r)
    (hh0 : h ≠ 0) (hh : h ≠ 1) (ht : t ≠ 0) (ht1 : t ≠ 1) (hkt : k = 1 + t * (h - 1))
    (hrr : (1 + (l : ℂ) * v) * r = (k : ℂ) * v)
    (hww : w = v + (s : ℂ) * (v - r) / r)
    (hzv : v - z = ((h : ℂ) - 1) * v * (z - 1))
    (hB : (z - c) * (v - r) = (t : ℂ) * (c - r) * (z - v))
    (he : (1 - c) * (z - r) / (r * (z - c)) = (l : ℂ) / ((k : ℂ) - 1) - 1)
    (hq : ∀ i j, j ∈ fourT7ContactIndices →
      g i = L * (((fourT7ProjectiveProduct z ![w, v, r, c] i -
        fourT7ProjectiveProduct z ![w, v, r, c] j) / ((z - c) * (v - r)))).im)
    (g3 : 0 < g 3) (g6 : 0 < g 6) (g10 : 0 < g 10) (g14 : 0 < g 14) (g18 : 0 < g 18) :
    (h - k) / (k - 1) < 0 ∧ 0 < h * (k - l - 1) / (h - k) ∧
    0 < s / (h - k) ∧ 0 < (k + l * s) / (h - k) ∧
    g 9 = (1 + s / (h - k) * (h - l - 1)) * g 3 := by
  let e := l / (k - 1) - 1
  let D := h - k
  let P := k + l * s
  let α := h * k - h * l - k
  let N : ℂ := (D : ℂ) * (1 / v) - (α : ℂ)
  let Q (i j : Fin 24) := (fourT7ProjectiveProduct z ![w, v, r, c] i -
      fourT7ProjectiveProduct z ![w, v, r, c] j) / ((z - c) * (v - r))
  change ∀ i j, j ∈ fourT7ContactIndices → g i = L * (Q i j).im at hq
  change D / (k - 1) < 0 ∧ 0 < h * (k - l - 1) / D ∧
    0 < s / D ∧ 0 < P / D ∧ g 9 = (1 + s / D * (h - l - 1)) * g 3
  have hk1 : k - 1 = t * (h - 1) := by linarith only [hkt]
  have hk1n : k - 1 ≠ 0 := by
    rw [hk1]
    exact mul_ne_zero ht (sub_ne_zero.mpr hh)
  have hDn : D ≠ 0 := by
    have heq : D = (1 - t) * (h - 1) := by dsimp only [D]; rw [hkt]; ring
    rw [heq]
    exact mul_ne_zero (sub_ne_zero.mpr ht1.symm) (sub_ne_zero.mpr hh)
  have hk1c : (k : ℂ) - 1 ≠ 0 := by exact_mod_cast hk1n
  have hk1eq : (k : ℂ) - 1 = (t : ℂ) * ((h : ℂ) - 1) := by exact_mod_cast hk1
  obtain ⟨q3raw, q6, q9, q10, q148, q140, q18⟩ := t7_chord_kernels z w v r c h t k l s
    hv1 hvz hr hzr hzc hvr hcr (by exact_mod_cast ht) hk1c hk1eq hww hzv hB he
  have q3 : Q 3 1 = (e : ℂ) * (z * r / (z - r)) := by
    simpa only [Q, e, Complex.ofReal_sub, Complex.ofReal_div, Complex.ofReal_one] using q3raw
  change Q 6 8 = -(1 + (s : ℂ) / r) at q6
  change Q 9 7 = (1 + (s : ℂ) / r) * Q 3 1 at q9
  change Q 10 8 = -(h : ℂ) / ((k : ℂ) - 1) * ((w - 1) / (v - 1)) at q10
  change Q 14 8 = w - 1 at q148
  change Q 14 0 = -v * Q 6 8 at q140
  change Q 18 4 = (-(h : ℂ) * (w - 1) + (k + (l : ℂ) * s) * (v - 1)) / ((k : ℂ) - 1) at q18
  have hg3 := hq 3 1 (by decide)
  have hg6 := hq 6 8 (by decide)
  have hg9 := hq 9 7 (by decide)
  have hg10 := hq 10 8 (by decide)
  have hg14 := hq 14 8 (by decide)
  have hg18 := hq 18 4 (by decide)
  rw [q148] at hg14
  have hkn : k ≠ 0 := by
    intro hk0
    have hmul : (1 + (l : ℂ) * v) * r = 0 := by simpa [hk0] using hrr
    have hvreal := congrArg Complex.im ((mul_eq_zero.mp hmul).resolve_right hr)
    simp only [Complex.add_im, Complex.one_im, Complex.mul_im, Complex.ofReal_im,
      Complex.ofReal_re, Complex.zero_im, zero_mul, add_zero, zero_add] at hvreal
    have hl0 : l ≠ 0 := by
      intro hl0
      have : (1 : ℂ) = 0 := by simpa [hl0] using (mul_eq_zero.mp hmul).resolve_right hr
      exact one_ne_zero this
    have hvi : v.im = 0 := (mul_eq_zero.mp hvreal).resolve_left hl0
    have hvr' : (v.re : ℂ) = v := by ext <;> simp [hvi]
    have hV : ((v.re - 1 : ℝ) : ℂ) = v - 1 := by rw [Complex.ofReal_sub, hvr', Complex.ofReal_one]
    have hg14' : g 14 = -v.re * g 6 := by
      rw [hq 14 0 (by decide), q140, ← hvr', ← Complex.ofReal_neg, Complex.im_ofReal_mul, hg6]
      ring
    have hg18' : g 18 = h * g 14 := by
      have hq18 : Q 18 4 = (h : ℂ) * (w - 1) - (l : ℂ) * s * (v - 1) := by
        rw [q18, hk0]; simp <;> ring
      rw [hg18, hq18, hg14, Complex.sub_im, Complex.im_ofReal_mul, ← Complex.ofReal_mul,
        Complex.im_ofReal_mul, Complex.sub_im, hvi, Complex.one_im]
      ring
    have hg10' : g 10 = h * g 14 / (v.re - 1) := by
      have hq10 : Q 10 8 = (h : ℂ) * ((w - 1) / (v - 1)) := by rw [q10, hk0]; simp
      rw [hg10, hq10, ← hV, Complex.im_ofReal_mul, Complex.div_ofReal_im, hg14]
      ring
    have hvn : v.re < 0 := by
      by_contra! hnonneg
      have hbad := mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hnonneg) g6.le
      rw [← hg14'] at hbad
      exact (not_lt_of_ge hbad) g14
    have hp : 0 < h * g 14 := by rwa [← hg18']
    have hneg := div_neg_of_pos_of_neg hp (by linarith only [hvn] : v.re - 1 < 0)
    exact (not_lt_of_ge g10.le) (hg10'.trans_lt hneg)
  have hkc : (k : ℂ) ≠ 0 := by exact_mod_cast hkn
  have hDc : (D : ℂ) ≠ 0 := by exact_mod_cast hDn
  have hx : (k : ℂ) * (1 / r) = 1 / v + (l : ℂ) := by
    calc
      _ = ((k : ℂ) * v) / (r * v) := by field_simp [hr, hv] <;> ring
      _ = _ := by rw [← hrr]; field_simp [hr, hv] <;> ring
  have hy : (1 : ℂ) / r = (1 / v + (l : ℂ)) / (k : ℂ) := by
    apply (eq_div_iff hkc).mpr
    rw [mul_comm, hx]
  have hz0 : (h : ℂ) * v = z * (1 + ((h : ℂ) - 1) * v) := by linear_combination hzv
  have hz' : (h : ℂ) * (1 / z) = 1 / v + (h : ℂ) - 1 := by
    calc
      _ = ((h : ℂ) * v) / (z * v) := by field_simp [hz, hv] <;> ring
      _ = _ := by rw [hz0]; field_simp [hz, hv] <;> ring
  have hdiff : (1 : ℂ) / r - 1 / z = (z - r) / (r * z) := by
    field_simp [hr, hz] <;> ring
  have hN : N = (h : ℂ) * k * ((1 : ℂ) / r - 1 / z) := by
    calc
      _ = (h : ℂ) * (1 / v + (l : ℂ)) - (k : ℂ) * (1 / v + (h : ℂ) - 1) := by
        dsimp only [N, D, α]
        push_cast
        ring
      _ = _ := by rw [← hx, ← hz']; ring
  have hden : N ≠ 0 := by
    intro hn
    rw [hN, hdiff] at hn
    exact mul_ne_zero (mul_ne_zero (by exact_mod_cast hh0) hkc)
      (div_ne_zero (sub_ne_zero.mpr hzr) (mul_ne_zero hr hz)) hn
  have q3' : Q 3 1 = ((e * h * k : ℝ) : ℂ) / N := by
    apply (eq_div_iff hden).mpr
    rw [q3, hN, hdiff]
    push_cast
    field_simp [hz, hr, sub_ne_zero.mpr hzr] <;> ring
  have hw1 : w - 1 = ((P / k : ℝ) : ℂ) * v + ((s / k - s - 1 : ℝ) : ℂ) := by
    rw [hww]
    push_cast
    calc
      _ = (v - 1) + (s : ℂ) * (v * (1 / r) - 1) := by field_simp [hr] <;> ring
      _ = _ := by rw [hy]; dsimp only [P]; push_cast; field_simp [hkc, hv] <;> ring
  have q9' : Q 9 7 = ((1 + s / D * (h - l - 1) : ℝ) : ℂ) * Q 3 1 + ((s * e * h / D : ℝ) : ℂ) := by
    rw [q9, q3', div_eq_mul_one_div (s : ℂ), hy]
    push_cast
    field_simp [hden, hkc, hDc, hv]
    dsimp only [N, D, α]
    push_cast
    field_simp [hv] <;> ring
  have q10' : Q 10 8 = ((-h * P / (k * (k - 1)) : ℝ) : ℂ) -
      ((h * e * s / k : ℝ) : ℂ) / (v - 1) := by
    rw [q10, hw1]
    dsimp only [P, e]
    push_cast
    field_simp [hkc, hk1c, sub_ne_zero.mpr hv1] <;> ring
  have q18' : Q 18 4 = ((-D / (k - 1) : ℝ) : ℂ) * (w - 1) +
      ((s * (k - l - 1) / (k - 1) : ℝ) : ℂ) := by
    rw [q18, hw1]
    dsimp only [D, P]
    push_cast
    field_simp [hkc, hk1c] <;> ring
  let ρ := L * v.im
  let V := Complex.normSq v
  let W := Complex.normSq (v - 1)
  let Z := Complex.normSq N
  have hV : 0 < V := Complex.normSq_pos.mpr hv
  have hW : 0 < W := Complex.normSq_pos.mpr (sub_ne_zero.mpr hv1)
  have hZ : 0 < Z := Complex.normSq_pos.mpr hden
  have him1 (x : ℂ) : ((1 : ℂ) / x).im = -x.im / Complex.normSq x := by
    simp [one_div, Complex.inv_im]
  have hNim : N.im = -D * v.im / V := by
    dsimp only [N, V]
    rw [Complex.sub_im, Complex.ofReal_im, sub_zero, Complex.im_ofReal_mul, him1]
    ring
  have hg3' : g 3 * Z * V = e * h * k * D * ρ := by
    rw [hg3, q3', Complex.div_im, Complex.ofReal_im, Complex.ofReal_re, hNim]
    dsimp only [ρ, Z]
    rw [zero_mul, zero_div, zero_sub]
    field_simp [hZ.ne', hV.ne'] <;> ring
  have hg6' : g 6 * k * V = s * ρ := by
    rw [hg6, q6, div_eq_mul_one_div (s : ℂ), hy]
    have hdiv : ((1 / v + (l : ℂ)) / (k : ℂ)).im = (-v.im / V) / k := by
      rw [Complex.div_ofReal_im, Complex.add_im, him1, Complex.ofReal_im, add_zero]
    rw [Complex.neg_im, Complex.add_im, Complex.one_im, zero_add, Complex.im_ofReal_mul, hdiv]
    dsimp only [ρ]
    field_simp [hkn, hV.ne'] <;> ring
  have hg10' : g 10 * W = h * e * (g 6 * V) := by
    have hsρ : g 6 * V = s * ρ / k := by
      apply (eq_div_iff hkn).mpr
      linear_combination hg6'
    rw [hg10, q10', Complex.sub_im, Complex.ofReal_im, Complex.div_im,
      Complex.ofReal_im, Complex.ofReal_re, Complex.sub_im, Complex.one_im, hsρ]
    dsimp only [W, ρ]
    field_simp [hkn, hW.ne'] <;> ring
  have hg14' : g 14 * k = P * ρ := by
    rw [hg14, hw1, Complex.add_im, Complex.im_ofReal_mul, Complex.ofReal_im, add_zero]
    dsimp only [ρ]
    field_simp [hkn] <;> ring
  have hg18' : g 18 = (-D / (k - 1)) * g 14 := by
    rw [hg18, q18', Complex.add_im, Complex.im_ofReal_mul, Complex.ofReal_im, add_zero, hg14]
    ring
  have hDsign : D / (k - 1) < 0 := by
    have hp : 0 < -D / (k - 1) := pos_of_mul_pos_left (by rw [← hg18']; exact g18) g14.le
    rw [neg_div] at hp
    linarith only [hp]
  have heh : 0 < h * e := pos_of_mul_pos_left (by rw [← hg10']; exact mul_pos g10 hW) (mul_nonneg g6.le hV.le)
  have hNsign : 0 < h * (k - l - 1) / D := by
    have hratio : 0 < -(k - 1) / D := by
      have heq : -(k - 1) / D = -(D / (k - 1))⁻¹ := by
        field_simp [hk1n, hDn] <;> ring
      rw [heq]
      exact neg_pos.mpr (inv_lt_zero.mpr hDsign)
    convert mul_pos heh hratio using 1
    dsimp only [e]
    field_simp [hk1n, hDn] <;> ring
  have hsD : 0 < s / D := by
    have heq : s / D * (g 3 * Z * V) = (h * e) * k ^ 2 * (g 6 * V) := by
      rw [hg3']
      calc
        _ = (h * e) * k * (s * ρ) := by field_simp [hDn] <;> ring
        _ = _ := by rw [← hg6']; ring
    exact pos_of_mul_pos_left (by rw [heq]; exact mul_pos (mul_pos heh (sq_pos_of_ne_zero hkn)) (mul_pos g6 hV))
      (mul_nonneg (mul_nonneg g3.le hZ.le) hV.le)
  have hPD : 0 < P / D := by
    have heq : P / D * (g 6 * V) = s / D * g 14 := by
      apply (mul_right_cancel₀ hkn)
      calc
        _ = P / D * (g 6 * k * V) := by ring
        _ = s / D * (g 14 * k) := by rw [hg6', hg14']; ring
        _ = _ := by ring
    exact pos_of_mul_pos_left (by rw [heq]; exact mul_pos hsD g14) (mul_nonneg g6.le hV.le)
  refine ⟨hDsign, hNsign, hsD, hPD, ?_⟩
  rw [hg9, q9', Complex.add_im, Complex.im_ofReal_mul, Complex.ofReal_im, add_zero, hg3]
  ring

/-- The order-four support inequality for exactly the six contacts of case T7.
The proof uses rational chord identities and the nonnegative squared-minor
certificate. Repeated and shared eigenvalues use the corresponding order-four
spectral results. -/
theorem fourT7_support (a b : Fin 4 → ℂ) (η : ℂ) (H : ℝ)
    (hn : ∀ i, H ≤ (η * matchingProduct a b (fourPerm i).symm).re)
    (hc : ∀ i ∈ fourT7ContactIndices, (η * matchingProduct a b (fourPerm i).symm).re = H)
    (hs : ∀ i ∉ fourT7ContactIndices, H < (η * matchingProduct a b (fourPerm i).symm).re)
    (U : Matrix (Fin 4) (Fin 4) ℂ) (hU : IsUnitary U) :
    H ≤ (η * determinantValue a b U).re := by
  have hbound (hh : Holds a b U) : H ≤ (η * determinantValue a b U).re := by
    obtain ⟨σ, hσ⟩ := (holds_iff_directional a b U).mp hh (-η)
    obtain ⟨i, hi⟩ := fourPerm_surjective σ.symm
    have hgi := hn i
    rw [hi, Equiv.symm_symm] at hgi
    simp only [neg_mul, Complex.neg_re, neg_le_neg_iff] at hσ
    exact hgi.trans hσ
  by_cases ha : Function.Injective a
  swap
  · exact hbound (holds_four_of_repeated_spectrum a b U hU (Or.inl ha))
  by_cases hb : Function.Injective b
  swap
  · exact hbound (holds_four_of_repeated_spectrum a b U hU (Or.inr hb))
  by_cases hzero : ∃ i j, a i + b j = 0
  · obtain ⟨i, j, hij⟩ := hzero
    exact hbound (holds_four_of_opposite_entries a b U hU hij)
  by_cases hη : η = 0
  · simpa [hη] using hn 0
  have hab (i j : Fin 4) : a i + b j ≠ 0 := fun hij => hzero ⟨i, j, hij⟩
  obtain ⟨K, z, C, hK, hz, hz1, hC, hsep, hprod⟩ := exists_fourT7_projective_products a b ha hb hab
  let w := C 0
  let v := C 1
  let r := C 2
  let c := C 3
  have hvec : C = ![w, v, r, c] := by
    funext j
    fin_cases j <;> rfl
  rw [hvec] at hC hsep hprod
  let κ := η * K
  let F := fourT7ProjectiveProduct z ![w, v, r, c]
  have hproj (i : Fin 24) : (η * matchingProduct a b (fourPerm i).symm).re = (κ * F i).re := by
    rw [hprod]
    dsimp only [κ, F]
    rw [mul_assoc]
  have hcontact (i : Fin 24) (hi : i ∈ fourT7ContactIndices) : (κ * F i).re = H :=
    (hproj i).symm.trans (hc i hi)
  obtain ⟨h, t, k, l, s, him, tim, kim, lim, sim, hh0, hh1, ht0, ht1, hkt, _hs0,
    _hz, _hc, hr, hw, hκ, hzv, hB, he⟩ :=
    fourT7_chart_real_parameters z w v r c κ H (mul_ne_zero hη hK) hz hz1 hC hsep hcontact
  lift h to ℝ using him
  lift t to ℝ using tim
  lift k to ℝ using kim
  lift l to ℝ using lim
  lift s to ℝ using sim
  let g (i : Fin 24) := (η * matchingProduct a b (fourPerm i).symm).re - H
  let L := -(κ * ((z - c) * (v - r))).im
  have hv0 : v ≠ 0 := (hsep 1).1
  have hv1 : v ≠ 1 := (hsep 1).2.1
  have hvz : v ≠ z := (hsep 1).2.2
  have hr0 : r ≠ 0 := (hsep 2).1
  have hzr : z ≠ r := (hsep 2).2.2.symm
  have hzc : z ≠ c := (hsep 3).2.2.symm
  have hvr : v ≠ r := hC.ne (by decide : (1 : Fin 4) ≠ 2)
  have hcr : c ≠ r := hC.ne (by decide : (3 : Fin 4) ≠ 2)
  have hq (i j : Fin 24) (hj : j ∈ fourT7ContactIndices) :
      g i = L * ((F i - F j) / ((z - c) * (v - r))).im := by
    have heq : κ * (F i - F j) = (κ * ((z - c) * (v - r))) *
        ((F i - F j) / ((z - c) * (v - r))) := by
      field_simp [sub_ne_zero.mpr hzc, sub_ne_zero.mpr hvr] <;> ring
    dsimp only [g, L]
    rw [hproj, ← hcontact j hj, ← Complex.sub_re, ← mul_sub, heq,
      Complex.mul_re, hκ, zero_mul, zero_sub, neg_mul]
  have hpos (i : Fin 24) (hi : i ∉ fourT7ContactIndices) : 0 < g i := sub_pos.mpr (hs i hi)
  obtain ⟨hD, hN, hsD, hPD, h9⟩ := t7_projected_kernels z w v r c h t k l s L g
    hz hv0 hv1 hvz hr0 hzr hzc hvr hcr
    (by exact_mod_cast hh0) (by exact_mod_cast hh1) (by exact_mod_cast ht0) (by exact_mod_cast ht1)
    (by exact_mod_cast hkt) hr hw hzv hB he hq
    (hpos 3 (by decide)) (hpos 6 (by decide)) (hpos 10 (by decide))
    (hpos 14 (by decide)) (hpos 18 (by decide))
  exact fourT7_support_of_interpolation_kernels a b η H hn hc U hU h k l s hD hN hsD hPD h9

end

end MOC
