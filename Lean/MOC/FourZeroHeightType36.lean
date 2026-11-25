import MOC.ContactCensus
import MOC.ProjectivePole
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

/-! The zero-height exclusion for the order-four contact type 36. -/

namespace MOC

/-- Type 36 in the lexicographic matching coordinates. -/
def fourZeroHeightType36Contacts : Finset (Fin 24) := {1, 4, 5, 6, 9, 12, 14}

/-- The five inactive products in the type 36 chart cannot have a common
strict sign. The factors are the exact imaginary numerators. -/
theorem fourZeroHeightType36_sign_certificate (p q z r k : ℝ)
    (hr : 0 < r) (hq : q ≠ 0)
    (h₀ : 0 < k * (-p * q * z * (z - 1) * (p - q)))
    (h₃ : 0 < k * (p * q * (z - 1) * (p - q) * r))
    (h₁₁ : 0 < k * (-p * z * (q - 1) * (p - q) * r))
    (h₁₉ : 0 < k * (p * z * (p - 1) * (p - q) * r))
    (h₇ : 0 < k * (p * q * (p - 1) * (q - z) * r)) : False := by
  let N := k * (-p * q * z * (z - 1) * (p - q))
  let P := k * (p * q * (z - 1) * (p - q) * r)
  let Q := k * (-p * z * (q - 1) * (p - q) * r)
  let R := k * (p * z * (p - 1) * (p - q) * r)
  change 0 < N at h₀
  change 0 < P at h₃
  change 0 < Q at h₁₁
  change 0 < R at h₁₉
  have hz : z < 0 := by
    have he : P * z = -N * r := by dsimp only [P, N]; ring
    exact neg_of_mul_neg_right (he.symm ▸ mul_neg_of_neg_of_pos (neg_lt_zero.mpr h₀) hr) h₃.le
  have hz₁ : z - 1 < 0 := by linarith only [hz]
  have hqsgn : q * (q - 1) < 0 := by
    have he : Q * (z - 1) * q ^ 2 = N * r * (q * (q - 1)) := by
      dsimp only [Q, N]
      ring
    have hs := mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg h₁₁ hz₁) (sq_pos_of_ne_zero hq)
    exact neg_of_mul_neg_right (he ▸ hs) (mul_pos h₀ hr).le
  have hq₀ : 0 < q := by
    by_contra h
    have hq' := le_of_not_gt h
    exact (not_le_of_gt hqsgn) (mul_nonneg_of_nonpos_of_nonpos hq' (by linarith only [hq']))
  have hq₁ : q < 1 := sub_neg.mp (neg_of_mul_neg_right hqsgn hq₀.le)
  have hp₁ : 1 < p := by
    have he : R * q * (1 - z) = N * r * (p - 1) := by dsimp only [R, N]; ring
    have hs := mul_pos (mul_pos h₁₉ hq₀) (by linarith only [hz] : 0 < 1 - z)
    exact sub_pos.mp ((mul_pos_iff_of_pos_left (mul_pos h₀ hr)).mp (he ▸ hs))
  have hp₀ : 0 < p := zero_lt_one.trans hp₁
  have hneg : -p * q * z * (z - 1) * (p - q) < 0 := by
    have h₁ := mul_neg_of_neg_of_pos (neg_lt_zero.mpr hp₀) hq₀
    have h₂ := mul_pos_of_neg_of_neg h₁ hz
    exact mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg h₂ hz₁) (sub_pos.mpr (hq₁.trans hp₁))
  have hn₇ := mul_pos
    (mul_pos (mul_pos (mul_pos hp₀ hq₀) (sub_pos.mpr hp₁)) (sub_pos.mpr (hz.trans hq₀))) hr
  have hk : 0 < k := pos_of_mul_pos_left h₇ hn₇.le
  exact (mul_neg_of_pos_of_neg hk hneg).not_gt h₀

private noncomputable def type36PoleProduct (x t y w z d : ℂ) (i : Fin 24) : ℂ :=
  let A : Fin 4 → ℂ := ![x, t, 0, y]
  let σ := (fourPerm i).symm
  (A (σ 0) - w) * (A (σ 2) - z) * (A (σ 3) - d)

private theorem type36_cubic_im (c₀ c₁ c₂ c₃ : ℝ) (t : ℂ) (ht : t ≠ 0) (ht₁ : t ≠ 1) :
    let F := (c₀ : ℂ) + (c₁ : ℂ) * t + (c₂ : ℂ) * t ^ 2 + (c₃ : ℂ) * t ^ 3
    let r := Complex.normSq t
    let s := Complex.normSq (1 - t)
    r * s * (F / (t * (1 - t))).im =
      t.im * (r * (c₀ + c₁ + c₂ + c₃) - s * c₀ - r * s * c₃) := by
  intro F r s
  have ht' : 1 - t ≠ 0 := sub_ne_zero.mpr ht₁.symm
  have hr : r ≠ 0 := (Complex.normSq_pos.mpr ht).ne'
  have hs : s ≠ 0 := (Complex.normSq_pos.mpr ht').ne'
  have he : F / (t * (1 - t)) = (c₀ : ℂ) / t +
      ((c₀ + c₁ + c₂ + c₃ : ℝ) : ℂ) / (1 - t) - ((c₂ + c₃ : ℝ) : ℂ) - (c₃ : ℂ) * t := by
    dsimp only [F]
    push_cast
    field_simp [ht, ht']
    <;> ring
  rw [he]
  simp only [Complex.sub_im, Complex.add_im, Complex.div_im, Complex.ofReal_im,
    Complex.ofReal_re, Complex.mul_im, Complex.one_im, zero_sub, zero_mul, mul_zero,
    zero_add, add_zero, sub_zero]
  field_simp [r, s, hr, hs] <;> ring

private theorem type36_factor_im (a b c d e f : ℝ) (t : ℂ) (ht : t ≠ 0) (ht₁ : t ≠ 1) :
    let F := ((a : ℂ) + (b : ℂ) * t) * ((c : ℂ) + (d : ℂ) * t) * ((e : ℂ) + (f : ℂ) * t)
    let r := Complex.normSq t
    let s := Complex.normSq (1 - t)
    r * s * (F / (t * (1 - t))).im =
      t.im * (r * ((a + b) * (c + d) * (e + f)) - s * (a * c * e) - r * s * (b * d * f)) := by
  intro F r s
  let c₀ := a * c * e
  let c₁ := a * c * f + a * d * e + b * c * e
  let c₂ := a * d * f + b * c * f + b * d * e
  let c₃ := b * d * f
  have hF : F = (c₀ : ℂ) + (c₁ : ℂ) * t + (c₂ : ℂ) * t ^ 2 + (c₃ : ℂ) * t ^ 3 := by
    dsimp only [F, c₀, c₁, c₂, c₃]
    push_cast
    ring
  rw [hF]
  refine (type36_cubic_im c₀ c₁ c₂ c₃ t ht ht₁).trans ?_
  dsimp only [c₀, c₁, c₂, c₃]
  ring

set_option maxHeartbeats 2500000 in
private theorem type36_normalized_exclusion (p q z : ℝ) (t ξ : ℂ)
    (hp : p ≠ 0) (hq : q ≠ 0) (hqz : q ≠ z) (ht : t ≠ 0) (ht₁ : t ≠ 1) (hξ : ξ ≠ 0) :
    let F := type36PoleProduct p t q ((p : ℂ) * t) z ((q : ℂ) * t)
    let g (i : Fin 24) := (ξ * F i).re
    g 1 = 0 → g 9 = 0 → 0 < g 0 → 0 < g 3 → 0 < g 11 → 0 < g 19 → 0 < g 7 → False := by
  intro F g h₁ h₉ h₀ h₃ h₁₁ h₁₉ h₇
  let r := Complex.normSq t
  let s := Complex.normSq (1 - t)
  let H := t * (1 - t)
  let μ := (ξ * H).im
  have hr : 0 < r := Complex.normSq_pos.mpr ht
  have hs : 0 < s := Complex.normSq_pos.mpr (sub_ne_zero.mpr ht₁.symm)
  have hH : H ≠ 0 := mul_ne_zero ht (sub_ne_zero.mpr ht₁.symm)
  have hcontact : (ξ * H).re = 0 := by
    have he : F 1 = ((-p * q * (q - z) : ℝ) : ℂ) * H := by
      change (↑p - ↑p * t) * (↑q - ↑z) * (0 - ↑q * t) = _
      dsimp only [H]
      push_cast
      ring
    change (ξ * F 1).re = 0 at h₁
    rw [he, mul_left_comm, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero] at h₁
    exact (mul_eq_zero.mp h₁).resolve_left
      (mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr hp) hq) (sub_ne_zero.mpr hqz))
  have hμ : μ ≠ 0 := fun e => mul_ne_zero hξ hH (Complex.ext hcontact e)
  have hg (i : Fin 24) : g i = -μ * (F i / H).im := by
    have he : ξ * F i = (ξ * H) * (F i / H) := by field_simp [hH] <;> ring
    change (ξ * F i).re = _
    rw [he, Complex.mul_re, hcontact, zero_mul, zero_sub, neg_mul]
  have hfi (i : Fin 24) (a b c d e f : ℝ)
      (h : F i = ((a : ℂ) + (b : ℂ) * t) * ((c : ℂ) + (d : ℂ) * t) * ((e : ℂ) + (f : ℂ) * t)) :
      r * s * (F i / H).im =
        t.im * (r * ((a + b) * (c + d) * (e + f)) - s * (a * c * e) - r * s * (b * d * f)) := by
    rw [h]
    exact type36_factor_im a b c d e f t ht ht₁
  have hF0 : r * s * (F 0 / H).im = t.im * (p * q * z * s) := by
    have he := hfi 0 (p) (-p) (-z) (0) (q) (-q) (by
      change (↑p - ↑p * t) * (0 - ↑z) * (↑q - ↑q * t) = _
      push_cast
      ring)
    exact he.trans (by ring)
  have hF3 : r * s * (F 3 / H).im = t.im * (-r * s * p * q) := by
    have he := hfi 3 (p) (-p) (-z) (1) (0) (-q) (by
      change (↑p - ↑p * t) * (t - ↑z) * (0 - ↑q * t) = _
      push_cast
      ring)
    exact he.trans (by ring)
  have hF11 : r * s * (F 11 / H).im = t.im * (-r * z * (p - q) * (q - 1)) := by
    have he := hfi 11 (q) (-p) (-z) (0) (0) (1 - q) (by
      change (↑q - ↑p * t) * (0 - ↑z) * (t - ↑q * t) = _
      push_cast
      ring)
    exact he.trans (by ring)
  have hF19 : r * s * (F 19 / H).im = t.im * (r * z * (p - 1) * (p - q)) := by
    have he := hfi 19 (0) (1 - p) (-z) (0) (p) (-q) (by
      change (t - ↑p * t) * (0 - ↑z) * (↑p - ↑q * t) = _
      push_cast
      ring)
    exact he.trans (by ring)
  have hF7 : r * s * (F 7 / H).im = t.im * (r * q * (p - 1) * (q - z)) := by
    have he := hfi 7 (0) (1 - p) (q - z) (0) (0) (-q) (by
      change (t - ↑p * t) * (↑q - ↑z) * (0 - ↑q * t) = _
      push_cast
      ring)
    exact he.trans (by ring)
  have hF9 : r * s * (F 9 / H).im = t.im * (-r * q * (p * s - (p - q) * (1 - z))) := by
    have he := hfi 9 (q) (-p) (-z) (1) (0) (-q) (by
      change (↑q - ↑p * t) * (t - ↑z) * (0 - ↑q * t) = _
      push_cast
      ring)
    exact he.trans (by ring)
  have htIm : t.im ≠ 0 := by
    intro h
    have he := hF0
    rw [h, zero_mul] at he
    have hz := (mul_eq_zero.mp he).resolve_left (mul_ne_zero hr.ne' hs.ne')
    exact h₀.ne' (by rw [hg, hz, mul_zero])
  have hIm9 : (F 9 / H).im = 0 := by
    rw [hg] at h₉
    exact (mul_eq_zero.mp h₉).resolve_left (neg_ne_zero.mpr hμ)
  have hS : p * s = (p - q) * (1 - z) := by
    rw [hIm9, mul_zero] at hF9
    have he := (mul_eq_zero.mp hF9.symm).resolve_left htIm
    exact sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_left (mul_ne_zero (neg_ne_zero.mpr hr.ne') hq))
  let k := (-μ * t.im) / (p * r * s)
  have hscale (i : Fin 24) (N : ℝ) (he : p * (r * s * (F i / H).im) = t.im * N) :
      g i = k * N := by
    rw [hg]
    dsimp only [k]
    field_simp [hp, hr.ne', hs.ne']
    linear_combination (-μ) * he
  have e₀ : g 0 = k * (-p * q * z * (z - 1) * (p - q)) := by
    apply hscale
    linear_combination p * hF0 + t.im * p * q * z * hS
  have e₃ : g 3 = k * (p * q * (z - 1) * (p - q) * r) := by
    apply hscale
    linear_combination p * hF3 - t.im * p * q * r * hS
  have e₁₁ : g 11 = k * (-p * z * (q - 1) * (p - q) * r) := by
    apply hscale
    linear_combination p * hF11
  have e₁₉ : g 19 = k * (p * z * (p - 1) * (p - q) * r) := by
    apply hscale
    linear_combination p * hF19
  have e₇ : g 7 = k * (p * q * (p - 1) * (q - z) * r) := by
    apply hscale
    linear_combination p * hF7
  exact fourZeroHeightType36_sign_certificate p q z r k hr hq
    (e₀ ▸ h₀) (e₃ ▸ h₃) (e₁₁ ▸ h₁₁) (e₁₉ ▸ h₁₉) (e₇ ▸ h₇)

private theorem type36_ratio_of_contacts {ξ F G u v D : ℂ} (hξ : ξ ≠ 0) (hD : D ≠ 0)
    (hF : F = D * u) (hG : G = D * v)
    (hf : (ξ * F).re = 0) (hg : (ξ * G).re = 0) : (u / v).im = 0 := by
  have hu : ((ξ * D) * u).re = 0 := by rwa [mul_assoc, ← hF]
  have hv : ((ξ * D) * v).re = 0 := by rwa [mul_assoc, ← hG]
  rw [← mul_div_mul_left u v (mul_ne_zero hξ hD)]
  simp [Complex.div_im, hu, hv]

private theorem type36_real_quotient {u v : ℂ} (hvu : v - u ≠ 0)
    (h : ((-u) / (v - u)).im = 0) : (u / v).im = 0 := by
  rw [Complex.div_im, ← sub_div] at h ⊢
  have hz := (div_eq_zero_iff.mp h).resolve_right (Complex.normSq_pos.mpr hvu).ne'
  simp only [Complex.neg_im, Complex.neg_re, Complex.sub_im, Complex.sub_re] at hz
  apply div_eq_zero_iff.mpr
  exact Or.inl (by linear_combination -hz)

private theorem type36_remove_real_factor {ξ F T : ℂ} {r : ℝ} (hr : r ≠ 0)
    (hF : F = (r : ℂ) * T) (hc : (ξ * F).re = 0) : (ξ * T).re = 0 := by
  rw [hF, mul_left_comm, Complex.re_ofReal_mul] at hc
  exact (mul_eq_zero.mp hc).resolve_left hr

private theorem type36_pole_scale (k x t y w z d : ℂ) (i : Fin 24) :
    type36PoleProduct (k * x) (k * t) (k * y) (k * w) (k * z) (k * d) i =
      k ^ 3 * type36PoleProduct x t y w z d i := by
  have hA (j : Fin 4) : (![k * x, k * t, 0, k * y] : Fin 4 → ℂ) j =
      k * (![x, t, 0, y] : Fin 4 → ℂ) j := by
    fin_cases j <;> simp [Matrix.cons_val]
  simp only [type36PoleProduct, hA]
  ring

set_option maxHeartbeats 3500000 in
/-- The exact seven-contact type 36 cannot occur at zero lower support
height when the original spectra and the marked spectral points are distinct. -/
theorem fourZeroHeightType36_impossible (a b : Fin 4 → ℂ) (η : ℂ)
    (ha : Function.Injective a) (hb : Function.Injective b) (hab : ∀ i j, a i + b j ≠ 0)
    (hη : η ≠ 0)
    (hc : ∀ i ∈ fourZeroHeightType36Contacts, (η * matchingProduct a b (fourPerm i).symm).re = 0)
    (hs : ∀ i ∉ fourZeroHeightType36Contacts, 0 < (η * matchingProduct a b (fourPerm i).symm).re) :
    False := by
  obtain ⟨c, X, Y, hcn, hX₂, hX₀, hX, _, hXY, hprod⟩ :=
    exists_projective_pole_chart a b 2 0 1 (by decide) ha hb hab
  let t := X 1
  let y := X 3
  let w := Y 0
  let z := Y 2
  let d := Y 3
  let F := type36PoleProduct 1 t y w z d
  let ξ := η * c
  have hξ : ξ ≠ 0 := mul_ne_zero hη hcn
  have hvec : X = ![1, t, 0, y] := by
    funext i
    fin_cases i <;> first | exact hX₀ | exact hX₂ | rfl
  have hscale (i : Fin 24) : η * matchingProduct a b (fourPerm i).symm = ξ * F i := by
    rw [hprod, show (Finset.univ : Finset (Fin 4)).erase 1 = {0, 2, 3} by decide +kernel,
      Finset.prod_insert (by decide : (0 : Fin 4) ∉ ({2, 3} : Finset (Fin 4))),
      Finset.prod_insert (by decide : (2 : Fin 4) ∉ ({3} : Finset (Fin 4))), Finset.prod_singleton]
    dsimp only [F, type36PoleProduct, ξ]
    rw [hvec]
    dsimp only [w, z, d]
    ring
  have hC (i : Fin 24) (hi : i ∈ fourZeroHeightType36Contacts) : (ξ * F i).re = 0 := by
    rw [← hscale]
    exact hc i hi
  have hS (i : Fin 24) (hi : i ∉ fourZeroHeightType36Contacts) : 0 < (ξ * F i).re := by
    rw [← hscale]
    exact hs i hi
  have ht : t ≠ 0 := fun h =>
    (by decide : (1 : Fin 4) ≠ 2) (hX (h.trans hX₂.symm))
  have hy : y ≠ 0 := fun h =>
    (by decide : (3 : Fin 4) ≠ 2) (hX (h.trans hX₂.symm))
  have hw : w ≠ 0 := fun h => hXY 2 0 (by decide) (hX₂.trans h.symm)
  have hz : z ≠ 0 := fun h => hXY 2 2 (by decide) (hX₂.trans h.symm)
  have hd : d ≠ 0 := fun h => hXY 2 3 (by decide) (hX₂.trans h.symm)
  have h1w : 1 - w ≠ 0 := sub_ne_zero.mpr (hX₀ ▸ hXY 0 0 (by decide))
  have h1z : 1 - z ≠ 0 := sub_ne_zero.mpr (hX₀ ▸ hXY 0 2 (by decide))
  have hyz : y - z ≠ 0 := sub_ne_zero.mpr (hXY 3 2 (by decide))
  have hyd : y - d ≠ 0 := sub_ne_zero.mpr (hXY 3 3 (by decide))
  have htd : t - d ≠ 0 := sub_ne_zero.mpr (hXY 1 3 (by decide))
  have htw : t - w ≠ 0 := sub_ne_zero.mpr (hXY 1 0 (by decide))
  have hF1 : F 1 = (1 - w) * (y - z) * (-d) := by
    change (1 - w) * (y - z) * (0 - d) = _
    rw [zero_sub]
  have hF4 : F 4 = (1 - w) * (y - z) * (t - d) := rfl
  have hF5 : F 5 = (1 - w) * (t - d) * (-z) := by
    change (1 - w) * (0 - z) * (t - d) = _
    ring
  have hF6 : F 6 = (t - w) * (y - d) * (-z) := by
    change (t - w) * (0 - z) * (y - d) = _
    ring
  have hF12 : F 12 = (t - w) * (y - d) * (1 - z) := by
    change (t - w) * (1 - z) * (y - d) = _
    ring
  have hF14 : F 14 = (1 - z) * (y - d) * (-w) := by
    change (0 - w) * (1 - z) * (y - d) = _
    ring
  have hF0 : F 0 = (1 - w) * (0 - z) * (y - d) := rfl
  have hqim : (d / t).im = 0 := type36_real_quotient htd
    (type36_ratio_of_contacts hξ (mul_ne_zero h1w hyz) hF1 hF4
      (hC 1 (by decide)) (hC 4 (by decide)))
  have hzim : z.im = 0 := by
    have he := type36_real_quotient h1z
      (type36_ratio_of_contacts hξ (mul_ne_zero htw hyd) hF6 hF12
        (hC 6 (by decide)) (hC 12 (by decide)))
    simpa only [div_one] using he
  have hyim : y.im = 0 := by
    have hhF4 : F 4 = (1 - w) * (t - d) * (y - z) := by rw [hF4]; ring
    have he := type36_real_quotient hyz
      (type36_ratio_of_contacts hξ (mul_ne_zero h1w htd) hF5 hhF4
        (hC 5 (by decide)) (hC 4 (by decide)))
    rw [Complex.div_im, ← sub_div] at he
    have hn := (div_eq_zero_iff.mp he).resolve_right (Complex.normSq_pos.mpr hy).ne'
    simp only [hzim, zero_mul, zero_sub, neg_eq_zero] at hn
    exact (mul_eq_zero.mp hn).resolve_left (fun e => hz (Complex.ext e hzim))
  have hpim : (w / t).im = 0 := by
    have hhF12 : F 12 = (1 - z) * (y - d) * (t - w) := by rw [hF12]; ring
    exact type36_real_quotient htw
      (type36_ratio_of_contacts hξ (mul_ne_zero h1z hyd) hF14 hhF12
        (hC 14 (by decide)) (hC 12 (by decide)))
  let p := (w / t).re
  let q := (d / t).re
  let Y₀ := y.re
  let Z₀ := z.re
  have hpc : (p : ℂ) = w / t := Complex.ext (by simp [p]) (by simpa using hpim.symm)
  have hqc : (q : ℂ) = d / t := Complex.ext (by simp [q]) (by simpa using hqim.symm)
  have hyc : (Y₀ : ℂ) = y := Complex.ext (by simp [Y₀]) (by simpa using hyim.symm)
  have hzc : (Z₀ : ℂ) = z := Complex.ext (by simp [Z₀]) (by simpa using hzim.symm)
  have hp₀ : p ≠ 0 := fun e => div_ne_zero hw ht (by simpa only [e, Complex.ofReal_zero] using hpc.symm)
  have hq₀ : q ≠ 0 := fun e => div_ne_zero hd ht (by simpa only [e, Complex.ofReal_zero] using hqc.symm)
  have hpt : (p : ℂ) * t = w := by rw [hpc, div_mul_cancel₀ _ ht]
  have hqt : (q : ℂ) * t = d := by rw [hqc, div_mul_cancel₀ _ ht]
  have hp₁ : p ≠ 1 := by
    intro e
    apply htw
    simpa only [e, Complex.ofReal_one, one_mul] using (sub_eq_zero.mpr hpt)
  have hz₀ : Z₀ ≠ 0 := fun e => hz (by simpa only [e, Complex.ofReal_zero] using hzc.symm)
  have hyz₀ : Y₀ - Z₀ ≠ 0 := by
    intro e
    apply hyz
    rw [← hyc, ← hzc, ← Complex.ofReal_sub, e, Complex.ofReal_zero]
  have htim : t.im ≠ 0 := by
    intro htIm
    have hwi : w.im = 0 := by
      rw [← hpt]
      simp [Complex.mul_im, htIm]
    have hdi : d.im = 0 := by
      rw [← hqt]
      simp [Complex.mul_im, htIm]
    have h1i : (F 1).im = 0 := by
      rw [hF1]
      simp [Complex.mul_im, Complex.sub_im, Complex.neg_im, hwi, hyim, hzim, hdi]
    have h0i : (F 0).im = 0 := by
      rw [hF0]
      simp [Complex.mul_im, Complex.sub_im, hwi, hyim, hzim, hdi]
    have h1n : F 1 ≠ 0 := by
      rw [hF1]
      exact mul_ne_zero (mul_ne_zero h1w hyz) (neg_ne_zero.mpr hd)
    have he := hC 1 (by decide)
    rw [Complex.mul_re, h1i, mul_zero, sub_zero] at he
    have hξr := (mul_eq_zero.mp he).resolve_right (fun e => h1n (Complex.ext e h1i))
    have hz' := hS 0 (by decide)
    rw [Complex.mul_re, hξr, h0i, zero_mul, mul_zero, sub_self] at hz'
    exact (lt_irrefl 0) hz'
  have hF1' : F 1 = ((-(q * (Y₀ - Z₀)) : ℝ) : ℂ) * (t * (1 - (p : ℂ) * t)) := by
    rw [hF1, ← hpt, ← hqt, ← hyc, ← hzc]
    push_cast
    ring
  have hF6' : F 6 = ((-(Z₀ * (1 - p)) : ℝ) : ℂ) * (t * ((Y₀ : ℂ) - (q : ℂ) * t)) := by
    rw [hF6, ← hpt, ← hqt, ← hyc, ← hzc]
    push_cast
    ring
  have hC1 := type36_remove_real_factor (neg_ne_zero.mpr (mul_ne_zero hq₀ hyz₀)) hF1' (hC 1 (by decide))
  have hC6 := type36_remove_real_factor (neg_ne_zero.mpr (mul_ne_zero hz₀ (sub_ne_zero.mpr hp₁.symm)))
    hF6' (hC 6 (by decide))
  have hf : ((1 - (p : ℂ) * t) / ((Y₀ : ℂ) - (q : ℂ) * t)).im = 0 :=
    type36_ratio_of_contacts hξ ht rfl rfl hC1 hC6
  have hyd' : (Y₀ : ℂ) - (q : ℂ) * t ≠ 0 := by simpa only [hyc, hqt] using hyd
  rw [Complex.div_im, ← sub_div] at hf
  have e := (div_eq_zero_iff.mp hf).resolve_right (Complex.normSq_pos.mpr hyd').ne'
  simp only [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.one_re, Complex.one_im, mul_zero, zero_mul,
    sub_zero, zero_sub, add_zero] at e
  have hprod' : t.im * (q - p * Y₀) = 0 := by linear_combination e
  have hqEq : q = p * Y₀ := sub_eq_zero.mp ((mul_eq_zero.mp hprod').resolve_left htim)
  let T := (p : ℂ) * t
  let Z := p * Z₀
  let ξ' := ξ / (p : ℂ) ^ 3
  have hpC : (p : ℂ) ≠ 0 := fun e' => hp₀ (Complex.ofReal_eq_zero.mp e')
  have hqZ : q ≠ Z := by
    intro e'
    have he : p * Y₀ = p * Z₀ := hqEq.symm.trans e'
    exact hyz₀ (sub_eq_zero.mpr (mul_left_cancel₀ hp₀ he))
  have hT₀ : T ≠ 0 := by simpa only [T, hpt] using hw
  have hT₁ : T ≠ 1 := by
    rw [show T = w from hpt]
    exact (sub_ne_zero.mp h1w).symm
  have hξ' : ξ' ≠ 0 := div_ne_zero hξ (pow_ne_zero _ hpC)
  have heQ : (q : ℂ) = (p : ℂ) * y := by rw [hqEq, Complex.ofReal_mul, hyc]
  have heZ : (Z : ℂ) = (p : ℂ) * z := by rw [show Z = p * Z₀ from rfl, Complex.ofReal_mul, hzc]
  have heD : (q : ℂ) * T = (p : ℂ) * d := by rw [← hqt]; dsimp only [T]; ring
  have heW : (p : ℂ) * T = (p : ℂ) * w := by rw [show T = w from hpt]
  have hrescale (i : Fin 24) :
      ξ' * type36PoleProduct p T q ((p : ℂ) * T) Z ((q : ℂ) * T) i = ξ * F i := by
    calc
      _ = ξ' * type36PoleProduct ((p : ℂ) * 1) ((p : ℂ) * t) ((p : ℂ) * y)
          ((p : ℂ) * w) ((p : ℂ) * z) ((p : ℂ) * d) i := by
        rw [heD, heZ, heW, heQ, mul_one]
      _ = ξ * F i := by
        rw [type36_pole_scale]
        dsimp only [ξ', F]
        rw [← mul_assoc, div_mul_cancel₀ _ (pow_ne_zero _ hpC)]
  have hC' (i : Fin 24) (hi : i ∈ fourZeroHeightType36Contacts) :
      (ξ' * type36PoleProduct p T q ((p : ℂ) * T) Z ((q : ℂ) * T) i).re = 0 := by
    rw [hrescale]
    exact hC i hi
  have hS' (i : Fin 24) (hi : i ∉ fourZeroHeightType36Contacts) :
      0 < (ξ' * type36PoleProduct p T q ((p : ℂ) * T) Z ((q : ℂ) * T) i).re := by
    rw [hrescale]
    exact hS i hi
  exact type36_normalized_exclusion p q Z T ξ' hp₀ hq₀ hqZ hT₀ hT₁ hξ'
    (hC' 1 (by decide)) (hC' 9 (by decide)) (hS' 0 (by decide)) (hS' 3 (by decide))
    (hS' 11 (by decide)) (hS' 19 (by decide)) (hS' 7 (by decide))

end MOC
