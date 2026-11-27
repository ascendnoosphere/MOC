import MOC.ContactCensus
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-! The distinct projective chart for the six mixed-budget pattern contacts. -/

namespace MOC

/-- The mixed-budget pattern products with `A = (z, 1, 0, x)` and `C = (w, v, ∞, t*v)`. -/
noncomputable def fourMixedBudgetPoleProduct (z x w v t : ℂ) (i : Fin 24) : ℂ :=
  let A : Fin 4 → ℂ := ![z, 1, 0, x]
  let σ := (fourPerm i).symm
  (A (σ 0) - w) * (A (σ 1) - v) * (A (σ 3) - t * v)

/-- The matching labels that enter the mixed-budget pattern contact and capacity identities. -/
def fourMixedBudgetRatioIndices : Fin 16 → Fin 24 := ![0, 1, 2, 3, 4, 6, 7, 8, 9, 10, 11, 12, 13, 16, 17, 22]

/-- Factored original products at the labels used by the mixed-budget pattern proof. -/
theorem fourMixedBudget_pole_product_values (z x w v t : ℂ) (i : Fin 16) :
    fourMixedBudgetPoleProduct z x w v t (fourMixedBudgetRatioIndices i) =
      (![(1 - v) * (z - w) * (x - t * v), t * v * (v - 1) * (z - w),
        -v * (z - w) * (x - t * v), -t * v * (x - v) * (z - w),
        v * (z - w) * (t * v - 1), (z - v) * (1 - w) * (x - t * v),
        t * v * (z - v) * (w - 1), -w * (z - v) * (x - t * v),
        -t * v * (z - v) * (x - w), w * (z - v) * (t * v - 1),
        -(z - v) * (x - w) * (t * v - 1), v * (w - 1) * (x - t * v),
        t * v * (x - v) * (w - 1), w * (x - v) * (t * v - 1),
        v * (x - w) * (t * v - 1), -w * (x - v) * (z - t * v)] : Fin 16 → ℂ) i := by
  have h : ∀ k : Fin 16,
      let σ := (fourPerm (fourMixedBudgetRatioIndices k)).symm
      σ 0 = (![0, 0, 0, 0, 0, 1, 1, 2, 3, 2, 3, 1, 1, 2, 3, 2] : Fin 16 → Fin 4) k ∧
      σ 1 = (![1, 1, 2, 3, 2, 0, 0, 0, 0, 0, 0, 2, 3, 3, 2, 3] : Fin 16 → Fin 4) k ∧
      σ 3 = (![3, 2, 3, 2, 1, 3, 2, 3, 2, 1, 1, 3, 2, 1, 1, 0] : Fin 16 → Fin 4) k := by
    decide +kernel
  obtain ⟨h₀, h₁, h₂⟩ := h i
  dsimp only [fourMixedBudgetPoleProduct]
  rw [h₀, h₁, h₂]
  fin_cases i <;> simp [Matrix.cons_val] <;> ring_nf <;> simp

private theorem im_eq_zero_of_pure_factor {p q : ℂ} (hp : p.re = 0) (hp₀ : p ≠ 0)
    (hq : (p * q).re = 0) : q.im = 0 := by
  have hpi : p.im ≠ 0 := fun h => hp₀ (Complex.ext (by simpa using hp) (by simpa using h))
  have him : -(p.im * q.im) = 0 := by simpa only [Complex.mul_re, hp, zero_mul, zero_sub] using hq
  exact (mul_eq_zero.mp (neg_eq_zero.mp him)).resolve_left hpi

/-- The first four contacts shared by mixed-budget pattern and ordered-ratio pattern make both projective
parameters real and determine the common support phase. -/
theorem fourMixedBudget_pole_line_parameters (z x w v t η : ℂ) (H : ℝ)
    (hzw : z ≠ w) (hv : v ≠ 0) (ht₁ : t ≠ 1) (hx₁ : x ≠ 1) (hη : η ≠ 0)
    (hc : ∀ i ∈ ({1, 2, 3, 4} : Finset (Fin 24)),
      (η * fourMixedBudgetPoleProduct z x w v t i).re = H) :
    t.im = 0 ∧ x.im = 0 ∧ (η * (v * (z - w))).re = 0 := by
  let F := fourMixedBudgetPoleProduct z x w v t
  let D := v * (z - w)
  let f := x - t * v
  have hD : D ≠ 0 := mul_ne_zero hv (sub_ne_zero.mpr hzw)
  have hηD : η * D ≠ 0 := mul_ne_zero hη hD
  have hF1 : F 1 = t * v * (v - 1) * (z - w) := fourMixedBudget_pole_product_values z x w v t 1
  have hF2 : F 2 = -v * (z - w) * f := fourMixedBudget_pole_product_values z x w v t 2
  have hF3 : F 3 = -t * v * (x - v) * (z - w) := fourMixedBudget_pole_product_values z x w v t 3
  have hF4 : F 4 = D * (t * v - 1) := fourMixedBudget_pole_product_values z x w v t 4
  have hline {i j : Fin 24} (hi : i ∈ ({1, 2, 3, 4} : Finset (Fin 24)))
      (hj : j ∈ ({1, 2, 3, 4} : Finset (Fin 24))) : (η * (F i - F j)).re = 0 := by
    change (η * (fourMixedBudgetPoleProduct z x w v t i - fourMixedBudgetPoleProduct z x w v t j)).re = 0
    rw [mul_sub, Complex.sub_re, hc i hi, hc j hj, sub_self]
  have h42 : F 4 - F 2 = D * (x - 1) := by rw [hF4, hF2]; dsimp only [D, f]; ring
  have h31 : F 3 - F 1 = -t * (F 4 - F 2) := by rw [h42, hF3, hF1]; dsimp only [D]; ring
  have h41 : F 4 - F 1 = D * (t - 1) := by rw [hF4, hF1]; dsimp only [D]; ring
  have ht_re : t.im = 0 := by
    have h42' := hline (i := 4) (j := 2) (by decide) (by decide)
    have h42₀ : η * (F 4 - F 2) ≠ 0 := by rw [h42]; exact mul_ne_zero hη (mul_ne_zero hD (sub_ne_zero.mpr hx₁))
    have h31' : (η * (F 4 - F 2) * t).re = 0 := by
      have h := hline (i := 3) (j := 1) (by decide) (by decide)
      rw [h31, show η * (-t * (F 4 - F 2)) = -(η * (F 4 - F 2) * t) by ring,
        Complex.neg_re, neg_eq_zero] at h
      exact h
    exact im_eq_zero_of_pure_factor h42' h42₀ h31'
  have hdir : (η * D).re = 0 := by
    have h := hline (i := 4) (j := 1) (by decide) (by decide)
    have htr : t.re - 1 ≠ 0 := fun he => ht₁ (Complex.ext (by simpa using sub_eq_zero.mp he)
      (by simpa using ht_re))
    rw [h41, ← mul_assoc, Complex.mul_re] at h
    simpa only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im, ht_re,
      sub_self, mul_zero, sub_zero, mul_eq_zero, htr, or_false] using h
  have hx_re : x.im = 0 := by
    have h := hline (i := 4) (j := 2) (by decide) (by decide)
    rw [h42, ← mul_assoc] at h
    simpa only [Complex.sub_im, Complex.one_im, sub_zero] using im_eq_zero_of_pure_factor hdir hηD h
  exact ⟨ht_re, hx_re, hdir⟩

/-- The six mixed-budget pattern contacts force real `x,t,r,u` with the stated solved chart.
Both divisions and the translated denominator of the capacity are nonzero. -/
theorem fourMixedBudget_normalized_chart (z x w v t η : ℂ) (H : ℝ)
    (hz : z ≠ 0) (hzv : z ≠ v) (hzw : z ≠ w) (hv : v ≠ 0) (hvw : v ≠ w)
    (htx : x ≠ t * v) (ht₁ : t ≠ 1) (hx₁ : x ≠ 1) (hη : η ≠ 0)
    (hc : ∀ i ∈ ({1, 2, 3, 4, 6, 8} : Finset (Fin 24)),
      (η * fourMixedBudgetPoleProduct z x w v t i).re = H) :
    t.im = 0 ∧ x.im = 0 ∧ (η * (v * (z - w))).re = 0 ∧
    ∃ r u : ℝ, (r : ℂ) ≠ 0 ∧ (u : ℂ) ≠ 0 ∧
      let G := x - (t + u) * v
      G ≠ 0 ∧ G - (r : ℂ) ≠ 0 ∧ z = (r : ℂ) * v / G ∧ w = (x - r - t * v) / u := by
  let F := fourMixedBudgetPoleProduct z x w v t
  let D := v * (z - w)
  let f := x - t * v
  have hD : D ≠ 0 := mul_ne_zero hv (sub_ne_zero.mpr hzw)
  have hηD : η * D ≠ 0 := mul_ne_zero hη hD
  have hF2 : F 2 = -v * (z - w) * f := fourMixedBudget_pole_product_values z x w v t 2
  have hF6 : F 6 = (z - v) * (1 - w) * f := fourMixedBudget_pole_product_values z x w v t 5
  have hF8 : F 8 = -w * (z - v) * f := fourMixedBudget_pole_product_values z x w v t 7
  have hline {i j : Fin 24} (hi : i ∈ ({1, 2, 3, 4, 6, 8} : Finset (Fin 24)))
      (hj : j ∈ ({1, 2, 3, 4, 6, 8} : Finset (Fin 24))) : (η * (F i - F j)).re = 0 := by
    change (η * (fourMixedBudgetPoleProduct z x w v t i - fourMixedBudgetPoleProduct z x w v t j)).re = 0
    rw [mul_sub, Complex.sub_re, hc i hi, hc j hj, sub_self]
  have hsub : ({1, 2, 3, 4} : Finset (Fin 24)) ⊆ {1, 2, 3, 4, 6, 8} := by decide
  obtain ⟨ht_re, hx_re, hdir⟩ := fourMixedBudget_pole_line_parameters z x w v t η H hzw hv ht₁ hx₁ hη
    (fun i hi => hc i (hsub hi))
  let R := (F 8 - F 2) / D
  let U := (F 6 - F 8) / D
  have hRD : R * D = z * (v - w) * f := by
    calc
      _ = F 8 - F 2 := div_mul_cancel₀ _ hD
      _ = _ := by rw [hF8, hF2]; ring
  have hUD : U * D = (z - v) * f := by
    calc
      _ = F 6 - F 8 := div_mul_cancel₀ _ hD
      _ = _ := by rw [hF6, hF8]; ring
  have hR₀ : R ≠ 0 := by
    intro h
    rw [h, zero_mul] at hRD
    exact mul_ne_zero (mul_ne_zero hz (sub_ne_zero.mpr hvw)) (sub_ne_zero.mpr htx) hRD.symm
  have hU₀ : U ≠ 0 := by
    intro h
    rw [h, zero_mul] at hUD
    exact mul_ne_zero (sub_ne_zero.mpr hzv) (sub_ne_zero.mpr htx) hUD.symm
  have hreal (p : ℂ) (i j : Fin 24) (h : p * D = F i - F j)
      (hi : i ∈ ({1, 2, 3, 4, 6, 8} : Finset (Fin 24)))
      (hj : j ∈ ({1, 2, 3, 4, 6, 8} : Finset (Fin 24))) : (p.re : ℂ) = p := by
    have him : p.im = 0 := im_eq_zero_of_pure_factor hdir hηD (by
      rw [show (η * D) * p = η * (p * D) by ring, h]
      exact hline hi hj)
    exact Complex.ext (by simp) (by simpa using him.symm)
  have hR := hreal R 8 2 (div_mul_cancel₀ _ hD) (by decide) (by decide)
  have hU := hreal U 6 8 (div_mul_cancel₀ _ hD) (by decide) (by decide)
  have hwid : w * U = f - R := by
    apply mul_right_cancel₀ hD
    dsimp only [D]
    change R * (v * (z - w)) = _ at hRD
    change U * (v * (z - w)) = _ at hUD
    linear_combination w * hUD + hRD
  let G := x - (t + U) * v
  have hzid : z * G = R * v := by
    change U * (v * (z - w)) = _ at hUD
    dsimp only [G, f] at hUD hwid ⊢
    linear_combination -hUD - v * hwid
  have hG : G ≠ 0 := by
    intro h
    rw [h, mul_zero] at hzid
    exact mul_ne_zero hR₀ hv hzid.symm
  have hGR : G - R ≠ 0 := by
    intro h
    have he := sub_eq_zero.mp h
    rw [he, mul_comm R v] at hzid
    exact hzv (mul_right_cancel₀ hR₀ hzid)
  refine ⟨ht_re, hx_re, hdir, R.re, U.re, ?_⟩
  rw [hR, hU]
  refine ⟨hR₀, hU₀, hG, hGR, (eq_div_iff hG).mpr hzid, (eq_div_iff hU₀).mpr ?_⟩
  dsimp only [f] at hwid
  linear_combination hwid

end MOC

/-! Ratios of mixed-budget pattern matching products after cancelling the common chart factors. -/

namespace MOC

set_option maxHeartbeats 1400000 in
/-- The ten original mixed-budget pattern ratios needed for the capacity argument. -/
theorem fourMixedBudget_exact_pole_ratios (x t r u z w v : ℂ)
    (hv : v ≠ 0) (hu : u ≠ 0) (hzw : z ≠ w) (hf : x - t * v ≠ 0)
    (hG : x - (t + u) * v ≠ 0) (hP : x - (t + u) * v - r ≠ 0)
    (hz : z = r * v / (x - (t + u) * v)) (hw : w = (x - r - t * v) / u) :
    let F := fourMixedBudgetPoleProduct z x w v t
    let R (i : Fin 24) := (F i - F 1) / (v * (z - w))
    let f := x - t * v
    let G := x - (t + u) * v
    let P := G - r
    let W := f - r
    let V := W - u
    let K := u * x - W
    let C := t * (1 - v)
    R 0 = x / v - x ∧ R 7 = t - t * v * (r + u) / f ∧ R 9 = t - t * v * (r + u * x) / f ∧
    R 10 = t - 1 + r - r * (x - 1) / f ∧ R 11 = -K * (t * v - 1) / f + C ∧
    R 12 = -(x - r - t - u) - r * V / P ∧ R 13 = -t * (x - v) * V * G / (f * P) + C ∧
    R 16 = -W * (x - v) * (t * v - 1) * G / (v * f * P) + C ∧
    R 17 = -K * (t * v - 1) * G / (f * P) + C ∧ R 22 = W * (x - v) * (r - t * G) / (f * P) + C := by
  intro F R f G P W V K C
  let D := v * (z - w)
  have hf' : f ≠ 0 := hf
  have hG' : G ≠ 0 := hG
  have hP' : P ≠ 0 := hP
  have hD₀ : D ≠ 0 := mul_ne_zero hv (sub_ne_zero.mpr hzw)
  have hz' : z = r * v / G := hz
  have hw' : w = W / u := by rw [hw]; dsimp only [W, f]; ring
  have hzw_eq : z - w = -f * P / (u * G) := by
    rw [hz', hw']
    field_simp [hu, hG']
    dsimp only [W, P, G, f]
    ring
  let Dn := -v * f * P
  have hDn : Dn ≠ 0 := mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr hv) hf') hP'
  have hD : D = Dn / (u * G) := by
    dsimp only [D]
    rw [hzw_eq]
    field_simp [hu, hG'] <;> dsimp only [Dn] <;> ring
  have hzv : z - v = -v * P / G := by rw [hz']; field_simp [hG']; dsimp only [P]; ring
  have hztv : z - t * v = v * (r - t * G) / G := by rw [hz']; field_simp [hG'] <;> ring
  have hw₁ : w - 1 = V / u := by rw [hw']; field_simp [hu]; rfl
  have hxw : x - w = K / u := by rw [hw']; field_simp [hu]; dsimp only [K]; ring
  have hF₀ : F 0 = (1 - v) * (z - w) * f := fourMixedBudget_pole_product_values z x w v t 0
  have hF₁ : F 1 = t * v * (v - 1) * (z - w) := fourMixedBudget_pole_product_values z x w v t 1
  have hF₇ : F 7 = t * v * (z - v) * (w - 1) := fourMixedBudget_pole_product_values z x w v t 6
  have hF₉ : F 9 = -t * v * (z - v) * (x - w) := fourMixedBudget_pole_product_values z x w v t 8
  have hF₁₀ : F 10 = w * (z - v) * (t * v - 1) := fourMixedBudget_pole_product_values z x w v t 9
  have hF₁₁ : F 11 = -(z - v) * (x - w) * (t * v - 1) := fourMixedBudget_pole_product_values z x w v t 10
  have hF₁₂ : F 12 = v * (w - 1) * f := fourMixedBudget_pole_product_values z x w v t 11
  have hF₁₃ : F 13 = t * v * (x - v) * (w - 1) := fourMixedBudget_pole_product_values z x w v t 12
  have hF₁₆ : F 16 = w * (x - v) * (t * v - 1) := fourMixedBudget_pole_product_values z x w v t 13
  have hF₁₇ : F 17 = v * (x - w) * (t * v - 1) := fourMixedBudget_pole_product_values z x w v t 14
  have hF₂₂ : F 22 = -w * (x - v) * (z - t * v) := fourMixedBudget_pole_product_values z x w v t 15
  have hR (i : Fin 24) : R i = F i / D + C := by
    change (F i - F 1) / D = _
    have h : F 1 = D * (t * (v - 1)) := by rw [hF₁]; dsimp only [D]; ring
    rw [h, sub_div, mul_div_cancel_left₀ _ hD₀]
    dsimp only [C]
    ring
  have hRnorm (i : Fin 24) (a b : ℂ) (hb : b ≠ 0)
      (hnum : F i * (u * G) * b = a * Dn) : R i = a / b + C := by
    rw [hR, hD, div_div_eq_mul_div, (div_eq_div_iff hDn hb).mpr hnum]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hR, hF₀]
    dsimp only [D]
    field_simp [hv, sub_ne_zero.mpr hzw] <;> dsimp only [f, C] <;> ring
  · rw [hRnorm 7 (t * v * V) f hf' (by
      rw [hF₇, hzv, hw₁]
      field_simp [hu, hG'] <;> dsimp only [Dn] <;> ring)]
    field_simp [hf'] <;> dsimp only [V, W, C] <;> ring
  · rw [hRnorm 9 (-t * v * K) f hf' (by
      rw [hF₉, hzv, hxw]
      field_simp [hu, hG'] <;> dsimp only [Dn] <;> ring)]
    field_simp [hf'] <;> dsimp only [K, W, C] <;> ring
  · rw [hRnorm 10 (W * (t * v - 1)) f hf' (by
      rw [hF₁₀, hzv, hw']
      field_simp [hu, hG'] <;> dsimp only [Dn] <;> ring)]
    field_simp [hf'] <;> dsimp only [W, f, C] <;> ring
  · apply hRnorm 11 _ _ hf'
    rw [hF₁₁, hzv, hxw]
    field_simp [hu, hG'] <;> dsimp only [Dn] <;> ring
  · rw [hRnorm 12 (-V * G) P hP' (by
      rw [hF₁₂, hw₁]
      field_simp [hu] <;> dsimp only [Dn] <;> ring)]
    field_simp [hP'] <;> dsimp only [P, V, W, f, C] <;> ring
  · apply hRnorm 13 _ _ (mul_ne_zero hf' hP')
    rw [hF₁₃, hw₁]
    field_simp [hu] <;> dsimp only [Dn] <;> ring
  · apply hRnorm 16 _ _ (mul_ne_zero (mul_ne_zero hv hf') hP')
    rw [hF₁₆, hw']
    field_simp [hu] <;> dsimp only [Dn] <;> ring
  · apply hRnorm 17 _ _ (mul_ne_zero hf' hP')
    rw [hF₁₇, hxw]
    field_simp [hu] <;> dsimp only [Dn] <;> ring
  · apply hRnorm 22 _ _ (mul_ne_zero hf' hP')
    rw [hF₂₂, hztv, hw']
    field_simp [hu, hG'] <;> dsimp only [Dn] <;> ring

end MOC
