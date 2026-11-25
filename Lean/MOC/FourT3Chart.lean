import MOC.ContactCensus
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-! Reality and denominator control for the distinct T3 projective chart. -/

namespace MOC

/-- The T3 pole product for `A = (z, 0, 1, x)` and `C = (w, v, t*v, ∞)`. -/
noncomputable def fourT3PoleProduct (z x w v t : ℂ) (i : Fin 24) : ℂ :=
  let A : Fin 4 → ℂ := ![z, 0, 1, x]
  let σ := (fourPerm i).symm
  (A (σ 0) - w) * (A (σ 1) - v) * (A (σ 2) - t * v)

private theorem vector_zero {α : Type*} (a b c d : α) : ![a, b, c, d] 0 = a := rfl
private theorem vector_one {α : Type*} (a b c d : α) : ![a, b, c, d] 1 = b := rfl
private theorem vector_two {α : Type*} (a b c d : α) : ![a, b, c, d] 2 = c := rfl
private theorem vector_three {α : Type*} (a b c d : α) : ![a, b, c, d] 3 = d := rfl

private theorem t3ContactDifferences (z x w v t : ℂ) :
    let F := fourT3PoleProduct z x w v t
    let D := v * (z - w)
    F 1 - F 0 = -D * (x - 1) ∧ F 2 - F 0 = -D * (t - 1) ∧
    F 3 - F 1 = -D * (x * (t - 1)) ∧ F 3 - F 2 = -D * (t * (x - 1)) ∧
    F 7 - F 1 = z * (v - w) * (x - t * v) ∧
    F 8 - F 2 = -t * v * (v - w) * (z - 1) := by
  let σ (i : Fin 24) := (fourPerm i).symm
  have h0 : σ 0 0 = 0 ∧ σ 0 1 = 1 ∧ σ 0 2 = 2 := by decide +kernel
  have h1 : σ 1 0 = 0 ∧ σ 1 1 = 1 ∧ σ 1 2 = 3 := by decide +kernel
  have h2 : σ 2 0 = 0 ∧ σ 2 1 = 2 ∧ σ 2 2 = 1 := by decide +kernel
  have h3 : σ 3 0 = 0 ∧ σ 3 1 = 3 ∧ σ 3 2 = 1 := by decide +kernel
  have h7 : σ 7 0 = 1 ∧ σ 7 1 = 0 ∧ σ 7 2 = 3 := by decide +kernel
  have h8 : σ 8 0 = 2 ∧ σ 8 1 = 0 ∧ σ 8 2 = 1 := by decide +kernel
  obtain ⟨h₀₀, h₀₁, h₀₂⟩ := h0
  obtain ⟨h₁₀, h₁₁, h₁₂⟩ := h1
  obtain ⟨h₂₀, h₂₁, h₂₂⟩ := h2
  obtain ⟨h₃₀, h₃₁, h₃₂⟩ := h3
  obtain ⟨h₇₀, h₇₁, h₇₂⟩ := h7
  obtain ⟨h₈₀, h₈₁, h₈₂⟩ := h8
  dsimp only [σ] at h₀₀ h₀₁ h₀₂ h₁₀ h₁₁ h₁₂ h₂₀ h₂₁ h₂₂ h₃₀ h₃₁ h₃₂ h₇₀ h₇₁ h₇₂ h₈₀ h₈₁ h₈₂
  simp only [fourT3PoleProduct, h₀₀, h₀₁, h₀₂, h₁₀, h₁₁, h₁₂, h₂₀, h₂₁, h₂₂,
    h₃₀, h₃₁, h₃₂, h₇₀, h₇₁, h₇₂, h₈₀, h₈₁, h₈₂,
    vector_zero, vector_one, vector_two, vector_three]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> ring

private theorem im_eq_zero_of_pure_factor {p q : ℂ} (hp : p.re = 0) (hp₀ : p ≠ 0)
    (hq : (p * q).re = 0) : q.im = 0 := by
  have hpi : p.im ≠ 0 := fun h => hp₀ (Complex.ext (by simpa using hp) (by simpa using h))
  have him : -(p.im * q.im) = 0 := by simpa only [Complex.mul_re, hp, zero_mul, zero_sub] using hq
  exact (mul_eq_zero.mp (neg_eq_zero.mp him)).resolve_left hpi

/-- The six T3 contacts force the chart parameters to be real and
the source denominators to be nonzero. -/
theorem fourT3_normalized_chart (z x w v t η : ℂ) (H : ℝ)
    (hz : z ≠ 0) (hz₁ : z ≠ 1) (hzv : z ≠ v) (hzw : z ≠ w) (hv : v ≠ 0) (hvw : v ≠ w)
    (htx : x ≠ t * v) (ht₀ : t ≠ 0) (ht₁ : t ≠ 1) (hx₁ : x ≠ 1) (hη : η ≠ 0)
    (hc : ∀ i ∈ ({0, 1, 2, 3, 7, 8} : Finset (Fin 24)),
      (η * fourT3PoleProduct z x w v t i).re = H) :
    t.im = 0 ∧ x.im = 0 ∧ (η * (v * (z - w))).re = 0 ∧
    ∃ r u : ℝ, (r : ℂ) ≠ 0 ∧ (u : ℂ) ≠ 0 ∧
      let G := ((u : ℂ) + t) * v - x
      let K := z - 1 - r
      G ≠ 0 ∧ K ≠ 0 ∧ z = (u : ℂ) * v / G ∧ w = (v * (z - 1) - (r : ℂ) * z) / K := by
  let F := fourT3PoleProduct z x w v t
  let D := v * (z - w)
  have hD : D ≠ 0 := mul_ne_zero hv (sub_ne_zero.mpr hzw)
  have hηD : η * D ≠ 0 := mul_ne_zero hη hD
  obtain ⟨h1, h2, h31, h32, h7, h8⟩ := t3ContactDifferences z x w v t
  change F 1 - F 0 = -D * (x - 1) at h1
  change F 2 - F 0 = -D * (t - 1) at h2
  change F 3 - F 1 = -D * (x * (t - 1)) at h31
  change F 3 - F 2 = -D * (t * (x - 1)) at h32
  have hline {i j : Fin 24} (hi : i ∈ ({0, 1, 2, 3, 7, 8} : Finset (Fin 24)))
      (hj : j ∈ ({0, 1, 2, 3, 7, 8} : Finset (Fin 24))) : (η * (F i - F j)).re = 0 := by
    change (η * (fourT3PoleProduct z x w v t i - fourT3PoleProduct z x w v t j)).re = 0
    rw [mul_sub, Complex.sub_re, hc i hi, hc j hj, sub_self]
  have htstable : η * (F 1 - F 0) * t = η * (F 3 - F 2) := by
    linear_combination η * t * h1 - η * h32
  have hxstable : η * (F 2 - F 0) * x = η * (F 3 - F 1) := by
    linear_combination η * x * h2 - η * h31
  have ht_re := im_eq_zero_of_pure_factor (hline (i := 1) (j := 0) (by decide) (by decide))
    (by rw [h1]; exact mul_ne_zero hη (mul_ne_zero (neg_ne_zero.mpr hD) (sub_ne_zero.mpr hx₁)))
    (by rw [htstable]; exact hline (i := 3) (j := 2) (by decide) (by decide))
  have hx_re := im_eq_zero_of_pure_factor (hline (i := 2) (j := 0) (by decide) (by decide))
    (by rw [h2]; exact mul_ne_zero hη (mul_ne_zero (neg_ne_zero.mpr hD) (sub_ne_zero.mpr ht₁)))
    (by rw [hxstable]; exact hline (i := 3) (j := 1) (by decide) (by decide))
  have htD : (η * D).re = 0 := by
    have h := hline (i := 2) (j := 0) (by decide) (by decide)
    have hid : η * (F 2 - F 0) = -(η * D) * (t - 1) := by linear_combination η * h2
    have htr : t.re - 1 ≠ 0 := fun hu => ht₁ (Complex.ext (by simpa using sub_eq_zero.mp hu)
      (by simpa only [Complex.one_im] using ht_re))
    rw [hid] at h
    simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.sub_re, Complex.sub_im,
      Complex.one_re, Complex.one_im, ht_re, sub_self, mul_zero, sub_zero, mul_eq_zero,
      neg_eq_zero, htr, or_false] at h
    exact h
  let R := (v - w) * (z - 1) / (z - w)
  let S := z * (x - t * v) / (v * (z - 1))
  have hRD : R * (z - w) = (v - w) * (z - 1) := div_mul_cancel₀ _ (sub_ne_zero.mpr hzw)
  have hSD : S * (v * (z - 1)) = z * (x - t * v) :=
    div_mul_cancel₀ _ (mul_ne_zero hv (sub_ne_zero.mpr hz₁))
  have hR₀ : R ≠ 0 := div_ne_zero (mul_ne_zero (sub_ne_zero.mpr hvw) (sub_ne_zero.mpr hz₁))
    (sub_ne_zero.mpr hzw)
  have hS₀ : S ≠ 0 := div_ne_zero (mul_ne_zero hz (sub_ne_zero.mpr htx))
    (mul_ne_zero hv (sub_ne_zero.mpr hz₁))
  have hR_re : R.im = 0 := by
    have h := hline (i := 8) (j := 2) (by decide) (by decide)
    have hid : η * (F 8 - F 2) = (η * D) * (-t * R) := by
      dsimp only [D]
      linear_combination η * h8 + η * t * v * hRD
    rw [hid] at h
    have hi := im_eq_zero_of_pure_factor htD hηD h
    have htr : t.re ≠ 0 := fun h => ht₀ (Complex.ext (by simpa using h) (by simpa using ht_re))
    simpa only [Complex.mul_im, Complex.neg_re, Complex.neg_im, ht_re, neg_zero, zero_mul,
      add_zero, mul_eq_zero, neg_eq_zero, htr, false_or] using hi
  have hS_re : S.im = 0 := by
    have h := hline (i := 7) (j := 1) (by decide) (by decide)
    have hmul : D * (R * S) = z * (v - w) * (x - t * v) := by
      dsimp only [D]
      calc
        _ = v * S * (R * (z - w)) := by ring
        _ = (v - w) * (S * (v * (z - 1))) := by rw [hRD]; ring
        _ = _ := by rw [hSD]; ring
    have hid : η * (F 7 - F 1) = (η * D) * (R * S) := by rw [h7, ← hmul, ← mul_assoc]
    rw [hid] at h
    have hi := im_eq_zero_of_pure_factor htD hηD h
    have hrr : R.re ≠ 0 := fun h => hR₀ (Complex.ext (by simpa using h) (by simpa using hR_re))
    simpa only [Complex.mul_im, hR_re, zero_mul, add_zero, mul_eq_zero, hrr, false_or] using hi
  have hR : (R.re : ℂ) = R := Complex.ext (by simp) (by simpa using hR_re.symm)
  have hS : (S.re : ℂ) = S := Complex.ext (by simp) (by simpa using hS_re.symm)
  refine ⟨ht_re, hx_re, htD, R.re, S.re, ?_⟩
  rw [hR, hS]
  let G := (S + t) * v - x
  let K := z - 1 - R
  have hzid : z * G = S * v := by dsimp only [G]; linear_combination hSD
  have hwid : w * K = v * (z - 1) - R * z := by dsimp only [K]; linear_combination hRD
  have hG : G ≠ 0 := by
    intro h
    rw [h, mul_zero] at hzid
    exact (mul_ne_zero hS₀ hv) hzid.symm
  have hK : K ≠ 0 := by
    intro h
    rw [h, mul_zero] at hwid
    have hRz : R = z - 1 := (sub_eq_zero.mp h).symm
    rw [hRz] at hwid
    have he : (v - z) * (z - 1) = 0 := by linear_combination -hwid
    exact mul_ne_zero (sub_ne_zero.mpr hzv.symm) (sub_ne_zero.mpr hz₁) he
  exact ⟨hR₀, hS₀, hG, hK, (eq_div_iff hG).mpr hzid, (eq_div_iff hK).mpr hwid⟩

end MOC
