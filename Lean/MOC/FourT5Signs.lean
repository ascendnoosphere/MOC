import MOC.FourT5Capacity
import Mathlib.Data.Fin.Basic

/-! Sign reduction from the original T5 gap identities to its three
endpoint certificates. The source gaps are divided by the positive magnitude
of the common chart scale. -/

namespace MOC

set_option maxHeartbeats 1500000 in
/-- The normalized original-product identities exhaust the T5 mixed branch. -/
theorem fourT5_capacity_of_normalized_gaps (x t r u σ ratio A : ℝ) (g : Fin 24 → ℝ)
    (ht : t ≠ 0) (ht₁ : t ≠ 1) (hr : r ≠ 0) (hratio_pos : 0 < ratio) (hA : A < 0)
    (hs : |σ| = 1) (hsx : σ * x < 0) (hg : ∀ i, 0 ≤ g i)
    (h9 : 0 < g 9) (h11 : 0 < g 11) (hx11 : x * g 11 = (x - 1) * g 9) :
    let L := x - r - t - u
    let H := -r * t + t * (x - 1) - u
    let W := t * (x - 1) - r - u
    let D := r * t + u * x
    let J := r + (t + u - 1) * x
    g 7 = -σ * t * x * (r + u) →
    g 10 = -σ * r * t * (x - 1) →
    0 ≤ -σ * r * u * L →
    g 17 = A - σ * t * u * x * (x - 1) →
    H * g 13 = t * L * A + σ * t * u * x * (t - 1) * W →
    H * g 22 = (t - 1) * (x - r) * A + σ * r * t * x * (t - 1) * (x - r - u - 1) →
    D * A = σ * r * u * (x * t * (t - 1) * (x - 1) - J * H * ratio) →
    A ^ 2 ≤ g 10 * g 13 ∨
      A ^ 2 * (g 22 + g 17 + g 7 - A) ≤ g 22 * g 17 * (g 7 + A) := by
  intro L H W D J h7 h10 h12 h17 h13 h22 hDA
  have hx₀ : x ≠ 0 := right_ne_zero_of_mul hsx.ne
  have hxSign : x < 0 ∨ 1 < x := by
    rcases lt_or_gt_of_ne hx₀ with h | h
    · exact Or.inl h
    · have hh : 0 < (x - 1) * g 9 := hx11 ▸ mul_pos h h11
      exact Or.inr (sub_pos.mp (pos_of_mul_pos_left hh h9.le))
  have hσx : x < 0 ∧ σ = 1 ∨ 1 < x ∧ σ = -1 := by
    rcases hxSign with hx | hx
    · have hσ : 0 < σ := by
        rcases mul_neg_iff.mp hsx with ha | ha
        · exact ha.1
        · exact False.elim ((not_lt_of_ge hx.le) ha.2)
      exact Or.inl ⟨hx, (abs_of_pos hσ).symm.trans hs⟩
    · have hx' := zero_lt_one.trans hx
      have hσ : σ < 0 := by
        rcases mul_neg_iff.mp hsx with ha | ha
        · exact False.elim ((not_lt_of_ge hx'.le) ha.2)
        · exact ha.1
      exact Or.inr ⟨hx, neg_eq_iff_eq_neg.mp ((abs_of_neg hσ).symm.trans hs)⟩
  have hcoeff : 0 < -σ * (x - 1) := by
    rcases hσx with ⟨hx, hσ⟩ | ⟨hx, hσ⟩
    · rw [hσ]; linarith only [hx]
    · rw [hσ]; linarith only [hx]
  have hxx : 0 < x * (x - 1) := by
    rcases hxSign with hx | hx
    · exact mul_pos_of_neg_of_neg hx (by linarith only [hx])
    · exact mul_pos (zero_lt_one.trans hx) (sub_pos.mpr hx)
  have hrt : 0 < r * t := by
    have h : 0 ≤ (-σ * (x - 1)) * (r * t) := by linarith only [h10, hg 10]
    exact lt_of_le_of_ne ((mul_nonneg_iff_of_pos_left hcoeff).mp h) (mul_ne_zero hr ht).symm
  have htu : 0 < -σ * (t * u) := by
    have h : 0 < (-σ * (t * u)) * (x * (x - 1)) := by linarith only [h17, hg 17, hA]
    exact (mul_pos_iff_of_pos_right hxx).mp h
  rcases hσx with ⟨hx, hσ⟩ | ⟨hx, hσ⟩
  · have htun : t * u < 0 := by rw [hσ] at htu; linarith only [htu]
    have htn : t < 0 := by
      by_contra! htn
      have htp := lt_of_le_of_ne htn ht.symm
      have hrp := pos_of_mul_pos_left hrt htp.le
      have hun := neg_of_mul_neg_right htun htp.le
      have hru : 0 ≤ r + u := by
        have h' : 0 ≤ (-t * x) * (r + u) := by rw [hσ] at h7; linarith only [h7, hg 7]
        exact (mul_nonneg_iff_of_pos_left (mul_pos_of_neg_of_neg (neg_lt_zero.mpr htp) hx)).mp h'
      have hL : 0 ≤ L := by
        rw [hσ] at h12
        have h' : 0 ≤ (-r * u) * L := by linarith only [h12]
        exact (mul_nonneg_iff_of_pos_left (mul_pos_of_neg_of_neg (neg_lt_zero.mpr hrp) hun)).mp h'
      dsimp only [L] at hL
      linarith only [hx, htp, hru, hL]
    have hrn := neg_of_mul_pos_left hrt htn.le
    have hup := pos_of_mul_neg_right htun htn.le
    have hRU : u ≤ -r := by
      rw [hσ] at h7
      have h' : 0 ≤ (t * x) * (-(r + u)) := by linarith only [h7, hg 7]
      have hsum := (mul_nonneg_iff_of_pos_left (mul_pos_of_neg_of_neg htn hx)).mp h'
      linarith only [hsum]
    have hL : 0 ≤ L := by
      rw [hσ] at h12
      have h' : 0 ≤ (-r * u) * L := by linarith only [h12]
      exact (mul_nonneg_iff_of_pos_left (mul_pos (neg_pos.mpr hrn) hup)).mp h'
    have hcap := fourT5_two_budget_of_negative_chart (-x) (-t) (-r) u (-A) (g 13) (g 22)
      (neg_pos.mpr hx) (neg_pos.mpr htn) (neg_pos.mpr hrn) hup hRU (neg_pos.mpr hA) (hg 13) (hg 22)
    have hcap' := hcap (by dsimp only [L] at hL; linarith only [hL])
      (by rw [hσ] at h17; linarith only [h17, hg 17])
      (by rw [hσ] at h13; dsimp only [L, H, W] at h13; linear_combination h13)
      (by rw [hσ] at h22; dsimp only [H] at h22; linear_combination h22)
    left
    have h10' : g 10 = (-r) * (-t) * (-x + 1) := by rw [h10, hσ]; ring
    rw [h10']
    convert hcap' using 1 <;> ring
  · have htu' : 0 < t * u := by rw [hσ] at htu; linarith only [htu]
    have hy := sub_pos.mpr hx
    have hx' := zero_lt_one.trans hx
    have htp : 0 < t := by
      by_contra! htp
      have htn : t < 0 := lt_of_le_of_ne htp ht
      have hrn := neg_of_mul_pos_left hrt htn.le
      have hun := neg_of_mul_pos_right htu' htn.le
      have htm : t - 1 < 0 := by linarith only [htn]
      have hxr : 0 < x - r := sub_pos.mpr (hrn.trans hx')
      have hxx' : 0 < x - r - u - 1 := by linarith only [hx, hrn, hun]
      have hfirst : 0 < (t - 1) * (x - r) * A :=
        mul_pos_of_neg_of_neg (mul_neg_of_neg_of_pos htm hxr) hA
      have hsecond : 0 < -((r * t) * x * (t - 1)) * (x - r - u - 1) :=
        mul_pos (neg_pos.mpr (mul_neg_of_pos_of_neg (mul_pos hrt hx') htm)) hxx'
      have hH : 0 < H := by
        have hp : 0 < H * g 22 := by rw [hσ] at h22; linarith only [h22, hfirst, hsecond]
        exact pos_of_mul_pos_left hp (hg 22)
      have hD : D < 0 := by
        have hp := mul_pos hH hx'
        have hn := mul_neg_of_pos_of_neg (mul_pos hy hxr) htn
        dsimp only [D]
        dsimp only [H] at hp
        linarith only [hp, hn]
      have hJ : J < 0 := by
        have hn : t + u - 1 < 0 := by linarith only [htn, hun]
        dsimp only [J]
        exact add_neg hrn (mul_neg_of_neg_of_pos hn hx')
      have hb : 0 < x * t * (t - 1) * (x - 1) - J * H * ratio := by
        have hp := mul_pos (mul_pos_of_neg_of_neg (mul_neg_of_pos_of_neg hx' htn) htm) hy
        have hn := mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hJ hH) hratio_pos
        linarith only [hp, hn]
      have hsru : σ * r * u < 0 := by
        rw [hσ]
        exact mul_neg_of_pos_of_neg (mul_pos_of_neg_of_neg (by norm_num) hrn) hun
      exact (not_lt_of_ge (mul_pos_of_neg_of_neg hD hA).le) (hDA.symm ▸ mul_neg_of_neg_of_pos hsru hb)
    have hrp := pos_of_mul_pos_left hrt htp.le
    have hup := pos_of_mul_pos_right htu' htp.le
    have hL : 0 ≤ L := by
      rw [hσ] at h12
      have hp : 0 ≤ (r * u) * L := by linarith only [h12]
      exact (mul_nonneg_iff_of_pos_left (mul_pos hrp hup)).mp hp
    have htlt : t < 1 := by
      by_contra hn
      have htgt := lt_of_le_of_ne (le_of_not_gt hn) ht₁.symm
      have heq : H = t * L + (t - 1) * (t + u) := by dsimp only [H, L]; ring
      have hH : 0 < H := by
        rw [heq]
        exact add_pos_of_nonneg_of_pos (mul_nonneg htp.le hL) (mul_pos (sub_pos.mpr htgt) (add_pos htp hup))
      have hW : 0 < W := by
        have heq' : W = H + r * (t - 1) := by dsimp only [W, H]; ring
        rw [heq']
        exact add_pos hH (mul_pos hrp (sub_pos.mpr htgt))
      have hfirst := mul_nonpos_of_nonneg_of_nonpos (mul_nonneg htp.le hL) hA.le
      have hsecond := mul_pos (mul_pos (mul_pos (mul_pos htp hup) hx') (sub_pos.mpr htgt)) hW
      rw [hσ] at h13
      linarith only [h13, hfirst, hsecond, mul_nonneg hH.le (hg 13)]
    have hH₀ : H ≠ 0 := by
      intro hH
      have hD : 0 < D := add_pos hrt (mul_pos hup hx')
      have hp := mul_neg_of_neg_of_pos
        (mul_neg_of_pos_of_neg (mul_pos hx' htp) (sub_neg.mpr htlt)) hy
      have hsru : σ * r * u < 0 := by
        rw [hσ]
        exact mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (by norm_num) hrp) hup
      rw [hH, mul_zero, zero_mul, sub_zero] at hDA
      exact (not_lt_of_ge (hDA.symm ▸ (mul_pos_of_neg_of_neg hsru hp).le)) (mul_neg_of_pos_of_neg hD hA)
    have h17' : g 17 = t * u * x * (x - 1) - (-A) := by rw [h17, hσ]; ring
    have h7' : g 7 = t * x * (r + u) := by rw [h7, hσ]; ring
    have h10' : g 10 = r * t * (x - 1) := by rw [h10, hσ]; ring
    have h13' : H * g 13 = t * (u * x * (1 - t) * W - L * (-A)) := by rw [hσ] at h13; linear_combination h13
    have h22' : H * g 22 = (1 - t) * ((x - r) * (-A) + r * t * x * (x - 1 - r - u)) := by
      rw [hσ] at h22
      linear_combination h22
    rcases lt_or_gt_of_ne hH₀ with hH | hH
    · left
      have hB : -A ≤ t * u * x * (x - 1) := by linarith only [h17', hg 17]
      have h := fourT5_two_budget_of_positive_chart x t r u (-A) (g 13) (g 22) hx htp htlt hrp hup
        (neg_pos.mpr hA) (hg 22) hL hH hB h13' h22'
      rw [h10']
      convert h using 1 <;> ring
    · right
      have h := fourT5_four_budget_of_positive_chart x t r u (-A) (g 22) (g 13) hx htp htlt hrp hup
        (neg_pos.mpr hA) (hg 13) hH h13' h22'
      rw [h17', h7']
      convert h using 1 <;> ring

end MOC
