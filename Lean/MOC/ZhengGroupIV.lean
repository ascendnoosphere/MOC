import MOC.FourContactCertificate
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! Direct matching-cubic certificates for Group IV of Zheng's order-four
preprint (DOI: 10.13140/RG.2.2.36790.25923, Appendix G). The coordinates
are the seven unspecified gaps after zero-height rectangle closure.
No normal-cone facet classification or support enumeration is used. -/

namespace MOC
namespace ZhengGroupIV

/-- Gap coordinates at labels (0,1,6,7,9,16,18) after T22 closure. -/
def lift22 {R : Type*} [CommRing R] (a b c d e f g : R) : Fin 14 → R :=
  ![a-b-c+d,-a+b+c-d,-g,-b+d,b-d,-a+b+c-d,d+f,-c+d,c-d,
    a-d-f,-b+d,-c+d,-e,-a+b+c-d+e+f+g]

/-- Gap coordinates at labels (0,1,6,7,8,16,18) after T23 closure. -/
def lift23 {R : Type*} [CommRing R] (a b c d e f g : R) : Fin 14 → R :=
  ![a-b-c+d,-a+b+c-d,-a+b-g,-b+d,b-d,0,c-e+f,0,c-d,
    a-c+e-f,-a+c-e,-c+d,e,c-d-e+f+g]

theorem cubic22 {R : Type*} [CommRing R] (a b c d e f g : R) :
    fourMatchingCubic (lift22 a b c d e f g) =
      (a*d-b*c)*(e+g+(f-a+b+c)-d)-a*e*g := by
  simp [fourMatchingCubic,lift22]
  ring

theorem cubic23 {R : Type*} [CommRing R] (a b c d e f g : R) :
    fourMatchingCubic (lift23 a b c d e f g) =
      (a*d-b*c)*(c-d+f+g)+b*e*(c+g-d) := by
  simp [fourMatchingCubic,lift23]
  ring

/-- Cubic vanishing implies the only two inequalities not already
provided by the linear T22 contact conditions. -/
theorem thresholds22 {a b c d e f g : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (he : 0 ≤ e) (hf : 0 ≤ f) (hg : 0 ≤ g)
    (hab : b ≤ a) (hac : c ≤ a)
    (h17 : 0 ≤ -a+b+c-d+e+f) (h22 : 0 ≤ -a+b+c-d+f+g)
    (hC : fourMatchingCubic (lift22 a b c d e f g) = 0) :
    0 ≤ a-b-c+d ∧ 0 ≤ f-a+b+c := by
  rw [cubic22] at hC
  constructor
  · by_contra! hn
    have ha' : 0 < a := by
      by_contra! hn'
      linarith
    have hm := mul_neg_of_pos_of_neg ha' hn
    have hn' := mul_nonneg (sub_nonneg.mpr hab) (sub_nonneg.mpr hac)
    have hdiff : a*d-b*c < 0 := by nlinarith only [hm,hn']
    have hfactor : 0 < e+g+(f-a+b+c)-d := by linarith
    linarith only [hC,mul_neg_of_neg_of_pos hdiff hfactor,
      mul_nonneg (mul_nonneg ha he) hg]
  · by_contra! hn
    have ha' : 0 < a := by linarith
    have he' : 0 < e-d := by linarith
    have hg' : 0 < g-d := by linarith
    have hfactor : 0 < e+g+(f-a+b+c)-d := by linarith
    have hu : (a*d-b*c)*(e+g+(f-a+b+c)-d) ≤ a*d*(e+g+(f-a+b+c)-d) :=
      mul_le_mul_of_nonneg_right (by linarith [mul_nonneg hb hc]) hfactor.le
    have hv : a*d*(e+g+(f-a+b+c)-d)-a*e*g < 0 := by
      have hh := mul_neg_of_pos_of_neg ha'
        (sub_neg.mpr (lt_of_le_of_lt (mul_nonpos_of_nonneg_of_nonpos hd hn.le)
          (mul_pos he' hg')))
      nlinarith only [hh]
    linarith only [hC,hu,hv]

/-- Cubic vanishing implies the only two inequalities not already
provided by the linear T23 contact conditions. -/
theorem thresholds23 {a b c d e f g : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (he : 0 ≤ e) (hf : 0 ≤ f) (hab : a ≤ b) (hdb : d ≤ b)
    (h17 : 0 ≤ -a+b+c-d-e+f) (h19 : 0 ≤ c-d+g)
    (h23 : 0 ≤ c-d-e+f+g)
    (hC : fourMatchingCubic (lift23 a b c d e f g) = 0) :
    0 ≤ b+c-a-d ∧ 0 ≤ f-e+c := by
  rw [cubic23] at hC
  constructor
  · by_contra! hn
    have hb' : 0 < b := by
      by_contra! hn'
      linarith
    have hm := mul_neg_of_pos_of_neg hb' hn
    have hn' := mul_nonneg (sub_nonneg.mpr hab) (sub_nonneg.mpr hdb)
    have hdiff : 0 < a*d-b*c := by nlinarith only [hm,hn']
    have hfactor : 0 < c-d+f+g := by
      by_contra! hn'
      linarith
    linarith only [hC,mul_pos hdiff hfactor,mul_nonneg (mul_nonneg hb he) (by linarith : 0 ≤ c+g-d)]
  · by_contra! hn
    have hb' : 0 < b := by linarith
    have hg' : 0 < g-d := by linarith
    have he' : 0 < e-c := by linarith
    have hd' : 0 ≤ c-d+f+g := by linarith
    have hu : -(b*c)*(c-d+f+g) ≤ (a*d-b*c)*(c-d+f+g) :=
      mul_le_mul_of_nonneg_right (by linarith [mul_nonneg ha hd]) hd'
    have hv : 0 < -(b*c)*(c-d+f+g)+b*e*(c+g-d) := by
      have hh := mul_pos hb'
        (add_pos_of_nonneg_of_pos (mul_nonneg (neg_nonneg.mpr hn.le) hc) (mul_pos he' hg'))
      nlinarith only [hh]
    linarith only [hC,hu,hv]


/-- The constructive interval for the coefficients of the eight ordinary
minor markers at T22. The eight inequalities express their nonnegativity. -/
theorem minor_coefficients22 {a b c d e f g : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (he : 0 ≤ e) (hf : 0 ≤ f) (hg : 0 ≤ g)
    (hab : b ≤ a) (hac : c ≤ a)
    (h11 : 0 ≤ c-d+e) (h15 : 0 ≤ b-d+e)
    (h17 : 0 ≤ -a+b+c-d+e+f) (h19 : 0 ≤ c-d+g)
    (h20 : 0 ≤ b-d+g) (h22 : 0 ≤ -a+b+c-d+f+g)
    (hC : fourMatchingCubic (lift22 a b c d e f g) = 0) :
    ∃ s : ℝ, 0 ≤ g-d+s ∧ 0 ≤ b-s ∧ 0 ≤ c-s ∧ 0 ≤ e-d+s ∧
      0 ≤ s ∧ 0 ≤ f-a+b+c-s ∧ 0 ≤ a-b-c+s ∧ 0 ≤ d-s := by
  obtain ⟨hA,hB⟩ := thresholds22 ha hb hc hd he hf hg hab hac h17 h22 hC
  let s := max (max 0 (b+c-a)) (max (d-e) (d-g))
  have hs (t : ℝ) (h₀ : 0 ≤ t) (h₁ : b+c-a ≤ t) (h₂ : d-e ≤ t) (h₃ : d-g ≤ t) :
      s ≤ t := max_le (max_le h₀ h₁) (max_le h₂ h₃)
  have h₀ : 0 ≤ s := (le_max_left _ _).trans (le_max_left _ _)
  have h₁ : b+c-a ≤ s := (le_max_right _ _).trans (le_max_left _ _)
  have h₂ : d-e ≤ s := (le_max_left _ _).trans (le_max_right _ _)
  have h₃ : d-g ≤ s := (le_max_right _ _).trans (le_max_right _ _)
  have hsb := hs b hb (by linarith) (by linarith) (by linarith)
  have hsc := hs c hc (by linarith) (by linarith) (by linarith)
  have hsd := hs d hd (by linarith) (by linarith) (by linarith)
  have hsf := hs (f-a+b+c) hB (by linarith) (by linarith) (by linarith)
  exact ⟨s,by linarith,by linarith,by linarith,by linarith,h₀,by linarith,by linarith,by linarith⟩

/-- Constructive minor coefficients at T23. -/
theorem minor_coefficients23 {a b c d e f g : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (he : 0 ≤ e) (hf : 0 ≤ f) (hg : 0 ≤ g)
    (hab : a ≤ b) (hdb : d ≤ b)
    (h10 : 0 ≤ -c+d+e) (h14 : 0 ≤ a-c+e)
    (h17 : 0 ≤ -a+b+c-d-e+f) (h19 : 0 ≤ c-d+g)
    (h21 : 0 ≤ a-d+g) (h23 : 0 ≤ c-d-e+f+g)
    (hC : fourMatchingCubic (lift23 a b c d e f g) = 0) :
    ∃ s : ℝ, 0 ≤ g-d+s ∧ 0 ≤ a-s ∧ 0 ≤ e-c+s ∧ 0 ≤ d-s ∧
      0 ≤ s ∧ 0 ≤ f-e+c-s ∧ 0 ≤ b-a-d+s ∧ 0 ≤ c-s := by
  obtain ⟨hA,hB⟩ := thresholds23 ha hb hc hd he hf hab hdb h17 h19 h23 hC
  let s := max (max 0 (c-e)) (max (a+d-b) (d-g))
  have hs (t : ℝ) (h₀ : 0 ≤ t) (h₁ : c-e ≤ t) (h₂ : a+d-b ≤ t) (h₃ : d-g ≤ t) :
      s ≤ t := max_le (max_le h₀ h₁) (max_le h₂ h₃)
  have h₀ : 0 ≤ s := (le_max_left _ _).trans (le_max_left _ _)
  have h₁ : c-e ≤ s := (le_max_right _ _).trans (le_max_left _ _)
  have h₂ : a+d-b ≤ s := (le_max_left _ _).trans (le_max_right _ _)
  have h₃ : d-g ≤ s := (le_max_right _ _).trans (le_max_right _ _)
  have hsa := hs a ha (by linarith) (by linarith) (by linarith)
  have hsc := hs c hc (by linarith) (by linarith) (by linarith)
  have hsd := hs d hd (by linarith) (by linarith) (by linarith)
  have hsf := hs (f-e+c) hB (by linarith) (by linarith) (by linarith)
  exact ⟨s,by linarith,by linarith,by linarith,by linarith,h₀,by linarith,by linarith,by linarith⟩

end ZhengGroupIV
end MOC
