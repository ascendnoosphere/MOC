import MOC.FourContactCertificate
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

/-! The three rectangular cases T18, T19, T20 in Group II of Zheng
(DOI: 10.13140/RG.2.2.36790.25923, Appendices E and G).
The six contacts force zero height. All brackets and markers are
described in the companion proof; this module proves the scalar
cubic signs and the existence of nonnegative marker coefficients. -/

namespace MOC.ZhengEarlyRectangles

def lift18 (a b c d e f g h : ℝ) : Fin 14 → ℝ :=
  ![0,a-e+f,-a+b+e-h,-f,0,a-b+d,-d-f+g,-d,0,-a+d+f-g,
    b-d,e-f,-a-c,2*a-b+c-e+g+h]
def lift19 (a b c d e f g h : ℝ) : Fin 14 → ℝ :=
  ![0,a-b-e+f,-a+e-h,b-f,0,a+d,-d-f+g,-d,0,-a+d+f-g,
    -d,e-f,-a+b-c,2*a-b+c-e+g+h]
def lift20 (a b c d e f g h : ℝ) : Fin 14 → ℝ :=
  ![0,a-b-e+f,-b+e-h,b-f,0,b+d,-d-f+g,-d,0,-a+d+f-g,
    a-b-d,e-f,-a+b-c,a+c-e+g+h]

theorem cubic18 (a b c d e f g h : ℝ) :
    fourMatchingCubic (lift18 a b c d e f g h) = a*c*h-a*d*f-b*c*e := by
  simp [fourMatchingCubic,lift18]
  ring

theorem cubic19 (a b c d e f g h : ℝ) :
    fourMatchingCubic (lift19 a b c d e f g h) = a*c*h+d*(b*e-a*f) := by
  simp [fourMatchingCubic,lift19]
  ring

theorem cubic20 (a b c d e f g h : ℝ) :
    fourMatchingCubic (lift20 a b c d e f g h) = c*(a*h-(a-b)*e)+d*(b*e-a*f) := by
  simp [fourMatchingCubic,lift20]
  ring

private theorem sum_of_maxes_le {x y z : ℝ}
    (hz : 0 ≤ z) (hx : x ≤ z) (hy : y ≤ z) (hxy : x+y ≤ z) :
    max 0 x + max 0 y ≤ z := by
  rcases le_total x 0 with hx' | hx' <;> rcases le_total y 0 with hy' | hy'
  · simp [max_eq_left hx',max_eq_left hy',hz]
  · simpa [max_eq_left hx',max_eq_right hy'] using hy
  · simpa [max_eq_right hx',max_eq_left hy'] using hx
  · simpa [max_eq_right hx',max_eq_right hy'] using hxy

/-- The two free coefficients for the T18 minor decomposition. -/
theorem choices18 {a b c d e f g h : ℝ}
    (ha : 0 ≤ a) (hc : 0 ≤ c) (hd : 0 ≤ d) (hf : 0 ≤ f) (hg : 0 ≤ g)
    (hh : 0 ≤ h) (hb : a ≤ b) (he : a ≤ e)
    (h19 : e ≤ f+h) (h20 : b ≤ d+h)
    (h21 : b+e-a-h ≤ c+d+f) (h22 : b+e-a-h ≤ g)
    (hC : fourMatchingCubic (lift18 a b c d e f g h) = 0) :
    ∃ s t : ℝ, 0 ≤ s ∧ s ≤ e-a ∧ s ≤ f ∧ 0 ≤ t ∧ t ≤ b-a ∧ t ≤ d ∧
      s+t ≤ g ∧ b+e-a-h ≤ s+t := by
  rw [cubic18] at hC
  let D := b+e-a-h
  have hA : a ≤ h ∧ D ≤ d+f := by
    rcases eq_or_lt_of_le hc with hc0 | hc'
    · have hG : D ≤ d+f := by dsimp [D]; linarith
      refine ⟨?_,hG⟩
      rcases eq_or_lt_of_le ha with ha0 | ha'
      · linarith
      have hdf : d*f = 0 := by
        have hzero : a*(d*f) = 0 := by
          linear_combination -hC - (a*h-b*e)*hc0
        exact (mul_eq_zero.mp hzero).resolve_left ha'.ne'
      rcases mul_eq_zero.mp hdf with h | h <;> linarith
    rcases eq_or_lt_of_le ha with ha0 | ha'
    · have hbe : b*e = 0 := by
        have hzero : c*(b*e) = 0 := by
          linear_combination -hC - (c*h-d*f)*ha0
        exact (mul_eq_zero.mp hzero).resolve_left hc'.ne'
      refine ⟨by linarith,?_⟩
      dsimp [D]
      rcases mul_eq_zero.mp hbe with h | h <;> linarith
    · have heq : (a*c)*(-D) = a*d*f+c*(b-a)*(e-a) := by
        dsimp [D]
        linear_combination hC
      have hnon : 0 ≤ (a*c)*(-D) := by
        rw [heq]
        have h₁ := sub_nonneg.mpr hb
        have h₂ := sub_nonneg.mpr he
        positivity
      have hnD := nonneg_of_mul_nonneg_right hnon (mul_pos ha' hc')
      dsimp [D] at hnD ⊢
      constructor <;> linarith
  let S := min (e-a) f
  let T := min (b-a) d
  have hS : 0 ≤ S := le_min (sub_nonneg.mpr he) hf
  have hT : 0 ≤ T := le_min (sub_nonneg.mpr hb) hd
  have hm : D ≤ S+T := by
    dsimp [S,T,D]
    rcases le_total (e-a) f with p | p <;> rcases le_total (b-a) d with q | q
    · rw [min_eq_left p,min_eq_left q]; linarith [hA.1]
    · rw [min_eq_left p,min_eq_right q]; linarith
    · rw [min_eq_right p,min_eq_left q]; linarith
    · rw [min_eq_right p,min_eq_right q]; simpa only [D,add_comm] using hA.2
  let u := max 0 D
  let s := min S u
  let t := u-s
  have hu : 0 ≤ u := le_max_left _ _
  have hs : 0 ≤ s := le_min hS hu
  have hsS : s ≤ S := min_le_left _ _
  have hsu : s ≤ u := min_le_right _ _
  have hun : u ≤ S+T := max_le (add_nonneg hS hT) hm
  have htT : t ≤ T := by
    dsimp [t,s]
    rcases le_total S u with hz | hz
    · rw [min_eq_left hz]; linarith
    · rw [min_eq_right hz]; linarith
  have hst : s+t = u := by dsimp [t]; ring
  exact ⟨s,t,hs,hsS.trans (min_le_left _ _),hsS.trans (min_le_right _ _),
    sub_nonneg.mpr hsu,htT.trans (min_le_left _ _),htT.trans (min_le_right _ _),
    hst ▸ max_le hg h22, hst ▸ le_max_right _ _⟩

/-- Nonnegative ranges for the T19 marker coefficients. -/
theorem choices19 {a b c d e f g h : ℝ}
    (ha : 0 ≤ a) (hc : 0 ≤ c) (hd : 0 ≤ d) (hf : 0 ≤ f) (hg : 0 ≤ g)
    (hh : 0 ≤ h) (hb : a ≤ b) (he : a ≤ e)
    (h15 : b ≤ c+f) (h17 : b-a-c ≤ g)
    (h19 : e ≤ f+h) (h21 : (e-a-h)+(b-a-c) ≤ f-a+d)
    (h22 : e-a-h ≤ g) (h23 : (e-a-h)+(b-a-c) ≤ g)
    (hC : fourMatchingCubic (lift19 a b c d e f g h) = 0) :
    let s := max 0 (e-a-h); let t := max 0 (b-a-c)
    0 ≤ s ∧ s ≤ e-a ∧ 0 ≤ t ∧ t ≤ b-a ∧ s+t ≤ f-a ∧ s+t ≤ g := by
  rw [cubic19] at hC
  have hbe : 0 ≤ b := ha.trans hb
  have hee : 0 ≤ e := ha.trans he
  have hB : a ≤ f ∧ (e-a-h)+(b-a-c) ≤ f-a := by
    rcases eq_or_lt_of_le hd with hd0 | hd'
    · have hs := h21
      rw [← hd0,add_zero] at hs
      refine ⟨?_,hs⟩
      by_contra! hag
      have ha' : 0 < a := hf.trans_lt hag
      have hhne : c*h = 0 := by
        have hn : a*(c*h) = 0 := by rw [← hd0,zero_mul,add_zero,mul_assoc] at hC; exact hC
        exact (mul_eq_zero.mp hn).resolve_left ha'.ne'
      rcases mul_eq_zero.mp hhne with h | h <;> linarith
    rcases eq_or_lt_of_le ha with ha0 | ha'
    · have hbe0 : b*e = 0 := by
        have heq : d*(b*e) = 0 := by simpa [← ha0] using hC
        exact (mul_eq_zero.mp heq).resolve_left hd'.ne'
      refine ⟨by linarith,?_⟩
      rcases mul_eq_zero.mp hbe0 with h | h <;> linarith
    · have heq : (a*d)*(f-(b+e-a)) = a*c*h+d*(b-a)*(e-a) := by
        linear_combination -hC
      have hnon : 0 ≤ (a*d)*(f-(b+e-a)) := by
        rw [heq]
        have h₁ := sub_nonneg.mpr hb
        have h₂ := sub_nonneg.mpr he
        positivity
      have hF := nonneg_of_mul_nonneg_right hnon (mul_pos ha' hd')
      constructor <;> linarith
  dsimp only
  exact ⟨le_max_left _ _,max_le (sub_nonneg.mpr he) (by linarith),
    le_max_left _ _,max_le (sub_nonneg.mpr hb) (by linarith),
    sum_of_maxes_le (sub_nonneg.mpr hB.1) (by linarith) (by linarith) hB.2,
    sum_of_maxes_le hg h22 h17 h23⟩

/-- Nonnegative ranges for the T20 marker coefficients. -/
theorem choices20 {a b c d e f g h : ℝ}
    (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (hf : 0 ≤ f) (hg : 0 ≤ g)
    (hh : 0 ≤ h) (hba : b ≤ a) (he : a ≤ e)
    (h15 : b ≤ c+f) (h19 : e ≤ f+h)
    (h20 : a-b ≤ d+h) (h22 : e-b-h ≤ g)
    (hC : fourMatchingCubic (lift20 a b c d e f g h) = 0) :
    let s := max 0 (e-b-h)
    b ≤ f ∧ a-b ≤ h ∧ 0 ≤ s ∧ s ≤ e-a ∧ s ≤ f-b ∧ s ≤ g := by
  rw [cubic20] at hC
  have ha : 0 ≤ a := hb.trans hba
  have hN : b ≤ f ∧ a-b ≤ h := by
    by_cases hcd : c+d = 0
    · have hc0 : c = 0 := by linarith
      have hd0 : d = 0 := by linarith
      constructor <;> linarith
    have hcd' : 0 < c+d := lt_of_le_of_ne (add_nonneg hc hd) (Ne.symm hcd)
    have h0 : a*(e-f) ≤ a*h := mul_le_mul_of_nonneg_left (by linarith) ha
    constructor
    · by_contra hcontra
      have hs : f < b := lt_of_not_ge hcontra
      have ha' : 0 < a := lt_of_lt_of_le (hf.trans_lt hs) hba
      have hF : 0 < b*e-a*f := by
        have hm := mul_le_mul_of_nonneg_left he hb
        have hp := mul_pos ha' (sub_pos.mpr hs)
        nlinarith only [hm,hp]
      have hH : b*e-a*f ≤ a*h-(a-b)*e := by nlinarith only [h0]
      have hP := mul_pos hcd' hF
      have hR := mul_le_mul_of_nonneg_left hH hc
      nlinarith only [hP,hR,hC]
    · by_contra hcontra
      have hs : h < a-b := lt_of_not_ge hcontra
      have ha' : 0 < a := by
        by_contra hz
        have ha0 : a = 0 := le_antisymm (le_of_not_gt hz) ha
        have hb0 : b = 0 := le_antisymm (ha0 ▸ hba) hb
        rw [ha0,hb0,sub_zero] at hs
        exact (not_lt_of_ge hh) hs
      have hm := mul_le_mul_of_nonneg_left he (sub_nonneg.mpr hba)
      have hp := mul_pos ha' (sub_pos.mpr hs)
      have hH : a*h-(a-b)*e < 0 := by nlinarith only [hm,hp]
      have hF : b*e-a*f ≤ a*h-(a-b)*e := by nlinarith only [h0]
      have hP := mul_neg_of_pos_of_neg hcd' hH
      have hR := mul_le_mul_of_nonneg_left hF hd
      nlinarith only [hP,hR,hC]
  dsimp only
  exact ⟨hN.1,hN.2,le_max_left _ _,max_le (sub_nonneg.mpr he) (by linarith [hN.2]),
    max_le (sub_nonneg.mpr hN.1) (by linarith),max_le hg h22⟩

end MOC.ZhengEarlyRectangles
