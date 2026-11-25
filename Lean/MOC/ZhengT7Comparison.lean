import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! Comparison from the exact rational chart for Zheng's T7
(DOI: 10.13140/RG.2.2.36790.25923, Appendix G). This module checks the
signs and constructive minor coefficients. The bracket chart and its
partial fractions are derived in ZhengT7Direct.md. -/

namespace MOC.ZhengT7

/-- The nontrivial chart's offset ordering signs the two projected
identities needed for the ordinary-minor decomposition. -/
theorem comparisons_of_chart {a b c d e M ℓ K N X Y F G : ℝ}
    (ha : a < 0) (he : 0 < e) (hed : e < d) (hdc : d < c) (hcb : c < b)
    (hM : 0 ≤ M) (hℓ : ℓ = a+b-c)
    (hK : K = a*(a*b-e*ℓ)-b*(a*b-d*ℓ))
    (hN : N = (a-c)*(c-e)+(b-c)*(d-c))
    (hG : K*(G-X) = (b-c)*M*X+b*N*Y)
    (hF : K*(F-X-Y) = -a*M*X+(a-c)*(a*e-b*d)*Y) :
    (0 < X → Y ≤ 0 → X ≤ G) ∧ (0 < X → 0 < Y → X+Y ≤ F) := by
  have hb : 0 < b := by linarith
  have hd : 0 < d := he.trans hed
  have hc : 0 < c := hd.trans hdc
  have hab : a*b < 0 := mul_neg_of_neg_of_pos ha hb
  have hlinear (t : ℝ) (ht : 0 < t) (htb : t < b) : a*b-t*ℓ < 0 := by
    by_cases h : 0 ≤ ℓ
    · linarith only [hab,mul_nonneg ht.le h]
    · have h₁ := mul_lt_mul_of_pos_left (show a < ℓ by linarith) ht
      have h₂ := mul_lt_mul_of_neg_left htb ha
      nlinarith only [h₁,h₂]
  have hK' : 0 < K := by
    rw [hK]
    exact sub_pos.mpr (lt_trans
      (mul_neg_of_pos_of_neg hb (hlinear d hd (hdc.trans hcb)))
      (mul_pos_of_neg_of_neg ha (hlinear e he (hed.trans (hdc.trans hcb)))))
  have hN' : N < 0 := by
    rw [hN]
    exact add_neg
      (mul_neg_of_neg_of_pos (sub_neg.mpr (ha.trans hc)) (sub_pos.mpr (hed.trans hdc)))
      (mul_neg_of_pos_of_neg (sub_pos.mpr hcb) (sub_neg.mpr hdc))
  have hBD : a*e-b*d < 0 := by
    linarith only [mul_neg_of_neg_of_pos ha he,mul_pos hb hd]
  constructor
  · intro hX hY
    have hh : 0 ≤ (b-c)*M*X+b*N*Y :=
      add_nonneg (mul_nonneg (mul_nonneg (sub_nonneg.mpr hcb.le) hM) hX.le)
        (mul_nonneg_of_nonpos_of_nonpos (mul_nonpos_of_nonneg_of_nonpos hb.le hN'.le) hY)
    rw [← hG] at hh
    exact sub_nonneg.mp (nonneg_of_mul_nonneg_right hh hK')
  · intro hX hY
    have hh : 0 ≤ -a*M*X+(a-c)*(a*e-b*d)*Y :=
      add_nonneg (mul_nonneg (mul_nonneg (neg_nonneg.mpr ha.le) hM) hX.le)
        (mul_nonneg (mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr (ha.trans hc).le) hBD.le) hY.le)
    rw [← hF] at hh
    have hge := nonneg_of_mul_nonneg_right hh hK'
    linarith only [hge]

/-- The two nonlinear comparisons and five elementary gap inequalities
make all ten ordinary-minor coefficients nonnegative. -/
theorem minor_coefficients {A B C D E F G J : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (hD : 0 ≤ D) (hJ : 0 ≤ J)
    (hF : 0 ≤ F) (hG : 0 ≤ G)
    (h14 : 0 ≤ E-B) (h15 : A-C ≤ F) (h19 : E-B-J ≤ F)
    (h22 : E-B-J ≤ G) (h23 : A-C+(E-B-J) ≤ G)
    (hGX : 0 < A-C → E-B-J < 0 → A-C ≤ G)
    (hFXY : 0 < A-C → 0 < E-B-J → A-C+(E-B-J) ≤ F) :
    let x := max 0 (E-B-J); let y := max 0 (A-C)
    0 ≤ x ∧ 0 ≤ J-E+B+x ∧ 0 ≤ C-A+y ∧ 0 ≤ y ∧
    0 ≤ D ∧ 0 ≤ G-x-y ∧ 0 ≤ B ∧ 0 ≤ F-x-y ∧ 0 ≤ A-y ∧ 0 ≤ E-B-x := by
  dsimp only
  let x := max 0 (E-B-J)
  let y := max 0 (A-C)
  have h0x : 0 ≤ x := le_max_left _ _
  have h0y : 0 ≤ y := le_max_left _ _
  have hYe : E-B-J ≤ x := le_max_right _ _
  have hXe : A-C ≤ y := le_max_right _ _
  have hx : x ≤ E-B := max_le h14 (by linarith)
  have hy : y ≤ A := max_le hA (by linarith)
  have hF' : x+y ≤ F := by
    by_cases hY : 0 < E-B-J
    · simp only [x,max_eq_right hY.le]
      by_cases hX : 0 < A-C
      · simp only [y,max_eq_right hX.le]
        linarith only [hFXY hX hY]
      · simp only [y,max_eq_left (le_of_not_gt hX),add_zero]
        exact h19
    · simp only [x,max_eq_left (le_of_not_gt hY),zero_add]
      exact max_le hF h15
  have hG' : x+y ≤ G := by
    by_cases hY : 0 < E-B-J
    · simp only [x,max_eq_right hY.le]
      by_cases hX : 0 < A-C
      · simp only [y,max_eq_right hX.le]
        linarith only [h23]
      · simp only [y,max_eq_left (le_of_not_gt hX),add_zero]
        exact h22
    · simp only [x,max_eq_left (le_of_not_gt hY),zero_add]
      apply max_le hG
      by_cases hX : 0 < A-C
      · by_cases hY' : E-B-J = 0
        · linarith only [hY',h23]
        · exact hGX hX (lt_of_le_of_ne (le_of_not_gt hY) hY')
      · exact (le_of_not_gt hX).trans hG
  change 0 ≤ x ∧ 0 ≤ J-E+B+x ∧ 0 ≤ C-A+y ∧ 0 ≤ y ∧
    0 ≤ D ∧ 0 ≤ G-x-y ∧ 0 ≤ B ∧ 0 ≤ F-x-y ∧ 0 ≤ A-y ∧ 0 ≤ E-B-x
  exact ⟨h0x,by linarith,by linarith,h0y,hD,by linarith,hB,by linarith,by linarith,by linarith⟩

end MOC.ZhengT7
