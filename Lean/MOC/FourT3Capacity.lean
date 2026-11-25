import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! The order and sign argument for the negative-defect branch of the
T3 projective chart. The equations are polynomial after clearing the
positive norm denominator and `T + 1`. -/

namespace MOC

/-- The real T3 chart forces the two-budget bound. The exceptional
stratum `r = -1, u = X` is evaluated in the original chart. -/
theorem fourT3_capacity_of_real_chart {X T r u A a b e f j k N q : ℝ}
    (hX : 0 < X) (hT : 0 < T) (hr : -1 ≤ r) (hru : r * u < 0)
    (ha : 0 < a) (hb : 0 < b) (he : 0 ≤ e) (hf : 0 ≤ f) (hj : 0 ≤ j)
    (hN : 0 < N) (hq : 0 < q) (hA : A < 0)
    (hAe : A = f - e + j) (h21 : 0 ≤ X * b + A) (hk : T * (e - j) = k)
    (hE : N * e = q * u * (T + 1) * ((1 + r) * T - r * u - X))
    (hJ : (T + 1) * (u - X) * j =
      -X * (1 + r) * a * (T + 1) + u * (T - X) * e)
    (hF : (X - T) * (f - e) = X * (T + 1) * b + (X + 1) * (T - u) * e)
    (hExceptional : r = -1 → u = X → T < X → j < 0) : A ^ 2 ≤ b * k := by
  have hT₁ : 0 < T + 1 := by linarith only [hT]
  have hX₁ : 0 < X + 1 := by linarith only [hX]
  have hr₁ : 0 ≤ 1 + r := by linarith only [hr]
  let C := (1 + r) * T - r * u - X
  change N * e = q * u * (T + 1) * C at hE
  have hC (hu : 0 < u) : 0 ≤ C :=
    (mul_nonneg_iff_of_pos_left (mul_pos (mul_pos hq hu) hT₁)).mp (hE ▸ mul_nonneg hN.le he)
  have hC' (hu : u < 0) : C ≤ 0 := by
    by_contra! hc
    exact (not_lt_of_ge (hE ▸ mul_nonneg hN.le he))
      (mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hq hu) hT₁) hc)
  rcases mul_neg_iff.mp hru with ⟨hrp, hun⟩ | ⟨hrn, hup⟩
  · have hXT : T < X := by
      have hc := hC' hun
      dsimp only [C] at hc
      nlinarith only [hc, hru, mul_pos hrp hT]
    have hTu : 0 < T - u := sub_pos.mpr (hun.trans hT)
    have hsum : 0 < (X - T) * (f - e) := by
      rw [hF]
      exact add_pos_of_pos_of_nonneg (mul_pos (mul_pos hX hT₁) hb)
        (mul_nonneg (mul_pos hX₁ hTu).le he)
    have hfe := (mul_pos_iff_of_pos_left (sub_pos.mpr hXT)).mp hsum
    linarith only [hA, hAe, hfe, hj]
  · have hc := hC hup
    have hTX : X ≤ T := by
      by_contra! hlt
      have hxu : X ≤ u := by
        by_contra! huX
        have hneg₀ := mul_nonpos_of_nonneg_of_nonpos hr₁ (sub_nonpos.mpr hlt.le)
        have hneg₁ := mul_neg_of_pos_of_neg (neg_pos.mpr hrn) (sub_neg.mpr huX)
        dsimp only [C] at hc
        nlinarith only [hc, hneg₀, hneg₁]
      rcases lt_or_eq_of_le hxu with huX | huX
      · have hleft : 0 ≤ (T + 1) * (u - X) * j :=
          mul_nonneg (mul_pos hT₁ (sub_pos.mpr huX)).le hj
        have hfirst : -X * (1 + r) * a * (T + 1) ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg
            (mul_nonpos_of_nonpos_of_nonneg
              (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hX.le) hr₁) ha.le) hT₁.le
        have hsecond : u * (T - X) * e ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg (mul_neg_of_pos_of_neg hup (sub_neg.mpr hlt)).le he
        rcases lt_or_eq_of_le hr with hrr | hrr
        · have hrr' : 0 < 1 + r := by linarith only [hrr]
          have hfirst' := mul_neg_of_neg_of_pos
            (mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (neg_neg_of_pos hX) hrr') ha) hT₁
          linarith only [hJ, hleft, hfirst', hsecond]
        · have hc' : 0 < C := by
            dsimp only [C]
            rw [← hrr]
            linarith only [huX]
          have hE' : 0 < N * e := hE.symm ▸ mul_pos (mul_pos (mul_pos hq hup) hT₁) hc'
          have he' := (mul_pos_iff_of_pos_left hN).mp hE'
          have hsecond' := mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hup (sub_neg.mpr hlt)) he'
          linarith only [hJ, hleft, hfirst, hsecond']
      · have hrr : r = -1 := by
          by_contra hne
          have hrr' : 0 < 1 + r := by
            have hlt' := lt_of_le_of_ne hr (Ne.symm (show r ≠ -1 from hne))
            linarith only [hlt']
          have hn := mul_neg_of_pos_of_neg hrr' (sub_neg.mpr hlt)
          dsimp only [C] at hc
          rw [← huX] at hc
          nlinarith only [hc, hn]
        exact (not_lt_of_ge hj) (hExceptional hrr huX.symm hlt)
    let d := -A
    have hd : 0 < d := neg_pos.mpr hA
    have hdb : d ≤ T * b := by
      have hxb := mul_le_mul_of_nonneg_right hTX hb.le
      dsimp only [d]
      linarith only [hxb, h21]
    have hdk : d * T ≤ k := by
      have hde : d ≤ e - j := by dsimp only [d]; linarith only [hAe, hf]
      rw [← hk, mul_comm d]
      exact mul_le_mul_of_nonneg_left hde hT.le
    calc
      A ^ 2 = d * d := by dsimp only [d]; ring
      _ ≤ d * (T * b) := mul_le_mul_of_nonneg_left hdb hd.le
      _ = b * (d * T) := by ring
      _ ≤ b * k := mul_le_mul_of_nonneg_left hdk hb.le

end MOC
