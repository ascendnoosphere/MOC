import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! The four-budget certificate for the positive T5 chart with `H > 0`. -/

namespace MOC

private theorem quadratic_nonneg_between_endpoints {a b c D d : ℝ}
    (hD : 0 < D) (hd : 0 ≤ d) (hdD : d ≤ D) (hc : 0 ≤ c)
    (ha : 0 ≤ a) (hE : 0 ≤ a + b * D - c * D ^ 2) : 0 ≤ a + b * d - c * d ^ 2 := by
  apply (mul_nonneg_iff_of_pos_left hD).mp
  have h₀ := mul_nonneg (sub_nonneg.mpr hdD) ha
  have h₁ := mul_nonneg hd hE
  have h₂ := mul_nonneg (mul_nonneg hc hD.le) (mul_nonneg hd (sub_nonneg.mpr hdD))
  nlinarith only [h₀, h₁, h₂]

set_option maxHeartbeats 1300000 in
/-- In the positive T5 chart, the positive-`H` branch satisfies the
four-budget capacity. The upper endpoint has a polynomial certificate
with all coefficients nonnegative in `W`, `r`, `u`, `t`, and `1 - t`. -/
theorem fourT5_four_budget_of_positive_chart (x t r u d a e : ℝ)
    (hx : 1 < x) (ht : 0 < t) (ht₁ : t < 1) (hr : 0 < r) (hu : 0 < u)
    (hd : 0 < d) (he : 0 ≤ e) :
    let y := x - 1
    let h := 1 - t
    let L := x - r - t - u
    let H := -r * t + t * y - u
    let W := t * y - r - u
    let B := t * u * x * y
    let C := t * x * (r + u)
    0 < H → H * e = t * (u * x * h * W - L * d) →
    H * a = h * ((x - r) * d + r * t * x * (y - r - u)) →
    d ^ 2 * (a + (B - d) + C + d) ≤ a * (B - d) * (C - d) := by
  intro y h L H W B C hH hE hA
  have hx₀ : 0 < x := zero_lt_one.trans hx
  have hy : 0 < y := sub_pos.mpr hx
  have hh : 0 < h := sub_pos.mpr ht₁
  have hL : 0 < L := by
    have hEq : H = t * L - h * (t + u) := by dsimp only [H, L, h, y]; ring
    exact pos_of_mul_pos_right (by linarith only [hEq, hH, mul_pos hh (add_pos ht hu)]) ht.le
  have hxr : 0 < x - r := by dsimp only [L] at hL; linarith only [hL, ht, hu]
  let U := u * x * h * W
  have heU : 0 ≤ U - L * d := by
    apply (mul_nonneg_iff_of_pos_left ht).mp
    exact hE ▸ mul_nonneg hH.le he
  have hU : 0 < U := (mul_pos hL hd).trans_le (sub_nonneg.mp heU)
  have hW : 0 < W := pos_of_mul_pos_right hU (mul_pos (mul_pos hu hx₀) hh).le
  have hyru : 0 < y - r - u := by
    have hty := mul_lt_mul_of_pos_right ht₁ hy
    dsimp only [W] at hW
    linarith only [hty, hW]
  let D := U / L
  have hD : 0 < D := div_pos (mul_pos (mul_pos (mul_pos hu hx₀) hh) hW) hL
  have hdD : d ≤ D := (le_div_iff₀ hL).mpr (by simpa only [mul_comm] using sub_nonneg.mp heU)
  let a₀ := h * r * t * x * (y - r - u) / H
  let a₁ := h * (x - r) / H
  let P := r * W ^ 2 + (r + u) * (r * (2 - t) + u * (1 - t)) * W +
    (r + u) ^ 2 * (1 - t) * (r + t + u)
  let Q (s : ℝ) := (a₀ + a₁ * s) * (B * C - (B + C) * s) - (B + C) * s ^ 2
  have ha₀ : 0 < a₀ := div_pos (mul_pos (mul_pos (mul_pos (mul_pos hh hr) ht) hx₀) hyru) hH
  have ha₁ : 0 < a₁ := div_pos (mul_pos hh hxr) hH
  have hB : 0 < B := mul_pos (mul_pos (mul_pos ht hu) hx₀) hy
  have hC : 0 < C := mul_pos (mul_pos ht hx₀) (add_pos hr hu)
  have ha : a = a₀ + a₁ * d := by
    dsimp only [a₀, a₁]
    field_simp [hH.ne']
    linear_combination hA
  have hLD : L * D = U := by
    dsimp only [D]
    field_simp [hL.ne'] <;> ring
  have hLa : L * (a₀ + a₁ * D) = x * h * (r * L + u * x * h) := by
    dsimp only [a₀, a₁, D]
    field_simp [hL.ne', hH.ne']
    dsimp only [U, H, L, W, h, y]
    ring
  have hpoly : x * h * (r * L + u * x * h) * (L * B * C - (B + C) * U) -
      (B + C) * U ^ 2 = u * x ^ 3 * (r + u) * h * P * L := by
    dsimp only [U, P, B, C, H, L, W, h, y]
    ring
  have hEnd : L ^ 2 * Q D = u * x ^ 3 * (r + u) * h * P * L := by
    calc
      _ = (L * (a₀ + a₁ * D)) * (L * B * C - (B + C) * (L * D)) -
          (B + C) * (L * D) ^ 2 := by dsimp only [Q]; ring
      _ = _ := by rw [hLa, hLD]; exact hpoly
  have hP : 0 ≤ P := by
    have h2t : 0 ≤ 2 - t := by linarith only [ht₁]
    have h1t : 0 ≤ 1 - t := sub_nonneg.mpr ht₁.le
    dsimp only [P]
    positivity
  have hEnd' : 0 ≤ Q D := by
    apply (mul_nonneg_iff_of_pos_left (pow_pos hL 2)).mp
    rw [hEnd]
    positivity
  let lin := a₁ * B * C - a₀ * (B + C)
  let quad := (a₁ + 1) * (B + C)
  have hrep (s : ℝ) : Q s = a₀ * B * C + lin * s - quad * s ^ 2 := by
    dsimp only [Q, lin, quad]
    ring
  have hQ : 0 ≤ Q d := by
    rw [hrep]
    apply quadratic_nonneg_between_endpoints hD hd.le hdD (by dsimp only [quad]; positivity)
      (by positivity)
    rwa [← hrep]
  apply sub_nonneg.mp
  rw [show a * (B - d) * (C - d) - d ^ 2 * (a + (B - d) + C + d) = Q d by
    dsimp only [Q]; rw [← ha]; ring]
  exact hQ

set_option maxHeartbeats 1300000 in
/-- The negative T5 chart satisfies the two-budget capacity. Each possible
upper endpoint has a polynomial certificate after clearing its positive or
negative denominator with the corresponding sign. -/
theorem fourT5_two_budget_of_negative_chart (X T R U d e f : ℝ)
    (hX : 0 < X) (hT : 0 < T) (hR : 0 < R) (hU : 0 < U) (hRU : U ≤ R)
    (hd : 0 < d) (he : 0 ≤ e) (hf : 0 ≤ f) :
    let L := R + T - X - U
    let H := T * (X + 1 - R) - U
    let W := R - U + T * (X + 1)
    let B := T * U * X * (X + 1)
    let G := R * T * (X + 1)
    0 ≤ L → d ≤ B → H * e = T * (L * d - U * X * (T + 1) * W) →
    H * f = (T + 1) * ((R - X) * d + R * T * X * (R - X - U - 1)) →
    d ^ 2 ≤ G * e := by
  intro L H W B G hL hdB hE hF
  have hX₁ : 0 < X + 1 := by linarith only [hX]
  have hT₁ : 0 < T + 1 := by linarith only [hT]
  have hW : 0 < W := by
    dsimp only [W]
    exact add_pos_of_nonneg_of_pos (sub_nonneg.mpr hRU) (mul_pos hT hX₁)
  have hB : 0 < B := mul_pos (mul_pos (mul_pos hT hU) hX) hX₁
  have hG : 0 < G := mul_pos (mul_pos hR hT) hX₁
  let E := U * X * (T + 1) * W
  let N := R * T * X * (X + U + 1 - R)
  have hF' : H * f = (T + 1) * ((R - X) * d - N) := by
    rw [hF]
    dsimp only [N]
    ring
  have hH : H < 0 := by
    by_contra! hH
    have hxR : 0 < X + 1 - R := by
      have h : 0 < T * (X + 1 - R) := by dsimp only [H] at hH; linarith only [hH, hU]
      exact (mul_pos_iff_of_pos_left hT).mp h
    have hN : 0 < N := mul_pos (mul_pos (mul_pos hR hT) hX) (by linarith only [hxR, hU])
    have h := (mul_nonneg_iff_of_pos_left hT₁).mp (hF' ▸ mul_nonneg hH hf)
    have hRX : 0 < R - X := pos_of_mul_pos_left (by linarith only [hN, h]) hd.le
    have hmono := mul_le_mul_of_nonneg_left hdB hRX.le
    have hpoly : (R - X) * B - N = -T * X * (R + U * X) * (X + 1 - R) := by
      dsimp only [N, B]
      ring
    have hneg : -T * X * (R + U * X) * (X + 1 - R) < 0 := by
      have hpos := mul_pos (mul_pos (mul_pos hT hX) (add_pos hR (mul_pos hU hX))) hxR
      linarith only [hpos]
    linarith only [h, hmono, hpoly, hneg]
  have hRX : 0 < R - X := by
    by_contra! h
    have hTR := mul_nonneg hT.le (neg_nonneg.mpr h)
    dsimp only [H] at hH
    dsimp only [L] at hL
    nlinarith only [h, hH, hL, hTR]
  let D := N / (R - X)
  have hdD : d ≤ D := (le_div_iff₀ hRX).mpr (by
    have h := nonpos_of_mul_nonpos_right (hF' ▸ mul_nonpos_of_nonpos_of_nonneg hH.le hf) hT₁
    nlinarith only [h])
  have hD : 0 < D := hd.trans_le hdD
  let Q (s : ℝ) := G * T * (E - L * s) + H * s ^ 2
  let P := R * (R - U) + (X + 1) * (R * T - (T + 1) * X)
  let V := -(X + 1) * H - R * (T + 1)
  have hbase : 0 ≤ G * T * E := by dsimp only [E]; positivity
  have hBEnd : Q B = -(T ^ 2 * U * X * (R + U * X) * (X + 1)) * V := by
    dsimp only [Q, V, E, G, B, L, H, W]
    ring
  have hDEnd : (R - X) ^ 2 * Q D = -H * R * T ^ 2 * X * (R + U * X) * P := by
    have hden : (R - X) * D = N := by dsimp only [D]; field_simp [hRX.ne'] <;> ring
    calc
      _ = G * T * (E * (R - X) ^ 2 - L * ((R - X) * D) * (R - X)) +
          H * ((R - X) * D) ^ 2 := by dsimp only [Q]; ring
      _ = _ := by
        rw [hden]
        dsimp only [G, E, L, N, H, W, P]
        ring
  have hrep (s : ℝ) : Q s = G * T * E + (-G * T * L) * s - (-H) * s ^ 2 := by
    dsimp only [Q]
    ring
  have hQ : 0 ≤ Q d := by
    rw [hrep]
    rcases le_or_gt R (X + 1) with h | h
    · have hV : V ≤ 0 := by
        have hi : V = -X * (T + 1) * (X + 1 - R) - (X + 1) * L := by
          dsimp only [V, H, L]; ring
        rw [hi]
        exact sub_nonpos.mpr ((mul_nonpos_of_nonpos_of_nonneg
          (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hX.le) hT₁.le) (sub_nonneg.mpr h)).trans
          (mul_nonneg hX₁.le hL))
      have hQB : 0 ≤ Q B := by
        rw [hBEnd, neg_mul_comm]
        refine mul_nonneg ?_ (neg_nonneg.mpr hV)
        exact mul_nonneg
          (mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg T) hU.le) hX.le)
            (add_nonneg hR.le (mul_nonneg hU.le hX.le)))
          hX₁.le
      apply quadratic_nonneg_between_endpoints hB hd.le hdB (neg_nonneg.mpr hH.le) hbase
      rwa [← hrep]
    · have hP : 0 ≤ P := by
        have hi : P = X * (T + 1) * (R - X - 1) + R * L := by dsimp only [P, L]; ring
        rw [hi]
        have hdiff : 0 < R - X - 1 := by linarith only [h]
        positivity
      have hQD : 0 ≤ Q D := by
        apply (mul_nonneg_iff_of_pos_left (pow_pos hRX 2)).mp
        rw [hDEnd]
        exact mul_nonneg
          (mul_nonneg
            (mul_nonneg (mul_nonneg (mul_nonneg (neg_nonneg.mpr hH.le) hR.le) (sq_nonneg T))
              hX.le)
            (add_nonneg hR.le (mul_nonneg hU.le hX.le)))
          hP
      apply quadratic_nonneg_between_endpoints hD hd.le hdD (neg_nonneg.mpr hH.le) hbase
      rwa [← hrep]
  apply sub_nonneg.mp
  apply (mul_nonneg_iff_of_pos_left (neg_pos.mpr hH)).mp
  have hi : -H * (G * e - d ^ 2) = Q d := by
    dsimp only [Q, E]
    linear_combination -G * hE
  rwa [hi]

set_option maxHeartbeats 1300000 in
/-- The positive T5 chart with `H < 0` satisfies the two-budget capacity. -/
theorem fourT5_two_budget_of_positive_chart (x t r u d e a : ℝ)
    (hx : 1 < x) (ht : 0 < t) (ht₁ : t < 1) (hr : 0 < r) (hu : 0 < u)
    (hd : 0 < d) (ha : 0 ≤ a) :
    let y := x - 1
    let h := 1 - t
    let L := x - r - t - u
    let H := -r * t + t * y - u
    let W := t * y - r - u
    let B := t * u * x * y
    let G := r * t * y
    0 ≤ L → H < 0 → d ≤ B → H * e = t * (u * x * h * W - L * d) →
    H * a = h * ((x - r) * d + r * t * x * (y - r - u)) → d ^ 2 ≤ G * e := by
  intro y h L H W B G hL hH hdB hE hA
  have hx₀ : 0 < x := zero_lt_one.trans hx
  have hy : 0 < y := sub_pos.mpr hx
  have hh : 0 < h := sub_pos.mpr ht₁
  have hxr : 0 < x - r := by dsimp only [L] at hL; linarith only [hL, ht, hu]
  have hW : W < 0 := by
    have heq : W = H - r * h := by dsimp only [W, H, h]; ring
    linarith only [heq, hH, mul_pos hr hh]
  have hB : 0 < B := mul_pos (mul_pos (mul_pos ht hu) hx₀) hy
  have hG : 0 < G := mul_pos (mul_pos hr ht) hy
  let E := u * x * h * W
  let N := r * t * x * (r + u - y)
  let D := N / (x - r)
  have hA' : H * a = h * ((x - r) * d - N) := by rw [hA]; dsimp only [N]; ring
  have hdD : d ≤ D := (le_div_iff₀ hxr).mpr (by
    have hnon := nonpos_of_mul_nonpos_right (hA' ▸ mul_nonpos_of_nonpos_of_nonneg hH.le ha) hh
    nlinarith only [hnon])
  have hD : 0 < D := hd.trans_le hdD
  let Q (s : ℝ) := G * t * (L * s - E) + H * s ^ 2
  let P := r * (r + u) - y * (r * t + h * x)
  let V := y * H + r * h
  have hbase : 0 ≤ G * t * (-E) := by
    have hE' : E < 0 := mul_neg_of_pos_of_neg (mul_pos (mul_pos hu hx₀) hh) hW
    exact mul_nonneg (mul_nonneg hG.le ht.le) (neg_nonneg.mpr hE'.le)
  have hBEnd : Q B = t ^ 2 * u * x * (r + u * x) * y * V := by
    dsimp only [Q, V, E, G, B, L, H, W, y, h]
    ring
  have hDEnd : (x - r) ^ 2 * Q D = H * r * t ^ 2 * x * (r + u * x) * P := by
    have hden : (x - r) * D = N := by dsimp only [D]; field_simp [hxr.ne'] <;> ring
    calc
      _ = G * t * (L * ((x - r) * D) * (x - r) - E * (x - r) ^ 2) +
          H * ((x - r) * D) ^ 2 := by dsimp only [Q]; ring
      _ = _ := by
        rw [hden]
        dsimp only [G, E, L, N, H, W, P, y, h]
        ring
  have hrep (s : ℝ) : Q s = G * t * (-E) + (G * t * L) * s - (-H) * s ^ 2 := by
    dsimp only [Q]
    ring
  have hQ : 0 ≤ Q d := by
    rw [hrep]
    rcases lt_or_ge r y with hlt | hle
    · have hP : P ≤ 0 := by
        have hi : P = -h * x * (y - r) - r * L := by dsimp only [P, L, y, h]; ring
        rw [hi]
        exact sub_nonpos.mpr ((mul_nonpos_of_nonpos_of_nonneg
          (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hh.le) hx₀.le) (sub_nonneg.mpr hlt.le)).trans
          (mul_nonneg hr.le hL))
      have hQD : 0 ≤ Q D := by
        apply (mul_nonneg_iff_of_pos_left (pow_pos hxr 2)).mp
        rw [hDEnd]
        exact mul_nonneg_of_nonpos_of_nonpos
          (mul_nonpos_of_nonpos_of_nonneg
            (mul_nonpos_of_nonpos_of_nonneg
              (mul_nonpos_of_nonpos_of_nonneg
                (mul_nonpos_of_nonpos_of_nonneg hH.le hr.le) (sq_nonneg t)) hx₀.le)
            (add_nonneg hr.le (mul_nonneg hu.le hx₀.le))) hP
      apply quadratic_nonneg_between_endpoints hD hd.le hdD (neg_nonneg.mpr hH.le) hbase
      rwa [← hrep]
    · have hV : 0 ≤ V := by
        have hi : V = y * L + h * (r - y) * (y + 1) := by dsimp only [V, H, L, y, h]; ring
        rw [hi]
        have hry : 0 ≤ r - y := sub_nonneg.mpr hle
        positivity
      have hQB : 0 ≤ Q B := by
        rw [hBEnd]
        exact mul_nonneg
          (mul_nonneg
            (mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg t) hu.le) hx₀.le)
              (add_nonneg hr.le (mul_nonneg hu.le hx₀.le)))
            hy.le)
          hV
      apply quadratic_nonneg_between_endpoints hB hd.le hdB (neg_nonneg.mpr hH.le) hbase
      rwa [← hrep]
  apply sub_nonneg.mp
  apply (mul_nonneg_iff_of_pos_left (neg_pos.mpr hH)).mp
  have hi : -H * (G * e - d ^ 2) = Q d := by
    dsimp only [Q, E]
    linear_combination -G * hE
  rwa [hi]

end MOC
