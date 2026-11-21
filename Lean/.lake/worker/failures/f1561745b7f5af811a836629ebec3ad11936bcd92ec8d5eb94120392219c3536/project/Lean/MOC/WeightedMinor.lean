import MOC.MixedBound
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! The analytic two-minor compensation inequality in quaternion
coordinates for order four. -/

namespace MOC

private theorem sum_sqrt_products_le {a b c d : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) :
    √(a * c) + √(b * d) ≤ √((a + b) * (c + d)) := by
  rw [Real.sqrt_mul ha, Real.sqrt_mul hb]
  apply Real.le_sqrt_of_sq_le
  have hnorm : (√a * √c + √b * √d) ^ 2 + (√a * √d - √b * √c) ^ 2 =
      (a + b) * (c + d) := by
    calc
      _ = ((√a) ^ 2 + (√b) ^ 2) * ((√c) ^ 2 + (√d) ^ 2) := by ring
      _ = _ := by rw [Real.sq_sqrt ha, Real.sq_sqrt hb, Real.sq_sqrt hc, Real.sq_sqrt hd]
  linarith only [hnorm, sq_nonneg (√a * √d - √b * √c)]

private theorem sq_abs_sub_abs_le (a b : ℝ) : (|a| - |b|) ^ 2 ≤ (a - b) ^ 2 := by
  simpa only [sq_abs] using
    (sq_le_sq₀ (abs_nonneg (|a| - |b|)) (abs_nonneg (a - b))).2
      (abs_abs_sub_abs_le_abs_sub a b)

private theorem abs_sum_lower (a b : ℝ) :
    (a + b) ^ 2 ≤ (|a| + |b|) ^ 2 ∧ (a - b) ^ 2 ≤ (|a| + |b|) ^ 2 := by
  have hab := add_nonneg (abs_nonneg a) (abs_nonneg b)
  constructor
  · simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg (a + b)) hab).2 (abs_add_le a b)
  · have h := abs_add_le a (-b)
    rw [← sub_eq_add_neg, abs_neg] at h
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg (a - b)) hab).2 h

private theorem weighted_probability_ordered (P R : Fin 4 → ℝ)
    (hP : ∀ i, 0 ≤ P i) (hR : ∀ i, 0 ≤ R i)
    (hPs : P 0 + P 1 + P 2 + P 3 = 1) (hRs : R 0 + R 1 + R 2 + R 3 = 1)
    (hv : 0 ≤ R 0 + R 2 - P 0 - P 2) :
    0 ≤ 2 * ((√(P 3 * R 0) - √(P 0 * R 3)) ^ 2 +
      (√(P 1 * R 2) - √(P 2 * R 1)) ^ 2) +
      (|P 0 + P 1 + R 0 + R 1 - 1| + |1 - P 1 - P 2 - R 1 - R 2|) ^ 2 -
      (R 0 + R 2 - P 0 - P 2) ^ 2 := by
  let u := R 2 - P 0
  let t := R 0 - P 2
  let w := P 3 - R 1
  let z := P 1 - R 3
  let v := R 0 + R 2 - P 0 - P 2
  let d₀ := P 0 + P 1 + R 0 + R 1 - 1
  let d₁ := 1 - P 1 - P 2 - R 1 - R 2
  let A := √(P 3 * R 0) - √(P 0 * R 3)
  let B := √(P 1 * R 2) - √(P 2 * R 1)
  have huv : u + t = v := by dsimp [u, t, v]; ring
  have hwv : w + z = v := by dsimp [w, z, v]; linarith only [hPs, hRs]
  have hd₀ : d₀ + d₁ = t - u := by dsimp [d₀, d₁, t, u]; ring
  have hd₁ : d₀ - d₁ = z - w := by
    dsimp [d₀, d₁, z, w]
    linarith only [hPs, hRs]
  have hfirst : v ^ 2 = (d₀ + d₁) ^ 2 + 4 * (u * t) := by rw [← huv, hd₀]; ring
  have hsecond : v ^ 2 = (d₀ - d₁) ^ 2 + 4 * (w * z) := by rw [← hwv, hd₁]; ring
  obtain ⟨hdplus, hdsub⟩ := abs_sum_lower d₀ d₁
  change 0 ≤ 2 * (A ^ 2 + B ^ 2) + (|d₀| + |d₁|) ^ 2 - v ^ 2
  by_cases hut : u * t ≤ 0
  · linarith only [hut, hfirst, hdplus, sq_nonneg A, sq_nonneg B]
  by_cases hwz : w * z ≤ 0
  · linarith only [hwz, hsecond, hdsub, sq_nonneg A, sq_nonneg B]
  have hbranches {x y : ℝ} (hxy : 0 < x * y) (hxyv : x + y = v) : 0 ≤ x ∧ 0 ≤ y := by
    rcases mul_pos_iff.mp hxy with h | h
    · exact ⟨h.1.le, h.2.le⟩
    · exfalso
      exact (not_lt_of_ge (show 0 ≤ v from hv)) (hxyv ▸ add_neg h.1 h.2)
  obtain ⟨hu, ht⟩ := hbranches (lt_of_not_ge hut) huv
  obtain ⟨hw, hz⟩ := hbranches (lt_of_not_ge hwz) hwv
  have hA := sum_sqrt_products_le hw (hR 1) ht (hP 2)
  have hB := sum_sqrt_products_le hz (hR 3) hu (hP 0)
  have hwP : w + R 1 = P 3 := by dsimp [w]; ring
  have htR : t + P 2 = R 0 := by dsimp [t]; ring
  have hzP : z + R 3 = P 1 := by dsimp [z]; ring
  have huR : u + P 0 = R 2 := by dsimp [u]; ring
  rw [hwP, htR, mul_comm (R 1)] at hA
  rw [hzP, huR, mul_comm (R 3)] at hB
  let X := √(w * t)
  let Y := √(z * u)
  have hX : 0 ≤ X := Real.sqrt_nonneg _
  have hY : 0 ≤ Y := Real.sqrt_nonneg _
  have hD : X + Y ≤ A + B := by dsimp [X, Y, A, B]; linarith only [hA, hB]
  have hDsq := (sq_le_sq₀ (add_nonneg hX hY) ((add_nonneg hX hY).trans hD)).2 hD
  have henergy : 4 * (X * Y) ≤ 2 * (A ^ 2 + B ^ 2) := by
    nlinarith only [hDsq, sq_nonneg (A - B), sq_nonneg (X - Y)]
  have hXY : (X * Y) ^ 2 = (u * t) * (w * z) := by
    dsimp [X, Y]
    rw [mul_pow, Real.sq_sqrt (mul_nonneg hw ht), Real.sq_sqrt (mul_nonneg hz hu)]
    ring
  rcases le_total (u * t) (w * z) with h | h
  · have hsq : (u * t) ^ 2 ≤ (X * Y) ^ 2 := by
      rw [hXY, sq]
      exact mul_le_mul_of_nonneg_left h (mul_nonneg hu ht)
    have hsmall := (sq_le_sq₀ (mul_nonneg hu ht) (mul_nonneg hX hY)).1 hsq
    linarith only [henergy, hsmall, hfirst, hdplus]
  · have hsq : (w * z) ^ 2 ≤ (X * Y) ^ 2 := by
      rw [hXY, sq]
      exact mul_le_mul_of_nonneg_right h (mul_nonneg hw hz)
    have hsmall := (sq_le_sq₀ (mul_nonneg hw hz) (mul_nonneg hX hY)).1 hsq
    linarith only [henergy, hsmall, hsecond, hdsub]

private theorem weighted_probability (P R : Fin 4 → ℝ)
    (hP : ∀ i, 0 ≤ P i) (hR : ∀ i, 0 ≤ R i)
    (hPs : P 0 + P 1 + P 2 + P 3 = 1) (hRs : R 0 + R 1 + R 2 + R 3 = 1) :
    0 ≤ 2 * ((√(P 3 * R 0) - √(P 0 * R 3)) ^ 2 +
      (√(P 1 * R 2) - √(P 2 * R 1)) ^ 2) +
      (|P 0 + P 1 + R 0 + R 1 - 1| + |1 - P 1 - P 2 - R 1 - R 2|) ^ 2 -
      (R 0 + R 2 - P 0 - P 2) ^ 2 := by
  by_cases hv : 0 ≤ R 0 + R 2 - P 0 - P 2
  · exact weighted_probability_ordered P R hP hR hPs hRs hv
  have hv' : 0 ≤ P 0 + P 2 - R 0 - R 2 := by linarith
  have h := weighted_probability_ordered R P hR hP hRs hPs hv'
  rw [show R 0 + R 1 + P 0 + P 1 - 1 = P 0 + P 1 + R 0 + R 1 - 1 by ring,
    show 1 - R 1 - R 2 - P 1 - P 2 = 1 - P 1 - P 2 - R 1 - R 2 by ring] at h
  rw [mul_comm (R 3), mul_comm (R 0), mul_comm (R 1), mul_comm (R 2)] at h
  nlinarith only [h]

/-- The canonical order-four mixed facet (F) and its two paired squared
minors satisfy (F + Q₁ + 2√(Q₀ Q₁) ≥ 0) in real quaternion coordinates. -/
theorem mixed_quaternion_weighted (q r : Fin 4 → ℝ)
    (hq : q 0 ^ 2 + q 1 ^ 2 + q 2 ^ 2 + q 3 ^ 2 = 1)
    (hr : r 0 ^ 2 + r 1 ^ 2 + r 2 ^ 2 + r 3 ^ 2 = 1) :
    let d₀ := q 0 ^ 2 + q 1 ^ 2 + r 0 ^ 2 + r 1 ^ 2 - 1
    let d₁ := 1 - q 1 ^ 2 - q 2 ^ 2 - r 1 ^ 2 - r 2 ^ 2
    let v := r 0 ^ 2 + r 2 ^ 2 - q 0 ^ 2 - q 2 ^ 2
    0 ≤ 2 * ((q 0 * r 3 - q 3 * r 0) ^ 2 + (q 1 * r 2 + q 2 * r 1) ^ 2) +
      d₀ ^ 2 - v ^ 2 + d₁ ^ 2 + 2 * √(d₀ ^ 2 * d₁ ^ 2) := by
  let d₀ := q 0 ^ 2 + q 1 ^ 2 + r 0 ^ 2 + r 1 ^ 2 - 1
  let d₁ := 1 - q 1 ^ 2 - q 2 ^ 2 - r 1 ^ 2 - r 2 ^ 2
  let v := r 0 ^ 2 + r 2 ^ 2 - q 0 ^ 2 - q 2 ^ 2
  have h := weighted_probability (fun i => q i ^ 2) (fun i => r i ^ 2)
    (fun i => sq_nonneg _) (fun i => sq_nonneg _) hq hr
  have hroot (i j : Fin 4) : √(q i ^ 2 * r j ^ 2) = |q i * r j| := by
    rw [← mul_pow, Real.sqrt_sq_eq_abs]
  change 0 ≤ 2 * ((√(q 3 ^ 2 * r 0 ^ 2) - √(q 0 ^ 2 * r 3 ^ 2)) ^ 2 +
    (√(q 1 ^ 2 * r 2 ^ 2) - √(q 2 ^ 2 * r 1 ^ 2)) ^ 2) +
    (|d₀| + |d₁|) ^ 2 - v ^ 2 at h
  simp only [hroot] at h
  have hcross : √(d₀ ^ 2 * d₁ ^ 2) = |d₀| * |d₁| := by
    rw [← mul_pow, Real.sqrt_sq_eq_abs, abs_mul]
  have hsum : (|d₀| + |d₁|) ^ 2 = d₀ ^ 2 + d₁ ^ 2 + 2 * √(d₀ ^ 2 * d₁ ^ 2) := by
    rw [add_sq, sq_abs, sq_abs, hcross]; ring
  have hminus := sq_abs_sub_abs_le (q 3 * r 0) (q 0 * r 3)
  have hplus := sq_abs_sub_abs_le (q 1 * r 2) (-(q 2 * r 1))
  simp only [abs_neg, sub_neg_eq_add] at hplus
  rw [hsum] at h
  change 0 ≤ 2 * ((q 0 * r 3 - q 3 * r 0) ^ 2 + (q 1 * r 2 + q 2 * r 1) ^ 2) +
    d₀ ^ 2 - v ^ 2 + d₁ ^ 2 + 2 * √(d₀ ^ 2 * d₁ ^ 2)
  nlinarith only [h, hminus, hplus]

/-- The weighted-minor inequality directly on the entries of the real
quaternion rotation. -/
theorem mixed_quaternion_rotation_weighted (q r : Fin 4 → ℝ)
    (hq : q 0 ^ 2 + q 1 ^ 2 + q 2 ^ 2 + q 3 ^ 2 = 1)
    (hr : r 0 ^ 2 + r 1 ^ 2 + r 2 ^ 2 + r 3 ^ 2 = 1) :
    let U := quaternionRotation q r
    let d₀ := U 2 2 * U 3 3 - U 2 3 * U 3 2
    let d₁ := U 1 1 * U 2 2 - U 1 2 * U 2 1
    let v := U 1 0 * U 3 2 - U 1 2 * U 3 0
    0 ≤ U 1 2 ^ 2 + U 2 1 ^ 2 + d₀ ^ 2 - v ^ 2 + d₁ ^ 2 + 2 * √(d₀ ^ 2 * d₁ ^ 2) := by
  obtain ⟨hentries, hprincipal, hmiddle, hoff⟩ := quaternionRotation_mixed_coordinates q r hq hr
  dsimp only
  rw [hentries, hprincipal, hmiddle, hoff]
  exact mixed_quaternion_weighted q r hq hr

end MOC
