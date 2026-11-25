import Mathlib.Tactic

namespace MOC

/-- The determinant factor for the eight-contact family with ordinary rays
13, 17, 18, 27, and 28 in that order. -/
def fourEightContactHigherFactor (a b c d e : ℝ) : ℝ :=
  1 + c + e + a^3 +
    b^2 + d^2 + 2*b + 2*d +
    3*a + 3*a^2 + a*b^2 + a*d^2 +
    b*e^2 + a^3*c + b^2*c + c*d^2 +
    c^2*d + a^3*e + b^2*e + d^2*e +
    b^2*d^2 + b^2*e^2 + c^2*d^2 - c*e^2 +
    -c^2*e - c^2*e^2 + 2*b*c + 2*b*e +
    2*a^2*b + 2*b*d^2 + 2*c*d + 2*d*e +
    2*a^2*d + 2*b^2*d + 3*a*c + 3*a*e +
    3*a^2*c + 3*a^2*e + 4*a*b + 4*a*d +
    4*b*d + a*c*e + a*b^2*c + a*d^2*e +
    a*b^2*d^2 + a*b^2*e^2 + a*c^2*d^2 + a^3*b*d +
    a^2*b*d^2 + a^2*b*e^2 + b*d^2*e^2 + a^3*c*e +
    b^2*c*d^2 + b^2*c*e^2 + a^2*b^2*d + a^2*c^2*d +
    b^2*c^2*d + b^2*d^2*e + c^2*d^2*e + a^2*b^2*d^2 +
    b^2*c^2*d^2 + b^2*d^2*e^2 - a^3*b*e - b*c^2*e^2 +
    -a^3*c*d - a^2*c*d^2 - a^2*c*e^2 - c*d^2*e^2 +
    -c^2*d*e^2 - a^2*b^2*e - a^2*c^2*e - b^2*c^2*e +
    -a^2*c^2*e^2 - 2*a*c*e^2 - 2*a*c^2*e - 2*a*c^2*e^2 +
    -2*b*c^2*e - 2*c*d*e^2 + 2*a*b*d^2 + 2*a*b*e^2 +
    2*a*b^2*d + 2*a*c^2*d + 2*a^2*b*c + 2*b*c*d^2 +
    2*b*c^2*d + 2*b*d*e^2 + 2*b*d^2*e + 2*b*c^2*d^2 +
    2*b^2*c*d + 2*a^2*c*e + 2*a^2*d*e + 2*b^2*d*e +
    2*b^2*d*e^2 + 3*a*b*e + 3*a*c*d + 3*a^2*b*d +
    4*a*b*c + 4*a*d*e + 4*b*c*d + 4*b*d*e +
    6*a*b*d + a*b*c*e + a*b*c*e^2 + a*b*c^2*d^2 +
    a*c*d*e + a*b^2*c*e^2 + a*c^2*d*e + a*b^2*d*e^2 +
    a*c^2*d^2*e + a^2*b*c*e + a^2*b*c*e^2 + b*c^2*d^2*e +
    a^2*c*d*e + b^2*c*d*e^2 + a^2*c^2*d*e - a*b*c*d^2 +
    -a*b*c^2*e^2 - a*b^2*c*d^2 - a*b^2*d*e - a*c^2*d*e^2 +
    -a*b^2*d^2*e - b*c*d*e - a^2*b*c*d - b*c*d*e^2 +
    -b*c*d^2*e - a^2*b*c*d^2 - b*c*d^2*e^2 - a^2*b*d*e +
    -b*c^2*d*e - b*c^2*d*e^2 - b^2*c*d*e - b^2*c*d^2*e +
    -a^2*b^2*d*e - b^2*c^2*d*e - 2*a*b*c^2*e - 2*a*c*d*e^2 +
    2*a*b*c^2*d + 2*a*b*d*e^2 + 3*a*b*c*d + 3*a*b*d*e

/-- On the positive-height cubic locus, singularity forces at least one
of the three star compensation inequalities. The cubic and determinant
factor equations are explicit hypotheses. -/
theorem fourEightContactHigherFactor_compensation
    {a b c d e h : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (hd : 0 < d) (he : 0 < e) (hh : 0 < h)
    (hCubic : a + (b + 1) * (d + 1) =
      h * ((b - c) * (d - e) + b + d + 1))
    (hFactor : fourEightContactHigherFactor a b c d e = 0) :
    1 ≤ c * e ∨ a + d ≤ a * c * d ∨ a + b ≤ a * b * e := by
  by_contra! hFailure
  rcases hFailure with ⟨hce, hcd, hbe⟩
  let q₀ := 1 - c * e
  let q₁ := a + d - a * c * d
  let q₂ := a + b - a * b * e
  let q₃ := (b - c) * (d - e) + b + d + 1
  have h₀ : 0 < q₀ := sub_pos.mpr hce
  have h₁ : 0 < q₁ := sub_pos.mpr hcd
  have h₂ : 0 < q₂ := sub_pos.mpr hbe
  have h₃ : 0 < q₃ := by
    have hNumerator : 0 < a + (b + 1) * (d + 1) := by positivity
    have hProduct : 0 < h * q₃ := by
      simpa only [q₃, ← hCubic] using hNumerator
    exact pos_of_mul_pos_left hProduct hh.le
  let remainder : ℝ := 5*b/11 + 5*d/11 + 10*a/11 + 30*a^2/11 +
    a*c + a*e + b*e^2 + a^3*c +
    c^2*d + a^3*e + b^2*e^2 + c^2*d^2 +
    2*b*e + 2*c*d + 2*a^2*c + 2*c*d^2 +
    2*a^2*e + 2*b^2*e + 7*b*d^2/11 + 7*b^2*d/11 +
    13*b*d/11 + 21*a*b/11 + 21*a*d/11 + a*b^2*c +
    a*d^2*e + b*d^2*e + a^2*b*e^2 + b*d^2*e^2 +
    b^2*c*d + a^2*c*e + a^3*c*e + b^2*c*d^2 +
    a^2*c^2*d + b^2*c^2*d + b^2*d^2*e + 2*a*b*c +
    2*a*b*e^2 + 2*a*d*e + 2*a*c^2*d + 2*a^2*b*c +
    2*b*c*d^2 + 2*b*c^2*d + 2*b*d*e^2 + 2*b*c^2*d^2 +
    2*a^2*d*e + 2*b^2*d*e + 2*b^2*d*e^2 + 3*b^2*c*e^2/11 +
    3*c^2*d^2*e/11 + 3*b^2*c^2*d^2/11 + 3*b^2*d^2*e^2/11 + 4*a*b*d^2/11 +
    4*a*b^2*d/11 + 4*a*b^2*d^2/11 + 5*a^2*b^2*d^2/11 + 8*a*b^2*e^2/11 +
    8*a*c^2*d^2/11 + 8*b^2*c*e/11 + 8*c*d^2*e/11 + 10*a^2*b*d^2/11 +
    10*a^2*b^2*d/11 + 20*a^2*b*d/11 + 26*a*b*d/11 + 36*b*c*d/11 +
    36*b*d*e/11 + 56*a*b*e/11 + 56*a*c*d/11 + a*b^2*c*e^2 +
    a*c^2*d^2*e + a^2*b*c*e + a^2*b*c*e^2 + b*c^2*d^2*e +
    a^2*c*d*e + b^2*c*d*e^2 + a^2*c^2*d*e + 2*a*b*c^2*d +
    2*a*b*d*e^2 + a*b*d^2*e/11 + a*b^2*c*d/11 + a^2*b*c*d/11 +
    a^2*b*d*e/11 + 14*a*b*c*e/11 + 14*a*c*d*e/11 + 39*a*b*c*d/11 +
    39*a*b*d*e/11 + a*b*c*d*e/11 + 6*a*b*c*d^2*e/11 + 6*a*b^2*c*d*e/11
  let w0 : ℝ := 5/11 + c + e + 3*a/11 +
    b^2*c + d^2*e + 2*a*c + 2*a*e +
    2*b*c + 2*d*e + 3*b*d^2/11 + 3*b^2*d/11 +
    5*c*e/11 + 6*b*e/11 + 6*c*d/11 + a*b*c +
    a*d*e + a^3*b*d + b*d^2*e + b^2*c*d +
    a^2*c*e + 3*b*c*e/11 + 3*c*d*e/11 + 8*a*c*e/11 +
    19*b*c*d/11 + 19*b*d*e/11 + a*b*c*e + a*c*d*e +
    b*c*d*e + a^2*b*c*e + a^2*c*d*e + a^2*b*c*d^2/11 +
    a^2*b^2*d*e/11
  let w00 : ℝ := a^2*b*d/11 + 5*a^2*b^2*d^2/11
  let w01 : ℝ := a*e
  let w012 : ℝ := b*d
  let w02 : ℝ := a*c
  let w03 : ℝ := 6/11 + 8*b/11 + 8*d/11 + 14*a/11 +
    a^2*b*d/11
  let w1 : ℝ := 10*a*d/11 + 3*a*c*d/11 + 5*b^2*d*e^2/11 + 5*a*b*c*d*e/11
  let w11 : ℝ := 3*b^2*e^2/11
  let w12 : ℝ := 3/11 + a + b/11 + d/11
  let w13 : ℝ := 3/11
  let w2 : ℝ := 10*a*b/11 + 3*a*b*e/11 + 5*b*c^2*d^2/11 + 5*a*b*c*d*e/11
  let w22 : ℝ := 3*c^2*d^2/11
  let w23 : ℝ := 3/11
  let w3 : ℝ := 7*a*b*d/11
  have hIdentity : fourEightContactHigherFactor a b c d e =
      remainder + w0 * q₀ + w00 * q₀ * q₀ + w01 * q₀ * q₁ +
      w012 * q₀ * q₁ * q₂ + w02 * q₀ * q₂ + w03 * q₀ * q₃ + w1 * q₁ +
      w11 * q₁ * q₁ + w12 * q₁ * q₂ + w13 * q₁ * q₃ + w2 * q₂ +
      w22 * q₂ * q₂ + w23 * q₂ * q₃ + w3 * q₃ := by
    unfold fourEightContactHigherFactor remainder w0 w00 w01 w012 w02 w03 w1 w11 w12 w13 w2 w22 w23 w3 q₀ q₁ q₂ q₃
    ring
  have hRemainder : 0 < remainder := by dsimp [remainder]; positivity
  have hw0 : 0 < w0 := by dsimp [w0]; positivity
  have hw00 : 0 < w00 := by dsimp [w00]; positivity
  have hw01 : 0 < w01 := by dsimp [w01]; positivity
  have hw012 : 0 < w012 := by dsimp [w012]; positivity
  have hw02 : 0 < w02 := by dsimp [w02]; positivity
  have hw03 : 0 < w03 := by dsimp [w03]; positivity
  have hw1 : 0 < w1 := by dsimp [w1]; positivity
  have hw11 : 0 < w11 := by dsimp [w11]; positivity
  have hw12 : 0 < w12 := by dsimp [w12]; positivity
  have hw13 : 0 < w13 := by dsimp [w13]; positivity
  have hw2 : 0 < w2 := by dsimp [w2]; positivity
  have hw22 : 0 < w22 := by dsimp [w22]; positivity
  have hw23 : 0 < w23 := by dsimp [w23]; positivity
  have hw3 : 0 < w3 := by dsimp [w3]; positivity
  have hPositive : 0 < fourEightContactHigherFactor a b c d e := by
    rw [hIdentity]
    positivity
  exact hPositive.ne' hFactor

end MOC
