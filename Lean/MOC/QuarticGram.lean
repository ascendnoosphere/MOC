import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! Exact scalar certificates for the quartic left by the real Cayley support
reduction. The Gram parameter depends on the actual spectral input. -/

namespace MOC

/-- A positive principal corner of the Gram matrix leaves a single scalar
Schur complement. The proof gives the corresponding two squares explicitly. -/
theorem quartic_nonneg_of_gram_parameter {A B C D E u : ℝ}
    (hA : 0 < A) (hΔ : 0 < A * E - u ^ 2)
    (hC : E * B ^ 2 - 2 * u * B * D + A * D ^ 2 ≤
      4 * (A * E - u ^ 2) * (C - 2 * u)) (t : ℝ) :
    0 ≤ A + B * t + C * t ^ 2 + D * t ^ 3 + E * t ^ 4 := by
  let Δ := A * E - u ^ 2
  have hidentity :
      (4 * A * Δ) * (A + B * t + C * t ^ 2 + D * t ^ 3 + E * t ^ 4) =
        Δ * (2 * A + B * t + 2 * u * t ^ 2) ^ 2 +
        (2 * Δ * t ^ 2 + (A * D - B * u) * t) ^ 2 +
        A * (4 * Δ * (C - 2 * u) - (E * B ^ 2 - 2 * u * B * D + A * D ^ 2)) * t ^ 2 := by
    dsimp only [Δ]
    ring
  have hscaled : 0 ≤ (4 * A * Δ) * (A + B * t + C * t ^ 2 + D * t ^ 3 + E * t ^ 4) := by
    rw [hidentity]
    exact add_nonneg (add_nonneg (mul_nonneg hΔ.le (sq_nonneg _)) (sq_nonneg _))
      (mul_nonneg (mul_nonneg hA.le (sub_nonneg.mpr hC)) (sq_nonneg _))
  exact nonneg_of_mul_nonneg_right hscaled (mul_pos (mul_pos (by norm_num) hA) hΔ)

/-- In the rank-one corner case, the cubic coefficient has to agree with the
same square. This includes the rank-two Cayley slice with zero leading term. -/
theorem quartic_nonneg_of_singular_gram_corner {A B C D E u : ℝ}
    (hA : 0 < A) (hΔ : A * E = u ^ 2) (hD : A * D = B * u)
    (hC : B ^ 2 ≤ 4 * A * (C - 2 * u)) (t : ℝ) :
    0 ≤ A + B * t + C * t ^ 2 + D * t ^ 3 + E * t ^ 4 := by
  have hidentity :
      (4 * A) * (A + B * t + C * t ^ 2 + D * t ^ 3 + E * t ^ 4) =
        (2 * A + B * t + 2 * u * t ^ 2) ^ 2 + (4 * A * (C - 2 * u) - B ^ 2) * t ^ 2 := by
    linear_combination (4 * t ^ 4) * hΔ + (4 * t ^ 3) * hD
  have hscaled : 0 ≤ (4 * A) * (A + B * t + C * t ^ 2 + D * t ^ 3 + E * t ^ 4) := by
    rw [hidentity]
    exact add_nonneg (sq_nonneg _) (mul_nonneg (sub_nonneg.mpr hC) (sq_nonneg _))
  exact nonneg_of_mul_nonneg_right hscaled (mul_pos (by norm_num) hA)

/-- The first test survives even though the relaxed odd-part bound fails. -/
theorem cayley_odd_envelope_example_nonneg (t : ℝ) :
    0 ≤ 16 * (46 * t ^ 4 - 24 * t ^ 3 + 93 * t ^ 2 + 24 * t + 43) := by
  have h := quartic_nonneg_of_gram_parameter
    (A := 688) (B := 384) (C := 1488) (D := -384) (E := 736) (u := 0)
    (by norm_num) (by norm_num) (by norm_num) t
  convert h using 1 <;> ring

/-- The Gram certificate allows a strictly negative middle coefficient. -/
theorem cayley_negative_middle_example_nonneg (t : ℝ) :
    0 ≤ 608 + 96 * t - 1632 * t ^ 2 - 864 * t ^ 3 + 7344 * t ^ 4 := by
  have h := quartic_nonneg_of_gram_parameter
    (A := 608) (B := 96) (C := -1632) (D := -864) (E := 7344) (u := -1500)
    (by norm_num) (by norm_num) (by norm_num) t
  convert h using 1 <;> ring

/-- The quadratic form of the monomial-basis Gram matrix for the quartic. -/
def quarticGramForm (A B C D E u x y z : ℝ) : ℝ :=
  A * x ^ 2 + B * x * y + (C - 2 * u) * y ^ 2 +
    D * y * z + E * z ^ 2 + 2 * u * x * z

/-- A singular endpoint corner of a nonnegative Gram form forces the odd
coefficients to be compatible with its null direction. -/
theorem quarticGram_odd_eq_of_singular_corner {A B C D E u : ℝ}
    (hcorner : A * E = u ^ 2)
    (hform : ∀ x y z, 0 ≤ quarticGramForm A B C D E u x y z) :
    A * D = B * u := by
  have hquad (y : ℝ) : 0 ≤ (C - 2 * u) * (y * y) + (B * u - D * A) * y + 0 := by
    have heq : quarticGramForm A B C D E u u y (-A) =
        (C - 2 * u) * (y * y) + (B * u - D * A) * y + 0 := by
      unfold quarticGramForm
      linear_combination A * hcorner
    rw [← heq]
    exact hform u y (-A)
  have hdisc : (B * u - D * A) ^ 2 ≤ 0 := by
    simpa only [discrim, mul_zero, sub_zero] using discrim_le_zero hquad
  have hzero := sq_eq_zero_iff.mp (le_antisymm hdisc (sq_nonneg (B * u - D * A)))
  exact (mul_comm A D).trans (sub_eq_zero.mp hzero).symm

/-- The two tested Cayley quartics rule out every universal constant multiple
of the positive geometric mean of the endpoint coefficients. The first is
`12 * (1 - t^2)^2`, from two disjoint plane rotations with equal speed,
spectra `(-1+2i, 2, -2+i, -2)` and `(-2+i, -2-2i, -1-2i, -2-i)`,
and support direction `1`. The second is the negative-middle example above. -/
theorem no_fixed_cayley_gram_scale (κ s : ℝ) (hs : s ^ 2 = 608 * 7344)
    (hfirst : ∀ x y z, 0 ≤ quarticGramForm 12 0 (-24) 0 12 (κ * 12) x y z)
    (hsecond : ∀ x y z, 0 ≤ quarticGramForm 608 96 (-1632) (-864) 7344 (κ * s) x y z) :
    False := by
  have h₁ := hfirst 1 0 1
  have h₂ := hfirst 0 1 0
  norm_num [quarticGramForm] at h₁ h₂
  have hκ : κ = -1 := by linarith only [h₁, h₂]
  rw [hκ, neg_one_mul] at hsecond
  have hc : (608 : ℝ) * 7344 = (-s) ^ 2 := by rw [neg_sq, hs]
  have hcompat := quarticGram_odd_eq_of_singular_corner hc hsecond
  have hvalue : s = 5472 := by linarith only [hcompat]
  norm_num [hvalue] at hs

end MOC
