import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Scalar certificates for two rectangle-free zero-height contact types
in the order-four census. The case numbers refer to the zero-based
representatives in `data/certificates/geometry/zero_height_faces.json`. -/

namespace MOC

/-- In type 37 the sole positive monomial completes a negative square.
The two negative pure cubes then force both mixed coefficients to vanish. -/
theorem zero_height_type37_mixed_zero {a α β : ℝ}
    (ha : 0 ≤ a) (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hcubic : 0 ≤ 2 * a * α * β - a * α ^ 2 - a * β ^ 2 - α ^ 3 - β ^ 3) :
    α = 0 ∧ β = 0 := by
  have hsq := mul_nonneg ha (sq_nonneg (α - β))
  have ha3 := pow_nonneg hα 3
  have hb3 := pow_nonneg hβ 3
  constructor
  · by_contra hn
    have hpos := pow_pos (lt_of_le_of_ne hα (Ne.symm hn)) 3
    linarith only [hcubic, hsq, hb3, hpos]
  · by_contra hn
    have hpos := pow_pos (lt_of_le_of_ne hβ (Ne.symm hn)) 3
    linarith only [hcubic, hsq, ha3, hpos]

/-- In type 44 the cubic upper bound forces a sufficient donor budget for
both mixed coefficients whenever their sum is positive. -/
theorem zero_height_type44_donor_budget {c p q α β : ℝ}
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hmixed : 0 < α + β)
    (hcubic : 0 ≤ c * p * q - p * q * (α + β) - (p + q) * (α + β) ^ 2 -
      (α ^ 3 + α ^ 2 * β + α * β ^ 2 + β ^ 3)) :
    0 < p ∧ 0 < q ∧ α + β + (α + β) ^ 2 / p ≤ c := by
  have hαβ : 0 < α ^ 2 + β ^ 2 := by
    rcases lt_or_eq_of_le hα with h | h
    · exact add_pos_of_pos_of_nonneg (sq_pos_of_pos h) (sq_nonneg β)
    · have hβ' : 0 < β := by linarith only [hmixed, h]
      exact add_pos_of_nonneg_of_pos (sq_nonneg α) (sq_pos_of_pos hβ')
  have hcube : 0 < α ^ 3 + α ^ 2 * β + α * β ^ 2 + β ^ 3 := by
    calc
      _ < (α + β) * (α ^ 2 + β ^ 2) := mul_pos hmixed hαβ
      _ = _ := by ring
  have hp' : 0 < p := by
    rcases lt_or_eq_of_le hp with h | h
    · exact h
    · rw [← h] at hcubic
      nlinarith only [hcubic, hcube, mul_nonneg hq (sq_nonneg (α + β))]
  have hq' : 0 < q := by
    rcases lt_or_eq_of_le hq with h | h
    · exact h
    · rw [← h] at hcubic
      nlinarith only [hcubic, hcube, mul_nonneg hp (sq_nonneg (α + β))]
  refine ⟨hp', hq', (mul_le_mul_left (mul_pos hp' hq')).mp ?_⟩
  have hcancel : p * q * ((α + β) ^ 2 / p) = q * (α + β) ^ 2 := by
    field_simp <;> ring
  nlinarith only [hcubic, hcube, mul_nonneg hp (sq_nonneg (α + β)), hcancel]

/-- A shared pair of squared minors compensates two mixed rays if each
satisfies the weighted-minor bound with that pair. -/
theorem two_mixed_rays_nonneg_of_donor_budget
    {c p α β Q₀ Q₁ f₁ f₂ : ℝ}
    (hp : 0 < p) (hα : 0 ≤ α) (hβ : 0 ≤ β) (hQ₀ : 0 ≤ Q₀) (hQ₁ : 0 ≤ Q₁)
    (hbudget : α + β + (α + β) ^ 2 / p ≤ c)
    (hf₁ : 0 ≤ f₁ + Q₁ + 2 * √(Q₀ * Q₁))
    (hf₂ : 0 ≤ f₂ + Q₁ + 2 * √(Q₀ * Q₁)) :
    0 ≤ α * f₁ + β * f₂ + p * Q₀ + c * Q₁ := by
  let L := α + β
  have hL : 0 ≤ L := add_nonneg hα hβ
  have hA : 0 ≤ p * Q₀ := mul_nonneg hp.le hQ₀
  have hB : 0 ≤ L ^ 2 / p * Q₁ := mul_nonneg (div_nonneg (sq_nonneg L) hp.le) hQ₁
  have hroot : √(p * Q₀) * √(L ^ 2 / p * Q₁) = L * √(Q₀ * Q₁) := by
    rw [← Real.sqrt_mul hA]
    have hprod : (p * Q₀) * (L ^ 2 / p * Q₁) = L ^ 2 * (Q₀ * Q₁) := by
      field_simp <;> ring
    rw [hprod, Real.sqrt_mul (sq_nonneg L), Real.sqrt_sq hL]
  have hsq := sq_nonneg (√(p * Q₀) - √(L ^ 2 / p * Q₁))
  rw [sub_sq, Real.sq_sqrt hA, Real.sq_sqrt hB, mul_assoc (2 : ℝ), hroot] at hsq
  have hcomp := add_nonneg (mul_nonneg hα hf₁) (mul_nonneg hβ hf₂)
  have hbudget' : L + L ^ 2 / p ≤ c := hbudget
  change 0 ≤ α * f₁ + β * f₂ + p * Q₀ + c * Q₁
  nlinarith only [hsq, hcomp, mul_le_mul_of_nonneg_right hbudget' hQ₁]

end MOC
