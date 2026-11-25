import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Affine root reductions for four of the order-four seven-contact families.

The input is a scalar equation for a determinant factor. The bilinear
resultant identities are explicit hypotheses. The ray lists use the indices
of `ordinaryCostRay` in `MOC.FourSupportConeClassification`.
-/

namespace MOC

private theorem sevenContact_affine_root {x a b : ℝ}
    (ha : a ≠ 0) (hroot : x * a + b = 0) :
    x = -b / a := by
  exact (eq_div_iff ha).2 (by linarith only [hroot])

private theorem sevenContact_bilinear_root {x y A B C D : ℝ}
    (hresultant : B * C - A * D ≠ 0)
    (hroot : x * (A * y + B) + (C * y + D) = 0) :
    A * y + B ≠ 0 ∧ x = -(C * y + D) / (A * y + B) := by
  have hslope : A * y + B ≠ 0 := by
    intro hzero
    have hintercept : C * y + D = 0 := by
      simpa only [hzero, mul_zero, zero_add] using hroot
    apply hresultant
    calc
      B * C - A * D = C * (A * y + B) - A * (C * y + D) := by ring
      _ = 0 := by rw [hzero, hintercept, mul_zero, mul_zero, sub_zero]
  exact ⟨hslope, sevenContact_affine_root hslope hroot⟩

/-- For the rays `(13,17,18,23,27,30)`, eliminate the coefficient `x`
of ray 27, using the coefficient `y` of ray 30. The coefficients `a,b,c,d`
are those of rays 13, 17, 18 and 23, in that order. -/
theorem fourSevenContactRay27Resultant_root
    {a b c d x y A B C D : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hresultant :
      B * C - A * D = (b + c * d) * (c + 1)^2 * (a + b + 1) * (a + d + 1)^2)
    (hroot : x * (A * y + B) + (C * y + D) = 0) :
    A * y + B ≠ 0 ∧ x = -(C * y + D) / (A * y + B) := by
  apply sevenContact_bilinear_root _ hroot
  rw [hresultant]
  exact ne_of_gt (by positivity)

/-- For the rays `(7,13,18,20,27,31)`, eliminate the coefficient `x`
of ray 20, using the coefficient `y` of ray 27. The coefficients `a,b,c,f`
are those of rays 7, 13, 18 and 31, in that order. -/
theorem fourSevenContactRay20Resultant_root
    {a b c f x y A B C D : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hf : 0 < f)
    (hresultant :
      B * C - A * D = f * (b + 1)^2 * (a + c + 1)^2 * (a * b + a + b + f + 1))
    (hroot : x * (A * y + B) + (C * y + D) = 0) :
    A * y + B ≠ 0 ∧ x = -(C * y + D) / (A * y + B) := by
  apply sevenContact_bilinear_root _ hroot
  rw [hresultant]
  exact ne_of_gt (by positivity)

/-- For the rays `(7,10,13,18,20,23)`, the factored slope in the
coefficient `x` of ray 13 is positive. The coefficients `a,b,d,e,f`
are those of the remaining rays, in the listed order. -/
theorem fourSevenContactRay13Slope_root
    {a b d e f x C : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hd : 0 < d) (he : 0 < e) (hf : 0 < f)
    (hroot : x * (((a + 1) * (b + 1) + e) * (a + f + 1) * (b + d + 1)) + C = 0) :
    0 < ((a + 1) * (b + 1) + e) * (a + f + 1) * (b + d + 1) ∧
      x = -C / (((a + 1) * (b + 1) + e) * (a + f + 1) * (b + d + 1)) := by
  have hslope : 0 < ((a + 1) * (b + 1) + e) * (a + f + 1) * (b + d + 1) := by
    positivity
  exact ⟨hslope, sevenContact_affine_root (ne_of_gt hslope) hroot⟩

/-- For the rays `(7,13,18,20,28,31)`, eliminate the coefficient `x`
of ray 20 when the product of the coefficients of rays 18 and 28 is
less than one. Here `y` is the coefficient of ray 31. The coefficients
`a,b,c,e` are those of rays 7, 13, 18 and 28, in that order. -/
theorem fourSevenContactRay20Resultant_root_or_pairBudget
    {a b c e x y A B C D : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (he : 0 < e)
    (hresultant : B * C - A * D =
      -(a * (c + 1) * (a + c + 1) * (b + e + 1) * ((a + 1) * (b + 1) - c * e)^2))
    (hroot : x * (A * y + B) + (C * y + D) = 0) :
    1 ≤ c * e ∨ (A * y + B ≠ 0 ∧ x = -(C * y + D) / (A * y + B)) := by
  by_cases hbudget : 1 ≤ c * e
  · exact Or.inl hbudget
  right
  have hpositive : 1 < (a + 1) * (b + 1) := by
    nlinarith only [ha, hb, mul_pos ha hb]
  have hdifference : 0 < (a + 1) * (b + 1) - c * e :=
    sub_pos.mpr ((lt_of_not_ge hbudget).trans hpositive)
  apply sevenContact_bilinear_root _ hroot
  rw [hresultant]
  exact ne_of_lt (neg_lt_zero.mpr (by positivity))

end MOC
