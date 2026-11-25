import MOC.FourInversePencilCertificates
import MOC.FourMatchingRelations

/-!
# Two order-four eight-contact profiles

The first result gives the sum of squares once the mixed determinant factor
vanishes. The second result restricts the height of the other profile.
-/

namespace MOC

noncomputable section

private def gramBudget (a b e : ℝ) : ℝ :=
  e * (a * b - 1) - (a + 1) * (b + 1)

private def budgetMultiplier (a b c d e : ℝ) : ℝ :=
  let z := (c + 1) * (d + 1)
  a * (b + z)^2 + e * z * (b + z) + (b + 1)^2 + c + d

private def positiveRemainder (a b c d e : ℝ) : ℝ :=
  (c + d) *
    (a * (b^3 * e + 2*b^2 + 3*b + 1) + b^2 * e^2 + 2*b^2 +
      b * (e^2 + 3*e + 3) + e * (b^3 + 2*b^2 + 1) + 1) +
  (c^2 + d^2) *
    (a * (b^2 * e + b + 1) + b^2 * e^2 + b * (e^2 + e + 1) +
      e * (b^2 + 1) + 1) +
  c*d *
    (a * (b^3 + 3*b^2*e + 3*b^2 + b*e + 6*b + 4) + b^3 + b^2*e^2 +
      3*b^2 + b * (5*e^2 + 7*e + 6) + e * (5*b^2 + 4) + 4) +
  (c + d)*c*d *
    (a * (b^2*e + b^2 + 2*b*e + 2*b + 2) + b^2 +
      b * (4*e^2 + 4*e + 2) + e * (b^2 + 2) + 2) +
  (c*d)^2 *
    (a * (b^2 + 2*b*e + b + 1) + b^2 + b * (3*e^2 + 3*e + 1) + e + 1)

/-- The constant-positive mixed factor for rays `(7, 13, 17, 27, 31)`,
written as a difference for the Gram certificate. -/
def fourEightContactSeventeenFactor (a b c d e : ℝ) : ℝ :=
  positiveRemainder a b c d e - budgetMultiplier a b c d e * gramBudget a b e

/-- Vanishing of the mixed factor forces enough weight for the matching
square on the mixed ray and ordinary rays `7`, `13`, and `31`. -/
theorem fourEightContactSeventeen_sos {a b c d e : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (he : 0 < e)
    (hfactor : fourEightContactSeventeenFactor a b c d e = 0) :
    IsRealMatchingSOS (fun p =>
      mixedCostRay 0 p + a * ordinaryCostRay 7 p + b * ordinaryCostRay 13 p +
        c * ordinaryCostRay 17 p + d * ordinaryCostRay 27 p + e * ordinaryCostRay 31 p) := by
  have hR : 0 < positiveRemainder a b c d e := by
    unfold positiveRemainder
    positivity
  have hQ : 0 < budgetMultiplier a b c d e := by
    unfold budgetMultiplier
    positivity
  have hprod : budgetMultiplier a b c d e * gramBudget a b e =
      positiveRemainder a b c d e := by
    change positiveRemainder a b c d e -
      budgetMultiplier a b c d e * gramBudget a b e = 0 at hfactor
    exact (sub_eq_zero.mp hfactor).symm
  have hP : 0 < gramBudget a b e := by
    by_contra! h
    have hle := mul_nonpos_of_nonneg_of_nonpos hQ.le h
    rw [hprod] at hle
    exact (not_le_of_gt hR) hle
  have hbudget : (a + 1) * (b + 1) < e * (a * b - 1) := sub_pos.mp hP
  have hpos : 0 < (a + 1) * (b + 1) := by positivity
  have hab : 1 < a * b := by
    by_contra! h
    exact (not_lt_of_ge (mul_nonpos_of_nonneg_of_nonpos he.le (sub_nonpos.mpr h)))
      (hpos.trans hbudget)
  have hs := fourMatchingSOS_of_gram_budget ha hab hbudget.le
  have hsd := fourMatchingSOS_add_ordinaryRay
    (fourMatchingSOS_add_ordinaryRay hs 17 hc.le) 27 hd.le
  convert hsd using 1
  funext p
  ring

/-- The mixed ray with compensation on ordinary rays
`(7, 13, 18, 23, 31)`. -/
def fourEightContactTwentyThreeGap (a b c d e : ℝ) (p : Fin 24) : ℝ :=
  mixedCostRay 0 p + a * ordinaryCostRay 7 p + b * ordinaryCostRay 13 p +
    c * ordinaryCostRay 18 p + d * ordinaryCostRay 23 p + e * ordinaryCostRay 31 p

private def twentyThreeCoordinates (a b c d e h : ℝ) : Fin 14 → ℝ :=
  ![d + e + 1, -d, a, 0, -e, -c - d, d - 1, -a - 1, -e, 1, c, -b - 1, b, h]

private theorem twentyThreeCoordinates_eval (a b c d e h : ℝ) (p : Fin 24) :
    fourMatchingEvaluation (twentyThreeCoordinates a b c d e h) p =
      fourEightContactTwentyThreeGap a b c d e p + h := by
  fin_cases p <;>
    norm_num [fourMatchingEvaluation, twentyThreeCoordinates, fourEightContactTwentyThreeGap, mixedCostRay,
      mixedCostRayInt, mixedCostSeedInt, ordinaryCostRay, ordinaryCostRayInt,
      fourCostRelabelIndex, fourCostPermutation, fourCostPair, fourPermIndex, fourPerm,
      Matrix.cons_val] <;> ring

/-- The negative radial height forces `d * c + e + 1 > d * e`
for the profile on rays `(7, 13, 18, 23, 31)`. -/
theorem fourEightContactTwentyThree_height_bound {a b c d e h : ℝ}
    (ha : 0 < a) (hb : 0 < b) (he : 0 < e) (hh : h < 0)
    (α β : Fin 4 → ℂ) (η : ℂ)
    (hvalues : ∀ p : Fin 24,
      (η * matchingProduct α β (fourPerm p).symm).re = fourEightContactTwentyThreeGap a b c d e p + h) :
    d * e < c * d + e + 1 := by
  have hcoords : twentyThreeCoordinates a b c d e h =
      fun j => (η * fourNoncrossingCoordinates (fourSpectralPoints α β) j).re := by
    apply fourMatchingEvaluation_injective
    funext p
    rw [twentyThreeCoordinates_eval, fourMatchingEvaluation_spectral_real_part, hvalues]
  have hzero := fourMatchingCubic_of_spectral_real_part α β η
  rw [← hcoords] at hzero
  have heq : fourMatchingCubic (twentyThreeCoordinates a b c d e h) =
      -((a + 1) * (b + 1) + e) + h * (d * e - c * d - e - 1) := by
    simp [fourMatchingCubic, twentyThreeCoordinates]
    ring
  rw [heq] at hzero
  by_contra! hn
  have hmul : h * (d * e - c * d - e - 1) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg hh.le (by linarith only [hn])
  have hpositive : 0 < (a + 1) * (b + 1) + e := by positivity
  linarith only [hzero, hmul, hpositive]

end
end MOC
