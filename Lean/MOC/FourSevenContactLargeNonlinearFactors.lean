import MOC.FourMatchingRelations
import MOC.FourSupportCostProfiles
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! Signed support height for six order-four contact families.
Each row of `sevenContactNonlinearRays` lists the six ordinary rays in
coefficient order. The mixed seed has coefficient one. -/

namespace MOC

noncomputable section

/-- Ordinary ray indices in the six seven-contact families. -/
def sevenContactNonlinearRays (family : Fin 6) : Fin 6 → Fin 34 :=
  ![![7, 10, 13, 18, 23, 27], ![13, 17, 18, 27, 30, 31], ![7, 13, 17, 20, 23, 31],
    ![7, 13, 18, 20, 23, 28], ![7, 13, 17, 27, 30, 31], ![7, 13, 17, 18, 27, 31]] family

/-- The gap at each lexicographically indexed permutation. -/
def sevenContactNonlinearGap (family : Fin 6) (a b c d e f : ℝ) (p : Fin 24) : ℝ :=
  let r (i : Fin 6) := ordinaryCostRay (sevenContactNonlinearRays family i) p
  (mixedCostSeedInt p : ℝ) + a * r 0 + b * r 1 + c * r 2 + d * r 3 + e * r 4 + f * r 5

/-- Constant coefficient in the matching cubic as a polynomial in height. -/
def sevenContactNonlinearHeightNumerator (family : Fin 6) (a b c d e f : ℝ) : ℝ :=
  ![(a + 1) * ((b + 1) * (c + 1) + f),
    a * (e + 1) + (f + 1) * (b * d + b * e + b + d * e + d + e + 1),
    (a + d + 1) * (b + c + 1) + f * (c + 1) * (d + 1),
    (a + d + 1) * (b + 1) + c * e * f,
    (a + f + 1) * (c + d + e + c * d + c * e + d * e + 1) + (a + 1) * b * (e + 1),
    (a + 1) * b + (a + f + 1) * (c + 1) * (e + 1)] family

/-- Negative of the linear coefficient of height in the matching cubic. -/
def sevenContactNonlinearHeightDenominator (family : Fin 6) (b c d e f : ℝ) : ℝ :=
  ![f + 1 + d * (e - f),
    b * d + (b + d + 1) * (f + e + 1) - c * d,
    (c + d + 1) * (f + 1) - e * f,
    1 + d + c * e + f * (c + e - d),
    (f + 1) * (c + d + 1) + e + c * d + c * e + d * e,
    (f + 1) * (c + e + 1) + c * e - d * e] family

set_option maxHeartbeats 8000000 in
/-- The normalized real profiles give an affine polynomial in height. -/
theorem sevenContactNonlinear_height_cubic (family : Fin 6) (a b c d e f h : ℝ) :
    fourMatchingCubic (fourMatchingCoordinatesOfValues
      (fun p => h - sevenContactNonlinearGap family a b c d e f p)) =
      sevenContactNonlinearHeightNumerator family a b c d e f -
        h * sevenContactNonlinearHeightDenominator family b c d e f := by
  fin_cases family <;>
    norm_num [fourMatchingCubic, fourMatchingCoordinatesOfValues, sevenContactNonlinearGap,
      sevenContactNonlinearRays, sevenContactNonlinearHeightNumerator,
      sevenContactNonlinearHeightDenominator, mixedCostSeedInt, ordinaryCostRay,
      ordinaryCostRayInt, fourCostPermutation, fourCostPair, fourPerm, Equiv.Perm.mul_apply,
      Equiv.Perm.one_apply, Equiv.swap_apply_def, Matrix.cons_val] <;> ring

theorem sevenContactNonlinear_heightNumerator_pos (family : Fin 6) {a b c d e f : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) (hf : 0 ≤ f) :
    0 < sevenContactNonlinearHeightNumerator family a b c d e f := by
  fin_cases family <;>
    norm_num [sevenContactNonlinearHeightNumerator, Matrix.cons_val] <;> positivity

/-- For nonnegative ordinary coefficients, actual spectral matching values
determine a nonzero height. At positive height the denominator is positive. -/
theorem sevenContactNonlinear_height_of_spectral
    (family : Fin 6) (α β : Fin 4 → ℂ) (η : ℂ) {a b c d e f h : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) (hf : 0 ≤ f)
    (hmatch : ∀ p : Fin 24,
      (η * matchingProduct α β (fourPerm p).symm).re =
        h - sevenContactNonlinearGap family a b c d e f p) :
    sevenContactNonlinearHeightDenominator family b c d e f ≠ 0 ∧
      h ≠ 0 ∧
      h = sevenContactNonlinearHeightNumerator family a b c d e f /
        sevenContactNonlinearHeightDenominator family b c d e f ∧
      (0 < h ↔ 0 < sevenContactNonlinearHeightDenominator family b c d e f) := by
  let x : Fin 14 → ℝ := fun j => (η * fourNoncrossingCoordinates (fourSpectralPoints α β) j).re
  have hvalues : fourMatchingEvaluation x =
      fun p => h - sevenContactNonlinearGap family a b c d e f p := by
    funext p
    rw [show fourMatchingEvaluation x p =
      (η * matchingProduct α β (fourPerm p).symm).re from
      fourMatchingEvaluation_spectral_real_part α β η p, hmatch]
  have hx : fourMatchingCoordinatesOfValues
      (fun p => h - sevenContactNonlinearGap family a b c d e f p) = x := by
    rw [← hvalues]
    exact fourMatchingEvaluation_leftInverse x
  have hcubic : fourMatchingCubic x = 0 := fourMatchingCubic_of_spectral_real_part α β η
  rw [← hx, sevenContactNonlinear_height_cubic] at hcubic
  have hprod : h * sevenContactNonlinearHeightDenominator family b c d e f =
      sevenContactNonlinearHeightNumerator family a b c d e f := by
    linarith only [hcubic]
  have hprod_pos : 0 < h * sevenContactNonlinearHeightDenominator family b c d e f := by
    rw [hprod]
    exact sevenContactNonlinear_heightNumerator_pos family ha hb hc hd he hf
  have hden : sevenContactNonlinearHeightDenominator family b c d e f ≠ 0 :=
    (mul_ne_zero_iff.mp hprod_pos.ne').2
  refine ⟨hden, (mul_ne_zero_iff.mp hprod_pos.ne').1, (eq_div_iff hden).2 hprod, ?_⟩
  constructor
  · intro hh
    exact pos_of_mul_pos_right hprod_pos hh.le
  · intro hd'
    exact pos_of_mul_pos_left hprod_pos hd'.le

end

end MOC
