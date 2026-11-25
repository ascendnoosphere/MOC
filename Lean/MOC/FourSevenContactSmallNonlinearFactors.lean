import MOC.FourMatchingRelations
import MOC.FourSupportCostProfiles
import Mathlib.Tactic.Positivity

/-! The common support height is a rational function of the six ordinary
coefficients in the specified seven-contact families. -/

open BigOperators

namespace MOC

/-- The ordinary ray labels in each of the six families. All labels start
at zero. The coefficient of the mixed ray is one. -/
def sevenContactSmallNonlinearRays : Fin 6 → Fin 6 → Fin 34 :=
  ![![13, 17, 18, 23, 27, 28],
    ![13, 17, 18, 23, 27, 31],
    ![7, 13, 17, 18, 27, 28],
    ![7, 13, 17, 23, 27, 31],
    ![7, 18, 20, 23, 28, 30],
    ![13, 17, 18, 27, 28, 30]]

/-- The normalized gap on a permutation. -/
def sevenContactSmallNonlinearGap (k : Fin 6) (x : Fin 6 → ℝ) (p : Fin 24) : ℝ :=
  (mixedCostSeedInt p : ℝ) +
    ∑ j, x j * ordinaryCostRay (sevenContactSmallNonlinearRays k j) p

/-- The constant term of the matching cubic in the height coordinate. -/
def sevenContactSmallNonlinearNumerator (k : Fin 6) (x : Fin 6 → ℝ) : ℝ :=
  let a := x 0
  let b := x 1
  let c := x 2
  let d := x 3
  let e := x 4
  let f := x 5
  ![a + b*e + b + c*d*f + e + 1,
    a + (b+1)*(e+1)*(f+1),
    (a+1)*(b + c*e + c + e + 1),
    (a+1)*(b + (c+1)*(e+1)) + (c+1)*(e+1)*f,
    (a+c+1)*(f+1) + b*d*e,
    (a+b+d+1)*(f+1) + b*d] k

/-- The negative of the height coefficient of the matching cubic. -/
def sevenContactSmallNonlinearDenominator (k : Fin 6) (x : Fin 6 → ℝ) : ℝ :=
  let a := x 0
  let b := x 1
  let c := x 2
  let d := x 3
  let e := x 4
  let f := x 5
  ![b*e - b*f + b + c*d - c*e + c*f + d*f + e + 1,
    b*e + b*f + b + c*d - c*e - d*f + e*f + e + f + 1,
    c*e - c*f + c - d*e + d*f + e + 1,
    c*e + c*f + c - d*f + e*f + e + f + 1,
    b*d + b*e - c*e + c*f + c + d*e - d*f + f + 1,
    b*d - b*e + b*f + b - c*d + c*e + d*f + d + f + 1] k

set_option maxHeartbeats 8000000 in
theorem sevenContactSmallNonlinear_cubic (k : Fin 6) (x : Fin 6 → ℝ) (H : ℝ) :
    fourMatchingCubic (fourMatchingCoordinatesOfValues
      (fun p => H - sevenContactSmallNonlinearGap k x p)) =
    sevenContactSmallNonlinearNumerator k x - H * sevenContactSmallNonlinearDenominator k x := by
  fin_cases k <;>
    norm_num [fourMatchingCubic, fourMatchingCoordinatesOfValues, sevenContactSmallNonlinearGap,
      sevenContactSmallNonlinearRays, sevenContactSmallNonlinearNumerator,
      sevenContactSmallNonlinearDenominator, mixedCostSeedInt, ordinaryCostRay, ordinaryCostRayInt,
      fourCostPermutation, fourCostPair, fourPerm, Equiv.Perm.mul_apply, Equiv.swap_apply_def,
      Matrix.cons_val, Fin.sum_univ_succ] <;>
    ring

theorem sevenContactSmallNonlinear_numerator_pos (k : Fin 6) (x : Fin 6 → ℝ)
    (hx : ∀ j, 0 ≤ x j) :
    0 < sevenContactSmallNonlinearNumerator k x := by
  have h0 := hx 0
  have h1 := hx 1
  have h2 := hx 2
  have h3 := hx 3
  have h4 := hx 4
  have h5 := hx 5
  fin_cases k <;>
    simp [sevenContactSmallNonlinearNumerator, Matrix.cons_val] <;>
    positivity

/-- For actual projected spectral products, the height and denominator
are nonzero. A positive height requires a positive denominator. -/
theorem sevenContactSmallNonlinear_height_of_spectral_gap
    (k : Fin 6) (x : Fin 6 → ℝ) (H : ℝ) (hx : ∀ j, 0 ≤ x j)
    (a b : Fin 4 → ℂ) (η : ℂ)
    (hgap : ∀ p : Fin 24, H - sevenContactSmallNonlinearGap k x p =
      (η * matchingProduct a b (fourPerm p).symm).re) :
    H ≠ 0 ∧ sevenContactSmallNonlinearDenominator k x ≠ 0 ∧
      H = sevenContactSmallNonlinearNumerator k x / sevenContactSmallNonlinearDenominator k x ∧
      (0 < H → 0 < sevenContactSmallNonlinearDenominator k x) := by
  let m := fun j => (η * fourNoncrossingCoordinates (fourSpectralPoints a b) j).re
  have hvals : (fun p => H - sevenContactSmallNonlinearGap k x p) = fourMatchingEvaluation m := by
    funext p
    exact (hgap p).trans (fourMatchingEvaluation_spectral_real_part a b η p).symm
  have hm : fourMatchingCubic m = 0 :=
    fourMatchingCubic_of_spectral_real_part a b η
  have hc := sevenContactSmallNonlinear_cubic k x H
  rw [hvals, fourMatchingEvaluation_leftInverse m, hm] at hc
  have hp := sevenContactSmallNonlinear_numerator_pos k x hx
  have hprod : H * sevenContactSmallNonlinearDenominator k x =
      sevenContactSmallNonlinearNumerator k x := by linarith only [hc]
  have hne : H * sevenContactSmallNonlinearDenominator k x ≠ 0 :=
    fun hz => hp.ne' (hprod.symm.trans hz)
  have hd := (mul_ne_zero_iff.mp hne).2
  refine ⟨(mul_ne_zero_iff.mp hne).1, hd, (eq_div_iff hd).2 hprod, ?_⟩
  intro hh
  exact pos_of_mul_pos_right (hprod.symm ▸ hp) hh.le

end MOC
