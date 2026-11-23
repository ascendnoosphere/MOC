import MOC.ThreeSharedRepeatedFiveSpace
import MOC.ThreeSharedRepeatedFiveCut01
import MOC.ThreeSharedRepeatedFiveCut02
import MOC.ThreeSharedRepeatedFiveCut03
import MOC.ThreeSharedRepeatedFiveCut04
import MOC.ThreeSharedRepeatedFiveCut05
import MOC.ThreeSharedRepeatedFiveCut06
import MOC.ThreeSharedRepeatedFiveCut07
import MOC.ThreeSharedRepeatedFiveCut08
import MOC.ThreeSharedRepeatedFiveCut09
import MOC.ThreeSharedRepeatedFiveCut10
import MOC.ThreeSharedRepeatedFiveCut11
import MOC.ThreeSharedRepeatedFiveCut12
import MOC.ThreeSharedRepeatedFiveCut13
import MOC.ThreeSharedRepeatedFiveCut14
import MOC.ThreeSharedRepeatedFiveCut15
import MOC.ThreeSharedRepeatedFiveCut16
import MOC.ThreeSharedRepeatedFiveCut17
import MOC.ThreeSharedRepeatedFiveCut18
import MOC.ThreeSharedRepeatedFiveCut19
import MOC.ThreeSharedRepeatedFiveCut20
import MOC.ThreeSharedRepeatedFiveCut21
import MOC.ThreeSharedRepeatedFiveCut22
import MOC.ThreeSharedRepeatedFiveCut23

/-! All nonnegative linear functions of the matching coefficients are
nonnegative sums of the 63 final rays. -/

open BigOperators MOC.IntegerRayCut

namespace MOC.ThreeSharedRepeatedFive

private theorem final_covered : Covered space stage23 := by
  have h01 := Cut01.covered initial_covered pool_mem
  have h02 := Cut02.covered h01 pool_mem
  have h03 := Cut03.covered h02 pool_mem
  have h04 := Cut04.covered h03 pool_mem
  have h05 := Cut05.covered h04 pool_mem
  have h06 := Cut06.covered h05 pool_mem
  have h07 := Cut07.covered h06 pool_mem
  have h08 := Cut08.covered h07 pool_mem
  have h09 := Cut09.covered h08 pool_mem
  have h10 := Cut10.covered h09 pool_mem
  have h11 := Cut11.covered h10 pool_mem
  have h12 := Cut12.covered h11 pool_mem
  have h13 := Cut13.covered h12 pool_mem
  have h14 := Cut14.covered h13 pool_mem
  have h15 := Cut15.covered h14 pool_mem
  have h16 := Cut16.covered h15 pool_mem
  have h17 := Cut17.covered h16 pool_mem
  have h18 := Cut18.covered h17 pool_mem
  have h19 := Cut19.covered h18 pool_mem
  have h20 := Cut20.covered h19 pool_mem
  have h21 := Cut21.covered h20 pool_mem
  have h22 := Cut22.covered h21 pool_mem
  have h23 := Cut23.covered h22 pool_mem
  exact h23

/-- Expand a nonnegative vector in the ten-coordinate evaluation space. -/
theorem exists_ray_weights (w : Fin 10 → ℝ)
    (h : ∀ i : Fin 33, 0 ≤ ∑ k, w k * (point i k : ℝ)) :
    ∃ μ : Fin 63 → ℝ, (∀ r, 0 ≤ μ r) ∧ ∀ i,
      (∑ k, w k * (point i k : ℝ)) = ∑ r, μ r * (finalRay r i : ℝ) := by
  obtain ⟨μ,hμ,he⟩ := final_covered.weights _ (score_mem w) (fun i _ => h i)
  refine ⟨μ, hμ, fun i => ?_⟩
  have hi := congrFun he i
  simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, realRow] using hi

end MOC.ThreeSharedRepeatedFive
