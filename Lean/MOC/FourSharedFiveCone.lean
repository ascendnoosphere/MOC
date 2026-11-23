import MOC.FourSharedFiveSpace
import MOC.FourSharedFiveCut01
import MOC.FourSharedFiveCut02
import MOC.FourSharedFiveCut03
import MOC.FourSharedFiveCut04
import MOC.FourSharedFiveCut05
import MOC.FourSharedFiveCut06
import MOC.FourSharedFiveCut07
import MOC.FourSharedFiveCut08
import MOC.FourSharedFiveCut09
import MOC.FourSharedFiveCut10
import MOC.FourSharedFiveCut11
import MOC.FourSharedFiveCut12
import MOC.FourSharedFiveCut13
import MOC.FourSharedFiveCut14
import MOC.FourSharedFiveCut15
import MOC.FourSharedFiveCut16
import MOC.FourSharedFiveCut17
import MOC.FourSharedFiveCut18
import MOC.FourSharedFiveCut19
import MOC.FourSharedFiveCut20
import MOC.FourSharedFiveCut21
import MOC.FourSharedFiveCut22
import MOC.FourSharedFiveCut23
import MOC.FourSharedFiveCut24
import MOC.FourSharedFiveCut25
import MOC.FourSharedFiveCut26
import MOC.FourSharedFiveCut27
import MOC.FourSharedFiveCut28
import MOC.FourSharedFiveCut29
import MOC.FourSharedFiveCut30
import MOC.FourSharedFiveCut31
import MOC.FourSharedFiveCut32
import MOC.FourSharedFiveCut33
import MOC.FourSharedFiveCut34
import MOC.FourSharedFiveCut35
import MOC.FourSharedFiveCut36
import MOC.FourSharedFiveCut37
import MOC.FourSharedFiveCut38
import MOC.FourSharedFiveCut39
import MOC.FourSharedFiveCut40
import MOC.FourSharedFiveCut41

/-! All nonnegative linear functions of the matching coefficients are
nonnegative sums of the 282 final rays. -/

open BigOperators MOC.IntegerRayCut

namespace MOC.FourSharedFive

private theorem final_covered : Covered space stage41 := by
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
  have h24 := Cut24.covered h23 pool_mem
  have h25 := Cut25.covered h24 pool_mem
  have h26 := Cut26.covered h25 pool_mem
  have h27 := Cut27.covered h26 pool_mem
  have h28 := Cut28.covered h27 pool_mem
  have h29 := Cut29.covered h28 pool_mem
  have h30 := Cut30.covered h29 pool_mem
  have h31 := Cut31.covered h30 pool_mem
  have h32 := Cut32.covered h31 pool_mem
  have h33 := Cut33.covered h32 pool_mem
  have h34 := Cut34.covered h33 pool_mem
  have h35 := Cut35.covered h34 pool_mem
  have h36 := Cut36.covered h35 pool_mem
  have h37 := Cut37.covered h36 pool_mem
  have h38 := Cut38.covered h37 pool_mem
  have h39 := Cut39.covered h38 pool_mem
  have h40 := Cut40.covered h39 pool_mem
  have h41 := Cut41.covered h40 pool_mem
  exact h41

/-- Expand a nonnegative vector in the ten-coordinate evaluation space. -/
theorem exists_ray_weights (w : Fin 10 → ℝ)
    (h : ∀ i : Fin 51, 0 ≤ ∑ k, w k * (point i k : ℝ)) :
    ∃ μ : Fin 282 → ℝ, (∀ r, 0 ≤ μ r) ∧ ∀ i,
      (∑ k, w k * (point i k : ℝ)) = ∑ r, μ r * (finalRay r i : ℝ) := by
  obtain ⟨μ,hμ,he⟩ := final_covered.weights _ (score_mem w) (fun i _ => h i)
  refine ⟨μ, hμ, fun i => ?_⟩
  have hi := congrFun he i
  simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, realRow] using hi

end MOC.FourSharedFive
