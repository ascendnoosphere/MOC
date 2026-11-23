import MOC.FourSharedFiveData
import MOC.IntegerPivotFrame

/-! Ten pivot evaluations reconstruct every ray and every coefficient column.
The pivot rays generate the cone at the first ten inequalities. -/

open BigOperators MOC.IntegerRayCut

namespace MOC.FourSharedFive

set_option maxRecDepth 32000
set_option maxHeartbeats 100000000

private theorem poolIdentity : ∀ r i, 16 * poolRay r i =
    ∑ k, poolRay r (pivot k) * factor k * initialRay k i := by
  apply blocks
  intro b
  fin_cases b <;> decide +kernel

private theorem pointIdentity : ∀ k i, 16 * point i k =
    ∑ j, point (pivot j) k * factor j * initialRay j i := by decide +kernel

private theorem pivot_imposed : ∀ k, pivot k ∈ stage00.imposed := by decide +kernel
private theorem factor_nonneg : ∀ k, 0 ≤ factor k := by decide +kernel

private def frame : PivotFrame 10 51 where
  pivot := pivot
  ray := initialRay
  factor := factor
  scale := 16
  scale_pos := by decide
  factor_nonneg := factor_nonneg

noncomputable abbrev space := frame.space

theorem pool_mem (r : Fin 999) : realRow (poolRay r) ∈ space :=
  frame.mem_of_reconstruction _ (poolIdentity r)

theorem score_mem (w : Fin 10 → ℝ) : (fun i => ∑ k, w k * (point i k : ℝ)) ∈ space :=
  frame.score_mem point pointIdentity w

theorem initial_covered : Covered space stage00 :=
  frame.initial_covered stage00.imposed pivot_imposed

end MOC.FourSharedFive
