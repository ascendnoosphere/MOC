import MOC.FourSharedFiveData

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

noncomputable section

def space : Submodule ℝ (Fin 51 → ℝ) where
  carrier := {v | ∀ i, 16 * v i = ∑ k, v (pivot k) * (factor k : ℝ) * (initialRay k i : ℝ)}
  zero_mem' := by simp
  add_mem' := by
    intro v w hv hw i
    change 16 * (v i + w i) = ∑ k, (v (pivot k) + w (pivot k)) * _ * _
    simp only [add_mul, mul_add, Finset.sum_add_distrib, hv i, hw i]
  smul_mem' := by
    intro c v hv i
    change 16 * (c * v i) = ∑ k, (c * v (pivot k)) * _ * _
    calc
      16 * (c * v i) = c * (16 * v i) := by ring
      _ = c * ∑ k, v (pivot k) * (factor k : ℝ) * (initialRay k i : ℝ) := by rw [hv i]
      _ = _ := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => by ring

theorem pool_mem (r : Fin 999) : realRow (poolRay r) ∈ space := by
  intro i
  change (16 : ℝ) * (poolRay r i : ℝ) = ∑ k, (poolRay r (pivot k) : ℝ) * _ * _
  exact_mod_cast poolIdentity r i

private theorem point_mem (k : Fin 10) : (fun i => (point i k : ℝ)) ∈ space := by
  intro i
  change (16 : ℝ) * (point i k : ℝ) = ∑ j, (point (pivot j) k : ℝ) * _ * _
  exact_mod_cast pointIdentity k i

theorem score_mem (w : Fin 10 → ℝ) : (fun i => ∑ k, w k * (point i k : ℝ)) ∈ space := by
  have he : (fun i => ∑ k, w k * (point i k : ℝ)) = ∑ k, w k • (fun i => (point i k : ℝ)) := by
    funext i
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [he]
  exact space.sum_mem fun k _ => space.smul_mem _ (point_mem k)

theorem initial_covered : Covered space stage00 := by
  constructor
  · intro v hv hz
    have h (k : Fin 10) : v (pivot k) = 0 := hz _ (pivot_imposed k)
    funext i
    change v i = 0
    have hh := hv i
    simp only [h, zero_mul, Finset.sum_const_zero] at hh
    linarith
  · intro v hv hn
    let w (k : Fin 10) := v (pivot k) * (factor k : ℝ) / 16
    refine ⟨w, fun k => div_nonneg (mul_nonneg (hn _ (pivot_imposed k))
      (by exact_mod_cast factor_nonneg k)) (by norm_num), ?_⟩
    funext i
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, realRow, w]
    change v i = ∑ k, v (pivot k) * (factor k : ℝ) / 16 * (initialRay k i : ℝ)
    simp_rw [div_mul_eq_mul_div, ← Finset.sum_div]
    apply (eq_div_iff (by norm_num : (16 : ℝ) ≠ 0)).mpr
    rw [mul_comm (v i) 16]
    exact hv i

end
end MOC.FourSharedFive
