import MOC.CommonWeights
import Mathlib.Analysis.Convex.Topology
import Mathlib.Topology.PartitionOfUnity
import Mathlib.Topology.Order.DenselyOrdered

/-! Approximation of pointwise convex combinations by continuous weights. -/

open BigOperators Filter Set Topology

namespace MOC

noncomputable section

variable {X κ : Type*} [TopologicalSpace X] [Fintype κ]

/-- Continuous probability weights give an exact approximation of any prescribed
positive precision to a pointwise convex combination on a compact Hausdorff base. -/
theorem exists_continuous_weights_of_pointwise
    [CompactSpace X] [T2Space X] (v : κ → C(X, ℂ)) (z : C(X, ℂ))
    (h : ∀ x : X, ∃ w : κ → ℝ, (∀ j, 0 ≤ w j) ∧ (∑ j, w j = 1) ∧
      (∑ j, (w j : ℂ) * v j x) = z x)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ w : κ → C(X, ℝ), (∀ j x, 0 ≤ w j x) ∧ (∀ x, ∑ j, w j x = 1) ∧
      ∀ x, ‖(∑ j, (w j x : ℂ) * v j x) - z x‖ < ε := by
  classical
  choose a ha hsum heq using h
  let e (y x : X) : ℂ := (∑ j, (a y j : ℂ) * v j x) - z x
  let U (y : X) : Set X := {x | ‖e y x‖ < ε / 2}
  have he (y : X) : Continuous (e y) := by
    unfold e
    fun_prop
  have ho (y : X) : IsOpen (U y) := isOpen_lt (he y).norm continuous_const
  have hc : univ ⊆ ⋃ y, U y := by
    intro x _
    apply mem_iUnion.mpr
    refine ⟨x, ?_⟩
    change ‖e x x‖ < ε / 2
    simp only [e, heq, sub_self, norm_zero]
    linarith
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover U ho hc
  have hc' : univ ⊆ ⋃ y : s, U y := by
    intro x hx
    obtain ⟨y, hy⟩ := mem_iUnion.mp (hs hx)
    obtain ⟨hys, hxy⟩ := mem_iUnion.mp hy
    exact mem_iUnion.mpr ⟨⟨y, hys⟩, hxy⟩
  obtain ⟨ρ, hρ⟩ := PartitionOfUnity.exists_isSubordinate isClosed_univ
    (fun y : s => U y) (fun y => ho y) hc'
  let w (j : κ) : C(X, ℝ) :=
    ∑ y : s, ρ y * ContinuousMap.const X (a y j)
  have hw (j : κ) (x : X) : w j x = ∑ y : s, ρ y x * a y j := by
    simp [w]
  have hr (x : X) : ∑ y : s, ρ y x = 1 := by
    simpa only [finsum_eq_sum_of_fintype] using ρ.sum_eq_one (mem_univ x)
  refine ⟨w, ?_, ?_, ?_⟩
  · intro j x
    rw [hw]
    exact Finset.sum_nonneg fun y _ => mul_nonneg (ρ.nonneg y x) (ha y j)
  · intro x
    calc
      ∑ j, w j x = ∑ j, ∑ y : s, ρ y x * a y j := by simp only [hw]
      _ = ∑ y : s, ∑ j, ρ y x * a y j := Finset.sum_comm
      _ = 1 := by simp only [← Finset.mul_sum, hsum, mul_one, hr]
  · intro x
    have hd : (∑ j, (w j x : ℂ) * v j x) - z x =
        ∑ y : s, (ρ y x : ℂ) * e y x := by
      have hz : (∑ y : s, (ρ y x : ℂ) * z x) = z x := by
        rw [← Finset.sum_mul, ← Complex.ofReal_sum, hr, Complex.ofReal_one, one_mul]
      calc
        (∑ j, (w j x : ℂ) * v j x) - z x =
            (∑ j, ∑ y : s, (ρ y x : ℂ) * ((a y j : ℂ) * v j x)) - z x := by
          simp only [hw, Complex.ofReal_sum, Complex.ofReal_mul, Finset.sum_mul, mul_assoc]
        _ = _ := by
          rw [Finset.sum_comm]
          simp only [e, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum, hz]
    have ht (y : s) : ‖(ρ y x : ℂ) * e y x‖ ≤ ρ y x * (ε / 2) := by
      by_cases hy : ρ y x = 0
      · simp [hy]
      have hx : x ∈ U y :=
        hρ y (subset_closure (show x ∈ Function.support (ρ y) from hy))
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (ρ.nonneg y x)]
      exact mul_le_mul_of_nonneg_left (le_of_lt hx) (ρ.nonneg y x)
    calc
      ‖(∑ j, (w j x : ℂ) * v j x) - z x‖
          ≤ ∑ y : s, ‖(ρ y x : ℂ) * e y x‖ := by
        rw [hd]
        exact norm_sum_le _ _
      _ ≤ ∑ y : s, ρ y x * (ε / 2) := Finset.sum_le_sum fun y _ => ht y
      _ = ε / 2 := by rw [← Finset.sum_mul, hr, one_mul]
      _ < ε := by linarith

/-- Arbitrarily accurate continuous convex combinations imply pointwise
membership in the finite convex hull. -/
theorem pointwise_mem_convexHull_of_continuous_approximation
    (v : κ → C(X, ℂ)) (z : C(X, ℂ))
    (h : ∀ ε : ℝ, 0 < ε → ∃ w : κ → C(X, ℝ), (∀ j x, 0 ≤ w j x) ∧
      (∀ x, ∑ j, w j x = 1) ∧ ∀ x, ‖(∑ j, (w j x : ℂ) * v j x) - z x‖ < ε)
    (x : X) : z x ∈ convexHull ℝ (range fun j => v j x) := by
  let K := convexHull ℝ (range fun j => v j x)
  have hK : IsClosed K := (Set.finite_range _).isCompact_convexHull.isClosed
  change z x ∈ K
  rw [← hK.closure_eq, Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨w, hw, hs, he⟩ := h ε hε
  refine ⟨∑ j, (w j x : ℂ) * v j x, ?_, ?_⟩
  · simpa only [Complex.real_smul] using
      (convex_convexHull ℝ (range fun j => v j x)).sum_mem
        (fun j _ => hw j x) (hs x)
        (fun j _ => subset_convexHull ℝ _ (mem_range_self j))
  · simpa only [dist_eq_norm, dist_comm] using he x

/-- One-sided agreement of a continuous function with a constant forces
agreement at the common endpoint. -/
theorem continuous_zero_eq_of_positive {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    {f : ℝ → Y} {y : Y} (hc : ContinuousAt f 0)
    (h : ∀ t : ℝ, 0 < t → f t = y) : f 0 = y := by
  have hE : f =ᶠ[𝓝[>] (0 : ℝ)] fun _ => y := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact h t ht
  exact tendsto_nhds_unique_of_eventuallyEq hc.continuousWithinAt tendsto_const_nhds hE

theorem continuous_zero_eq_of_open_half {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    {f : ℝ → Y} {y : Y} (hc : ContinuousWithinAt f (Icc (-1) 1) 0) (s : Bool)
    (h : ∀ t : ℝ, t ∈ (if s then Ioo 0 1 else Ioo (-1) 0) → f t = y) :
    f 0 = y := by
  cases s
  · have hE : f =ᶠ[𝓝[<] (0 : ℝ)] fun _ => y := by
      filter_upwards [Ioo_mem_nhdsLT (show (-1 : ℝ) < 0 by norm_num)] with t ht
      exact h t ht
    have hN : Icc (-1 : ℝ) 1 ∈ 𝓝[<] (0 : ℝ) :=
      mem_of_superset (Ioo_mem_nhdsLT (show (-1 : ℝ) < 0 by norm_num)) (fun t ht =>
        ⟨ht.1.le, ht.2.le.trans (by norm_num)⟩)
    exact tendsto_nhds_unique_of_eventuallyEq (hc.mono_left (nhdsWithin_le_of_mem hN))
      tendsto_const_nhds hE
  · have hE : f =ᶠ[𝓝[>] (0 : ℝ)] fun _ => y := by
      filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with t ht
      exact h t ht
    have hN : Icc (-1 : ℝ) 1 ∈ 𝓝[>] (0 : ℝ) :=
      mem_of_superset (Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)) (fun t ht =>
        ⟨(by norm_num : (-1 : ℝ) ≤ 0).trans ht.1.le, ht.2.le⟩)
    exact tendsto_nhds_unique_of_eventuallyEq (hc.mono_left (nhdsWithin_le_of_mem hN))
      tendsto_const_nhds hE

end

end MOC
