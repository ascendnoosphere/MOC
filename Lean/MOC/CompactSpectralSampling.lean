import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.NormedSpace.Real
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.EMetricSpace.Paracompact
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.Topology.PartitionOfUnity

/-! Finite positive sampling on compact metric spaces. -/

open BigOperators

namespace MOC

noncomputable section

/-- Real sampling weights as complex continuous functions. -/
def sampleWeightComplex {X : Type*} [TopologicalSpace X] (p : C(X, ℝ)) : C(X, ℂ) :=
  ⟨fun y => (p y : ℂ), Complex.continuous_ofReal.comp p.continuous⟩

@[simp] theorem sampleWeightComplex_apply {X : Type*} [TopologicalSpace X]
    (p : C(X, ℝ)) (y : X) : sampleWeightComplex p y = (p y : ℂ) := rfl

/-- The error of a positive weighted sample is at most a common bound
on the errors at its nonzero weights. -/
theorem compact_sample_sum_error_le {E ι : Type*} [SeminormedAddCommGroup E]
    [NormedSpace ℝ E] [Fintype ι] (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hws : ∑ i, w i = 1) (v : E) (samples : ι → E) (δ : ℝ)
    (hclose : ∀ i, w i ≠ 0 → ‖v - samples i‖ ≤ δ) :
    ‖v - ∑ i, w i • samples i‖ ≤ δ := by
  have he : (∑ i, w i • (v - samples i)) = v - ∑ i, w i • samples i := by
    simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, hws, one_smul]
  rw [← he]
  calc
    _ ≤ ∑ i, ‖w i • (v - samples i)‖ := norm_sum_le _ _
    _ ≤ ∑ i, w i * δ := by
      apply Finset.sum_le_sum
      intro i _
      by_cases h : w i = 0
      · simp only [h, zero_smul, norm_zero, zero_mul, le_refl]
      · rw [norm_smul_of_nonneg (hw i)]
        exact mul_le_mul_of_nonneg_left (hclose i h) (hw i)
    _ = δ := by rw [← Finset.sum_mul, hws, one_mul]

/-- The pointwise sampling bound applies to any function whose
values satisfy the error bound on the active samples. -/
theorem compact_sample_function_error_le {X E : Type*} [TopologicalSpace X]
    [SeminormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}
    (x : Fin n → X) (p : Fin n → C(X, ℝ)) (hnon : ∀ i y, 0 ≤ p i y)
    (hone : (∑ i, p i) = 1) (g : X → E) (δ : ℝ)
    (hclose : ∀ i y, p i y ≠ 0 → ‖g y - g (x i)‖ ≤ δ) (y : X) :
    ‖g y - ∑ i, p i y • g (x i)‖ ≤ δ := by
  have hsum : ∑ i, p i y = 1 := by
    have h := congrArg (fun q : C(X, ℝ) => q y) hone
    simpa only [ContinuousMap.sum_apply, ContinuousMap.one_apply] using h
  exact compact_sample_sum_error_le (fun i => p i y) (fun i => hnon i y) hsum
    (g y) (fun i => g (x i)) δ (fun i => hclose i y)

section Metric

variable {X : Type*} [MetricSpace X] [CompactSpace X]

/-- A finite positive partition of unity with samples at the centers of
balls of the specified radius. Nonzero weights only use nearby samples. -/
theorem exists_compact_sample_partition (radius : ℝ) (hr : 0 < radius) :
    ∃ (n : ℕ) (x : Fin n → X) (p : Fin n → C(X, ℝ)),
      (∀ i y, 0 ≤ p i y) ∧ (∑ i, p i) = 1 ∧
      ∀ i y, p i y ≠ 0 → dist y (x i) < radius := by
  classical
  obtain ⟨t, _, ht, hcover⟩ := finite_cover_balls_of_compact
    (X := X) (s := Set.univ) isCompact_univ hr
  letI : Fintype t := ht.fintype
  let e := (Fintype.equivFin t).symm
  let x (i : Fin (Fintype.card t)) : X := (e i : t)
  let U (i : Fin (Fintype.card t)) : Set X := Metric.ball (x i) radius
  have hc : Set.univ ⊆ ⋃ i, U i := by
    intro y hy
    have hy' : ∃ z ∈ t, dist y z < radius := by
      simpa only [Set.mem_iUnion, exists_prop, Metric.mem_ball] using hcover hy
    obtain ⟨z, hz, hyz⟩ := hy'
    refine Set.mem_iUnion.mpr ⟨e.symm ⟨z, hz⟩, ?_⟩
    simpa only [U, Metric.mem_ball, x, Equiv.apply_symm_apply] using hyz
  obtain ⟨q, hq⟩ := PartitionOfUnity.exists_isSubordinate_of_locallyFinite
    isClosed_univ U (fun _ => Metric.isOpen_ball) (locallyFinite_of_finite U) hc
  refine ⟨Fintype.card t, x, fun i => q i, q.nonneg, ?_, ?_⟩
  · ext y : 1
    rw [ContinuousMap.sum_apply, ContinuousMap.one_apply, ← finsum_eq_sum_of_fintype]
    exact q.sum_eq_one (Set.mem_univ y)
  · intro i y hy
    have hsu : y ∈ Function.support (q i : X → ℝ) := hy
    exact hq i (subset_closure hsu)

/-- The same finite partition approximates every map in the family.
Its nonzero weights also satisfy the prescribed bound on sample distance. -/
theorem exists_compact_spectral_sampling_with_radius
    {ρ : Type*} [Fintype ρ] (f : ρ → C(X, ℂ)) (δ radius : ℝ)
    (hδ : 0 < δ) (hr : 0 < radius) :
    ∃ (n : ℕ) (x : Fin n → X) (p : Fin n → C(X, ℝ)),
      (∀ i y, 0 ≤ p i y) ∧ (∑ i, p i) = 1 ∧
      (∀ i y, p i y ≠ 0 → dist y (x i) < radius) ∧
      ∀ r, ‖f r - ∑ i, (f r (x i)) • sampleWeightComplex (p i)‖ ≤ δ := by
  let F : C(X, ρ → ℂ) :=
    ⟨fun y r => f r y, continuous_pi fun r => (f r).continuous⟩
  obtain ⟨η, hη, hmod⟩ := F.uniform_continuity δ hδ
  obtain ⟨n, x, p, hnon, hone, hnear⟩ :=
    exists_compact_sample_partition (X := X) (min η radius) (lt_min hη hr)
  refine ⟨n, x, p, hnon, hone, ?_, ?_⟩
  · intro i y hy
    exact (hnear i y hy).trans_le (min_le_right _ _)
  · intro r
    apply (ContinuousMap.norm_le _ hδ.le).mpr
    intro y
    have hclose (i : Fin n) (z : X) (hi : p i z ≠ 0) : ‖f r z - f r (x i)‖ ≤ δ := by
      have hd : dist z (x i) < η := (hnear i z hi).trans_le (min_le_left _ _)
      have hv : dist (F z) (F (x i)) < δ := hmod hd
      have hc := (dist_pi_lt_iff hδ).mp hv r
      simpa only [F, ContinuousMap.coe_mk, dist_eq_norm] using hc.le
    have he (i : Fin n) : f r (x i) * (p i y : ℂ) = p i y • f r (x i) := by
      rw [RCLike.real_smul_eq_coe_mul, mul_comm]
    simp only [ContinuousMap.sub_apply, ContinuousMap.sum_apply, ContinuousMap.smul_apply,
      sampleWeightComplex_apply, smul_eq_mul, he]
    exact compact_sample_function_error_le x p hnon hone (f r) δ hclose y

/-- Simultaneous uniform approximation by a finite positive sampling
partition. -/
theorem exists_compact_spectral_sampling {ρ : Type*} [Fintype ρ] (f : ρ → C(X, ℂ))
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ (n : ℕ) (x : Fin n → X) (p : Fin n → C(X, ℝ)),
      (∀ i y, 0 ≤ p i y) ∧ (∑ i, p i) = 1 ∧
      ∀ r, ‖f r - ∑ i, (f r (x i)) • sampleWeightComplex (p i)‖ ≤ δ := by
  obtain ⟨n, x, p, hp, hsum, _, herror⟩ :=
    exists_compact_spectral_sampling_with_radius f δ 1 hδ zero_lt_one
  exact ⟨n, x, p, hp, hsum, herror⟩

end Metric

end

end MOC
