import MOC.UniversalMatchingWeights
import MOC.Support

/-! An exact continuous selection near the spectral origin must have
universal matching weights at the origin. -/

open BigOperators Filter Matrix
open scoped Topology

namespace MOC

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem origin_weightedMatchingValue_scale (a b : ι → ℂ) (c : ℂ)
    (p : Equiv.Perm ι → ℝ) :
    weightedMatchingValue (fun i => c * a i) (fun i => c * b i) p =
      c ^ Fintype.card ι * weightedMatchingValue a b p := by
  unfold weightedMatchingValue
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  rw [matchingProduct_scale, mul_left_comm]

/-- Exact weights on a neighborhood of zero, continuous at zero, exist
precisely when one probability law works for every pair of spectra. -/
theorem hasUniversalMatchingWeights_iff_continuous_at_spectral_origin (U : Matrix ι ι ℂ) :
    HasUniversalMatchingWeights U ↔
      ∃ w : ((ι → ℂ) × (ι → ℂ)) → Equiv.Perm ι → ℝ,
        ContinuousAt w (0, 0) ∧ (∀ σ, 0 ≤ w (0, 0) σ) ∧ (∑ σ, w (0, 0) σ) = 1 ∧
        ∀ᶠ s : (ι → ℂ) × (ι → ℂ) in 𝓝 (0, 0),
          weightedMatchingValue s.1 s.2 (w s) = determinantValue s.1 s.2 U := by
  constructor
  · rintro ⟨p, hp, hsum, hpdet⟩
    exact ⟨fun _ => p, continuousAt_const, hp, hsum,
      Eventually.of_forall (fun s => (hpdet s.1 s.2).symm)⟩
  · rintro ⟨w, hw, hw₀, hmass, hnear⟩
    refine ⟨w (0, 0), hw₀, hmass, fun a b => ?_⟩
    let path (t : ℝ) : (ι → ℂ) × (ι → ℂ) :=
      (fun i => (t : ℂ) * a i, fun i => (t : ℂ) * b i)
    have hpath : Continuous path := by unfold path; fun_prop
    have hzero : path 0 = (0, 0) := by
      simp only [path, Complex.ofReal_zero, zero_mul, Pi.zero_def]
    have hray : Tendsto path (𝓝[>] (0 : ℝ)) (𝓝 (0, 0)) := by
      rw [← hzero]
      exact hpath.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have hweighted : Continuous (fun p : Equiv.Perm ι → ℝ => weightedMatchingValue a b p) := by
      unfold weightedMatchingValue
      fun_prop
    have hlim : Tendsto (fun t => weightedMatchingValue a b (w (path t))) (𝓝[>] (0 : ℝ))
        (𝓝 (weightedMatchingValue a b (w (0, 0)))) :=
      hweighted.continuousAt.tendsto.comp (hw.tendsto.comp hray)
    have heq : ∀ᶠ t in 𝓝[>] (0 : ℝ),
        weightedMatchingValue a b (w (path t)) = determinantValue a b U := by
      filter_upwards [hray.eventually hnear, self_mem_nhdsWithin] with t ht htpos
      change weightedMatchingValue (fun i => (t : ℂ) * a i) (fun i => (t : ℂ) * b i)
          (w (path t)) =
        determinantValue (fun i => (t : ℂ) * a i) (fun i => (t : ℂ) * b i) U at ht
      change 0 < t at htpos
      rw [origin_weightedMatchingValue_scale, determinantValue_scale] at ht
      exact mul_left_cancel₀ (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr htpos.ne')) ht
    exact (tendsto_nhds_unique_of_eventuallyEq hlim tendsto_const_nhds heq).symm

end MOC
