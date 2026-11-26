import MOC.CompactSpectralSampling
import MOC.TracialContinuousSpectralChart
import MOC.TracialPositivePartition
import Mathlib.Tactic.NoncommRing

/-! The trace Gram bound for ordered finite-rank continuous kernels. -/

open BigOperators Set

namespace MOC

noncomputable section

variable {A X Y ρ : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [MetricSpace X] [CompactSpace X] [MetricSpace Y] [CompactSpace Y] [Fintype ρ]

/-- The continuous function of two spectral variables given by the finite-rank kernel. -/
def continuousKernelFunction (f : ρ → C(X, ℂ)) (g : ρ → C(Y, ℂ)) : C(X × Y, ℂ) :=
  ∑ r, (f r).comp ⟨Prod.fst, continuous_fst⟩ * (g r).comp ⟨Prod.snd, continuous_snd⟩

theorem continuousKernelFunction_apply (f : ρ → C(X, ℂ)) (g : ρ → C(Y, ℂ)) (p : X × Y) :
    continuousKernelFunction f g p = ∑ r, f r p.1 * g r p.2 := by
  simp only [continuousKernelFunction, ContinuousMap.sum_apply, ContinuousMap.mul_apply,
    ContinuousMap.comp_apply, ContinuousMap.coe_mk]

private theorem spectralSampling_expansion
    (φ : C(X, ℂ) →⋆ₐ[ℂ] A) (ψ : C(Y, ℂ) →⋆ₐ[ℂ] A)
    {ι κ : Type*} [Fintype ι] [Fintype κ] (x : ι → X) (y : κ → Y)
    (p : ι → C(X, ℝ)) (q : κ → C(Y, ℝ)) (f : ρ → C(X, ℂ)) (g : ρ → C(Y, ℂ)) :
    tracialContinuousKernel φ ψ
      (fun r => ∑ i, f r (x i) • continuousMapOfReal (p i))
      (fun r => ∑ j, g r (y j) • continuousMapOfReal (q j)) =
    tracialPositivePartitionKernel (fun i => φ (continuousMapOfReal (p i)))
      (fun j => ψ (continuousMapOfReal (q j))) (fun i j => continuousKernelFunction f g (x i, y j)) := by
  simp only [tracialContinuousKernel, tracialPositivePartitionKernel, continuousKernelFunction_apply,
    map_sum, map_smul, Finset.sum_mul, Finset.mul_sum, smul_mul_smul_comm, Finset.sum_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  exact Finset.sum_comm

private theorem tracialContinuousKernel_approx_norm
    (φ : C(X, ℂ) →⋆ₐ[ℂ] A) (ψ : C(Y, ℂ) →⋆ₐ[ℂ] A)
    (f f' : ρ → C(X, ℂ)) (g g' : ρ → C(Y, ℂ)) {δ : ℝ}
    (hd : 0 ≤ δ) (hd₁ : δ ≤ 1)
    (hf : ∀ r, ‖f' r - f r‖ ≤ δ) (hg : ∀ r, ‖g' r - g r‖ ≤ δ) :
    ‖tracialContinuousKernel φ ψ f' g' - tracialContinuousKernel φ ψ f g‖ ≤
      δ * ∑ r, (‖g r‖ + (‖f r‖ + 1)) := by
  have hterm (r : ρ) :
      ‖φ (f' r) * ψ (g' r) - φ (f r) * ψ (g r)‖ ≤ δ * (‖g r‖ + (‖f r‖ + 1)) := by
    have hφ : ‖φ (f' r) - φ (f r)‖ ≤ δ := by
      rw [← map_sub]
      exact (continuousSpectralChart_norm_le φ _).trans (hf r)
    have hψ : ‖ψ (g' r) - ψ (g r)‖ ≤ δ := by
      rw [← map_sub]
      exact (continuousSpectralChart_norm_le ψ _).trans (hg r)
    have hf' : ‖φ (f' r)‖ ≤ ‖f r‖ + 1 := by
      calc
        _ = ‖(φ (f' r) - φ (f r)) + φ (f r)‖ := by rw [sub_add_cancel]
        _ ≤ ‖φ (f' r) - φ (f r)‖ + ‖φ (f r)‖ := norm_add_le _ _
        _ ≤ 1 + ‖f r‖ := add_le_add (hφ.trans hd₁) (continuousSpectralChart_norm_le φ _)
        _ = _ := add_comm _ _
    have he : φ (f' r) * ψ (g' r) - φ (f r) * ψ (g r) =
        (φ (f' r) - φ (f r)) * ψ (g r) + φ (f' r) * (ψ (g' r) - ψ (g r)) := by
      noncomm_ring
    rw [he]
    calc
      _ ≤ ‖(φ (f' r) - φ (f r)) * ψ (g r)‖ +
          ‖φ (f' r) * (ψ (g' r) - ψ (g r))‖ := norm_add_le _ _
      _ ≤ ‖φ (f' r) - φ (f r)‖ * ‖ψ (g r)‖ +
          ‖φ (f' r)‖ * ‖ψ (g' r) - ψ (g r)‖ :=
        add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
      _ ≤ δ * ‖g r‖ + (‖f r‖ + 1) * δ :=
        add_le_add (mul_le_mul hφ (continuousSpectralChart_norm_le ψ _) (norm_nonneg _) hd)
          (mul_le_mul hf' hψ (norm_nonneg _) (by positivity))
      _ = _ := by ring
  rw [tracialContinuousKernel, tracialContinuousKernel, ← Finset.sum_sub_distrib, Finset.mul_sum]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun r _ => hterm r)

private theorem sum_continuousMapOfReal_partition {Z ι : Type*} [TopologicalSpace Z]
    [Fintype ι] (p : ι → C(Z, ℝ)) (hp : ∑ i, p i = 1) :
    (∑ i, continuousMapOfReal (p i)) = (1 : C(Z, ℂ)) := by
  rw [← map_sum (continuousMapOfReal (X := Z)), hp, map_one]

/-- Every uniform bound on the squared modulus of a continuous kernel
bounds the trace of the Gram operator of its ordered evaluation. -/
theorem tracialContinuousKernel_gram_trace_le
    (τ : A →L[ℂ] ℂ) (hτ : IsNormalizedTracialState τ)
    (φ : C(X, ℂ) →⋆ₐ[ℂ] A) (ψ : C(Y, ℂ) →⋆ₐ[ℂ] A)
    (f : ρ → C(X, ℂ)) (g : ρ → C(Y, ℂ)) (b : ℝ)
    (hb : ∀ p, Complex.normSq (continuousKernelFunction f g p) ≤ b) :
    (τ (star (tracialContinuousKernel φ ψ f g) * tracialContinuousKernel φ ψ f g)).re ≤ b := by
  classical
  let S : Set A := {T | (τ (star T * T)).re ≤ b}
  have hS : IsClosed S :=
    isClosed_le (Complex.continuous_re.comp (τ.continuous.comp (continuous_star.mul continuous_id)))
      continuous_const
  change tracialContinuousKernel φ ψ f g ∈ S
  apply hS.closure_subset
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  let M := ∑ r, (‖g r‖ + (‖f r‖ + 1))
  have hM : 0 ≤ M := Finset.sum_nonneg fun _ _ => by positivity
  let δ := min 1 (ε / (M + 1))
  have hd : 0 < δ := lt_min zero_lt_one (div_pos hε (by positivity))
  have hd₁ : δ ≤ 1 := min_le_left _ _
  obtain ⟨ι, x, p, hp, hpsum, hf⟩ := exists_compact_spectral_sampling f δ hd
  obtain ⟨κ, y, q, hq, hqsum, hg⟩ := exists_compact_spectral_sampling g δ hd
  let f' (r : ρ) := ∑ i, f r (x i) • continuousMapOfReal (p i)
  let g' (r : ρ) := ∑ j, g r (y j) • continuousMapOfReal (q j)
  let P (i : Fin ι) := φ (continuousMapOfReal (p i))
  let Q (j : Fin κ) := ψ (continuousMapOfReal (q j))
  let K (i : Fin ι) (j : Fin κ) := continuousKernelFunction f g (x i, y j)
  have hcast {Z : Type*} [TopologicalSpace Z] (w : C(Z, ℝ)) :
      sampleWeightComplex w = continuousMapOfReal w := by ext z; rfl
  have hP (i : Fin ι) : 0 ≤ P i := continuousSpectralChart_nonneg φ (p i) (hp i)
  have hQ (j : Fin κ) : 0 ≤ Q j := continuousSpectralChart_nonneg ψ (q j) (hq j)
  have hPsum : ∑ i, P i = 1 := by
    change (∑ i, φ (continuousMapOfReal (p i))) = 1
    rw [← map_sum, sum_continuousMapOfReal_partition p hpsum, map_one]
  have hQsum : ∑ j, Q j = 1 := by
    change (∑ j, ψ (continuousMapOfReal (q j))) = 1
    rw [← map_sum, sum_continuousMapOfReal_partition q hqsum, map_one]
  let T := tracialContinuousKernel φ ψ f' g'
  have hT : T = tracialPositivePartitionKernel P Q K := spectralSampling_expansion φ ψ x y p q f g
  have hTmem : T ∈ S := by
    change (τ (star T * T)).re ≤ b
    rw [hT]
    have hh := tracialPositivePartitionKernel_gram_trace_le τ hτ P Q hP hQ hPsum hQsum K
    obtain ⟨hpos, _, _, hmass⟩ := tracialPositivePartition_overlap_coupling τ hτ P Q hP hQ hPsum hQsum
    refine hh.trans ?_
    calc
      _ ≤ ∑ i, ∑ j, (τ (P i * Q j)).re * b :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
          mul_le_mul_of_nonneg_left (hb (x i, y j)) (hpos i j)
      _ = b := by simp only [← Finset.sum_mul, hmass, one_mul]
  refine ⟨T, hTmem, ?_⟩
  rw [dist_comm, dist_eq_norm]
  have hTclose := tracialContinuousKernel_approx_norm φ ψ f f' g g' hd.le hd₁
    (fun r => by simpa only [f', hcast, norm_sub_rev] using hf r)
    (fun r => by simpa only [g', hcast, norm_sub_rev] using hg r)
  refine hTclose.trans_lt ?_
  calc
    δ * M ≤ (ε / (M + 1)) * M := mul_le_mul_of_nonneg_right (min_le_right _ _) hM
    _ < ε := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity : 0 < M + 1)]
      nlinarith only [hε]

end

end MOC
