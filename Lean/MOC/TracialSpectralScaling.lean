import MOC.TracialSpectralKernel
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Pi
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog

/-! Logarithms and scalar order bounds for finite spectral scalings. -/

open BigOperators

namespace MOC.SpectralProjectionPartition

noncomputable section

variable {A : Type*} [CStarAlgebra A]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private def coordinateHom (P : SpectralProjectionPartition ι A) : (ι → ℂ) →⋆ₐ[ℂ] A where
  toFun x := ∑ i, x i • P.proj i
  map_one' := by simp only [Pi.one_apply, one_smul, P.sum_proj]
  map_zero' := by simp only [Pi.zero_apply, zero_smul, Finset.sum_const_zero]
  map_add' x y := by simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_mul' x y := by
    change (∑ i, (x i * y i) • P.proj i) =
      (∑ i, x i • P.proj i) * (∑ j, y j • P.proj j)
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum, Finset.sum_eq_single i]
    · rw [smul_mul_smul_comm, P.mul_proj, if_pos rfl]
    · intro j _ hji
      rw [smul_mul_smul_comm, P.mul_proj, if_neg (Ne.symm hji), smul_zero]
    · intro h
      exact (h hi).elim
  commutes' c := by
    change (∑ i, c • P.proj i) = algebraMap ℂ A c
    rw [← Finset.smul_sum, P.sum_proj, Algebra.algebraMap_eq_smul_one]
  map_star' x := by
    simp only [Pi.star_apply, star_sum, star_smul, P.selfAdjoint]

private theorem coordinateHom_continuous (P : SpectralProjectionPartition ι A) :
    Continuous (coordinateHom P) := by
  change Continuous (fun x : ι → ℂ => ∑ i, x i • P.proj i)
  exact continuous_finset_sum _ fun i _ => (continuous_apply i).smul continuous_const

private theorem coordinate_spectrum (d : ι → ℝ) :
    spectrum ℝ (fun i => (d i : ℂ)) = Set.range d := by
  rw [Pi.spectrum_eq]
  ext x
  simp only [Set.mem_iUnion, Set.mem_range]
  have hs (i : ι) : spectrum ℝ (d i : ℂ) = {d i} := by
    change spectrum ℝ (algebraMap ℝ ℂ (d i)) = _
    exact spectrum.scalar_eq _
  simp only [hs, Set.mem_singleton_iff]
  exact ⟨fun ⟨i, hi⟩ => ⟨i, hi.symm⟩, fun ⟨i, hi⟩ => ⟨i, hi.symm⟩⟩

private theorem scale_spectrum_subset (P : SpectralProjectionPartition ι A) (d : ι → ℝ) :
    spectrum ℝ (∑ i, (d i : ℂ) • P.proj i) ⊆ Set.range d := by
  have h := AlgHom.spectrum_apply_subset ((coordinateHom P).restrictScalars ℝ)
    (fun i => (d i : ℂ))
  rw [coordinate_spectrum d] at h
  exact h

/-- A scaling with real coefficients is self-adjoint. -/
theorem scale_selfAdjoint (P : SpectralProjectionPartition ι A) (d : ι → ℝ) :
    IsSelfAdjoint (∑ i, (d i : ℂ) • P.proj i) := by
  change star (∑ i, (d i : ℂ) • P.proj i) = _
  simp only [star_sum, star_smul, Complex.star_def, Complex.conj_ofReal, P.selfAdjoint]

/-- Strictly positive coefficients place the real spectrum of the
scaling in the open positive half-line. -/
theorem scale_spectrum_pos (P : SpectralProjectionPartition ι A) (d : ι → ℝ)
    (hd : ∀ i, 0 < d i) (x : ℝ)
    (hx : x ∈ spectrum ℝ (∑ i, (d i : ℂ) • P.proj i)) : 0 < x := by
  obtain ⟨i, rfl⟩ := scale_spectrum_subset P d hx
  exact hd i

/-- The operator logarithm of a strictly positive finite scaling is
the same projection sum with the scalar logarithms as coefficients. -/
theorem log_scale (P : SpectralProjectionPartition ι A) (d : ι → ℝ)
    (hd : ∀ i, 0 < d i) :
    CFC.log (∑ i, (d i : ℂ) • P.proj i) =
      ∑ i, (Real.log (d i) : ℂ) • P.proj i := by
  let a : ι → ℂ := fun i => (d i : ℂ)
  let φ := coordinateHom P
  have ha_i (i : ι) : IsSelfAdjoint (a i) := by
    change star (d i : ℂ) = d i
    rw [Complex.star_def, Complex.conj_ofReal]
  have ha : IsSelfAdjoint a := by
    change star a = a
    funext i
    simpa only [Pi.star_apply] using ha_i i
  have hφa : IsSelfAdjoint (φ a) := P.scale_selfAdjoint d
  have hcont : ContinuousOn Real.log (spectrum ℝ a) := by
    change ContinuousOn Real.log (spectrum ℝ (fun i => (d i : ℂ)))
    rw [coordinate_spectrum d]
    apply Real.continuousOn_log.mono
    intro x hx
    obtain ⟨i, rfl⟩ := hx
    exact (hd i).ne'
  have hlog : cfc Real.log a = fun i => (Real.log (d i) : ℂ) := by
    have hc : ContinuousOn Real.log (⋃ i, spectrum ℝ (a i)) := by
      rwa [← Pi.spectrum_eq a]
    rw [cfc_map_pi (S := ℂ) Real.log a hc ha ha_i]
    funext i
    change CFC.log (algebraMap ℝ ℂ (d i)) = algebraMap ℝ ℂ (Real.log (d i))
    exact CFC.log_algebraMap
  change cfc Real.log (φ a) = φ (fun i => (Real.log (d i) : ℂ))
  rw [← φ.map_cfc Real.log a hcont (coordinateHom_continuous P) ha hφa, hlog]

/-- A complex linear trace of the operator logarithm is the sum of the
scalar logarithms weighted by the trace of each projection. -/
theorem trace_log_scale (P : SpectralProjectionPartition ι A) (d : ι → ℝ)
    (hd : ∀ i, 0 < d i) (τ : A →L[ℂ] ℂ) :
    (τ (CFC.log (∑ i, (d i : ℂ) • P.proj i))).re =
      ∑ i, Real.log (d i) * (τ (P.proj i)).re := by
  rw [P.log_scale d hd, map_sum, Complex.re_sum]
  simp only [map_smul, smul_eq_mul, Complex.re_ofReal_mul]

variable [PartialOrder A] [StarOrderedRing A]

/-- Scalar lower and upper bounds on the squared coefficients give
the corresponding operator bounds on the square of the scaling. -/
theorem scale_square_bounds (P : SpectralProjectionPartition ι A) (d : ι → ℝ)
    (m M : ℝ) (hm : ∀ i, m ≤ d i ^ 2) (hM : ∀ i, d i ^ 2 ≤ M) :
    let L := ∑ i, (d i : ℂ) • P.proj i
    algebraMap ℝ A m ≤ L * L ∧ L * L ≤ algebraMap ℝ A M := by
  let L := ∑ i, (d i : ℂ) • P.proj i
  change algebraMap ℝ A m ≤ L * L ∧ L * L ≤ algebraMap ℝ A M
  have hL : IsSelfAdjoint L := P.scale_selfAdjoint d
  have hpow : cfc (fun t : ℝ => t ^ 2) L = L * L := by
    simpa only [pow_two] using cfc_pow_id (R := ℝ) L 2 hL
  have hcont : ContinuousOn (fun t : ℝ => t ^ 2) (spectrum ℝ L) :=
    (continuous_id.pow 2).continuousOn
  rw [← hpow]
  refine ⟨(algebraMap_le_cfc_iff _ m L hcont hL).mpr ?_,
    (cfc_le_algebraMap_iff _ M L hcont hL).mpr ?_⟩
  · intro t ht
    obtain ⟨i, rfl⟩ := scale_spectrum_subset P d ht
    exact hm i
  · intro t ht
    obtain ⟨i, rfl⟩ := scale_spectrum_subset P d ht
    exact hM i

/-- Strictly positive scaling coefficients supply strictly positive
scalar lower and upper bounds for the operator square. -/
theorem scale_exists_square_bounds (P : SpectralProjectionPartition ι A) (d : ι → ℝ)
    (hd : ∀ i, 0 < d i) :
    let L := ∑ i, (d i : ℂ) • P.proj i
    ∃ m M : ℝ, 0 < m ∧ 0 < M ∧ algebraMap ℝ A m ≤ L * L ∧ L * L ≤ algebraMap ℝ A M := by
  classical
  rcases isEmpty_or_nonempty ι with hι | hι
  · letI := hι
    exact ⟨1, 1, zero_lt_one, zero_lt_one,
      P.scale_square_bounds d 1 1 (fun i => isEmptyElim i) (fun i => isEmptyElim i)⟩
  · letI := hι
    obtain ⟨i, _, hi⟩ := Finset.exists_min_image Finset.univ (fun i => d i ^ 2) Finset.univ_nonempty
    obtain ⟨j, _, hj⟩ := Finset.exists_max_image Finset.univ (fun i => d i ^ 2) Finset.univ_nonempty
    exact ⟨d i ^ 2, d j ^ 2, pow_pos (hd i) 2, pow_pos (hd j) 2,
      P.scale_square_bounds d _ _ (fun k => hi k (Finset.mem_univ k))
        (fun k => hj k (Finset.mem_univ k))⟩

end

end MOC.SpectralProjectionPartition
