import MOC.ContinuousWeightCounterexample

/-! Exact probability weights cannot always be selected continuously,
even for two spectral rays on which determinant inclusion holds. -/

open BigOperators

namespace MOC

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem weightedMatchingValue_scale (a b : ι → ℂ) (c : ℂ)
    (w : Equiv.Perm ι → ℝ) :
    weightedMatchingValue (fun i => c * a i) (fun i => c * b i) w =
      c ^ Fintype.card ι * weightedMatchingValue a b w := by
  unfold weightedMatchingValue
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  rw [matchingProduct_scale, mul_left_comm]

theorem exact_matching_weights_at_ray_limit (a b : ι → ℂ) (U : Matrix ι ι ℂ)
    (w : ℝ → Equiv.Perm ι → ℝ) (hc : ContinuousAt w 0)
    (h : ∀ t : ℝ, 0 < t →
      weightedMatchingValue (fun i => (t : ℂ) * a i) (fun i => (t : ℂ) * b i) (w t) =
        determinantValue (fun i => (t : ℂ) * a i) (fun i => (t : ℂ) * b i) U) :
    weightedMatchingValue a b (w 0) = determinantValue a b U := by
  have hvalue : Continuous (fun v : Equiv.Perm ι → ℝ => weightedMatchingValue a b v) := by
    unfold weightedMatchingValue
    fun_prop
  refine continuous_zero_eq_of_positive (hvalue.continuousAt.comp hc) ?_
  intro t ht
  have he := h t ht
  rw [weightedMatchingValue_scale, determinantValue_scale] at he
  exact mul_left_cancel₀ (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr ht.ne')) he

open ContinuousWeightCounterexample

/-- Two positive rays have individual determinant hull certificates.
A selection of exact weights on them cannot extend continuously to the
zero spectra while keeping a probability law there. -/
theorem no_continuous_matching_selection_at_zero :
    ¬ ∃ w : ((Fin 4 → ℂ) × (Fin 4 → ℂ)) → Equiv.Perm (Fin 4) → ℝ,
      ContinuousAt w (0, 0) ∧ (∀ σ, 0 ≤ w (0, 0) σ) ∧ (∑ σ, w (0, 0) σ = 1) ∧
      ∀ (s : Bool) (t : ℝ), 0 < t →
        let a : Fin 4 → ℂ := fun i => (t : ℂ) * leftSpectrum s i
        let b : Fin 4 → ℂ := fun i => (t : ℂ) * rightSpectrum i
        weightedMatchingValue a b (w (a, b)) = determinantValue a b mixer := by
  rintro ⟨w, hcontinuous, hnonnegative, hmass, hweights⟩
  refine no_common_weights_two_spectra ⟨w (0, 0), hnonnegative, hmass, fun s => ?_⟩
  let p (t : ℝ) : (Fin 4 → ℂ) × (Fin 4 → ℂ) :=
    (fun i => (t : ℂ) * leftSpectrum s i, fun i => (t : ℂ) * rightSpectrum i)
  have hp : Continuous p := by
    unfold p
    fun_prop
  have hp0 : p 0 = (0, 0) := by
    simp only [p, Complex.ofReal_zero, zero_mul, Pi.zero_def]
  have hc' : ContinuousAt w (p 0) := by rwa [hp0]
  have hc : ContinuousAt (fun t => w (p t)) 0 := hc'.comp hp.continuousAt
  have he := exact_matching_weights_at_ray_limit (leftSpectrum s) rightSpectrum mixer
    (fun t => w (p t)) hc (hweights s)
  simpa only [hp0] using he

end
end MOC
