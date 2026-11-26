import MOC.PencilSeparation
import MOC.TranslatedDeterminantPolynomial
import MOC.Variational
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-! Moment inequalities detect strict violations of a continuous bound. -/

open MeasureTheory
open scoped BigOperators InnerProductSpace

namespace MOC

private theorem moment_powers_iff_pointwise {X : Type*} [TopologicalSpace X]
    [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] [Measure.IsOpenPosMeasure μ]
    (f : X → ℝ) (hf : Continuous f) (hfn : ∀ x, 0 ≤ f x) (R : ℝ) (hR : 0 ≤ R) :
    (∀ k : ℕ, 0 < k → (∫ x, f x ^ k ∂μ) ≤ R ^ k) ↔ ∀ x, f x ≤ R := by
  classical
  have hi (k : ℕ) : Integrable (fun x => f x ^ k) μ :=
    (hf.pow k).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  constructor
  · intro h x
    by_contra! hx
    obtain ⟨c, hRc, hcx⟩ := exists_between hx
    have hc : 0 < c := hR.trans_lt hRc
    let S : Set X := {y | c < f y}
    have hS : IsOpen S := isOpen_lt continuous_const hf
    have hμ : 0 < μ.real S :=
      ENNReal.toReal_pos (hS.measure_ne_zero μ ⟨x, hcx⟩) (measure_ne_top μ S)
    have hratio : R / c < 1 := (div_lt_one hc).mpr hRc
    obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hμ hratio
    have hk' : (R / c) ^ (k + 1) < μ.real S := by
      rw [pow_succ]
      exact (mul_le_of_le_one_right (pow_nonneg (div_nonneg hR hc.le) k) hratio.le).trans_lt hk
    have hgap : R ^ (k + 1) < μ.real S * c ^ (k + 1) := by
      rw [div_pow] at hk'
      exact (div_lt_iff₀ (pow_pos hc _)).mp hk'
    have hlow : μ.real S * c ^ (k + 1) ≤ ∫ y, f y ^ (k + 1) ∂μ := by
      rw [← smul_eq_mul, ← integral_indicator_const _ hS.measurableSet]
      apply integral_mono ((integrable_const _).indicator hS.measurableSet) (hi (k + 1))
      intro y
      by_cases hy : y ∈ S
      · rw [Set.indicator_of_mem hy]
        exact pow_le_pow_left₀ hc.le (show c < f y from hy).le _
      · rw [Set.indicator_of_not_mem hy]
        exact pow_nonneg (hfn y) _
    exact (not_lt_of_ge (h (k + 1) (Nat.zero_lt_succ k))) (hgap.trans_le hlow)
  · intro h k _
    have hp := integral_mono (hi k) (integrable_const (R ^ k) (μ := μ))
      (fun x => pow_le_pow_left₀ (hfn x) (h x) k)
    simpa only [integral_const, measureReal_univ_eq_one, one_smul] using hp

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The set of unitary matrices, with its subspace topology. -/
abbrev UnitaryMixer (ι : Type*) [Fintype ι] [DecidableEq ι] :=
  {U : Matrix ι ι ℂ // IsUnitary U}

/-- If `R w` is the squared farthest matching distance from `w`, moment
bounds for all positive integer powers are equivalent to the hull claim.
The probability measure must give positive mass to nonempty open sets. -/
theorem determinant_hull_iff_all_moments (a b : ι → ℂ)
    [MeasurableSpace (UnitaryMixer ι)] [BorelSpace (UnitaryMixer ι)]
    (μ : Measure (UnitaryMixer ι)) [IsProbabilityMeasure μ] [Measure.IsOpenPosMeasure μ]
    (R : ℂ → ℝ)
    (hR : ∀ w, (∀ p : Equiv.Perm ι, Complex.normSq (matchingProduct a b p - w) ≤ R w) ∧
      ∃ p : Equiv.Perm ι, Complex.normSq (matchingProduct a b p - w) = R w) :
    (∀ U : UnitaryMixer ι, Holds a b U.val) ↔
      ∀ (w : ℂ) (k : ℕ), 0 < k →
        (∫ U : UnitaryMixer ι, Complex.normSq (determinantValue a b U.val - w) ^ k ∂μ) ≤ R w ^ k := by
  letI : CompactSpace (UnitaryMixer ι) := isCompact_iff_compactSpace.mp isCompact_setOf_isUnitary
  have hm (w : ℂ) : (∀ k : ℕ, 0 < k →
      (∫ U : UnitaryMixer ι, Complex.normSq (determinantValue a b U.val - w) ^ k ∂μ) ≤ R w ^ k) ↔
      ∀ U : UnitaryMixer ι, Complex.normSq (determinantValue a b U.val - w) ≤ R w := by
    have hc : Continuous (fun U : UnitaryMixer ι =>
        Complex.normSq (determinantValue a b U.val - w)) := by
      unfold determinantValue
      fun_prop
    obtain ⟨p, hp⟩ := (hR w).2
    exact moment_powers_iff_pointwise μ _ hc (fun _ => Complex.normSq_nonneg _) (R w)
      (by rw [← hp]; exact Complex.normSq_nonneg _)
  constructor
  · intro h w
    apply (hm w).mpr
    intro U
    obtain ⟨p, hp⟩ := (holds_iff_farthest_matching_distance a b U.val).mp (h U) w
    exact hp.trans ((hR w).1 p)
  · intro h U
    apply (holds_iff_farthest_matching_distance a b U.val).mpr
    intro w
    obtain ⟨p, hp⟩ := (hR w).2
    refine ⟨p, ?_⟩
    rw [hp]
    exact (hm w).mp (h w) U

/-- The hull test can use the powers of the translated determinant polynomial. -/
theorem determinant_hull_iff_polynomial_moments (a b : ι → ℂ)
    [MeasurableSpace (UnitaryMixer ι)] [BorelSpace (UnitaryMixer ι)]
    (μ : Measure (UnitaryMixer ι)) [IsProbabilityMeasure μ] [Measure.IsOpenPosMeasure μ]
    (R : ℂ → ℝ)
    (hR : ∀ w, (∀ p : Equiv.Perm ι, Complex.normSq (matchingProduct a b p - w) ≤ R w) ∧
      ∃ p : Equiv.Perm ι, Complex.normSq (matchingProduct a b p - w) = R w) :
    (∀ U : UnitaryMixer ι, Holds a b U.val) ↔
      ∀ (w : ℂ) (k : ℕ), 0 < k →
        (∫ U : UnitaryMixer ι, Complex.normSq (translatedDeterminantPolynomial a b w U.val) ^ k ∂μ) ≤
          R w ^ k := by
  simp_rw [show ∀ (w : ℂ) (U : UnitaryMixer ι),
    Complex.normSq (translatedDeterminantPolynomial a b w U.val) =
      Complex.normSq (determinantValue a b U.val - w) from
    fun w U => translatedDeterminantPolynomial_normSq_unitary a b w U.val U.property]
  exact determinant_hull_iff_all_moments a b μ R hR

/-- On a finite-dimensional function space, if each pair of point evaluations
is related by a linear isometry, the squared evaluation norm is the dimension.
Here the norm on the function space is its mean-square norm. -/
theorem evaluation_sq_le_dimension_mul_integral {X E : Type*}
    [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] [CompleteSpace E]
    (μ : Measure X) [IsProbabilityMeasure μ] (ev : X → E →L[ℂ] ℂ)
    (hc : ∀ e, Continuous fun x => ev x e)
    (hi : ∀ e, (∫ x, ‖ev x e‖ ^ 2 ∂μ) = ‖e‖ ^ 2)
    (htrans : ∀ x y, ∃ T : E ≃ₗᵢ[ℂ] E, ∀ e, ev x e = ev y (T e))
    (x : X) (e : E) : ‖ev x e‖ ^ 2 ≤
      (Module.finrank ℂ E : ℝ) * (∫ y, ‖ev y e‖ ^ 2 ∂μ) := by
  let b := stdOrthonormalBasis ℂ E
  have hnorm_le (x y : X) : ‖ev x‖ ≤ ‖ev y‖ := by
    obtain ⟨T, hT⟩ := htrans x y
    apply (ev x).opNorm_le_bound (norm_nonneg _)
    intro z
    rw [hT z, ← T.norm_map z]
    exact (ev y).le_opNorm (T z)
  have hnorm_eq (y : X) : ‖ev y‖ = ‖ev x‖ := le_antisymm (hnorm_le y x) (hnorm_le x y)
  have hsum (y : X) : (∑ i, ‖ev y (b i)‖ ^ 2) = ‖ev x‖ ^ 2 := by
    let z := (InnerProductSpace.toDual ℂ E).symm (ev y)
    have hz : ‖z‖ = ‖ev y‖ := (InnerProductSpace.toDual ℂ E).symm.norm_map _
    calc
      _ = ∑ i, ‖⟪b i, z⟫_ℂ‖ ^ 2 := by
        apply Finset.sum_congr rfl
        intro i _
        rw [← InnerProductSpace.toDual_symm_apply (x := b i) (y := ev y), norm_inner_symm]
      _ = _ := by rw [b.sum_sq_norm_inner, hz, hnorm_eq y]
  have hdim : (Module.finrank ℂ E : ℝ) = ‖ev x‖ ^ 2 := by
    have heq := congrArg (fun f : X → ℝ => ∫ y, f y ∂μ) (funext hsum)
    change (∫ y, ∑ i, ‖ev y (b i)‖ ^ 2 ∂μ) = ∫ _ : X, ‖ev x‖ ^ 2 ∂μ at heq
    rw [integral_finset_sum _ (fun i _ =>
      ((hc (b i)).norm.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)),
      integral_const, measureReal_univ_eq_one, one_smul] at heq
    simpa only [hi, b.orthonormal.1, one_pow, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one] using heq
  calc
    _ ≤ (‖ev x‖ * ‖e‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) ((ev x).le_opNorm e) 2
    _ = _ := by rw [mul_pow, ← hdim, hi e]

end MOC
