import MOC.FugledeKadisonTraceLog
import Mathlib.Algebra.Star.BigOperators
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Ring

/-! Finite ordered spectral kernels in a tracial operator algebra. -/

open BigOperators

namespace MOC

noncomputable section

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- A finite complete family of orthogonal projections in the algebra. -/
structure SpectralProjectionPartition (ι A : Type*) [Fintype ι] [DecidableEq ι]
    [Ring A] [StarRing A] where
  proj : ι → A
  selfAdjoint : ∀ i, star (proj i) = proj i
  mul_proj : ∀ i k, proj i * proj k = if i = k then proj i else 0
  sum_proj : ∑ i, proj i = 1

/-- The ordered evaluation of a finite kernel on two projection families. -/
def tracialSpectralKernel (P : SpectralProjectionPartition ι A)
    (Q : SpectralProjectionPartition κ A) (K : ι → κ → ℂ) : A :=
  ∑ i, ∑ j, K i j • (P.proj i * Q.proj j)

/-- The trace overlap weights of the two projection families. -/
def tracialProjectionOverlap (τ : A →L[ℂ] ℂ)
    (P : SpectralProjectionPartition ι A) (Q : SpectralProjectionPartition κ A)
    (i : ι) (j : κ) : ℝ :=
  (τ (P.proj i * Q.proj j)).re

private theorem tracial_projection_cross
    (τ : A →L[ℂ] ℂ) (hτ : IsNormalizedTracialState τ)
    (P : SpectralProjectionPartition ι A) (Q : SpectralProjectionPartition κ A)
    (i k : ι) (j l : κ) :
    τ (star (P.proj i * Q.proj j) * (P.proj k * Q.proj l)) =
      if i = k ∧ j = l then τ (P.proj i * Q.proj j) else 0 := by
  rw [star_mul, P.selfAdjoint, Q.selfAdjoint]
  have hmul : (Q.proj j * P.proj i) * (P.proj k * Q.proj l) =
      (Q.proj j * (P.proj i * P.proj k)) * Q.proj l := by noncomm_ring
  rw [hmul, P.mul_proj]
  by_cases hik : i = k
  · subst k
    simp only [true_and, if_true]
    rw [hτ.cyclic (Q.proj j * P.proj i) (Q.proj l), ← mul_assoc, Q.mul_proj]
    by_cases hjl : j = l
    · subst l
      simp only [if_true]
      exact hτ.cyclic _ _
    · simp only [if_neg hjl, if_neg (Ne.symm hjl), zero_mul, map_zero]
  · simp only [if_neg hik, false_and, if_false, mul_zero, zero_mul, map_zero]

/-- The trace overlaps form a nonnegative coupling of the spectral masses. -/
theorem tracialProjectionOverlap_coupling
    (τ : A →L[ℂ] ℂ) (hτ : IsNormalizedTracialState τ)
    (P : SpectralProjectionPartition ι A) (Q : SpectralProjectionPartition κ A) :
    (∀ i j, 0 ≤ tracialProjectionOverlap τ P Q i j) ∧
      (∀ i, (∑ j, tracialProjectionOverlap τ P Q i j) = (τ (P.proj i)).re) ∧
      (∀ j, (∑ i, tracialProjectionOverlap τ P Q i j) = (τ (Q.proj j)).re) ∧
      (∑ i, ∑ j, tracialProjectionOverlap τ P Q i j) = 1 := by
  have hrow (i : ι) : (∑ j, tracialProjectionOverlap τ P Q i j) = (τ (P.proj i)).re := by
    unfold tracialProjectionOverlap
    rw [← Complex.re_sum, ← map_sum, ← Finset.mul_sum, Q.sum_proj, mul_one]
  refine ⟨fun i j => ?_, hrow, fun j => ?_, ?_⟩
  · have hp := hτ.positive _ (star_mul_self_nonneg (P.proj i * Q.proj j))
    simpa only [tracialProjectionOverlap, tracial_projection_cross τ hτ P Q i i j j,
      true_and, if_true] using hp
  · unfold tracialProjectionOverlap
    rw [← Complex.re_sum, ← map_sum, ← Finset.sum_mul, P.sum_proj, one_mul]
  · simp only [hrow]
    rw [← Complex.re_sum, ← map_sum, P.sum_proj, hτ.one, Complex.one_re]

/-- The trace of the Gram operator of the ordered evaluation equals the
mean of the squared kernel modulus under the trace overlaps. -/
theorem tracialSpectralKernel_gram_trace
    (τ : A →L[ℂ] ℂ) (hτ : IsNormalizedTracialState τ)
    (P : SpectralProjectionPartition ι A) (Q : SpectralProjectionPartition κ A)
    (K : ι → κ → ℂ) :
    (τ (star (tracialSpectralKernel P Q K) * tracialSpectralKernel P Q K)).re =
      ∑ i, ∑ j, tracialProjectionOverlap τ P Q i j * Complex.normSq (K i j) := by
  have hterm (i k : ι) (j l : κ) :
      τ (star (K i j • (P.proj i * Q.proj j)) * (K k l • (P.proj k * Q.proj l))) =
        if i = k ∧ j = l then (Complex.normSq (K i j) : ℂ) *
          τ (P.proj i * Q.proj j) else 0 := by
    rw [star_smul, smul_mul_smul_comm, map_smul, smul_eq_mul,
      tracial_projection_cross τ hτ P Q]
    by_cases he : i = k ∧ j = l
    · obtain ⟨rfl, rfl⟩ := he
      simp only [true_and, if_true]
      rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self]
    · simp only [if_neg he, mul_zero]
  have hsum (i : ι) (j : κ) :
      (∑ k : ι, ∑ l : κ, if i = k ∧ j = l then
        (Complex.normSq (K i j) : ℂ) * τ (P.proj i * Q.proj j) else 0) =
        (Complex.normSq (K i j) : ℂ) * τ (P.proj i * Q.proj j) := by
    rw [Finset.sum_eq_single i]
    · simp
    · intro k _ hk
      simp [Ne.symm hk]
    · simp
  unfold tracialSpectralKernel
  simp only [star_sum, Finset.sum_mul, Finset.mul_sum, map_sum, hterm, hsum,
    Complex.re_sum, Complex.re_ofReal_mul, tracialProjectionOverlap, mul_comm]

/-- Spectral row and column scaling is multiplication on the left and
right in the original algebra. -/
theorem tracialSpectralKernel_scale
    (P : SpectralProjectionPartition ι A) (Q : SpectralProjectionPartition κ A)
    (K : ι → κ → ℂ) (u : ι → ℂ) (v : κ → ℂ) :
    (∑ i, u i • P.proj i) * tracialSpectralKernel P Q K * (∑ j, v j • Q.proj j) =
      tracialSpectralKernel P Q (fun i j => u i * K i j * v j) := by
  let L := ∑ i, u i • P.proj i
  let R := ∑ j, v j • Q.proj j
  have hL (i : ι) : L * P.proj i = u i • P.proj i := by
    simp only [L, Finset.sum_mul, smul_mul_assoc, P.mul_proj, smul_ite, smul_zero]
    simp
  have hR (j : κ) : Q.proj j * R = v j • Q.proj j := by
    simp only [R, Finset.mul_sum, mul_smul_comm, Q.mul_proj, smul_ite, smul_zero]
    simp
  change L * (∑ i, ∑ j, K i j • (P.proj i * Q.proj j)) * R = _
  unfold tracialSpectralKernel
  simp only [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [mul_smul_comm, smul_mul_assoc, ← mul_assoc L (P.proj i), mul_assoc (L * P.proj i),
    hL, hR, smul_mul_smul_comm, smul_smul]
  congr 1 <;> ring

/-- The addition kernel gives the sum of the two spectral operators. -/
theorem tracialSpectralKernel_add (P : SpectralProjectionPartition ι A)
    (Q : SpectralProjectionPartition κ A) (a : ι → ℂ) (b : κ → ℂ) :
    tracialSpectralKernel P Q (fun i j => a i + b j) =
      (∑ i, a i • P.proj i) + ∑ j, b j • Q.proj j := by
  have hrow (i : ι) : (∑ j, a i • (P.proj i * Q.proj j)) = a i • P.proj i := by
    rw [← Finset.smul_sum, ← Finset.mul_sum, Q.sum_proj, mul_one]
  have hcol (j : κ) : (∑ i, b j • (P.proj i * Q.proj j)) = b j • Q.proj j := by
    rw [← Finset.smul_sum, ← Finset.sum_mul, P.sum_proj, one_mul]
  unfold tracialSpectralKernel
  simp only [add_smul, Finset.sum_add_distrib, hrow]
  rw [Finset.sum_comm (f := fun i j => b j • (P.proj i * Q.proj j))]
  simp only [hcol]

/-- If the squared kernel modulus has a positive upper bound under the
trace overlaps, its logarithm bounds the analytic determinant. -/
theorem fugledeKadisonLog_spectralKernel_le_overlap_bound
    (τ : A →L[ℂ] ℂ) (hτ : IsNormalizedTracialState τ)
    (P : SpectralProjectionPartition ι A) (Q : SpectralProjectionPartition κ A)
    (K : ι → κ → ℂ) (u : ℝ) (hu : 0 < u)
    (h : (∑ i, ∑ j, tracialProjectionOverlap τ P Q i j * Complex.normSq (K i j)) ≤ u) :
    fugledeKadisonLog τ (tracialSpectralKernel P Q K) ≤ (Real.log u / 2 : ℝ) := by
  apply fugledeKadisonLog_le_log_trace_bound τ hτ _ u hu
  rw [tracialSpectralKernel_gram_trace τ hτ]
  exact h

/-- A kernel bounded by one on a finite spectral product has analytic
determinant at most one. -/
theorem fugledeKadisonLog_spectralKernel_nonpos
    (τ : A →L[ℂ] ℂ) (hτ : IsNormalizedTracialState τ)
    (P : SpectralProjectionPartition ι A) (Q : SpectralProjectionPartition κ A)
    (K : ι → κ → ℂ) (hK : ∀ i j, Complex.normSq (K i j) ≤ 1) :
    fugledeKadisonLog τ (tracialSpectralKernel P Q K) ≤ 0 := by
  obtain ⟨hn, _, _, hs⟩ := tracialProjectionOverlap_coupling τ hτ P Q
  have hm : (∑ i, ∑ j, tracialProjectionOverlap τ P Q i j * Complex.normSq (K i j)) ≤ 1 := by
    rw [← hs]
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j _
    exact mul_le_of_le_one_right (hn i j) (hK i j)
  have h := fugledeKadisonLog_spectralKernel_le_overlap_bound τ hτ P Q K 1 zero_lt_one hm
  simpa only [Real.log_one, zero_div, EReal.coe_zero] using h

end

end MOC
