import MOC.FugledeKadisonTraceLog
import Mathlib.Algebra.Star.BigOperators
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Tactic.NoncommRing

/-! Gram bounds for ordered products of two finite positive partitions of the identity. -/

open BigOperators

namespace MOC

noncomputable section

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- If the positive weights sum to one, the Gram operator of their left weighted sum
is at most the sum of the weighted Gram operators. -/
theorem positivePartition_jensen (P X : ι → A) (hP : ∀ i, 0 ≤ P i) (hPsum : ∑ i, P i = 1) :
    star (∑ i, P i * X i) * (∑ i, P i * X i) ≤ ∑ i, star (X i) * P i * X i := by
  let S := ∑ i, P i * X i
  have hself (i : ι) : star (P i) = P i := (IsSelfAdjoint.of_nonneg (hP i)).star_eq
  have hstar : (∑ i, star (X i) * P i) = star S := by
    simp only [S, star_sum, star_mul, hself]
  have hright : (∑ i, star (X i) * P i * S) = star S * S := by
    rw [← Finset.sum_mul, hstar]
  have hleft : (∑ i, star S * (P i * X i)) = star S * S := by
    rw [← Finset.mul_sum]
  have hconstant : (∑ i, star S * P i * S) = star S * S := by
    rw [← Finset.sum_mul, ← Finset.mul_sum, hPsum, mul_one]
  have hexpand (i : ι) :
      star (X i - S) * P i * (X i - S) =
        star (X i) * P i * X i - star (X i) * P i * S -
          star S * (P i * X i) + star S * P i * S := by
    rw [star_sub]
    noncomm_ring
  have hvariance : 0 ≤ ∑ i, star (X i - S) * P i * (X i - S) :=
    Finset.sum_nonneg fun i _ => conjugate_nonneg (hP i) (X i - S)
  apply sub_nonneg.mp
  simpa only [hexpand, Finset.sum_add_distrib, Finset.sum_sub_distrib, hright,
    hleft, hconstant, sub_add_cancel] using hvariance

private theorem positivePartition_scalar_gram_le (Q : κ → A) (hQ : ∀ j, 0 ≤ Q j)
    (hQsum : ∑ j, Q j = 1) (k : κ → ℂ) :
    (∑ j, k j • Q j) * star (∑ j, k j • Q j) ≤ ∑ j, (Complex.normSq (k j) : ℂ) • Q j := by
  let X (j : κ) := star (k j) • (1 : A)
  have hself (j : κ) : star (Q j) = Q j := (IsSelfAdjoint.of_nonneg (hQ j)).star_eq
  have hsum : (∑ j, Q j * X j) = star (∑ j, k j • Q j) := by
    simp only [X, mul_smul_comm, mul_one, star_sum, star_smul, hself]
  have hterm (j : κ) : star (X j) * Q j * X j = (Complex.normSq (k j) : ℂ) • Q j := by
    rw [show star (X j) = k j • (1 : A) by simp only [X, star_smul, star_star, star_one]]
    change ((k j • (1 : A)) * Q j) * (star (k j) • 1) = _
    rw [smul_mul_assoc, one_mul, smul_mul_smul_comm, mul_one, Complex.star_def, Complex.mul_conj]
  simpa only [hsum, star_star, hterm] using positivePartition_jensen Q X hQ hQsum

/-- A positive trace assigns a nonnegative real part to the product of two positive elements
when it is cyclic. -/
theorem tracial_positive_product_nonneg (τ : A →L[ℂ] ℂ) (hτ : IsNormalizedTracialState τ)
    {X Y : A} (hX : 0 ≤ X) (hY : 0 ≤ Y) : 0 ≤ (τ (X * Y)).re := by
  let S := CFC.sqrt X
  have hS : 0 ≤ S := CFC.sqrt_nonneg
  have hsq : S * S = X := CFC.sqrt_mul_sqrt_self X hX
  have htrace : τ (X * Y) = τ (S * Y * S) := calc
    τ (X * Y) = τ (S * (S * Y)) := by rw [← mul_assoc, hsq]
    _ = τ (S * Y * S) := hτ.cyclic _ _
  rw [htrace]
  exact hτ.positive _ (conjugate_nonneg_of_nonneg hY hS)

private theorem tracial_positive_left_mono (τ : A →L[ℂ] ℂ) (hτ : IsNormalizedTracialState τ)
    {P X Y : A} (hP : 0 ≤ P) (h : X ≤ Y) : (τ (P * X)).re ≤ (τ (P * Y)).re := by
  have hn := tracial_positive_product_nonneg τ hτ hP (sub_nonneg.mpr h)
  simpa only [mul_sub, map_sub, Complex.sub_re, sub_nonneg] using hn

/-- The ordered evaluation of a complex kernel on two finite families of operators. -/
def tracialPositivePartitionKernel (P : ι → A) (Q : κ → A) (K : ι → κ → ℂ) : A :=
  ∑ i, ∑ j, K i j • (P i * Q j)

/-- The overlap weights of two positive partitions form a probability law.
Their marginals are the traces of the individual weights. -/
theorem tracialPositivePartition_overlap_coupling (τ : A →L[ℂ] ℂ) (hτ : IsNormalizedTracialState τ)
    (P : ι → A) (Q : κ → A) (hP : ∀ i, 0 ≤ P i) (hQ : ∀ j, 0 ≤ Q j)
    (hPsum : ∑ i, P i = 1) (hQsum : ∑ j, Q j = 1) :
    (∀ i j, 0 ≤ (τ (P i * Q j)).re) ∧
      (∀ i, (∑ j, (τ (P i * Q j)).re) = (τ (P i)).re) ∧
      (∀ j, (∑ i, (τ (P i * Q j)).re) = (τ (Q j)).re) ∧
      (∑ i, ∑ j, (τ (P i * Q j)).re) = 1 := by
  have hrow (i : ι) : (∑ j, (τ (P i * Q j)).re) = (τ (P i)).re := by
    rw [← Complex.re_sum, ← map_sum, ← Finset.mul_sum, hQsum, mul_one]
  refine ⟨fun i j => tracial_positive_product_nonneg τ hτ (hP i) (hQ j), hrow, ?_, ?_⟩
  · intro j
    rw [← Complex.re_sum, ← map_sum, ← Finset.sum_mul, hPsum, one_mul]
  · simp only [hrow]
    rw [← Complex.re_sum, ← map_sum, hPsum, hτ.one, Complex.one_re]

/-- For two positive partitions of the identity, the overlap mean of the squared
kernel modulus bounds the trace of the Gram operator of the ordered evaluation. -/
theorem tracialPositivePartitionKernel_gram_trace_le (τ : A →L[ℂ] ℂ) (hτ : IsNormalizedTracialState τ)
    (P : ι → A) (Q : κ → A) (hP : ∀ i, 0 ≤ P i) (hQ : ∀ j, 0 ≤ Q j)
    (hPsum : ∑ i, P i = 1) (hQsum : ∑ j, Q j = 1) (K : ι → κ → ℂ) :
    (τ (star (tracialPositivePartitionKernel P Q K) * tracialPositivePartitionKernel P Q K)).re ≤
      ∑ i, ∑ j, (τ (P i * Q j)).re * Complex.normSq (K i j) := by
  let B (i : ι) := ∑ j, K i j • Q j
  let V (i : ι) := ∑ j, (Complex.normSq (K i j) : ℂ) • Q j
  have hkernel : tracialPositivePartitionKernel P Q K = ∑ i, P i * B i := by
    simp only [tracialPositivePartitionKernel, B, Finset.mul_sum, mul_smul_comm]
  have hrow (i : ι) : (τ (star (B i) * P i * B i)).re ≤
      ∑ j, (τ (P i * Q j)).re * Complex.normSq (K i j) := by
    have hgram : B i * star (B i) ≤ V i := positivePartition_scalar_gram_le Q hQ hQsum (K i)
    have he : τ (star (B i) * P i * B i) = τ (P i * (B i * star (B i))) := by
      rw [mul_assoc, hτ.cyclic (star (B i)) (P i * B i), mul_assoc]
    rw [he]
    refine (tracial_positive_left_mono τ hτ (hP i) hgram).trans ?_
    change (τ (P i * ∑ j, (Complex.normSq (K i j) : ℂ) • Q j)).re ≤ _
    rw [Finset.mul_sum, map_sum, Complex.re_sum]
    apply le_of_eq
    apply Finset.sum_congr rfl
    intro j _
    rw [mul_smul_comm, map_smul, smul_eq_mul, Complex.re_ofReal_mul, mul_comm]
  rw [hkernel]
  have hleft := positivePartition_jensen P B hP hPsum
  have ht := hτ.positive _ (sub_nonneg.mpr hleft)
  rw [map_sub, Complex.sub_re, sub_nonneg, map_sum, Complex.re_sum] at ht
  exact ht.trans (Finset.sum_le_sum fun i _ => hrow i)

end

end MOC
