import MOC.Core
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Trace

/-! Trace weights for the relative unitary determinant Hessian. -/

open BigOperators Matrix

namespace MOC

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A traceless skew-Hermitian term has zero support contribution when the
projected imaginary coefficient is constant across all the diagonal entries. -/
theorem re_trace_skew_mul_diagonal_eq_zero (E : Matrix ι ι ℂ) (hE : Eᴴ = -E) (htr : E.trace = 0)
    (p : ι → ℂ) (ω : ℂ) (c : ℝ) (hc : ∀ i, (ω * p i).im = c) :
    (ω * (E * diagonal p).trace).re = 0 := by
  have hre (i : ι) : (E i i).re = 0 := by
    have he := congrArg (fun M : Matrix ι ι ℂ => (M i i).re) hE
    simp only [Matrix.conjTranspose_apply, Matrix.neg_apply, Complex.star_def,
      Complex.conj_re, Complex.neg_re] at he
    linarith only [he]
  have hsum : ∑ i, (E i i).im = 0 := by
    simpa only [Matrix.trace, Matrix.diag_apply, Complex.im_sum, Complex.zero_im] using
      congrArg Complex.im htr
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_diagonal, Finset.mul_sum, Complex.re_sum]
  calc
    _ = ∑ i, -(c * (E i i).im) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [show ω * (E i i * p i) = (ω * p i) * E i i by ring,
        Complex.mul_re, hre, hc, mul_zero, zero_sub]
    _ = _ := by rw [Finset.sum_neg_distrib, ← Finset.mul_sum, hsum, mul_zero, neg_zero]

/-- After off-block cancellation, the projected quadratic traces depend only
on the prescribed real diagonal of the compressed Hermitian direction. -/
theorem re_trace_quadratic_of_diagonal_compression
    (A : Matrix ι ι ℂ) (hA : A.IsHermitian) (p : ι → ℂ) (v : ι → ℝ) (ω : ℂ)
    (hdiag : ∀ i, A i i = (v i : ℂ))
    (hblock : ∀ i j, i ≠ j → p i = p j → A i j = 0)
    (hcross : ∀ i j, p i ≠ p j → (ω * (p i + p j - 2 * p i * p j)).re = 0) :
    (ω * (((A * A) * diagonal p).trace - ((A * diagonal p) * (A * diagonal p)).trace)).re =
      ∑ i, (v i) ^ 2 * (ω * (p i * (1 - p i))).re := by
  let N (i j : ι) := Complex.normSq (A i j)
  let T := (ω * (((A * A) * diagonal p).trace - ((A * diagonal p) * (A * diagonal p)).trace)).re
  have hpair (i j : ι) : A i j * A j i = (N i j : ℂ) := by
    have he : star (A i j) = A j i := congrArg (fun B : Matrix ι ι ℂ => B j i) hA.eq
    rw [← he, Complex.star_def, Complex.mul_conj]
  have hN (i j : ι) : N i j = N j i := by
    apply Complex.ofReal_injective
    rw [← hpair i j, ← hpair j i, mul_comm]
  have hfirst : ((A * A) * diagonal p).trace = ∑ i, ∑ j, A i j * A j i * p i := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_diagonal]
    simp only [Matrix.mul_apply, Finset.sum_mul]
  have hsecond : ((A * diagonal p) * (A * diagonal p)).trace = ∑ i, ∑ j, A i j * A j i * (p i * p j) := by
    simp only [Matrix.trace, Matrix.diag_apply]
    apply Finset.sum_congr rfl
    intro i _
    rw [Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro j _
    simp only [Matrix.mul_diagonal]
    ring
  have hT₁ : T = ∑ i, ∑ j, N i j * (ω * (p i - p i * p j)).re := by
    simp only [T, hfirst, hsecond, ← Finset.sum_sub_distrib, ← mul_sub, hpair,
      Finset.mul_sum, Complex.re_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [mul_left_comm, Complex.re_ofReal_mul]
  have hT₂ : T = ∑ i, ∑ j, N i j * (ω * (p j - p j * p i)).re := by
    rw [hT₁, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hN j i]
  have htwo : 2 * T = ∑ i, ∑ j, N i j * (ω * (p i + p j - 2 * p i * p j)).re := by
    rw [two_mul]
    calc
      _ = (∑ i, ∑ j, N i j * (ω * (p i - p i * p j)).re) +
          (∑ i, ∑ j, N i j * (ω * (p j - p j * p i)).re) := congrArg₂ (· + ·) hT₁ hT₂
      _ = _ := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i _
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j _
        rw [← mul_add, ← Complex.add_re, ← mul_add,
          show (p i - p i * p j) + (p j - p j * p i) = p i + p j - 2 * p i * p j by ring]
  have hterm (i j : ι) : N i j * (ω * (p i + p j - 2 * p i * p j)).re =
      if i = j then 2 * ((v i) ^ 2 * (ω * (p i * (1 - p i))).re) else 0 := by
    by_cases hij : i = j
    · subst j
      rw [if_pos rfl, show p i + p i - 2 * p i * p i = ((2 : ℝ) : ℂ) * (p i * (1 - p i)) by
        push_cast; ring, mul_left_comm, Complex.re_ofReal_mul]
      simp only [N, hdiag, Complex.normSq_ofReal, pow_two]
      ring
    · rw [if_neg hij]
      by_cases h : p i = p j
      · simp [N, hblock i j hij h]
      · rw [hcross i j h, mul_zero]
  simp_rw [hterm] at htwo
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true, ← Finset.mul_sum] at htwo
  change T = _
  linarith only [htwo]

end MOC
