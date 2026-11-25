import MOC.Weights
import Mathlib.Analysis.MeanInequalities
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-! Phase cuts for the real-signed determinant law.
The entrywise Gram tangent of these phases is the direction studied in
Tadej–Życzkowski, DOI: 10.1016/j.laa.2008.02.036. No integrability of
first-order phase defects and no positivity of signed weights is assumed. -/

open Matrix BigOperators
open scoped ComplexOrder

namespace MOC

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem posSemidef_det_re_le_one_of_trace_le_card {A : Matrix ι ι ℂ}
    (hA : A.PosSemidef) (ht : A.trace.re ≤ Fintype.card ι) : A.det.re ≤ 1 := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · letI := hι
    simp
  letI := hι
  let eig := hA.1.eigenvalues
  have hnon (i : ι) : 0 ≤ eig i := hA.eigenvalues_nonneg i
  have hs : ∑ i, eig i = A.trace.re := by
    have hh : (↑(∑ i, eig i) : ℂ) = A.trace := by
      rw [Complex.ofReal_sum]
      conv_rhs => rw [hA.1.spectral_theorem]
      rw [Matrix.trace_mul_cycle, unitary.coe_star_mul_self, Matrix.one_mul, Matrix.trace_diagonal]
      rfl
    simpa only [Complex.ofReal_re] using congrArg Complex.re hh
  have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hprod : 0 ≤ ∏ i, eig i := Finset.prod_nonneg (fun i _ => hnon i)
  have hgm := Real.geom_mean_le_arith_mean (Finset.univ : Finset ι)
    (fun _ => (1 : ℝ)) eig (by simp) (by simpa using hn) (fun i _ => hnon i)
  have hmean : (∑ i, eig i) / Fintype.card ι ≤ 1 := by
    rw [hs, div_le_one hn]
    exact ht
  have hpow : (∏ i, eig i) ^ (Fintype.card ι : ℝ)⁻¹ ≤ 1 := by
    exact (by simpa using hgm : (∏ i, eig i) ^ (Fintype.card ι : ℝ)⁻¹ ≤
      (∑ i, eig i) / Fintype.card ι).trans hmean
  have hp := (Real.rpow_le_rpow_iff hprod zero_le_one (inv_pos.mpr hn)).mp
    (by simpa only [Real.one_rpow] using hpow)
  rw [hA.1.det_eq_prod_eigenvalues]
  have hpC : ((↑(∏ i, eig i) : ℂ)).re ≤ 1 := by simpa only [Complex.ofReal_re] using hp
  simpa only [Complex.ofReal_prod] using hpC

/-- A rowwise contraction of a unitary's entries has determinant modulus at
most one. This is valid in the closed polydisc, with independent entries. -/
theorem unitary_entrywise_polydisc_det_normSq_le_one
    (U : Matrix ι ι ℂ) (hU : IsUnitary U) (z : ι → ι → ℂ)
    (hz : ∀ i j, Complex.normSq (z i j) ≤ 1) :
    Complex.normSq (Matrix.of (fun i j => U i j * z i j)).det ≤ 1 := by
  let V : Matrix ι ι ℂ := Matrix.of fun i j => U i j * z i j
  have hr (X : Matrix ι ι ℂ) (i : ι) :
      ((X * Xᴴ) i i).re = ∑ j, Complex.normSq (X i j) := by
    rw [Matrix.mul_apply, Complex.re_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [Matrix.conjTranspose_apply, Complex.star_def, Complex.mul_conj]
    rfl
  have ht : (Matrix.trace (V * Vᴴ)).re ≤ Fintype.card ι := by
    unfold Matrix.trace
    rw [Complex.re_sum]
    calc
      _ = ∑ i, ∑ j, Complex.normSq (V i j) := by
        simp only [Matrix.diag_apply, hr]
      _ ≤ ∑ i, ∑ j, Complex.normSq (U i j) := by
        apply Finset.sum_le_sum
        intro i _
        apply Finset.sum_le_sum
        intro j _
        simp only [V, Matrix.of_apply, map_mul]
        exact mul_le_of_le_one_right (Complex.normSq_nonneg _) (hz i j)
      _ = _ := by simp [← hr, hU.1]
  have hb := posSemidef_det_re_le_one_of_trace_le_card
    (Matrix.posSemidef_self_mul_conjTranspose V) ht
  rw [Matrix.det_mul, Matrix.det_conjTranspose, Complex.star_def, Complex.mul_conj,
    Complex.ofReal_re] at hb
  exact hb

/-- The phase character of a matching on an entrywise phase matrix. -/
def matchingPhase (z : ι → ι → ℂ) (σ : Equiv.Perm ι) : ℂ :=
  ∏ j, z (σ j) j

private theorem signed_polydisc_det_eq (U : Matrix ι ι ℂ) (z : ι → ι → ℂ) :
    ∑ σ, signedWeight U σ * matchingPhase z σ =
      (Matrix.of (fun i j => U i j * z i j)).det / U.det := by
  rw [Matrix.det_apply', Finset.sum_div]
  apply Finset.sum_congr rfl
  intro σ _
  simp only [matchingPhase, signedWeight, leibnizTerm, Matrix.of_apply, Finset.prod_mul_distrib]
  ring

/-- Real signed expectations of phase products obey the support bound
in every unit direction. This statement does not make the signed law a
positive-definite characteristic function. -/
theorem real_signed_polydisc_phase_support (U : Matrix ι ι ℂ) (hU : IsUnitary U)
    (z : ι → ι → ℂ) (hz : ∀ i j, Complex.normSq (z i j) ≤ 1)
    (ξ : ℂ) (hξ : Complex.normSq ξ ≤ 1) :
    (∑ σ, realSignedWeight U σ * (ξ * matchingPhase z σ).re) ≤ 1 := by
  let w (σ : Equiv.Perm ι) := ξ * matchingPhase z σ
  have hdetU : Complex.normSq U.det = 1 := by
    have h := congrArg Matrix.det hU.1
    rw [Matrix.det_mul, Matrix.det_conjTranspose, Matrix.det_one, Complex.star_def,
      Complex.mul_conj] at h
    exact_mod_cast h
  have hmajor (v : ι → ι → ℂ) (hv : ∀ i j, Complex.normSq (v i j) ≤ 1)
      (ζ : ℂ) (hζ : Complex.normSq ζ ≤ 1) :
      (∑ σ, signedWeight U σ * (ζ * matchingPhase v σ)).re ≤ 1 := by
    have he : ∑ σ, signedWeight U σ * (ζ * matchingPhase v σ) =
        ζ * ((Matrix.of (fun i j => U i j * v i j)).det / U.det) := by
      rw [← signed_polydisc_det_eq, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro σ _
      ring
    rw [he]
    have he' := unitary_entrywise_polydisc_det_normSq_le_one U hU v hv
    have hn : Complex.normSq (ζ * ((Matrix.of (fun i j => U i j * v i j)).det / U.det)) ≤ 1 := by
      simp only [map_mul, map_div₀, hdetU, div_one]
      exact (mul_le_of_le_one_right (Complex.normSq_nonneg _) he').trans hζ
    rw [Complex.normSq_apply] at hn
    nlinarith [sq_nonneg ((ζ * ((Matrix.of (fun i j => U i j * v i j)).det / U.det)).im)]
  have h1 := hmajor z hz ξ hξ
  have h2 := hmajor (fun i j => star (z i j)) (by simpa [Complex.star_def] using hz)
    (star ξ) (by simpa [Complex.star_def] using hξ)
  have hstar (σ : Equiv.Perm ι) : star (w σ) =
      star ξ * matchingPhase (fun i j => star (z i j)) σ := by
    simp [w, matchingPhase, Complex.star_def, map_prod, mul_comm]
  rw [Complex.re_sum] at h1 h2
  simp_rw [← hstar] at h2
  have hs (σ : Equiv.Perm ι) :
      (signedWeight U σ * w σ).re + (signedWeight U σ * star (w σ)).re =
        2 * (realSignedWeight U σ * (w σ).re) := by
    simp [realSignedWeight, Complex.star_def, Complex.mul_re]
    ring
  have hsum :
      (∑ σ, ((signedWeight U σ * w σ).re +
        (signedWeight U σ * star (w σ)).re)) =
      ∑ σ, 2 * (realSignedWeight U σ * (w σ).re) :=
    Finset.sum_congr rfl (fun σ _ => hs σ)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  change (∑ σ, realSignedWeight U σ * (w σ).re) ≤ 1
  change (∑ σ, (signedWeight U σ * w σ).re) ≤ 1 at h1
  linarith

/-- The contact-compatible phase loss has nonnegative physical expectation. -/
theorem real_signed_unitary_phase_cut_nonneg (U : Matrix ι ι ℂ) (hU : IsUnitary U)
    (z : ι → ι → ℂ) (hz : ∀ i j, Complex.normSq (z i j) = 1)
    (r : Equiv.Perm ι) :
    0 ≤ ∑ σ, realSignedWeight U σ *
      (1 - (star (matchingPhase z r) * matchingPhase z σ).re) := by
  have hξ : Complex.normSq (star (matchingPhase z r)) = 1 := by
    simp [Complex.star_def, matchingPhase, map_prod, hz]
  simpa only [mul_sub, Finset.sum_sub_distrib, mul_one, sum_realSignedWeight U hU,
    sub_nonneg] using real_signed_polydisc_phase_support U hU z (fun i j => (hz i j).le)
      (star (matchingPhase z r)) hξ.le

/-- Any finite phase grid gives a positive semidefinite Gram matrix
from the signed phase losses. With characters as test vectors this is
the finite analogue of the Toeplitz test. It does not claim nonnegative
individual Fourier coefficients or completeness of these tests. -/
theorem phase_loss_grid_posSemidef {T K : Type*} [Fintype T] [Fintype K]
    (U : Matrix ι ι ℂ) (hU : IsUnitary U)
    (z : T → ι → ι → ℂ) (hz : ∀ t i j, Complex.normSq (z t i j) = 1)
    (r : Equiv.Perm ι) (χ : K → T → ℂ) :
    let loss (t : T) := ∑ σ, realSignedWeight U σ *
      (1 - (star (matchingPhase (z t) r) * matchingPhase (z t) σ).re)
    (Matrix.of (fun i j =>
      ∑ t, (loss t : ℂ) * star (χ i t) * χ j t) : Matrix K K ℂ).PosSemidef := by
  intro loss
  let B : Matrix T K ℂ := Matrix.of fun t i => (Real.sqrt (loss t) : ℂ) * χ i t
  have hnon (t : T) : 0 ≤ loss t := real_signed_unitary_phase_cut_nonneg U hU (z t) (hz t) r
  have hB : (Matrix.of (fun i j =>
      ∑ t, (loss t : ℂ) * star (χ i t) * χ j t) : Matrix K K ℂ) = Bᴴ * B := by
    ext i j : 1
    simp only [B, Matrix.of_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
    apply Finset.sum_congr rfl
    intro t _
    rw [star_mul', Complex.star_def, Complex.conj_ofReal]
    have ht : (Real.sqrt (loss t) : ℂ) * (Real.sqrt (loss t) : ℂ) = (loss t : ℂ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hnon t)]
    rw [← ht]
    ring
  rw [hB]
  exact Matrix.posSemidef_conjTranspose_mul_self B

end

end MOC
