import MOC.FeedbackInterference
import MOC.Pencil
import MOC.RankTwoKernelInclusion
import MOC.Transfer

/-! The Laurent determinant on a one-coordinate unitary completion. -/

open BigOperators Matrix
open scoped ComplexConjugate

namespace MOC

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem det_two_rankOne_perturbations (A : Matrix ι ι ℂ)
    (u u' : Matrix ι (Fin 1) ℂ) (v v' : Matrix (Fin 1) ι ℂ) :
    ∃ a b c : ℂ, ∀ z : ℂ,
      (A + z • (u * v) + z • (u' * v')).det = a + b * z + c * z ^ 2 := by
  let p (x y : ℂ) := (A + x • (u * v) + y • (u' * v')).det
  have hx (x y : ℂ) : p x y = (1 - x) * p 0 y + x * p 1 y := by
    have he (z : ℂ) : p z y = (A + y • (u' * v') + z • (u * v)).det := by
      dsimp only [p]
      rw [add_right_comm]
    rw [he x, he 0, he 1, det_rankOne_affine]
    simp only [zero_smul, add_zero, one_smul]
  have hy (x y : ℂ) : p x y = (1 - y) * p x 0 + y * p x 1 := by
    dsimp only [p]
    rw [det_rankOne_affine]
    simp only [zero_smul, add_zero, one_smul]
  refine ⟨p 0 0, p 1 0 + p 0 1 - 2 * p 0 0,
    p 1 1 - p 1 0 - p 0 1 + p 0 0, fun z => ?_⟩
  change p z z = _
  rw [hx z z, hy 0 z, hy 1 z]
  ring

/-- An affine rank-one completion with singular zero phase has a Laurent
determinant with exponents from minus one to one after spectral weighting. -/
theorem rankOneCompletion_det_laurent (a b : ι → ℂ) (A : Matrix ι ι ℂ)
    (u : Matrix ι (Fin 1) ℂ) (v : Matrix (Fin 1) ι ℂ)
    (hA : A.det = 0) (hW : (A + u * v).det ≠ 0) :
    ∃ α β γ : ℂ, ∀ z : ℂ, z ≠ 0 →
      kernelDeterminantValue (Matrix.of fun i j => a i + b j) (A + z • (u * v)) =
        α * z + β + γ / z := by
  let W (z : ℂ) := A + z • (u * v)
  let N := diagonal a * A + A * diagonal b
  have hN (z : ℂ) : (Matrix.of fun i j => (a i + b j) * W z i j) =
      N + z • ((diagonal a * u) * v) + z • (u * (v * diagonal b)) := by
    have h (V : Matrix ι ι ℂ) : (Matrix.of fun i j => (a i + b j) * V i j) =
        diagonal a * V + V * diagonal b := by
      ext i j
      simp only [Matrix.of_apply, Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_mul]
      ring
    rw [h]
    simp only [W, N, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_assoc]
    abel
  obtain ⟨p, q, r, hp⟩ := det_two_rankOne_perturbations N (diagonal a * u) u v (v * diagonal b)
  let d := (A + u * v).det
  refine ⟨r / d, q / d, p / d, fun z hz => ?_⟩
  change (Matrix.of fun i j => (a i + b j) * W z i j).det / (W z).det = _
  rw [hN, hp]
  have hd : (W z).det = z * d := by
    dsimp only [W, d]
    rw [det_rankOne_affine, hA, mul_zero, zero_add]
  rw [hd]
  field_simp [d, hW, hz]
  <;> ring

/-- For a nonboundary anchor, the affine Schur transfer is the rank-one
completion with singular zero phase and unitary modulus-one phases. -/
theorem affineSchurTransfer_det_laurent (a b : ι → ℂ) (d : ℂ)
    (r : Matrix (Fin 1) ι ℂ) (c : Matrix ι (Fin 1) ℂ) (D : Matrix ι ι ℂ)
    (hU : IsUnitary (fromBlocks (scalar (Fin 1) d) r c D))
    (hd : Complex.normSq d < 1) :
    ∃ α β γ : ℂ, ∀ z : ℂ, z ≠ 0 →
      kernelDeterminantValue (Matrix.of fun i j => a i + b j) (affineSchurTransfer d r c D z) =
        α * z + β + γ / z := by
  let q := 1 - (Complex.normSq d : ℂ)
  let A := affineSchurTransfer d r c D 0
  let u := q⁻¹ • c
  have hW (z : ℂ) : affineSchurTransfer d r c D z = A + z • (u * r) := by
    change D + ((z + star d) / q) • (c * r) =
      D + ((0 + star d) / q) • (c * r) + z • ((q⁻¹ • c) * r)
    simp only [zero_add, add_div, add_smul, Matrix.smul_mul, smul_smul, div_eq_mul_inv]
    abel
  have hq : q ≠ 0 := by
    dsimp only [q]
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub]
    exact Complex.ofReal_ne_zero.mpr (sub_pos.mpr hd).ne'
  have hden : 1 - star d * d = q := by
    dsimp only [q]
    rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self]
  have hA : A.det = 0 := by
    have he : A = schurTransfer d r c D (star d) := by
      simp only [A, affineSchurTransfer, schurTransfer, hden, q, zero_add]
    rw [he, det_schurTransfer_of_unitary d r c D (star d) hU (hden.trans_ne hq),
      sub_self, zero_div, mul_zero]
  have hOne : (A + u * r).det ≠ 0 := by
    have h := det_ne_zero_of_unitary
      (affineSchurTransfer_unitary d r c D 1 hU hd Complex.normSq_one)
    rwa [hW 1, one_smul] at h
  obtain ⟨α, β, γ, h⟩ := rankOneCompletion_det_laurent a b A u r hA hOne
  exact ⟨α, β, γ, fun z hz => by rw [hW]; exact h z hz⟩

/-- Laplace expansion along any row is a squared-entry-weighted sum of
the deleted cofactor ratios. Zero entries contribute zero. -/
theorem determinantValue_eq_deletion_cofactor_average (a b : ι → ℂ)
    (U : Matrix ι ι ℂ) (hU : IsUnitary U) (i : ι) :
    determinantValue a b U = ∑ j,
      (Complex.normSq (U i j) : ℂ) * (a i + b j) *
        ((Matrix.of fun k l => (a k + b l) * U k l).adjugate j i / U.adjugate j i) := by
  rw [← feedbackPositiveCofactor_row a b U hU i]
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : U i j = 0
  · simp only [h, zero_mul, Complex.normSq_zero, Complex.ofReal_zero]
  · have hstar : star (U i j) ≠ 0 := by simpa only [star_ne_zero] using h
    rw [feedbackPositiveCofactor, adjugate_unitary U hU, Matrix.smul_apply,
      Matrix.conjTranspose_apply, smul_eq_mul, ← Complex.mul_conj, ← Complex.star_def]
    field_simp [det_ne_zero_of_unitary hU, hstar] <;> ring

omit [Fintype ι] [DecidableEq ι] in
/-- The support value of a Laurent ellipse is its center projection plus
the modulus of the combined first harmonic. -/
theorem laurentEllipse_support (η α β γ : ℂ) :
    IsGreatest {s : ℝ | ∃ z : ℂ, ‖z‖ = 1 ∧ s = (η * (α * z + β + γ / z)).re}
      ((η * β).re + ‖η * α + conj (η * γ)‖) := by
  let k := η * α + conj (η * γ)
  have hre (z : ℂ) (hz : ‖z‖ = 1) :
      (η * (α * z + β + γ / z)).re = (η * β).re + (k * z).re := by
    rw [div_eq_mul_inv, Complex.inv_eq_conj hz]
    simp only [k, Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im]
    ring
  constructor
  · by_cases hk : k = 0
    · refine ⟨1, norm_one, ?_⟩
      rw [hre 1 norm_one, hk]
      simp only [zero_mul, Complex.zero_re, norm_zero]
    · have hn : ‖k‖ ≠ 0 := norm_ne_zero_iff.mpr hk
      have hn' : (‖k‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hn
      let z : ℂ := conj k / (‖k‖ : ℂ)
      have hz : ‖z‖ = 1 := by
        simp only [z, norm_div, Complex.norm_conj, Complex.norm_of_nonneg (norm_nonneg k),
          div_self hn]
      have hp : k * z = (‖k‖ : ℂ) := by
        rw [z, ← mul_div_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_pow,
          pow_two, mul_div_cancel_right₀ _ hn']
      exact ⟨z, hz, by rw [hre z hz, hp, Complex.ofReal_re]⟩
  · rintro s ⟨z, hz, rfl⟩
    rw [hre z hz]
    apply add_le_add_left
    simpa only [norm_mul, hz, mul_one] using Complex.re_le_norm (k * z)

end

end MOC
