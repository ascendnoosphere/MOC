import MOC.Normal
import MOC.RankTwoOverlap
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-! The six-dimensional example in *Two-edge matchings and a rank condition
for the Marcus–de Oliveira conjecture*. -/

open BigOperators Complex Matrix

namespace MOC.RankTwoOverlapExample

noncomputable section

private def firstNonzero : Fin 4 → ℂ := ![1, 2, 3, I]
private def secondNonzero : Fin 4 → ℂ := ![4, 7, -1 + I, 2 - I]

def firstSpectrum : Fin 6 → ℂ := Fin.addCases firstNonzero (fun _ : Fin 2 => 0)
def secondSpectrum : Fin 6 → ℂ := Fin.addCases secondNonzero (fun _ : Fin 2 => 0)

/-- The adjoint of the normalized four-dimensional Fourier matrix,
completed by two coordinate columns. -/
def firstBasis : Matrix (Fin 6) (Fin 6) ℂ :=
  (1 / 2 : ℂ) • !![1, 1, 1, 1, 0, 0;
    1, -I, -1, I, 0, 0;
    1, -1, 1, -1, 0, 0;
    1, I, -1, -I, 0, 0;
    0, 0, 0, 0, 2, 0;
    0, 0, 0, 0, 0, 2]

/-- The four columns of the rotated second frame, completed by the two
real orthogonal complements in its coordinate planes. -/
def secondBasis : Matrix (Fin 6) (Fin 6) ℂ :=
  (1 / 390 : ℂ) • !![195 - 130 * I, 65 - 260 * I, -65 - 130 * I, 65, 0, 0;
    -65 + 130 * I, -65 * I, -195 - 130 * I, -260 + 65 * I, 0, 0;
    156, -156, 156, -156, -234, 0;
    75, 75 * I, -75, -75 * I, 0, -360;
    117, -117, 117, -117, 312, 0;
    180, 180 * I, -180, -180 * I, 0, 150]

def firstMatrix : Matrix (Fin 6) (Fin 6) ℂ :=
  firstBasis * diagonal firstSpectrum * firstBasisᴴ

def secondMatrix : Matrix (Fin 6) (Fin 6) ℂ :=
  secondBasis * diagonal secondSpectrum * secondBasisᴴ

private def firstFrame : Matrix (Fin 6) (Fin 4) ℂ :=
  firstBasis.submatrix id (Fin.castAdd 2)

private def secondFrame : Matrix (Fin 6) (Fin 4) ℂ :=
  secondBasis.submatrix id (Fin.castAdd 2)

private def firstCommonFrame : Matrix (Fin 4) (Fin 2) ℂ :=
  (1 / 2 : ℂ) • !![1, 1; 1, I; 1, -1; 1, -I]

private def secondCommonFrame : Matrix (Fin 4) (Fin 2) ℂ :=
  (1 / 6 : ℂ) • !![3 + 2 * I, -1 - 2 * I; 1 + 4 * I, I;
    -1 + 2 * I, -3 + 2 * I; 1, -4 - I]

private def gramUpperFactor : Matrix (Fin 6) (Fin 6) ℂ :=
  !![1, 0, 0, 0, 0, 0; 0, 1, 0, 0, 0, 0;
     0, 0, 1, 0, 12 / 41, 0; 0, 0, 0, 1, 0, 30 / 97;
     0, 0, 0, 0, 1, 0; 0, 0, 0, 0, 0, 1]

private def gramPivots : Fin 6 → ℂ := ![2, 2, 41 / 25, 194 / 169, 9 / 41, 72 / 97]

theorem firstBasis_unitary : IsUnitary firstBasis := by
  have h : firstBasis * firstBasisᴴ = 1 := by
    ext i j : 1
    fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
      norm_num [firstBasis, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply,
        Matrix.conjTranspose_apply, Matrix.one_apply, Matrix.cons_val,
        Fin.sum_univ_succ, Complex.star_def, Complex.conj_re, Complex.conj_im,
        Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im,
        Complex.normSq_apply, Complex.add_re, Complex.add_im]
  exact ⟨h, Matrix.mul_eq_one_comm.mp h⟩

theorem secondBasis_unitary : IsUnitary secondBasis := by
  have h : secondBasis * secondBasisᴴ = 1 := by
    ext i j : 1
    fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
      norm_num [secondBasis, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply,
        Matrix.conjTranspose_apply, Matrix.one_apply, Matrix.cons_val,
        Fin.sum_univ_succ, Complex.star_def, Complex.conj_re, Complex.conj_im,
        Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im,
        Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im]
  exact ⟨h, Matrix.mul_eq_one_comm.mp h⟩

private theorem firstNonzero_ne (j : Fin 4) : firstNonzero j ≠ 0 := by
  fin_cases j <;> norm_num [firstNonzero]

private theorem secondNonzero_ne (j : Fin 4) : secondNonzero j ≠ 0 := by
  intro h
  have hr := congrArg Complex.re h
  fin_cases j <;> norm_num [secondNonzero, Complex.add_re, Complex.sub_re] at hr

private theorem support_card_of_nonzero (d : Fin 4 → ℂ) (hd : ∀ i, d i ≠ 0) :
    (spectralSupport (Fin.addCases d (fun _ : Fin 2 => 0))).card = 4 := by
  have hs : spectralSupport (Fin.addCases d (fun _ : Fin 2 => 0)) =
      (Finset.univ : Finset (Fin 4)).image (Fin.castAdd 2) := by
    ext i
    refine Fin.addCases (m := 4) (n := 2) ?_ ?_ i
    · intro j
      have h₁ : Fin.castAdd 2 j ∈ spectralSupport (Fin.addCases d (fun _ : Fin 2 => 0)) := by
        simp [spectralSupport, Fin.addCases_left, hd j]
      have h₂ : Fin.castAdd 2 j ∈ (Finset.univ : Finset (Fin 4)).image (Fin.castAdd 2) :=
        Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩
      exact iff_of_true h₁ h₂
    · intro j
      constructor
      · intro hj
        simp [spectralSupport, Fin.addCases_right] at hj
      · intro hj
        obtain ⟨k, _, hk⟩ := Finset.mem_image.mp hj
        have hval : k.val = 4 + j.val := congrArg Fin.val hk
        have hlt := k.isLt
        omega
  have hinj : Function.Injective (Fin.castAdd 2 : Fin 4 → Fin 6) := by
    intro x y h
    exact Fin.ext (congrArg Fin.val h)
  rw [hs, Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]

theorem ranks : firstMatrix.rank = 4 ∧ secondMatrix.rank = 4 := by
  constructor
  · rw [firstMatrix, ← spectralSupport_card_eq_rank_conjugated_diagonal _ _ firstBasis_unitary]
    exact support_card_of_nonzero firstNonzero firstNonzero_ne
  · rw [secondMatrix, ← spectralSupport_card_eq_rank_conjugated_diagonal _ _ secondBasis_unitary]
    exact support_card_of_nonzero secondNonzero secondNonzero_ne

theorem spectra :
    firstMatrix.charpoly.roots = (Finset.univ : Finset (Fin 6)).val.map firstSpectrum ∧
      secondMatrix.charpoly.roots = (Finset.univ : Finset (Fin 6)).val.map secondSpectrum :=
  ⟨roots_unitary_diagonalization firstSpectrum firstBasis_unitary,
    roots_unitary_diagonalization secondSpectrum secondBasis_unitary⟩

private theorem supported_basis_sum (W : Matrix (Fin 6) (Fin 6) ℂ) (d : Fin 4 → ℂ) :
    W * diagonal (Fin.addCases d (fun _ : Fin 2 => 0)) * Wᴴ =
      W.submatrix id (Fin.castAdd 2) * diagonal d * (W.submatrix id (Fin.castAdd 2))ᴴ := by
  ext i j : 1
  calc
    _ = ∑ k : Fin 6, W i k * Fin.addCases d (fun _ : Fin 2 => (0 : ℂ)) k *
          star (W j k) := by
      rw [Matrix.mul_apply]
      simp only [Matrix.mul_diagonal, Matrix.conjTranspose_apply]
    _ = ∑ k : Fin 4, W i (Fin.castAdd 2 k) * d k * star (W j (Fin.castAdd 2 k)) := by
      rw [Fin.sum_univ_add (a := 4) (b := 2)]
      simp [Fin.addCases_left, Fin.addCases_right]
    _ = _ := by
      rw [Matrix.mul_apply]
      simp only [Matrix.mul_diagonal, Matrix.conjTranspose_apply, Matrix.submatrix_apply,
        id_eq]

private theorem firstCommonFrame_isometry : firstCommonFrameᴴ * firstCommonFrame = 1 := by
  ext i j : 1
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    norm_num [firstCommonFrame, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Matrix.one_apply, Matrix.cons_val, Fin.sum_univ_succ,
      Complex.star_def, Complex.conj_re, Complex.conj_im, Complex.mul_re, Complex.mul_im,
      Complex.div_re, Complex.div_im, Complex.normSq_apply, Complex.add_re, Complex.add_im]

private theorem secondCommonFrame_isometry : secondCommonFrameᴴ * secondCommonFrame = 1 := by
  ext i j : 1
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    norm_num [secondCommonFrame, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Matrix.one_apply, Matrix.cons_val, Fin.sum_univ_succ,
      Complex.star_def, Complex.conj_re, Complex.conj_im, Complex.mul_re, Complex.mul_im,
      Complex.div_re, Complex.div_im, Complex.normSq_apply, Complex.add_re, Complex.add_im,
      Complex.sub_re, Complex.sub_im]

private theorem common_frame : firstFrame * firstCommonFrame = secondFrame * secondCommonFrame := by
  ext i j : 1
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    norm_num [firstFrame, secondFrame, firstCommonFrame, secondCommonFrame,
      firstBasis, secondBasis, Matrix.submatrix_apply, Matrix.smul_apply, smul_eq_mul,
      Matrix.mul_apply, Matrix.cons_val, Fin.castAdd, Fin.sum_univ_succ,
      Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im,
      Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im]

private theorem gram_factorization :
    firstFrame * firstFrameᴴ + secondFrame * secondFrameᴴ =
      gramUpperFactorᵀ * diagonal gramPivots * gramUpperFactor := by
  ext i j : 1
  simp only [Matrix.add_apply]
  have ht (i j : Fin 6) : (gramUpperFactorᵀ * diagonal gramPivots) i j =
      gramUpperFactor j i * gramPivots j := by
    rw [Matrix.mul_diagonal, Matrix.transpose_apply]
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    norm_num [firstFrame, secondFrame, firstBasis, secondBasis, Matrix.submatrix_apply,
      Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.cons_val, Fin.castAdd, Fin.sum_univ_succ, ht, gramUpperFactor, gramPivots,
      Complex.star_def, Complex.conj_re, Complex.conj_im, Complex.mul_re, Complex.mul_im,
      Complex.div_re, Complex.div_im, Complex.normSq_apply, Complex.add_re, Complex.add_im,
      Complex.sub_re, Complex.sub_im]

private theorem gramUpperFactor_det : gramUpperFactor.det = 1 := by
  have h : gramUpperFactor.BlockTriangular id := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> norm_num [gramUpperFactor, Fin.lt_def] at hij ⊢
  rw [Matrix.det_of_upperTriangular h]
  norm_num [gramUpperFactor, Matrix.cons_val, Fin.prod_univ_succ]

private theorem gram_det :
    (firstFrame * firstFrameᴴ + secondFrame * secondFrameᴴ).det = 5184 / 4225 := by
  rw [gram_factorization, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
    gramUpperFactor_det, Matrix.det_diagonal, one_mul, mul_one]
  norm_num [gramPivots, Fin.prod_univ_succ]

/-- The mass assigned to matchings of the nonzero supports in the compression. -/
theorem covering_mass :
    (firstFrame * firstFrameᴴ + secondFrame * secondFrameᴴ).det / 4 = 1296 / 4225 := by
  rw [gram_det]
  norm_num

private theorem compressed_sum :
    firstCommonFrameᴴ * diagonal (fun j => (firstNonzero j)⁻¹) * firstCommonFrame +
      secondCommonFrameᴴ * diagonal (fun j => (secondNonzero j)⁻¹) * secondCommonFrame =
        (1 / 5040 : ℂ) • !![2811 - 1582 * I, -991 - 428 * I;
          913 - 776 * I, 2547 - 1694 * I] := by
  ext i j : 1
  simp only [Matrix.add_apply]
  have ht (E : Matrix (Fin 4) (Fin 2) ℂ) (d : Fin 4 → ℂ) (i : Fin 2) (j : Fin 4) :
      (Eᴴ * diagonal d) i j = star (E j i) * d j := by
    rw [Matrix.mul_diagonal, Matrix.conjTranspose_apply]
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    norm_num [firstCommonFrame, secondCommonFrame, firstNonzero, secondNonzero,
      Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply, Matrix.cons_val, Fin.sum_univ_succ,
      ht, Complex.star_def, Complex.conj_re, Complex.conj_im, Complex.mul_re,
      Complex.mul_im, Complex.div_re, Complex.div_im, Complex.inv_re, Complex.inv_im,
      Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im]

/-- The exact determinant of the sum in the six-dimensional example. -/
theorem determinant_sum : (firstMatrix + secondMatrix).det = (-225594 + 186786 * I) / 4225 := by
  let e : Fin 6 ⊕ Fin 2 ≃ Fin 4 ⊕ Fin 4 := Fintype.equivOfCardEq (by simp [Fintype.card_sum])
  have hG : IsUnit (firstFrame * firstFrameᴴ + secondFrame * secondFrameᴴ).det := by
    rw [gram_det]
    exact isUnit_iff_ne_zero.mpr (by norm_num)
  have hprod :
      ((∏ j, firstNonzero j) * ∏ j, secondNonzero j) = -504 - 168 * I := by
    apply Complex.ext <;>
      norm_num [firstNonzero, secondNonzero, Fin.prod_univ_succ, Complex.mul_re,
        Complex.mul_im, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im]
  unfold firstMatrix secondMatrix firstSpectrum secondSpectrum
  rw [supported_basis_sum firstBasis firstNonzero,
    supported_basis_sum secondBasis secondNonzero]
  change (firstFrame * diagonal firstNonzero * firstFrameᴴ +
    secondFrame * diagonal secondNonzero * secondFrameᴴ).det = _
  rw [det_support_frames e firstFrame secondFrame firstCommonFrame secondCommonFrame
    firstCommonFrame_isometry secondCommonFrame_isometry common_frame hG
    firstNonzero secondNonzero firstNonzero_ne secondNonzero_ne,
    hprod, gram_det, compressed_sum, Fintype.card_fin, Matrix.det_fin_two]
  apply Complex.ext <;>
    norm_num [Matrix.smul_apply, smul_eq_mul, Matrix.cons_val, Complex.mul_re,
      Complex.mul_im, Complex.div_re, Complex.div_im, Complex.normSq_apply,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im]

theorem inclusion : Holds firstSpectrum secondSpectrum (firstBasisᴴ * secondBasis) := by
  apply holds_of_support_excess_two _ _ _
    (relative_unitary firstBasis secondBasis firstBasis_unitary secondBasis_unitary)
  change (spectralSupport (Fin.addCases firstNonzero (fun _ : Fin 2 => 0))).card +
      (spectralSupport (Fin.addCases secondNonzero (fun _ : Fin 2 => 0))).card = _
  rw [support_card_of_nonzero firstNonzero firstNonzero_ne,
    support_card_of_nonzero secondNonzero secondNonzero_ne, Fintype.card_fin]

theorem identity_matching_product :
    matchingProduct firstSpectrum secondSpectrum (Equiv.refl (Fin 6)) = 0 := by
  unfold matchingProduct
  apply Finset.prod_eq_zero (Finset.mem_univ (Fin.natAdd 4 (0 : Fin 2)))
  simp [firstSpectrum, secondSpectrum, Fin.addCases_right]

/-- The exact determinant is in the hull of the example's matching products. -/
theorem exact_value_mem_hull :
    (-225594 + 186786 * I) / 4225 ∈
      convexHull ℝ (Set.range (matchingProduct firstSpectrum secondSpectrum)) := by
  rw [← determinant_sum]
  rw [firstMatrix, secondMatrix, determinantValue_relative
    firstSpectrum secondSpectrum firstBasis secondBasis firstBasis_unitary]
  exact inclusion

end

end MOC.RankTwoOverlapExample
