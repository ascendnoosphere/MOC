import MOC.Core

/-! A real orthogonal mixer of twice the size recovers the square of a
complex spectral determinant. The two spectral lists may be arbitrary. -/

open Matrix
open scoped ComplexConjugate

namespace MOC

noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The usual real matrix of a complex linear map, with its entries
included in the complex numbers. -/
def realOrthogonalDouble (U : Matrix ι ι ℂ) : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ :=
  let X := U.map (fun z => (z.re : ℂ))
  let Y := U.map (fun z => (z.im : ℂ))
  fromBlocks X (-Y) Y X

omit [Fintype ι] [DecidableEq ι] in
theorem realOrthogonalDouble_im (U : Matrix ι ι ℂ) (i j : ι ⊕ ι) :
    (realOrthogonalDouble U i j).im = 0 := by
  cases i <;> cases j <;> simp [realOrthogonalDouble]

private def splitPair (X Y : Matrix ι ι ℂ) : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ :=
  fromBlocks X 0 0 Y

private def splitMixer (U : Matrix ι ι ℂ) := splitPair U Uᴴᵀ

private def splitBasis : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ :=
  fromBlocks 1 1 ((-Complex.I) • (1 : Matrix ι ι ℂ)) (Complex.I • (1 : Matrix ι ι ℂ))

private def inverseBasis : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ :=
  (2 : ℂ)⁻¹ • fromBlocks (1 : Matrix ι ι ℂ) (Complex.I • (1 : Matrix ι ι ℂ))
    1 ((-Complex.I) • (1 : Matrix ι ι ℂ))

private theorem splitBasis_right_inv : splitBasis (ι := ι) * inverseBasis = 1 := by
  rw [inverseBasis, Matrix.mul_smul, splitBasis, fromBlocks_multiply]
  simp [Matrix.mul_smul, Matrix.smul_mul, smul_smul, Complex.I_mul_I,
    ← Matrix.fromBlocks_smul, ← Matrix.fromBlocks_one, add_smul, ← add_smul]
  rw [fromBlocks_smul]
  simp only [smul_zero, fromBlocks_inj, true_and, and_self]
  ext i j
  simp only [Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]
  ring

private theorem cancel_basis {X Y : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ}
    (h : X * splitBasis = Y * splitBasis) : X = Y := by
  have he := congrArg (fun M : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ => M * inverseBasis) h
  simpa only [Matrix.mul_assoc, splitBasis_right_inv, Matrix.mul_one] using he

private theorem double_intertwines (U : Matrix ι ι ℂ) :
    realOrthogonalDouble U * splitBasis = splitBasis * splitMixer U := by
  simp only [realOrthogonalDouble, splitBasis, splitMixer, splitPair, fromBlocks_multiply,
    Matrix.mul_zero, Matrix.zero_mul, Matrix.one_mul, Matrix.mul_one, add_zero, zero_add,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.fromBlocks_inj]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ext i j <;>
    simp [Matrix.add_apply, Matrix.neg_apply, Matrix.smul_apply, Matrix.map_apply,
      Matrix.transpose_apply, Matrix.conjTranspose_apply, Complex.star_def, Complex.mul_re,
      Complex.mul_im]
  all_goals apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]

omit [Fintype ι] [DecidableEq ι] in
private theorem double_adjoint (U : Matrix ι ι ℂ) :
    (realOrthogonalDouble U)ᴴ = realOrthogonalDouble Uᴴ := by
  ext i j
  cases i <;> cases j <;> simp [realOrthogonalDouble, Matrix.conjTranspose_apply,
    Complex.star_def]

omit [DecidableEq ι] in
private theorem split_mul (U V : Matrix ι ι ℂ) :
    splitMixer (U * V) = splitMixer U * splitMixer V := by
  simp [splitMixer, splitPair, fromBlocks_multiply, Matrix.conjTranspose_mul, Matrix.transpose_mul]

private theorem double_mul (U V : Matrix ι ι ℂ) :
    realOrthogonalDouble (U * V) = realOrthogonalDouble U * realOrthogonalDouble V := by
  apply cancel_basis
  rw [double_intertwines, Matrix.mul_assoc, double_intertwines, ← Matrix.mul_assoc,
    double_intertwines, Matrix.mul_assoc, ← split_mul]

private theorem double_one : realOrthogonalDouble (1 : Matrix ι ι ℂ) = 1 := by
  apply cancel_basis
  rw [double_intertwines]
  simp [splitMixer, splitPair]

/-- A unitary matrix gives a real orthogonal matrix of twice the size. -/
theorem realOrthogonalDouble_isUnitary (U : Matrix ι ι ℂ) (hU : IsUnitary U) :
    IsUnitary (realOrthogonalDouble U) := by
  constructor
  · rw [double_adjoint, ← double_mul, hU.1, double_one]
  · rw [double_adjoint, ← double_mul, hU.2, double_one]

private theorem diagonal_intertwines (a : ι → ℂ) :
    diagonal (Sum.elim a a) * splitBasis =
      splitBasis * splitPair (diagonal a) (diagonal a) := by
  rw [← fromBlocks_diagonal]
  simp only [splitBasis, splitPair, fromBlocks_multiply, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.zero_mul, Matrix.mul_zero, Matrix.one_mul, Matrix.mul_one, zero_add, add_zero,
    smul_zero]

omit [Fintype ι] [DecidableEq ι] in
private theorem conjugate_adjoint (U : Matrix ι ι ℂ) : Uᴴᵀᴴ = Uᵀ := by
  ext i j
  simp [Matrix.conjTranspose_apply, Matrix.transpose_apply]

private theorem determinant_conjugate_mixer (a b : ι → ℂ) (U : Matrix ι ι ℂ) :
    determinantValue a b Uᴴᵀ = determinantValue a b U := by
  unfold determinantValue
  conv_rhs => rw [← Matrix.det_transpose]
  congr 1
  simp [Matrix.transpose_add, Matrix.transpose_mul, Matrix.mul_assoc, conjugate_adjoint]

/-- Repeating both complex spectral lists squares their spectral determinant. -/
theorem determinantValue_realOrthogonalDouble (a b : ι → ℂ) (U : Matrix ι ι ℂ) :
    determinantValue (Sum.elim a a) (Sum.elim b b) (realOrthogonalDouble U) =
      determinantValue a b U ^ 2 := by
  let R := realOrthogonalDouble U
  let S := splitBasis (ι := ι)
  let V := splitMixer U
  let A := splitPair (diagonal a) (diagonal a)
  let B := splitPair (diagonal b) (diagonal b)
  have hR : R * S = S * V := double_intertwines U
  have hR' : Rᴴ * S = S * Vᴴ := by
    rw [show Rᴴ = realOrthogonalDouble Uᴴ from double_adjoint U, double_intertwines]
    simp [V, S, splitMixer, splitPair, fromBlocks_conjTranspose, conjugate_adjoint]
  have hA : diagonal (Sum.elim a a) * S = S * A := diagonal_intertwines a
  have hB : diagonal (Sum.elim b b) * S = S * B := diagonal_intertwines b
  have h : (diagonal (Sum.elim a a) + R * diagonal (Sum.elim b b) * Rᴴ) * S =
      S * (A + V * B * Vᴴ) := by
    rw [Matrix.add_mul, Matrix.mul_add, hA, Matrix.mul_assoc, hR', ← Matrix.mul_assoc,
      Matrix.mul_assoc R, hB, ← Matrix.mul_assoc, hR, Matrix.mul_assoc, Matrix.mul_assoc]
    rw [Matrix.mul_assoc V]
  have hn : S.det ≠ 0 := by
    have hi := congrArg Matrix.det (splitBasis_right_inv (ι := ι))
    rw [Matrix.det_mul, Matrix.det_one] at hi
    exact left_ne_zero_of_mul_eq_one hi
  have hd := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_mul, mul_comm S.det] at hd
  have he := mul_right_cancel₀ hn hd
  change determinantValue (Sum.elim a a) (Sum.elim b b) (realOrthogonalDouble U) =
    (A + V * B * Vᴴ).det at he
  rw [he]
  have hf : (A + V * B * Vᴴ).det = determinantValue a b U * determinantValue a b Uᴴᵀ := by
    simp only [A, B, V, splitMixer, splitPair, fromBlocks_conjTranspose, fromBlocks_multiply,
      Matrix.conjTranspose_zero, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add,
      fromBlocks_add, det_fromBlocks_zero₂₁, determinantValue]
  rw [hf, determinant_conjugate_mixer, pow_two]

end
end MOC
