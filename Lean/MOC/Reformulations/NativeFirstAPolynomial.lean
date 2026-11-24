import MOC.Reformulations.FirstMatrix
import Mathlib.LinearAlgebra.Determinant

/-! Matrix polynomial roots and the top alternating action. -/

open BigOperators Matrix Polynomial

namespace MOC.Reformulations
noncomputable section

/-- Leading coefficient equal to the identity, with all higher coefficients zero. -/
def IsMonicMatrixPolynomial {n : ℕ} (m : ℕ) (P : Matrix (Fin n) (Fin n) ℂ[X]) : Prop :=
  (∀ i j, (P i j).coeff m = if i = j then 1 else 0) ∧
    ∀ k, m < k → ∀ i j, (P i j).coeff k = 0

/-- Atlas 010, using its explicitly allowed diagonal root realization rather than
assuming a companion matrix is normal. The roots are roots of actual polynomial
matrix determinants with the prescribed monic matrix degree. -/
def nativeMonicMatrixPolynomialRoots : Prop :=
  ∀ (m r : ℕ), 0 < m →
    ∀ (P Q : Matrix (Fin r) (Fin r) ℂ[X]),
    IsMonicMatrixPolynomial m P → IsMonicMatrixPolynomial m Q →
    ∀ (a b : Fin (m * r) → ℂ) (U : Matrix (Fin (m * r)) (Fin (m * r)) ℂ),
    P.det.roots = Finset.univ.val.map a → Q.det.roots = Finset.univ.val.map b →
    IsUnitary U → Holds a b U

private def linearPolynomialMatrix {r : ℕ} (a : Fin r → ℂ) :
    Matrix (Fin r) (Fin r) ℂ[X] :=
  diagonal (fun i => X - C (a i))

private theorem linearPolynomialMatrix_monic {r : ℕ} (a : Fin r → ℂ) :
    IsMonicMatrixPolynomial 1 (linearPolynomialMatrix a) := by
  constructor
  · intro i j
    by_cases h : i = j
    · subst j
      simp [linearPolynomialMatrix, Polynomial.coeff_sub, Polynomial.coeff_C]
    · simp [linearPolynomialMatrix, Matrix.diagonal_apply_ne _ h, h]
  · intro k hk i j
    have hk1 : k ≠ 1 := Nat.ne_of_gt hk
    have hk0 : k ≠ 0 := by omega
    by_cases h : i = j
    · subst j
      simp [linearPolynomialMatrix, Polynomial.coeff_sub, Polynomial.coeff_X, Polynomial.coeff_C,
        hk1, Ne.symm hk1, hk0, Ne.symm hk0]
    · simp [linearPolynomialMatrix, Matrix.diagonal_apply_ne _ h]

private theorem linearPolynomialMatrix_roots {r : ℕ} (a : Fin r → ℂ) :
    (linearPolynomialMatrix a).det.roots = Finset.univ.val.map a := by
  have hOne : IsUnitary (1 : Matrix (Fin r) (Fin r) ℂ) := by simp [IsUnitary]
  have hroots := roots_unitary_diagonalization a hOne
  have hpoly : (diagonal a).charpoly = (linearPolynomialMatrix a).det := by
    unfold Matrix.charpoly linearPolynomialMatrix
    congr 1
    ext i j
    by_cases h : i = j
    · subst j; simp [Matrix.charmatrix, Matrix.scalar]
    · simp [Matrix.charmatrix, Matrix.scalar, Matrix.diagonal_apply_ne _ h, h]
  simpa only [Matrix.one_mul, Matrix.mul_one, Matrix.conjTranspose_one, hpoly] using hroots

theorem moc_iff_nativeMonicMatrixPolynomialRoots :
    MOCIsTrue ↔ nativeMonicMatrixPolynomialRoots := by
  constructor
  · intro h m r _ P Q hP hQ a b U ha hb hU
    exact h (m * r) a b U hU
  · intro h r a b U hU
    -- Degree one realizes precisely the characteristic roots of every diagonal.
    have hr := h 1 r Nat.one_pos (linearPolynomialMatrix a) (linearPolynomialMatrix b)
      (linearPolynomialMatrix_monic a) (linearPolynomialMatrix_monic b)
    rw [one_mul] at hr
    exact hr a b U (linearPolynomialMatrix_roots a) (linearPolynomialMatrix_roots b) hU

/-- Coefficient of the top alternating coordinate on the standard frame.
`Basis.det_comp` is the universal top-exterior action identity. -/
def topAlternatingCoefficient {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  let e := Pi.basisFun ℂ (Fin n)
  e.det (A.toLin' ∘ e)

theorem topAlternatingCoefficient_eq_det {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    topAlternatingCoefficient A = A.det := by
  unfold topAlternatingCoefficient
  dsimp only
  rw [Basis.det_comp, Basis.det_self, mul_one, ← LinearMap.det_toMatrix',
    LinearMap.toMatrix'_toLin']

/-- Atlas 014 with the action on the top exterior line expressed as the top
alternating coefficient of the actual matrix sum, not a sum of two coefficients. -/
def nativeTopExteriorHull : Prop :=
  ∀ (n : ℕ) (A B U : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n → ℂ),
    IsStarNormal A → IsStarNormal B → IsUnitary U →
    A.charpoly.roots = Finset.univ.val.map a →
    B.charpoly.roots = Finset.univ.val.map b →
    topAlternatingCoefficient (A + U * B * Uᴴ) ∈
      convexHull ℝ (Set.range (matchingProduct a b))

theorem moc_iff_nativeTopExteriorHull : MOCIsTrue ↔ nativeTopExteriorHull := by
  simp only [nativeTopExteriorHull, topAlternatingCoefficient_eq_det]
  exact moc_iff_complexMatrices

end
end MOC.Reformulations
