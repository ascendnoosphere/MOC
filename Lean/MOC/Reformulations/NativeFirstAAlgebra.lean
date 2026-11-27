import MOC.Reformulations.FirstMatrix
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Determinant

/-! Native finite algebra constructions. The determinant here is the one
of the actual regular multiplication map in the chosen orthonormal coordinates. -/

open BigOperators Matrix

namespace MOC.Reformulations

noncomputable section

private theorem leftRegularPi {n : ℕ} (a : Fin n → ℂ) :
    Algebra.leftMulMatrix (Pi.basisFun ℂ (Fin n)) a = diagonal a := by
  ext i j
  rw [Algebra.leftMulMatrix_eq_repr_mul, Pi.basisFun_repr, Pi.basisFun_apply]
  by_cases hij : i = j
  · subst j
    simp [Pi.mul_apply, Pi.single_apply]
  · simp [Matrix.diagonal_apply_ne a hij, Pi.mul_apply, Pi.single_apply, hij, Ne.symm hij]

private theorem diagonal_normal {n : ℕ} (a : Fin n → ℂ) : IsStarNormal (diagonal a) := by
  constructor
  change Commute (diagonal a)ᴴ (diagonal a)
  rw [Matrix.diagonal_conjTranspose, Commute, SemiconjBy, Matrix.diagonal_mul_diagonal,
    Matrix.diagonal_mul_diagonal]
  exact congrArg Matrix.diagonal (funext fun i => mul_comm _ _)

private theorem diagonal_charpoly_roots {n : ℕ} (a : Fin n → ℂ) :
    (diagonal a).charpoly.roots = (Finset.univ : Finset (Fin n)).val.map a := by
  have hOne : IsUnitary (1 : Matrix (Fin n) (Fin n) ℂ) := isUnitary_one
  simpa using roots_unitary_diagonalization a hOne

/-- Every finite complex algebra is represented on itself by left
multiplication, and the basis fixes its Hermitian inner product. -/
def nativeLeftRegularAlgebra : Prop :=
  ∀ (n : ℕ) (A : Type) [Ring A] [Algebra ℂ A]
    (e : Basis (Fin n) ℂ A) (x y : A) (U : Matrix (Fin n) (Fin n) ℂ)
    (a b : Fin n → ℂ),
    IsStarNormal (Algebra.leftMulMatrix e x) →
    IsStarNormal (Algebra.leftMulMatrix e y) → IsUnitary U →
    (Algebra.leftMulMatrix e x).charpoly.roots = (Finset.univ : Finset (Fin n)).val.map a →
    (Algebra.leftMulMatrix e y).charpoly.roots = (Finset.univ : Finset (Fin n)).val.map b →
    (Algebra.leftMulMatrix e x + U * Algebra.leftMulMatrix e y * Uᴴ).det ∈
      convexHull ℝ (Set.range (matchingProduct a b))

theorem moc_iff_nativeLeftRegularAlgebra : MOCIsTrue ↔ nativeLeftRegularAlgebra := by
  constructor
  · intro h n A _ _ e x y U a b hX hY hU ha hb
    exact moc_iff_complexMatrices.mp h n _ _ U a b hX hY hU ha hb
  · intro h n a b U hU
    have hx := leftRegularPi a
    have hy := leftRegularPi b
    have hr := h n (Fin n → ℂ) (Pi.basisFun ℂ (Fin n)) a b U a b
      (hx.symm ▸ diagonal_normal a) (hy.symm ▸ diagonal_normal b) hU
      (hx.symm ▸ diagonal_charpoly_roots a) (hy.symm ▸ diagonal_charpoly_roots b)
    rw [hx, hy] at hr
    exact hr

/-- In a split finite commutative algebra, the norm of the sum equals the
identity matching product. The proof uses the coordinate characters of
the split algebra. -/
theorem splitCoordinateAlgebraNorm {n : ℕ} (a b : Fin n → ℂ) :
    (LinearMap.det (Algebra.lmul ℂ (Fin n → ℂ) (a + b))) = matchingProduct a b 1 := by
  rw [← LinearMap.det_toMatrix (Pi.basisFun ℂ (Fin n))]
  change (Algebra.leftMulMatrix (Pi.basisFun ℂ (Fin n)) (a + b)).det = _
  rw [leftRegularPi, Matrix.det_diagonal]
  rfl

theorem splitCoordinateAlgebraNorm_mem_hull {n : ℕ} (a b : Fin n → ℂ) :
    (LinearMap.det (Algebra.lmul ℂ (Fin n → ℂ) (a + b))) ∈ convexHull ℝ (Set.range (matchingProduct a b)) := by
  rw [splitCoordinateAlgebraNorm]
  exact subset_convexHull ℝ _ ⟨1, rfl⟩

/-- The defining nondegeneracy of the bilinear form `(x,y) ↦ f (x*y)`. -/
def IsFrobeniusFunctional {A : Type} [Ring A] [Algebra ℂ A] (f : A →ₗ[ℂ] ℂ) : Prop :=
  (∀ x, (∀ y, f (x * y) = 0) → x = 0) ∧
  (∀ y, (∀ x, f (x * y) = 0) → y = 0)

private def coordinateSum (n : ℕ) : (Fin n → ℂ) →ₗ[ℂ] ℂ :=
  ∑ i, LinearMap.proj i

private theorem coordinateSum_mul_single {n : ℕ} (a : Fin n → ℂ) (i : Fin n) :
    coordinateSum n (a * Pi.single i 1) = a i := by
  simp only [coordinateSum, LinearMap.sum_apply, LinearMap.proj_apply, Pi.mul_apply,
    Pi.single_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [hji, hji.symm]
  · simp

private theorem coordinateSum_frobenius (n : ℕ) :
    IsFrobeniusFunctional (coordinateSum n) := by
  constructor
  · intro a ha
    funext i
    simpa only [coordinateSum_mul_single, Pi.zero_apply] using ha (Pi.single i 1)
  · intro a ha
    funext i
    simpa only [mul_comm (Pi.single i 1) a, coordinateSum_mul_single, Pi.zero_apply] using
      ha (Pi.single i 1)

/-- The regular matrix comparison for a finite complex Frobenius algebra.
The Frobenius functional forms part of the algebra data. -/
def nativeFrobeniusAlgebra : Prop :=
  ∀ (n : ℕ) (A : Type) [Ring A] [Algebra ℂ A]
    (f : A →ₗ[ℂ] ℂ), IsFrobeniusFunctional f →
    ∀ (e : Basis (Fin n) ℂ A) (x y : A) (U : Matrix (Fin n) (Fin n) ℂ)
      (a b : Fin n → ℂ),
    IsStarNormal (Algebra.leftMulMatrix e x) →
    IsStarNormal (Algebra.leftMulMatrix e y) → IsUnitary U →
    (Algebra.leftMulMatrix e x).charpoly.roots = (Finset.univ : Finset (Fin n)).val.map a →
    (Algebra.leftMulMatrix e y).charpoly.roots = (Finset.univ : Finset (Fin n)).val.map b →
    (Algebra.leftMulMatrix e x + U * Algebra.leftMulMatrix e y * Uᴴ).det ∈
      convexHull ℝ (Set.range (matchingProduct a b))

theorem moc_iff_nativeFrobeniusAlgebra : MOCIsTrue ↔ nativeFrobeniusAlgebra := by
  constructor
  · intro h n A _ _ f hf e x y U a b hX hY hU ha hb
    exact moc_iff_nativeLeftRegularAlgebra.mp h n A e x y U a b hX hY hU ha hb
  · intro h n a b U hU
    have hx := leftRegularPi a
    have hy := leftRegularPi b
    have hr := h n (Fin n → ℂ) (coordinateSum n) (coordinateSum_frobenius n)
      (Pi.basisFun ℂ (Fin n)) a b U a b
      (hx.symm ▸ diagonal_normal a) (hy.symm ▸ diagonal_normal b) hU
      (hx.symm ▸ diagonal_charpoly_roots a) (hy.symm ▸ diagonal_charpoly_roots b)
    rw [hx, hy] at hr
    exact hr

end

end MOC.Reformulations
