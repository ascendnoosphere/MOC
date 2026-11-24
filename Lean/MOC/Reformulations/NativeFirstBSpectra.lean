import MOC.Reformulations.NativeFirstB
import Mathlib.LinearAlgebra.Quotient.Basic

/-! Native finite Laplacians, finite specialization, and degree-zero
Hochschild blocks. These are actual operator constructions, not arbitrary
spectral recodings. The degree-zero results do not replace higher homology. -/

open BigOperators Matrix

namespace MOC.Reformulations.NativeFirstB

noncomputable section

/-- The chain Laplacian `dPlusdPlus† + dMinus†dMinus` on the given oriented chain basis. -/
def chainLaplacian {n p q : ℕ} (dPlus : Matrix (Fin n) (Fin p) ℂ)
    (dMinus : Matrix (Fin q) (Fin n) ℂ) : Mat n :=
  dPlus * dPlusᴴ + dMinusᴴ * dMinus

theorem chainLaplacian_hermitian {n p q : ℕ} (dPlus : Matrix (Fin n) (Fin p) ℂ)
    (dMinus : Matrix (Fin q) (Fin n) ℂ) : (chainLaplacian dPlus dMinus).IsHermitian := by
  change (chainLaplacian dPlus dMinus)ᴴ = _
  simp [chainLaplacian, Matrix.conjTranspose_add, Matrix.conjTranspose_mul]

/-- 076: the actual Laplacian on a simplicial chain space; the roots
include any harmonic zero modes. -/
theorem simplicialLaplacianHull {n p q : ℕ}
    (dPlus ePlus : Matrix (Fin n) (Fin p) ℂ) (dMinus eMinus : Matrix (Fin q) (Fin n) ℂ)
    (U : Mat n) (hU : IsUnitary U) (a b : Fin n → ℝ)
    (ha : HasRoots (chainLaplacian dPlus dMinus) (fun j => a j))
    (hb : HasRoots (chainLaplacian ePlus eMinus) (fun j => b j)) :
    OperatorHull (chainLaplacian dPlus dMinus) (chainLaplacian ePlus eMinus) U
      (fun j => a j) (fun j => b j) :=
  diracBlockHull _ _ _ _ _ (chainLaplacian_hermitian dPlus dMinus)
    (chainLaplacian_hermitian ePlus eMinus) hU ha hb

/-- 080: the chosen positive eigenmode blocks of two Hodge Laplacians.
A rectangular isometry records each chosen orthonormal spectral window.
The conclusion concerns the compression, without a zeta determinant. -/
theorem hodgeWindowHull {m p n : ℕ} (A : Mat m) (B : Mat p)
    (V : Matrix (Fin m) (Fin n) ℂ) (W : Matrix (Fin p) (Fin n) ℂ)
    (_hV : Vᴴ * V = 1) (_hW : Wᴴ * W = 1)
    (hA : A.IsHermitian) (hB : B.IsHermitian) (U : Mat n) (hU : IsUnitary U)
    (a b : Fin n → ℝ) (_ha₀ : ∀ j, 0 < a j) (_hb₀ : ∀ j, 0 < b j)
    (ha : HasRoots (Vᴴ * A * V) (fun j => a j))
    (hb : HasRoots (Wᴴ * B * W) (fun j => b j)) :
    OperatorHull (Vᴴ * A * V) (Wᴴ * B * W) U (fun j => a j) (fun j => b j) := by
  apply diracBlockHull _ _ _ _ _ _ _ hU ha hb
  · change (Vᴴ * A * V)ᴴ = _
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      hA.eq, Matrix.mul_assoc]
  · change (Wᴴ * B * W)ᴴ = _
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      hB.eq, Matrix.mul_assoc]

/-- 089: specialize the actual finite free coefficient matrices at the
given ring character. Normality is required after specialization. -/
theorem equivariantSpecializationHull (h : MOCIsTrue) {R : Type*} [CommRing R]
    {n : ℕ} (χ : R →+* ℂ) (A B : Matrix (Fin n) (Fin n) R) (U : Mat n)
    (a b : Fin n → ℂ) (hA : IsStarNormal (χ.mapMatrix A))
    (hB : IsStarNormal (χ.mapMatrix B)) (hU : IsUnitary U)
    (ha : HasRoots (χ.mapMatrix A) a) (hb : HasRoots (χ.mapMatrix B) b) :
    OperatorHull (χ.mapMatrix A) (χ.mapMatrix B) U a b :=
  operatorHull_of_moc h _ _ _ _ _ hA hB hU ha hb

/-- 090 finite matrix case, with normalized log determinant and
permutation couplings of the equally weighted spectral occurrences. -/
theorem finiteNormalizedPositiveDeterminantBounds {n : ℕ} (a b : Fin n → ℝ)
    (ha : ∀ j, 0 < a j) (hb : ∀ j, 0 < b j) (U : Mat n) (hU : IsUnitary U) :
    let d := (determinantValue (fun j => (a j : ℂ)) (fun j => (b j : ℂ)) U).re
    ∃ lo hi : Equiv.Perm (Fin n),
      Real.exp ((∑ j, Real.log (a (lo j) + b j)) / n) ≤ Real.exp (Real.log d / n) ∧
      Real.exp (Real.log d / n) ≤ Real.exp ((∑ j, Real.log (a (hi j) + b j)) / n) := by
  obtain ⟨_, lo, hi, hlo, hhi⟩ := positiveRealSpectra_log_bounds a b ha hb U hU
  exact ⟨lo, hi,
    Real.exp_le_exp.mpr (div_le_div_of_nonneg_right hlo (Nat.cast_nonneg n)),
    Real.exp_le_exp.mpr (div_le_div_of_nonneg_right hhi (Nat.cast_nonneg n))⟩

/-- A finite, nondegenerate persistence interval. -/
structure BarcodeInterval where
  birth : ℝ
  death : ℝ
  nondegenerate : birth < death

def BarcodeInterval.lifetime (i : BarcodeInterval) : ℝ := i.death - i.birth

/-- 091: native barcode lifetime operators. The mixing is not asserted
to be a morphism of persistence modules. -/
theorem barcodeLifetimeHull {n : ℕ} (a b : Fin n → BarcodeInterval)
    (U : Mat n) (hU : IsUnitary U) :
    Holds (fun j => (a j).lifetime) (fun j => (b j).lifetime) U :=
  holds_of_real_spectra (fun j => (a j).lifetime) (fun j => (b j).lifetime) U hU

/-- The vector span of commutators, defining the degree-zero Hochschild
homology quotient as a vector space, not as a quotient ring. -/
def linearCommutatorSpan (R : Type*) [Ring R] [Algebra ℂ R] : Submodule ℂ R :=
  Submodule.span ℂ {z | ∃ x y : R, z = x * y - y * x}

def degreeZeroHochschildAction {R : Type*} [Ring R] [Algebra ℂ R] (f : R →ₐ[ℂ] R) :
    (R ⧸ linearCommutatorSpan R) →ₗ[ℂ] (R ⧸ linearCommutatorSpan R) :=
  (linearCommutatorSpan R).mapQ (linearCommutatorSpan R) f.toLinearMap (by
    apply Submodule.span_le.mpr
    rintro _ ⟨x, y, rfl⟩
    change f (x * y - y * x) ∈ linearCommutatorSpan R
    rw [map_sub, map_mul, map_mul]
    exact Submodule.subset_span ⟨f x, f y, rfl⟩)

/-- 086 in degree zero (also the degree-zero cyclic quotient of 088). -/
theorem degreeZeroHochschildHull (h : MOCIsTrue) {R : Type*} [Ring R] [Algebra ℂ R]
    {n : ℕ} (e : Basis (Fin n) ℂ (R ⧸ linearCommutatorSpan R)) (f g : R →ₐ[ℂ] R)
    (U : Mat n) (a b : Fin n → ℂ)
    (hA : IsStarNormal (LinearMap.toMatrix e e (degreeZeroHochschildAction f)))
    (hB : IsStarNormal (LinearMap.toMatrix e e (degreeZeroHochschildAction g)))
    (hU : IsUnitary U)
    (ha : HasRoots (LinearMap.toMatrix e e (degreeZeroHochschildAction f)) a)
    (hb : HasRoots (LinearMap.toMatrix e e (degreeZeroHochschildAction g)) b) :
    OperatorHull (LinearMap.toMatrix e e (degreeZeroHochschildAction f))
      (LinearMap.toMatrix e e (degreeZeroHochschildAction g)) U a b :=
  operatorHull_of_moc h _ _ _ _ _ hA hB hU ha hb

/-- 087 in degree zero: an algebra automorphism acts on the center. -/
def centerAutomorphismAction {R : Type*} [Ring R] [Algebra ℂ R] (f : R ≃ₐ[ℂ] R) :
    Subalgebra.center ℂ R →ₗ[ℂ] Subalgebra.center ℂ R where
  toFun x := ⟨f x, by
    apply Subalgebra.mem_center_iff.mpr
    intro y
    obtain ⟨z, rfl⟩ := f.surjective y
    rw [← map_mul, ← map_mul, (Subalgebra.mem_center_iff.mp x.property) z]⟩
  map_add' _ _ := Subtype.ext (map_add f _ _)
  map_smul' _ _ := Subtype.ext (map_smul f _ _)

theorem degreeZeroHochschildCohomologyHull (h : MOCIsTrue)
    {R : Type*} [Ring R] [Algebra ℂ R] {n : ℕ}
    (e : Basis (Fin n) ℂ (Subalgebra.center ℂ R)) (f g : R ≃ₐ[ℂ] R)
    (U : Mat n) (a b : Fin n → ℂ)
    (hA : IsStarNormal (LinearMap.toMatrix e e (centerAutomorphismAction f)))
    (hB : IsStarNormal (LinearMap.toMatrix e e (centerAutomorphismAction g)))
    (hU : IsUnitary U)
    (ha : HasRoots (LinearMap.toMatrix e e (centerAutomorphismAction f)) a)
    (hb : HasRoots (LinearMap.toMatrix e e (centerAutomorphismAction g)) b) :
    OperatorHull (LinearMap.toMatrix e e (centerAutomorphismAction f))
      (LinearMap.toMatrix e e (centerAutomorphismAction g)) U a b :=
  operatorHull_of_moc h _ _ _ _ _ hA hB hU ha hb

end

end MOC.Reformulations.NativeFirstB
