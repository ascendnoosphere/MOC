import MOC.Hermitian
import Mathlib.LinearAlgebra.Matrix.PosDef

/-! Actual Hermitian, positive-definite, circle and Gram restrictions. -/

open BigOperators Matrix
open scoped ComplexOrder

namespace MOC.Reformulations
noncomputable section

/-- The Hermitian determinant hull for real spectra. -/
theorem hermitianSpectralHull {n : ℕ} (a b : Fin n → ℝ)
    (U : Matrix (Fin n) (Fin n) ℂ) (hU : IsUnitary U) :
    Holds (fun i => (a i : ℂ)) (fun i => (b i : ℂ)) U :=
  holds_of_real_spectra a b U hU

/-- The determinant hull for two positive spectra. -/
theorem positiveDefiniteSpectralHull {n : ℕ} (a b : Fin n → ℝ)
    (_ha : ∀ i, 0 < a i) (_hb : ∀ i, 0 < b i)
    (U : Matrix (Fin n) (Fin n) ℂ) (hU : IsUnitary U) :
    Holds (fun i => (a i : ℂ)) (fun i => (b i : ℂ)) U :=
  hermitianSpectralHull a b U hU

/-- Actual Hermitian matrix comparison. The canonical real spectral lists
come from the spectral theorem and need no normality assumption beyond
Hermitian symmetry. -/
theorem hermitianMatrixHull {n : ℕ} (A B U : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.IsHermitian) (hB : B.IsHermitian) (hU : IsUnitary U) :
    (A + U * B * Uᴴ).det ∈ convexHull ℝ
      (Set.range (matchingProduct
        (fun i => (hA.eigenvalues i : ℂ)) (fun i => (hB.eigenvalues i : ℂ)))) := by
  let V : Matrix (Fin n) (Fin n) ℂ := hA.eigenvectorUnitary
  let W : Matrix (Fin n) (Fin n) ℂ := hB.eigenvectorUnitary
  have hV : IsUnitary V :=
    ⟨Matrix.mem_unitaryGroup_iff.mp hA.eigenvectorUnitary.2,
      Matrix.mem_unitaryGroup_iff'.mp hA.eigenvectorUnitary.2⟩
  have hW : IsUnitary W :=
    ⟨Matrix.mem_unitaryGroup_iff.mp hB.eigenvectorUnitary.2,
      Matrix.mem_unitaryGroup_iff'.mp hB.eigenvectorUnitary.2⟩
  have hUt : IsUnitary Uᴴ :=
    ⟨by simpa only [Matrix.conjTranspose_conjTranspose] using hU.2,
      by simpa only [Matrix.conjTranspose_conjTranspose] using hU.1⟩
  have hUW : IsUnitary (U * W) := by
    simpa only [Matrix.conjTranspose_conjTranspose] using relative_unitary Uᴴ W hUt hW
  let a (i : Fin n) : ℂ := hA.eigenvalues i
  let b (i : Fin n) : ℂ := hB.eigenvalues i
  have ha : A = V * diagonal a * Vᴴ := hA.spectral_theorem
  have hb : B = W * diagonal b * Wᴴ := hB.spectral_theorem
  have he : U * B * Uᴴ = (U * W) * diagonal b * (U * W)ᴴ := by
    rw [hb]
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  have hv : (A + U * B * Uᴴ).det = determinantValue a b (Vᴴ * (U * W)) := by
    rw [he, ha, determinantValue_relative a b V (U * W) hV]
  change (A + U * B * Uᴴ).det ∈ convexHull ℝ (Set.range (matchingProduct a b))
  rw [hv]
  exact holds_of_real_spectra hA.eigenvalues hB.eigenvalues _ (relative_unitary V _ hV hUW)

/-- The determinant hull for two positive definite matrices. -/
theorem positiveDefiniteMatrixHull {n : ℕ} (A B U : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.PosDef) (hB : B.PosDef) (hU : IsUnitary U) :
    (A + U * B * Uᴴ).det ∈ convexHull ℝ
      (Set.range (matchingProduct
        (fun i => (hA.isHermitian.eigenvalues i : ℂ))
        (fun i => (hB.isHermitian.eigenvalues i : ℂ)))) :=
  hermitianMatrixHull A B U hA.isHermitian hB.isHermitian hU

/-- The determinant hull for Gram matrices of rectangular maps.
The Hermitian theorem applies to their squared singular values. -/
theorem gramMatrixHull {n p q : ℕ}
    (X : Matrix (Fin p) (Fin n) ℂ) (Y : Matrix (Fin q) (Fin n) ℂ)
    (U : Matrix (Fin n) (Fin n) ℂ) (hU : IsUnitary U) :
    (Xᴴ * X + U * (Yᴴ * Y) * Uᴴ).det ∈ convexHull ℝ
      (Set.range (matchingProduct
        (fun i => ((Matrix.isHermitian_transpose_mul_self X).eigenvalues i : ℂ))
        (fun i => ((Matrix.isHermitian_transpose_mul_self Y).eigenvalues i : ℂ)))) :=
  hermitianMatrixHull _ _ U (Matrix.isHermitian_transpose_mul_self X)
    (Matrix.isHermitian_transpose_mul_self Y) hU

/-- The determinant hull for the positive semidefinite square roots of
rectangular Gram matrices. -/
theorem rectangularAbsoluteHull {n p q : ℕ}
    (X : Matrix (Fin p) (Fin n) ℂ) (Y : Matrix (Fin q) (Fin n) ℂ)
    (U : Matrix (Fin n) (Fin n) ℂ) (hU : IsUnitary U) :
    let hX := Matrix.posSemidef_conjTranspose_mul_self X
    let hY := Matrix.posSemidef_conjTranspose_mul_self Y
    (hX.sqrt + U * hY.sqrt * Uᴴ).det ∈ convexHull ℝ
      (Set.range (matchingProduct
        (fun i => ((hX.posSemidef_sqrt.isHermitian).eigenvalues i : ℂ))
        (fun i => ((hY.posSemidef_sqrt.isHermitian).eigenvalues i : ℂ)))) := by
  dsimp
  exact hermitianMatrixHull _ _ U
    (Matrix.posSemidef_conjTranspose_mul_self X).posSemidef_sqrt.isHermitian
    (Matrix.posSemidef_conjTranspose_mul_self Y).posSemidef_sqrt.isHermitian hU

/-- The hull for purely imaginary spectra. Skew-symmetric real matrices
have purely imaginary complex spectra; the direction comparison holds for
arbitrary unitary mixing of those lists, without a Pfaffian strengthening. -/
theorem imaginarySpectralHull {n : ℕ} (a b : Fin n → ℝ)
    (U : Matrix (Fin n) (Fin n) ℂ) (hU : IsUnitary U) :
    Holds (fun i => Complex.I * (a i : ℂ)) (fun i => Complex.I * (b i : ℂ)) U := by
  simpa only [add_zero, sub_zero] using holds_of_common_affine_line a b Complex.I 0 U hU

end
end MOC.Reformulations
