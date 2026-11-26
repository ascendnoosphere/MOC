import MOC.GrassmannianImageStars
import MOC.BivectorPhaseFactorization
import MOC.Core
import Mathlib.LinearAlgebra.Matrix.Trace

/-! The induced action of an order-five unitary on skew bivectors. -/

open BigOperators Matrix

namespace MOC

private theorem congruence_skew (U : GrassmannianMatrix) (A : bivectorSkewSpace) :
    U * (A : GrassmannianMatrix) * Uᵀ ∈ bivectorSkewSpace := by
  have hA : (A : GrassmannianMatrix)ᵀ = -(A : GrassmannianMatrix) :=
    Matrix.ext fun i j => A.property i j
  have he : (U * (A : GrassmannianMatrix) * Uᵀ)ᵀ = -(U * (A : GrassmannianMatrix) * Uᵀ) := by
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, hA, Matrix.mul_neg,
      Matrix.neg_mul, Matrix.mul_assoc]
  exact fun i j => congrArg (fun B : GrassmannianMatrix => B i j) he

private def bivectorCongruence (U : GrassmannianMatrix) : bivectorSkewSpace →ₗ[ℂ] bivectorSkewSpace where
  toFun A := ⟨U * (A : GrassmannianMatrix) * Uᵀ, congruence_skew U A⟩
  map_add' A B := by
    apply Subtype.ext
    change U * ((A : GrassmannianMatrix) + (B : GrassmannianMatrix)) * Uᵀ = _
    simp only [Matrix.mul_add, Matrix.add_mul] <;> rfl
  map_smul' c A := by
    apply Subtype.ext
    change U * (c • (A : GrassmannianMatrix)) * Uᵀ = _
    simp only [Matrix.mul_smul, Matrix.smul_mul] <;> rfl

private theorem bivectorCongruence_apply_apply (U V : GrassmannianMatrix) (A : bivectorSkewSpace) :
    (bivectorCongruence V (bivectorCongruence U A) : GrassmannianMatrix) =
      (V * U) * (A : GrassmannianMatrix) * (V * U)ᵀ := by
  change V * (U * (A : GrassmannianMatrix) * Uᵀ) * Vᵀ = _
  simp only [Matrix.transpose_mul, Matrix.mul_assoc]

/-- A unitary on the vector space induces congruence on skew matrices. -/
def grassmannianUnitaryAction (U : GrassmannianMatrix) (hU : IsUnitary U) :
    bivectorSkewSpace ≃ₗ[ℂ] bivectorSkewSpace where
  toLinearMap := bivectorCongruence U
  invFun := bivectorCongruence Uᴴ
  left_inv A := by
    apply Subtype.ext
    change (bivectorCongruence Uᴴ (bivectorCongruence U A) : GrassmannianMatrix) = _
    rw [bivectorCongruence_apply_apply, hU.2, Matrix.one_mul, Matrix.transpose_one, Matrix.mul_one]
  right_inv A := by
    apply Subtype.ext
    change (bivectorCongruence U (bivectorCongruence Uᴴ A) : GrassmannianMatrix) = _
    rw [bivectorCongruence_apply_apply, hU.1, Matrix.one_mul, Matrix.transpose_one, Matrix.mul_one]

private theorem bivectorMatrixPair_eq_trace (A B : GrassmannianMatrix) :
    bivectorMatrixPair A B = (Aᴴ * B).trace := by
  simp only [bivectorMatrixPair, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply]
  exact Finset.sum_comm

private theorem bivectorCongruence_pair (U : GrassmannianMatrix) (hU : IsUnitary U)
    (A B : GrassmannianMatrix) :
    bivectorMatrixPair (U * A * Uᵀ) (U * B * Uᵀ) = bivectorMatrixPair A B := by
  have htrans : (Uᴴ)ᵀ = (Uᵀ)ᴴ := by ext i j; rfl
  have hUT : Uᵀ * (Uᵀ)ᴴ = 1 := by
    simpa only [Matrix.transpose_mul, Matrix.transpose_one, htrans] using congrArg Matrix.transpose hU.2
  have he : (U * A * Uᵀ)ᴴ * (U * B * Uᵀ) = (Uᵀ)ᴴ * (Aᴴ * B) * Uᵀ := by
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Uᴴ U, hU.2, Matrix.one_mul]
  rw [bivectorMatrixPair_eq_trace, bivectorMatrixPair_eq_trace, he, Matrix.trace_mul_cycle,
    hUT, Matrix.one_mul]

/-- Every order-five unitary gives a skew-space cone preserver that
preserves the Frobenius pairing and acts on both factors of each wedge. -/
theorem exists_grassmannian_preserver_of_unitary (U : GrassmannianMatrix) (hU : IsUnitary U) :
    ∃ W : bivectorSkewSpace ≃ₗ[ℂ] bivectorSkewSpace,
      (∀ A : bivectorSkewSpace, PluckerBivector (A : GrassmannianMatrix) →
        PluckerBivector (W A : GrassmannianMatrix)) ∧
      (∀ A B : bivectorSkewSpace, bivectorMatrixPair (W A) (W B) = bivectorMatrixPair A B) ∧
      ∀ x y : GrassmannianVector, (W (bivectorSkew x y) : GrassmannianMatrix) =
        bivectorMatrix (U *ᵥ x) (U *ᵥ y) := by
  refine ⟨grassmannianUnitaryAction U hU, ?_, ?_, ?_⟩
  · intro A hA
    obtain ⟨x, y, h⟩ := (pluckerBivector_iff_decomposable _).mp hA
    change PluckerBivector (U * (A : GrassmannianMatrix) * Uᵀ)
    rw [h, bivectorMatrix_congr]
    exact (pluckerBivector_iff_decomposable _).mpr ⟨_, _, rfl⟩
  · exact fun A B => bivectorCongruence_pair U hU A B
  · exact bivectorMatrix_congr U

end MOC
