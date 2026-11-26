import MOC.SpectralDeterminantStability
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Block

/-! The determinant-side identities for normalized Pfaffians of skew-unitaries. -/

open BigOperators Matrix
open scoped ComplexOrder

namespace MOC

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The bipartite skew matrix associated to a relative unitary mixer. -/
def bipartiteSkewMixer (U : Matrix ι ι ℂ) : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ :=
  Matrix.fromBlocks 0 U (-Uᵀ) 0

theorem transpose_bipartiteSkewMixer (U : Matrix ι ι ℂ) :
    (bipartiteSkewMixer U)ᵀ = -bipartiteSkewMixer U := by
  simp [bipartiteSkewMixer, Matrix.fromBlocks_transpose, Matrix.fromBlocks_neg]

theorem isUnitary_bipartiteSkewMixer (U : Matrix ι ι ℂ) (hU : IsUnitary U) :
    IsUnitary (bipartiteSkewMixer U) := by
  have hs : (Uᵀ)ᴴ = (Uᴴ)ᵀ := by
    ext i j : 1
    rfl
  have h₁ : Uᵀ * (Uᵀ)ᴴ = 1 := by
    rw [hs, ← Matrix.transpose_mul, hU.2, Matrix.transpose_one]
  have h₂ : (Uᵀ)ᴴ * Uᵀ = 1 := by
    rw [hs, ← Matrix.transpose_mul, hU.1, Matrix.transpose_one]
  constructor <;> simp [bipartiteSkewMixer, Matrix.fromBlocks_conjTranspose,
    Matrix.fromBlocks_multiply, Matrix.fromBlocks_one, hU.1, hU.2, h₁, h₂]

/-- The off-diagonal block of the bipartite pencil is the usual
entrywise spectral-sum kernel. -/
theorem bipartiteSkewMixer_pencil (U : Matrix ι ι ℂ) (a b : ι → ℂ) :
    let D := Matrix.diagonal (Sum.elim a b)
    let M := Matrix.diagonal a * U + U * Matrix.diagonal b
    bipartiteSkewMixer U * D + D * bipartiteSkewMixer U =
      Matrix.fromBlocks 0 M (-Mᵀ) 0 := by
  dsimp only [bipartiteSkewMixer]
  rw [← Matrix.fromBlocks_diagonal]
  simp only [Matrix.fromBlocks_multiply, Matrix.fromBlocks_add, Matrix.zero_mul,
    Matrix.mul_zero, zero_add, add_zero, Matrix.transpose_add, Matrix.transpose_mul,
    Matrix.diagonal_transpose, Matrix.neg_mul, Matrix.mul_neg, neg_add]
  rw [add_comm (U * Matrix.diagonal b)]

/-- If a Pfaffian satisfies its square identity, the square of its
normalized value is the spectral determinant with repeated labels. -/
theorem normalizedPfaffian_sq_of_square_identity (pf : Matrix ι ι ℂ → ℂ)
    (hpf : ∀ M : Matrix ι ι ℂ, Mᵀ = -M → pf M ^ 2 = M.det)
    (J : Matrix ι ι ℂ) (hJ : IsUnitary J) (hskew : Jᵀ = -J) (z : ι → ℂ) :
    (pf (J * Matrix.diagonal z + Matrix.diagonal z * J) / pf J) ^ 2 =
      determinantValue z z Jᴴ := by
  let D := Matrix.diagonal z
  have hD : Dᵀ = D := Matrix.diagonal_transpose z
  have hM : (J * D + D * J)ᵀ = -(J * D + D * J) := by
    simp only [Matrix.transpose_add, Matrix.transpose_mul, hD, hskew, Matrix.mul_neg,
      Matrix.neg_mul, neg_add, add_comm]
  have hfactor : J * (D + Jᴴ * D * J) = J * D + D * J := by
    rw [Matrix.mul_add, ← Matrix.mul_assoc J (Jᴴ * D) J, ← Matrix.mul_assoc J Jᴴ D,
      hJ.1, Matrix.one_mul]
  change (pf (J * D + D * J) / pf J) ^ 2 = (D + Jᴴ * D * Jᴴᴴ).det
  rw [div_pow, hpf _ hM, hpf _ hskew, Matrix.conjTranspose_conjTranspose,
    ← hfactor, Matrix.det_mul]
  exact mul_div_cancel_left₀ _ (det_ne_zero_of_unitary hJ)

/-- The square identity and the determinant half-plane theorem prove
nonvanishing of the normalized Pfaffian on the product of upper half-planes. -/
theorem normalizedPfaffian_ne_zero_of_im_pos (pf : Matrix ι ι ℂ → ℂ)
    (hpf : ∀ M : Matrix ι ι ℂ, Mᵀ = -M → pf M ^ 2 = M.det)
    (J : Matrix ι ι ℂ) (hJ : IsUnitary J) (hskew : Jᵀ = -J) (z : ι → ℂ)
    (hz : ∀ i, 0 < (z i).im) :
    pf (J * Matrix.diagonal z + Matrix.diagonal z * J) / pf J ≠ 0 := by
  intro hh
  have he := normalizedPfaffian_sq_of_square_identity pf hpf J hJ hskew z
  rw [hh, zero_pow (by norm_num : 2 ≠ 0)] at he
  exact determinantValue_ne_zero_of_im_pos z z Jᴴ hz (fun i => (hz i).le) he.symm

/-- On positive real labels, the determinant on the square side is positive. -/
theorem repeated_spectral_determinant_pos (J : Matrix ι ι ℂ) (x : ι → ℝ)
    (hx : ∀ i, 0 < x i) :
    0 < determinantValue (fun i => (x i : ℂ)) (fun i => (x i : ℂ)) Jᴴ := by
  let D := Matrix.diagonal (fun i => (x i : ℂ))
  have hD : D.PosDef := Matrix.PosDef.diagonal fun i => Complex.zero_lt_real.mpr (hx i)
  have hcong : (Jᴴ * D * J).PosSemidef := hD.posSemidef.conjTranspose_mul_mul_same J
  change 0 < (D + Jᴴ * D * Jᴴᴴ).det
  rw [Matrix.conjTranspose_conjTranspose]
  exact (hD.add_posSemidef hcong).det_pos

end MOC
