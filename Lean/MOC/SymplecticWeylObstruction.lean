import MOC.Core
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Mathlib.Tactic.FinCases

/-! The Weyl group preserves the conjugate-pair matching products in this
order-four example, while a compact symplectic mixer changes the determinant. -/

namespace MOC

open Matrix

/-- The type `C₂` Weyl permutations in coordinates where indices at distance
two form a conjugate pair. The addition is modulo four. -/
def PreservesSymplecticPairs (σ : Equiv.Perm (Fin 4)) : Prop :=
  ∀ i, σ (i + 2) = σ i + 2

private def symplecticFirstLabels : Fin 4 → GaussianInt := ![-1, 1, -1, 1]

private def symplecticSecondLabels : Fin 4 → GaussianInt :=
  ![⟨-1, 2⟩, ⟨-1, 2⟩, ⟨-1, -2⟩, ⟨-1, -2⟩]

private def symplecticWitnessMixer : Matrix (Fin 4) (Fin 4) ℂ :=
  (1 / 2 : ℂ) • !![1, 1, 1, -1; -1, 1, -1, -1; -1, 1, 1, 1; 1, 1, -1, 1]

/-- The standard alternating form in order four. -/
def symplecticFormFour : Matrix (Fin 4) (Fin 4) ℂ :=
  !![0, 0, 1, 0; 0, 0, 0, 1; -1, 0, 0, 0; 0, -1, 0, 0]

private def symplecticWitnessSum : Matrix (Fin 4) (Fin 4) GaussianInt :=
  !![-2, 0, 0, ⟨0, 2⟩; 0, 0, ⟨0, 2⟩, 0; 0, ⟨0, 2⟩, -2, 0; ⟨0, 2⟩, 0, 0, 0]

private theorem symplecticWitness_unitary : IsUnitary symplecticWitnessMixer := by
  have h : symplecticWitnessMixer * symplecticWitnessMixerᴴ = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [symplecticWitnessMixer, Matrix.mul_apply, Fin.sum_univ_four,
        Matrix.conjTranspose_apply, Matrix.one_apply, Complex.star_def,
        Matrix.smul_apply, smul_eq_mul, Matrix.cons_val_two, Matrix.cons_val_three,
        Matrix.vecHead, Matrix.vecTail] <;> ring
  exact ⟨h, Matrix.mul_eq_one_comm.mp h⟩

private theorem symplecticWitness_preserves_form :
    symplecticWitnessMixer * symplecticFormFour =
      symplecticFormFour * symplecticWitnessMixer.map star := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [symplecticWitnessMixer, symplecticFormFour, Matrix.mul_apply, Fin.sum_univ_four,
      Matrix.map_apply, Complex.star_def, Matrix.smul_apply, smul_eq_mul,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail] <;> ring

private theorem symplecticWitness_det :
    determinantValue (GaussianInt.toComplex ∘ symplecticFirstLabels)
      (GaussianInt.toComplex ∘ symplecticSecondLabels) symplecticWitnessMixer = 16 := by
  let g := GaussianInt.toComplex
  have hsum : diagonal (g ∘ symplecticFirstLabels) +
      symplecticWitnessMixer * diagonal (g ∘ symplecticSecondLabels) *
        symplecticWitnessMixerᴴ = symplecticWitnessSum.map g := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [symplecticWitnessMixer, symplecticWitnessSum,
        symplecticFirstLabels, symplecticSecondLabels, g, Matrix.add_apply,
        Matrix.mul_apply, Fin.sum_univ_four, GaussianInt.toComplex_def', Matrix.diagonal_apply,
        Matrix.conjTranspose_apply, Matrix.map_apply, Complex.star_def, Matrix.smul_apply,
        smul_eq_mul, Function.comp_apply, map_neg, map_one,
        Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail] <;> ring
  have hdet : symplecticWitnessSum.det = 16 := by
    rw [Matrix.det_succ_column_zero]
    simp only [Matrix.det_fin_three, Fin.sum_univ_four]
    decide +kernel
  rw [determinantValue, hsum, ← RingHom.mapMatrix_apply, ← g.map_det, hdet, map_ofNat]

private theorem symplecticWitness_matching (σ : Equiv.Perm (Fin 4))
    (hσ : PreservesSymplecticPairs σ) :
    matchingProduct (GaussianInt.toComplex ∘ symplecticFirstLabels)
      (GaussianInt.toComplex ∘ symplecticSecondLabels) σ = 32 := by
  have h : ∀ τ : Equiv.Perm (Fin 4), PreservesSymplecticPairs τ →
      (∏ j, (symplecticFirstLabels (τ j) + symplecticSecondLabels j)) = 32 := by
    change ∀ τ : Equiv.Perm (Fin 4), (∀ i, τ (i + 2) = τ i + 2) → _
    decide +kernel
  simpa only [matchingProduct, Function.comp_apply, map_prod, map_add, map_ofNat] using
    congrArg GaussianInt.toComplex (h σ hσ)

/-- In the compact symplectic group of order four, the determinant can be
sixteen while all conjugate-pair Weyl products are thirty-two. -/
theorem symplectic_weyl_hull_obstruction :
    ∃ (a b : Fin 4 → ℂ) (U : Matrix (Fin 4) (Fin 4) ℂ),
      IsUnitary U ∧ U * symplecticFormFour = symplecticFormFour * U.map star ∧
      (∀ i : Fin 4, a (i + 2) = star (a i)) ∧ (∀ i : Fin 4, b (i + 2) = star (b i)) ∧
      determinantValue a b U = 16 ∧
      (∀ σ, PreservesSymplecticPairs σ → matchingProduct a b σ = 32) := by
  refine ⟨GaussianInt.toComplex ∘ symplecticFirstLabels,
    GaussianInt.toComplex ∘ symplecticSecondLabels, symplecticWitnessMixer,
    symplecticWitness_unitary, symplecticWitness_preserves_form, ?_, ?_,
    symplecticWitness_det, symplecticWitness_matching⟩
  · intro i
    fin_cases i <;> norm_num [Function.comp_apply, symplecticFirstLabels,
      GaussianInt.toComplex_def', Complex.star_def, map_neg, map_one]
  · intro i
    fin_cases i <;> norm_num [Function.comp_apply, symplecticSecondLabels,
      GaussianInt.toComplex_def', Complex.star_def]

end MOC
