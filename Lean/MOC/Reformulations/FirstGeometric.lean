import MOC.Reformulations.FirstStructured
import Mathlib.LinearAlgebra.AffineSpace.AffineMap
import Mathlib.Tactic.LinearCombination
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! Finite geometric realizations. A statement about matrix lifts is not a
statement about projective eigenvalue ratios without those lifts. -/

open Matrix

namespace MOC.Reformulations
noncomputable section

/-- The determinant of the sum of affine linear parts is
insensitive to their translation parts. -/
def affineLinearParts : Prop :=
  ∀ (n : ℕ) (f g : (Fin n → ℂ) →ᵃ[ℂ] (Fin n → ℂ))
    (U : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n → ℂ),
    let A := LinearMap.toMatrix' f.linear
    let B := LinearMap.toMatrix' g.linear
    IsStarNormal A → IsStarNormal B → IsUnitary U →
    A.charpoly.roots = (Finset.univ : Finset (Fin n)).val.map a →
    B.charpoly.roots = (Finset.univ : Finset (Fin n)).val.map b →
    (A + U * B * Uᴴ).det ∈ convexHull ℝ (Set.range (matchingProduct a b))

theorem moc_iff_affineLinearParts : MOCIsTrue ↔ affineLinearParts := by
  rw [moc_iff_complexMatrices]
  constructor
  · intro h n f g U a b
    dsimp only
    intro hA hB hU ha hb
    exact h n _ _ U a b hA hB hU ha hb
  · intro h n A B U a b hA hB hU ha hb
    simpa only [LinearMap.toAffineMap_linear, LinearMap.toMatrix'_toLin'] using
      h n A.toLin'.toAffineMap B.toLin'.toAffineMap U a b
        (by simpa only [LinearMap.toAffineMap_linear, LinearMap.toMatrix'_toLin'] using hA)
        (by simpa only [LinearMap.toAffineMap_linear, LinearMap.toMatrix'_toLin'] using hB)
        hU
        (by simpa only [LinearMap.toAffineMap_linear, LinearMap.toMatrix'_toLin'] using ha)
        (by simpa only [LinearMap.toAffineMap_linear, LinearMap.toMatrix'_toLin'] using hb)

/-- Restriction to nonzero spectra. An opposite scalar shift avoids every
forbidden point without changing the determinant or the comparison products. -/
def nonzeroSpectra : Prop :=
  ∀ (n : ℕ) (a b : Fin n → ℂ) (U : Matrix (Fin n) (Fin n) ℂ),
    IsUnitary U → (∀ i, a i ≠ 0) → (∀ i, b i ≠ 0) → Holds a b U

theorem moc_iff_nonzeroSpectra : MOCIsTrue ↔ nonzeroSpectra := by
  classical
  constructor
  · intro h n a b U hU _ _
    exact h n a b U hU
  · intro h n a b U hU
    let S : Finset ℂ := Finset.univ.image (fun i => -a i) ∪ Finset.univ.image b
    obtain ⟨t, ht⟩ := S.exists_not_mem
    have ha (i : Fin n) : a i + t ≠ 0 := by
      intro he
      have ht' : t = -a i := by linear_combination he
      apply ht
      exact Finset.mem_union.mpr (Or.inl (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, ht'.symm⟩))
    have hb (i : Fin n) : b i - t ≠ 0 := by
      intro he
      apply ht
      exact Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr
        ⟨i, Finset.mem_univ _, sub_eq_zero.mp he⟩))
    exact (holds_shift_iff a b hU t).mp (h n _ _ U hU ha hb)

/-- In spectral coordinates, an invertible normal projective lift
has nonzero diagonal entries. Opposite shifts prove the exact equivalence
without a limiting argument. -/
theorem moc_iff_projectiveDiagonalLifts :
    MOCIsTrue ↔
      ∀ (n : ℕ) (a b : Fin n → ℂ) (U : Matrix (Fin n) (Fin n) ℂ),
        IsUnit (diagonal a).det → IsUnit (diagonal b).det → IsUnitary U → Holds a b U := by
  rw [moc_iff_nonzeroSpectra]
  constructor
  · intro h n a b U ha hb hU
    rw [isUnit_iff_ne_zero, Matrix.det_diagonal] at ha hb
    exact h n a b U hU (fun i => Finset.prod_ne_zero_iff.mp ha i (Finset.mem_univ _))
      (fun i => Finset.prod_ne_zero_iff.mp hb i (Finset.mem_univ _))
  · intro h n a b U hU ha hb
    apply h n a b U _ _ hU
    · rw [isUnit_iff_ne_zero, Matrix.det_diagonal]
      exact Finset.prod_ne_zero_iff.mpr fun i _ => ha i
    · rw [isUnit_iff_ne_zero, Matrix.det_diagonal]
      exact Finset.prod_ne_zero_iff.mpr fun i _ => hb i

/-- The spectrum of conjugation on the selected reference column. An
invertible diagonal matrix realizes any nonzero ratio list on this
subspace. -/
def selectedConjugationSpectrum : Prop :=
  ∀ (n : ℕ) (a b : Fin n ⊕ Fin 1 → ℂ), (∀ i, a i ≠ 0) → (∀ i, b i ≠ 0) →
    ∀ (U : Matrix (Fin n) (Fin n) ℂ), IsUnitary U →
      Holds (fun i => a (.inl i) / a (.inr 0)) (fun i => b (.inl i) / b (.inr 0)) U

theorem moc_iff_selectedConjugationSpectrum : MOCIsTrue ↔ selectedConjugationSpectrum := by
  constructor
  · intro h n a b _ _ U hU
    exact h n _ _ U hU
  · intro h
    apply moc_iff_nonzeroSpectra.mpr
    intro n a b U hU ha hb
    have ha' : ∀ i, Sum.elim a (fun _ : Fin 1 => (1 : ℂ)) i ≠ 0 := by
      intro i
      cases i with
      | inl i => exact ha i
      | inr i => exact one_ne_zero
    have hb' : ∀ i, Sum.elim b (fun _ : Fin 1 => (1 : ℂ)) i ≠ 0 := by
      intro i
      cases i with
      | inl i => exact hb i
      | inr i => exact one_ne_zero
    simpa using h n _ _ ha' hb' U hU

/-- On one complex line the scalar determinant comparison is
unconditional. No conclusion about unrestricted orders follows from it. -/
theorem lineFiberHull (a b : Fin 1 → ℂ) (U : Matrix (Fin 1) (Fin 1) ℂ)
    (hU : IsUnitary U) : Holds a b U :=
  conjecture_le_three (by decide) a b U hU

end
end MOC.Reformulations
