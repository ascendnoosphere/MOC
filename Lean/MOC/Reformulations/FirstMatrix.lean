import MOC.Claim
import MOC.Normal
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! Matrix formulations of the Marcus–de Oliveira conjecture. A proposition defined here is
not asserted unconditionally. Restricted spectral forms and verified logical links
to the unrestricted conjecture are stated separately. -/

open Matrix BigOperators

namespace MOC.Reformulations
noncomputable section

private theorem unitary_star {n : ℕ} {U : Matrix (Fin n) (Fin n) ℂ}
    (hU : IsUnitary U) : IsUnitary Uᴴ :=
  ⟨by simpa only [Matrix.conjTranspose_conjTranspose] using hU.2,
    by simpa only [Matrix.conjTranspose_conjTranspose] using hU.1⟩

private theorem unitary_mul {n : ℕ} {U V : Matrix (Fin n) (Fin n) ℂ}
    (hU : IsUnitary U) (hV : IsUnitary V) : IsUnitary (U * V) :=
  by simpa only [Matrix.conjTranspose_conjTranspose] using
    relative_unitary Uᴴ V (unitary_star hU) hV

/-- Two normal summands given by actual, independently diagonalized complex matrices
in a common basis, with an arbitrary unitary change of the second summand. -/
private theorem hull_of_realizations (h : MOCIsTrue) {n : ℕ}
    (a b : Fin n → ℂ) (V W U : Matrix (Fin n) (Fin n) ℂ)
    (hV : IsUnitary V) (hW : IsUnitary W) (hU : IsUnitary U) :
    (V * diagonal a * Vᴴ + U * (W * diagonal b * Wᴴ) * Uᴴ).det ∈
      convexHull ℝ (Set.range (matchingProduct a b)) := by
  have he : U * (W * diagonal b * Wᴴ) * Uᴴ =
      (U * W) * diagonal b * (U * W)ᴴ := by
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [he, determinantValue_relative a b V (U * W) hV]
  exact h n a b _ (relative_unitary V _ hV (unitary_mul hU hW))

/-- Complex normal summands and their characteristic roots.
The unrotated case is the existing intrinsic matrix formulation. -/
def complexMatrices : Prop :=
  ∀ (n : ℕ) (A B U : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n → ℂ),
    IsStarNormal A → IsStarNormal B → IsUnitary U →
    A.charpoly.roots = (Finset.univ : Finset (Fin n)).val.map a →
    B.charpoly.roots = (Finset.univ : Finset (Fin n)).val.map b →
    (A + U * B * Uᴴ).det ∈ convexHull ℝ (Set.range (matchingProduct a b))

theorem moc_iff_complexMatrices : MOCIsTrue ↔ complexMatrices := by
  constructor
  · intro h n A B U a b hA hB hU ha hb
    obtain ⟨a', V, hV, rfl⟩ := exists_unitary_diagonalization A hA
    obtain ⟨b', W, hW, rfl⟩ := exists_unitary_diagonalization B hB
    rw [roots_unitary_diagonalization a' hV] at ha
    rw [roots_unitary_diagonalization b' hW] at hb
    obtain ⟨e, rfl⟩ := exists_perm_of_equal_multisets a a' ha.symm
    obtain ⟨f, rfl⟩ := exists_perm_of_equal_multisets b b' hb.symm
    rw [matchingRange_relabel]
    exact hull_of_realizations h a' b' V W U hV hW hU
  · intro h n
    apply conjecture_iff_normalConjecture.mpr
    intro A B a b hA hB ha hb
    simpa using h n A B 1 a b hA hB isUnitary_one ha hb

/-- Normal spectra in orthonormal mode coordinates. Repeated entries record the ranks
of their spectral projections. The two diagonalizing frames need not agree. -/
def normalFrames : Prop :=
  ∀ (n : ℕ) (a b : Fin n → ℂ) (V W U : Matrix (Fin n) (Fin n) ℂ),
    IsUnitary V → IsUnitary W → IsUnitary U →
    (V * diagonal a * Vᴴ + U * (W * diagonal b * Wᴴ) * Uᴴ).det ∈
      convexHull ℝ (Set.range (matchingProduct a b))

theorem moc_iff_normalFrames : MOCIsTrue ↔ normalFrames := by
  constructor
  · intro h n a b V W U hV hW hU
    exact hull_of_realizations h a b V W U hV hW hU
  · intro h n a b U hU
    simpa [Holds, determinantValue] using
      h n a b 1 1 U isUnitary_one isUnitary_one hU

/-- Use the characteristic roots of arbitrary complex matrices. The determinant
is that of the sum of their diagonal representatives in unitary position. -/
def nonnormalSpectralRepresentatives : Prop :=
  ∀ (n : ℕ) (A B U : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n → ℂ),
    A.charpoly.roots = (Finset.univ : Finset (Fin n)).val.map a →
    B.charpoly.roots = (Finset.univ : Finset (Fin n)).val.map b →
    IsUnitary U → Holds a b U

theorem moc_iff_nonnormalSpectralRepresentatives : MOCIsTrue ↔ nonnormalSpectralRepresentatives := by
  constructor
  · intro h n A B U a b ha hb hU
    exact h n a b U hU
  · intro h n a b U hU
    have hroots (s : Fin n → ℂ) :
        (diagonal s).charpoly.roots = (Finset.univ : Finset (Fin n)).val.map s := by
      simpa using roots_unitary_diagonalization s isUnitary_one
    exact h n (diagonal a) (diagonal b) U a b (hroots a) (hroots b) hU

/-- Two commuting normal tuples. Each side is diagonal in its own
frame. The condition is a separate hull for each linear evaluation. -/
def commutingTupleProjections : Prop :=
  ∀ (n k : ℕ) (a b : Fin n → Fin k → ℂ) (c : Fin k → ℂ)
    (U : Matrix (Fin n) (Fin n) ℂ), IsUnitary U →
    Holds (fun i => ∑ l, c l * a i l) (fun i => ∑ l, c l * b i l) U

theorem moc_iff_commutingTupleProjections : MOCIsTrue ↔ commutingTupleProjections := by
  constructor
  · intro h n k a b c U hU
    exact h n _ _ U hU
  · intro h n a b U hU
    simpa using h n 1 (fun i _ => a i) (fun i _ => b i) (fun _ => 1) U hU

/-- For normalized pencils the invertible denominators can be
the identity. The roots are those of the normalized matrices. -/
def normalizedPencils : Prop :=
  ∀ (n : ℕ) (A B C D U : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n → ℂ),
    IsUnit B.det → IsUnit D.det → IsStarNormal (B⁻¹ * A) → IsStarNormal (D⁻¹ * C) →
    IsUnitary U →
    (B⁻¹ * A).charpoly.roots = (Finset.univ : Finset (Fin n)).val.map a →
    (D⁻¹ * C).charpoly.roots = (Finset.univ : Finset (Fin n)).val.map b →
    (B⁻¹ * A + U * (D⁻¹ * C) * Uᴴ).det ∈
      convexHull ℝ (Set.range (matchingProduct a b))

theorem moc_iff_normalizedPencils : MOCIsTrue ↔ normalizedPencils := by
  rw [moc_iff_complexMatrices]
  constructor
  · intro h n A B C D U a b _ _ hA hC hU ha hb
    exact h n _ _ U a b hA hC hU ha hb
  · intro h n A C U a b hA hC hU ha hb
    simpa using h n A 1 C 1 U a b (by simp) (by simp)
      (by simpa using hA) (by simpa using hC) hU
      (by simpa using ha) (by simpa using hb)

/-- Complex scalar realizations of matrices over any commutative ring.
The complex hull does not live over the original coefficient ring. -/
def commutativeRingMatrices : Prop :=
  ∀ (R : Type) [CommRing R], ∀ (e : R →+* ℂ) (n : ℕ)
    (A B : Matrix (Fin n) (Fin n) R) (U : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n → ℂ),
    IsStarNormal (A.map e) → IsStarNormal (B.map e) → IsUnitary U →
    (A.map e).charpoly.roots = (Finset.univ : Finset (Fin n)).val.map a →
    (B.map e).charpoly.roots = (Finset.univ : Finset (Fin n)).val.map b →
    (A.map e + U * (B.map e) * Uᴴ).det ∈ convexHull ℝ (Set.range (matchingProduct a b))

theorem moc_iff_commutativeRingMatrices : MOCIsTrue ↔ commutativeRingMatrices := by
  rw [moc_iff_complexMatrices]
  constructor
  · intro h R _ e n A B U a b hA hB hU ha hb
    exact h n _ _ U a b hA hB hU ha hb
  · intro h n A B U a b hA hB hU ha hb
    simpa using h ℂ (RingHom.id ℂ) n A B U a b
      (by simpa using hA) (by simpa using hB) hU (by simpa using ha) (by simpa using hb)

end
end MOC.Reformulations
