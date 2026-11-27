import MOC.TwoSpectralCircles
import MOC.Normal

open Matrix

namespace MOC.Reformulations

/-- The determinant hull for two spectra on the unit circle. -/
theorem unitarySpectralHull {n : ℕ} (a b : Fin n → ℂ)
    (ha : ∀ i, Complex.normSq (a i) = 1) (hb : ∀ i, Complex.normSq (b i) = 1)
    (U : Matrix (Fin n) (Fin n) ℂ) (hU : IsUnitary U) : Holds a b U := by
  apply holds_of_circular_spectra a b 0 0 1 1 _ _ U hU
  · simpa using ha
  · simpa using hb

private theorem unitarySpectrum {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : IsUnitary A) :
    ∃ (a : Fin n → ℂ) (V : Matrix (Fin n) (Fin n) ℂ),
      IsUnitary V ∧ A = V * diagonal a * Vᴴ ∧ ∀ i, Complex.normSq (a i) = 1 := by
  have hnormal : IsStarNormal A := by
    constructor
    change Commute Aᴴ A
    show Aᴴ * A = A * Aᴴ
    rw [hA.1, hA.2]
  obtain ⟨a, V, hV, ha⟩ := exists_unitary_diagonalization A hnormal
  refine ⟨a, V, hV, ha, fun i => ?_⟩
  have hd : Vᴴ * A * V = diagonal a := by
    rw [ha]
    calc
      _ = (Vᴴ * V) * diagonal a * (Vᴴ * V) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hV.2, Matrix.one_mul, Matrix.mul_one]
  have hunit : (Vᴴ * A * V)ᴴ * (Vᴴ * A * V) = 1 := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    calc
      _ = Vᴴ * (Aᴴ * (V * Vᴴ) * A) * V := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hV.1, Matrix.mul_one, hA.2, Matrix.mul_one, hV.2]
  rw [hd, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal] at hunit
  have hi := congrArg (fun M : Matrix (Fin n) (Fin n) ℂ => (M i i).re) hunit
  simpa only [Matrix.diagonal_apply_eq, Matrix.one_apply_eq, Function.comp_apply, Pi.star_apply,
    Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re, Complex.one_re] using hi

/-- The determinant hull for unitary summands at any relative unitary position. -/
theorem unitaryMatrixHull {n : ℕ} (A B U : Matrix (Fin n) (Fin n) ℂ)
    (a b : Fin n → ℂ) (hA : IsUnitary A) (hB : IsUnitary B) (hU : IsUnitary U)
    (ha : A.charpoly.roots = (Finset.univ : Finset (Fin n)).val.map a)
    (hb : B.charpoly.roots = (Finset.univ : Finset (Fin n)).val.map b) :
    (A + U * B * Uᴴ).det ∈ convexHull ℝ (Set.range (matchingProduct a b)) := by
  obtain ⟨a', V, hV, hAV, hca⟩ := unitarySpectrum A hA
  obtain ⟨b', W, hW, hBW, hcb⟩ := unitarySpectrum B hB
  rw [hAV, roots_unitary_diagonalization a' hV] at ha
  rw [hBW, roots_unitary_diagonalization b' hW] at hb
  obtain ⟨e, rfl⟩ := exists_perm_of_equal_multisets a a' ha.symm
  obtain ⟨f, rfl⟩ := exists_perm_of_equal_multisets b b' hb.symm
  have hUadj : IsUnitary Uᴴ :=
    ⟨by simpa only [Matrix.conjTranspose_conjTranspose] using hU.2,
      by simpa only [Matrix.conjTranspose_conjTranspose] using hU.1⟩
  have hUW : IsUnitary (U * W) := by
    simpa only [Matrix.conjTranspose_conjTranspose] using relative_unitary Uᴴ W hUadj hW
  have hB' : U * B * Uᴴ = (U * W) * diagonal b' * (U * W)ᴴ := by
    rw [hBW]
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [matchingRange_relabel, hB', hAV, determinantValue_relative a' b' V (U * W) hV]
  exact unitarySpectralHull a' b' hca hcb _ (relative_unitary V (U * W) hV hUW)

end MOC.Reformulations
