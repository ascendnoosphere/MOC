import MOC.SecularChamberSpectrum
import MOC.Support

/-! The lower-order comparison at a boundary residue vector. -/

open BigOperators Finset Matrix Polynomial

namespace MOC

noncomputable section

private theorem det_of_scalar_column {n : ℕ} {K : Type*} [CommRing K]
    (M : Matrix (Fin (n+1)) (Fin (n+1)) K) (i : Fin (n+1))
    (hi : ∀ j, j ≠ i → M j i = 0) :
    M.det = M i i * (M.submatrix i.succAbove i.succAbove).det := by
  rw [Matrix.det_succ_column M i, sum_eq_single i]
  · have hs : (-1 : K) ^ ((i : ℕ) + (i : ℕ)) = 1 := by
      rw [← two_mul, pow_mul]
      simp
    rw [hs, one_mul]
  · intro j _ hj
    rw [hi j hj, mul_zero, zero_mul]
  · exact fun h => (h (mem_univ i)).elim

/-- At an idle coordinate the secular polynomial factors into the
scalar diagonal root and the secular polynomial on the other coordinates. -/
theorem secularCharacteristic_zero_residue {n : ℕ}
    (d r : Fin (n+1) → ℝ) (i : Fin (n+1)) (hr : r i = 0) :
    secularCharacteristic d r =
      (X - C (d i)) * secularCharacteristic (d ∘ i.succAbove) (r ∘ i.succAbove) := by
  let D : Matrix (Fin (n+1)) (Fin (n+1)) ℝ :=
    diagonal d + vecMulVec (fun _ => 1) r
  have hD : D.charpoly = secularCharacteristic d r := by
    change (diagonal d + vecMulVec (fun _ => 1) r).charpoly = _
    rw [charpoly_diagonal_add_outer]
    congr 1
    funext j
    exact one_mul _
  have hS : D.submatrix i.succAbove i.succAbove =
      diagonal (d ∘ i.succAbove) + vecMulVec (fun _ => 1) (r ∘ i.succAbove) := by
    ext j k : 1
    simp only [D, Matrix.submatrix_apply, Matrix.add_apply, Matrix.vecMulVec_apply,
      Matrix.diagonal_apply, Fin.succAbove_right_inj, Function.comp_apply, one_mul]
  have hC : ∀ j, j ≠ i → D.charmatrix j i = 0 := by
    intro j hj
    simp only [Matrix.charmatrix_apply_ne _ _ _ hj, D, Matrix.add_apply,
      Matrix.diagonal_apply_ne _ hj, Matrix.vecMulVec_apply, hr, one_mul, add_zero, map_zero, neg_zero]
  have hCii : D.charmatrix i i = X - C (d i) := by
    simp [D, hr, Matrix.vecMulVec_apply]
  have hCs : D.charmatrix.submatrix i.succAbove i.succAbove =
      (D.submatrix i.succAbove i.succAbove).charmatrix := by
    ext j k : 1
    by_cases h : j = k
    · subst k
      simp only [Matrix.submatrix_apply, Matrix.charmatrix_apply_eq]
    · have h' : i.succAbove j ≠ i.succAbove k := Fin.succAbove_right_injective.ne h
      rw [Matrix.submatrix_apply, Matrix.charmatrix_apply_ne _ _ _ h',
        Matrix.charmatrix_apply_ne _ _ _ h, Matrix.submatrix_apply]
  rw [← hD, Matrix.charpoly, det_of_scalar_column _ i hC, hCii, hCs, ← Matrix.charpoly,
    hS, charpoly_diagonal_add_outer]
  congr 2
  funext j
  exact one_mul _

/-- A zero residue supplies an eigenvalue label to delete along with its
diagonal coordinate. -/
theorem exists_secularCharacteristic_deleted_label {n : ℕ}
    (d r h : Fin (n+1) → ℝ) (i : Fin (n+1)) (hr : r i = 0)
    (hh : secularCharacteristic d r = ∏ j, (X - C (h j))) :
    ∃ k : Fin (n+1), h k = d i ∧
      secularCharacteristic (d ∘ i.succAbove) (r ∘ i.succAbove) =
        ∏ j : Fin n, (X - C (h (k.succAbove j))) := by
  have he := secularCharacteristic_zero_residue d r i hr
  rw [hh] at he
  have hz := congrArg (Polynomial.eval (d i)) he
  simp only [eval_prod, eval_mul, eval_sub, eval_X, eval_C, sub_self, zero_mul] at hz
  obtain ⟨k, _, hk⟩ := prod_eq_zero_iff.mp hz
  have hkd : h k = d i := (sub_eq_zero.mp hk).symm
  refine ⟨k, hkd, ?_⟩
  rw [Fin.prod_univ_succAbove _ k, hkd] at he
  exact (mul_left_cancel₀ (X_sub_C_ne_zero (d i)) he).symm

def secularExtendPermutation {n : ℕ} (i k : Fin (n+1))
    (σ : Equiv.Perm (Fin n)) : Equiv.Perm (Fin (n+1)) :=
  (finSuccEquiv' i).trans ((Equiv.optionCongr σ).trans (finSuccEquiv' k).symm)

theorem secularExtendPermutation_at {n : ℕ} (i k : Fin (n+1))
    (σ : Equiv.Perm (Fin n)) : secularExtendPermutation i k σ i = k := by
  simp [secularExtendPermutation, finSuccEquiv'_at]

theorem secularExtendPermutation_succAbove {n : ℕ} (i k : Fin (n+1))
    (σ : Equiv.Perm (Fin n)) (j : Fin n) :
    secularExtendPermutation i k σ (i.succAbove j) = k.succAbove (σ j) := by
  simp [secularExtendPermutation, finSuccEquiv'_succAbove]

/-- Dictionary between real secular labels and roots of the quadratic spectral image. -/
def secularQuadraticLabels {n : ℕ} (h : Fin n → ℝ) (c e : ℂ) (j : Fin n) : ℂ :=
  (h j : ℂ)^2 + c * h j + e

/-- The smaller-order scalar hull lifts at a zero residue. This claim uses
no distinctness of either set of labels. -/
theorem secular_hull_of_zero_residue {n : ℕ}
    (d r h : Fin (n+1) → ℝ) (i : Fin (n+1)) (hr : r i = 0)
    (hh : secularCharacteristic d r = ∏ j, (X - C (h j))) (c e : ℂ)
    (a : Fin (n+1) → ℂ)
    (hSmall : ∀ k : Fin (n+1), h k = d i →
      secularCharacteristic (d ∘ i.succAbove) (r ∘ i.succAbove) =
        (∏ j : Fin n, (X - C (h (k.succAbove j)))) →
      (secularQuadraticColumnMatrix (d ∘ i.succAbove) (r ∘ i.succAbove) c e (a ∘ i.succAbove)).det ∈
        convexHull ℝ (Set.range (matchingProduct
          (secularQuadraticLabels (h ∘ k.succAbove) c e) (a ∘ i.succAbove)))) :
    (secularQuadraticColumnMatrix d r c e a).det ∈
      convexHull ℝ (Set.range (matchingProduct (secularQuadraticLabels h c e) a)) := by
  obtain ⟨k, hk, hpoly⟩ := exists_secularCharacteristic_deleted_label d r h i hr hh
  have hx := hSmall k hk hpoly
  rw [det_secularQuadraticColumnMatrix_zero_residue d r c e a i hr]
  let m : ℂ := (d i : ℂ)^2 + c * d i + e + a i
  let p := matchingProduct (secularQuadraticLabels (h ∘ k.succAbove) c e) (a ∘ i.succAbove)
  have hp (σ : Equiv.Perm (Fin n)) :
      m * p σ = matchingProduct (secularQuadraticLabels h c e) a (secularExtendPermutation i k σ) := by
    unfold p matchingProduct
    rw [Fin.prod_univ_succAbove _ i, secularExtendPermutation_at]
    simp only [secularQuadraticLabels, secularExtendPermutation_succAbove, Function.comp_apply, hk]
    rfl
  have hh' := hull_of_common_factor (k := m) rfl (fun σ => rfl) hx
  refine convexHull_mono ?_ hh'
  rintro _ ⟨σ, rfl⟩
  exact ⟨secularExtendPermutation i k σ, (hp σ).symm⟩

end

end MOC
