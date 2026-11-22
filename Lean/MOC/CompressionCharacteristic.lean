import MOC.Interlacing
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

/-! The characteristic polynomial of a principal compression separates
labels on the deleted row's support from untouched spectral factors. -/

open BigOperators Matrix Polynomial

namespace MOC

noncomputable section

variable {n : ℕ}

/-- The compression's characteristic polynomial is a weighted sum of the
one-root deletions of the parent characteristic polynomial. -/
theorem charpoly_principal_unitary_diagonalization (β : Fin (n + 1) → ℂ)
    (U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (hU : IsUnitary U) (p : Fin (n + 1)) :
    ((U * diagonal β * Uᴴ).submatrix p.succAbove p.succAbove).charpoly =
      ∑ i, Polynomial.C (Complex.normSq (U p i) : ℂ) *
        ∏ j ∈ Finset.univ.erase i, (X - Polynomial.C (β j)) := by
  let B := U * diagonal β * Uᴴ
  let M := B.submatrix p.succAbove p.succAbove
  change M.charpoly = _
  letI : Infinite ℂ := Infinite.of_injective (fun k : ℕ => (k : ℂ)) Nat.cast_injective
  apply Polynomial.funext
  intro z
  have heval : M.charpoly.eval z = (Matrix.scalar (Fin n) z - M).det := by
    rw [Matrix.charpoly, Matrix.eval_det, Matrix.matPolyEquiv_charmatrix,
      Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  have hshift : U * diagonal (fun j => z - β j) * Uᴴ =
      z • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) - B := by
    rw [← Matrix.diagonal_sub (fun _ : Fin (n + 1) => z) β,
      ← Matrix.smul_one_eq_diagonal, Matrix.mul_sub, Matrix.sub_mul,
      Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hU.1]
  have hsub : (U * diagonal (fun j => z - β j) * Uᴴ).submatrix p.succAbove p.succAbove =
      Matrix.scalar (Fin n) z - M := by
    rw [hshift]
    change z • ((1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ).submatrix p.succAbove p.succAbove) - M = _
    rw [Matrix.submatrix_one p.succAbove Fin.succAbove_right_injective, Matrix.scalar_apply,
      Matrix.smul_one_eq_diagonal]
  rw [heval, ← hsub, det_principal_unitary_diagonalization (fun j => z - β j) hU p]
  simp only [Polynomial.eval_finset_sum, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X]

/-- Zero entries in the deleted row preserve those spectral roots with
their multiplicities. The remaining factor is the weighted deletion
polynomial on the nonzero support. -/
theorem charpoly_principalCompression_support_factorization (β : Fin (n + 1) → ℂ)
    (U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (hU : IsUnitary U) (p : Fin (n + 1)) :
    let S := Finset.univ.filter (fun i => U p i ≠ 0)
    ((U * diagonal β * Uᴴ).submatrix p.succAbove p.succAbove).charpoly =
      (∏ j ∈ Finset.univ \ S, (X - Polynomial.C (β j))) *
        ∑ i ∈ S, Polynomial.C (Complex.normSq (U p i) : ℂ) *
          ∏ j ∈ S.erase i, (X - Polynomial.C (β j)) := by
  classical
  intro S
  let f (j : Fin (n + 1)) := X - Polynomial.C (β j)
  let a (j : Fin (n + 1)) := Polynomial.C (Complex.normSq (U p j) : ℂ)
  rw [charpoly_principal_unitary_diagonalization β U hU p]
  change (∑ i, a i * ∏ j ∈ Finset.univ.erase i, f j) =
    (∏ j ∈ Finset.univ \ S, f j) * ∑ i ∈ S, a i * ∏ j ∈ S.erase i, f j
  have hsum : (∑ i ∈ S, a i * ∏ j ∈ Finset.univ.erase i, f j) =
      ∑ i, a i * ∏ j ∈ Finset.univ.erase i, f j := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro i _ hi
    have hz : U p i = 0 := by simpa [S] using hi
    simp [a, hz, Complex.normSq_zero]
  rw [← hsum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hdisjoint : Disjoint (Finset.univ \ S) (S.erase i) := by
    rw [Finset.disjoint_left]
    intro j hj hj'
    exact (Finset.mem_sdiff.mp hj).2 ((Finset.mem_erase.mp hj').2)
  have hpart : Finset.univ.erase i = (Finset.univ \ S) ∪ S.erase i := by
    ext j
    by_cases hj : j ∈ S
    · simp [hj]
    · have hji : j ≠ i := fun he => hj (he.symm ▸ hi)
      simp [hj, hji]
  rw [hpart, Finset.prod_union hdisjoint]
  ring

/-- The compressed eigenvalue multiset consists of the untouched spectral
values and the roots of the weighted deletion polynomial on the support. -/
theorem roots_principalCompression_support_factorization (β : Fin (n + 1) → ℂ)
    (U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (hU : IsUnitary U) (p : Fin (n + 1)) :
    let S := Finset.univ.filter (fun i => U p i ≠ 0)
    ((U * diagonal β * Uᴴ).submatrix p.succAbove p.succAbove).charpoly.roots =
      (Finset.univ \ S).val.map β +
        (∑ i ∈ S, Polynomial.C (Complex.normSq (U p i) : ℂ) *
          ∏ j ∈ S.erase i, (X - Polynomial.C (β j))).roots := by
  classical
  intro S
  let M := (U * diagonal β * Uᴴ).submatrix p.succAbove p.succAbove
  let P := ∏ j ∈ Finset.univ \ S, (X - Polynomial.C (β j))
  let Q := ∑ i ∈ S, Polynomial.C (Complex.normSq (U p i) : ℂ) *
    ∏ j ∈ S.erase i, (X - Polynomial.C (β j))
  change M.charpoly.roots = (Finset.univ \ S).val.map β + Q.roots
  have h : M.charpoly = P * Q := charpoly_principalCompression_support_factorization β U hU p
  have hne : P * Q ≠ 0 := h ▸ (Matrix.charpoly_monic M).ne_zero
  rw [h, Polynomial.roots_mul hne]
  have hp : P.roots = (Finset.univ \ S).val.map β := by
    simpa only [P, Finset.prod_eq_multiset_prod, Multiset.map_map, Function.comp_apply] using
      Polynomial.roots_multiset_prod_X_sub_C ((Finset.univ \ S).val.map β)
  rw [hp]

end

end MOC
