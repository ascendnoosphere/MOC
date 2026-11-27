import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! The squared determinant of a Cauchy matrix, by a singleton Schur complement. -/

open BigOperators Finset Matrix

namespace MOC

noncomputable section

variable {K : Type*} [Field K]

/-- Rows have nodes `y` and columns have nodes `x`. -/
def cauchyMatrix {n : ℕ} (y x : Fin n → K) : Matrix (Fin n) (Fin n) K :=
  Matrix.of fun i j => (x j - y i)⁻¹

/-- The product of all differences between unequal indices. -/
def directedNodeDifferences {n : ℕ} (x : Fin n → K) : K :=
  ∏ i, ∏ j, if i = j then 1 else x i - x j

/-- The product of the denominators of a Cauchy matrix. -/
def cauchyDenominator {n : ℕ} (y x : Fin n → K) : K :=
  ∏ i, ∏ j, (x j - y i)

private theorem directedNodeDifferences_succ {n : ℕ} (x : Fin (n + 1) → K) :
    directedNodeDifferences x =
      (∏ j : Fin n, (x 0 - x j.succ)) *
      (∏ j : Fin n, (x j.succ - x 0)) * directedNodeDifferences (x ∘ Fin.succ) := by
  unfold directedNodeDifferences
  rw [Fin.prod_univ_succ]
  have hzero : (∏ j : Fin (n + 1), if (0 : Fin (n + 1)) = j then 1 else x 0 - x j) =
      ∏ j : Fin n, (x 0 - x j.succ) := by
    rw [Fin.prod_univ_succ]
    simp only [if_pos rfl, ite_true, one_mul]
    apply Finset.prod_congr rfl
    intro j _
    exact if_neg (Ne.symm j.succ_ne_zero)
  have hsucc (i : Fin n) :
      (∏ j : Fin (n + 1), if i.succ = j then 1 else x i.succ - x j) =
        (x i.succ - x 0) * ∏ j : Fin n, if i = j then 1 else x i.succ - x j.succ := by
    rw [Fin.prod_univ_succ]
    simp
  simp_rw [hzero, hsucc, Finset.prod_mul_distrib, Function.comp_apply]
  exact (mul_assoc _ _ _).symm

private theorem cauchyDenominator_succ {n : ℕ} (y x : Fin (n + 1) → K) :
    cauchyDenominator y x = (x 0 - y 0) *
      (∏ j : Fin n, (x j.succ - y 0)) *
      (∏ i : Fin n, (x 0 - y i.succ)) * cauchyDenominator (y ∘ Fin.succ) (x ∘ Fin.succ) := by
  unfold cauchyDenominator
  rw [Fin.prod_univ_succ]
  have hzero : (∏ j : Fin (n + 1), (x j - y 0)) =
      (x 0 - y 0) * ∏ j : Fin n, (x j.succ - y 0) := Fin.prod_univ_succ _
  have hsucc (i : Fin n) : (∏ j : Fin (n + 1), (x j - y i.succ)) =
      (x 0 - y i.succ) * ∏ j : Fin n, (x j.succ - y i.succ) := Fin.prod_univ_succ _
  simp_rw [hzero, hsucc, Finset.prod_mul_distrib, Function.comp_apply]
  rw [mul_assoc ((x 0 - y 0) * ∏ j : Fin n, (x j.succ - y 0))]

private theorem cauchy_schur_det {n : ℕ} (y x : Fin (n + 1) → K)
    (hn : ∀ i j, x j ≠ y i) :
    (cauchyMatrix y x).det = (x 0 - y 0)⁻¹ *
      (∏ i : Fin n, (y i.succ - y 0)/(x 0 - y i.succ)) *
      (∏ j : Fin n, (x 0 - x j.succ)/(x j.succ - y 0)) *
      (cauchyMatrix (y ∘ Fin.succ) (x ∘ Fin.succ)).det := by
  let p := x 0 - y 0
  let A : Matrix (Fin 1) (Fin 1) K := diagonal (fun _ => p⁻¹)
  let Ainv : Matrix (Fin 1) (Fin 1) K := diagonal (fun _ => p)
  let B : Matrix (Fin 1) (Fin n) K := Matrix.of fun _ j => (x j.succ - y 0)⁻¹
  let C : Matrix (Fin n) (Fin 1) K := Matrix.of fun i _ => (x 0 - y i.succ)⁻¹
  let D := cauchyMatrix (y ∘ Fin.succ) (x ∘ Fin.succ)
  have hp : p ≠ 0 := sub_ne_zero.mpr (hn 0 0)
  letI : Invertible A := {
    invOf := Ainv
    invOf_mul_self := by
      simp only [Ainv, A, Matrix.diagonal_mul_diagonal, mul_inv_cancel₀ hp, Matrix.diagonal_one]
    mul_invOf_self := by
      simp only [A, Ainv, Matrix.diagonal_mul_diagonal, inv_mul_cancel₀ hp, Matrix.diagonal_one] }
  have hInv : ⅟ A = Ainv := rfl
  let e : Fin 1 ⊕ Fin n ≃ Fin (n + 1) :=
    finSumFinEquiv.trans (finCongr (Nat.add_comm 1 n))
  have he₀ (i : Fin 1) : e (Sum.inl i) = 0 := by
    apply Fin.ext
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    rfl
  have he₁ (i : Fin n) : e (Sum.inr i) = i.succ := by
    apply Fin.ext
    change 1 + i.val = i.val + 1
    omega
  have hblock : (cauchyMatrix y x).submatrix e e = Matrix.fromBlocks A B C D := by
    ext i j : 1
    rcases i with i | i <;> rcases j with j | j
    · have hij : i = j := Subsingleton.elim _ _
      subst j
      simp only [Matrix.submatrix_apply, he₀, cauchyMatrix, Matrix.of_apply, Matrix.fromBlocks_apply₁₁,
        A, Matrix.diagonal_apply_eq, p]
    · simp only [Matrix.submatrix_apply, he₀, he₁, cauchyMatrix, Matrix.of_apply,
        Matrix.fromBlocks_apply₁₂, B]
    · simp only [Matrix.submatrix_apply, he₀, he₁, cauchyMatrix, Matrix.of_apply,
        Matrix.fromBlocks_apply₂₁, C]
    · simp only [Matrix.submatrix_apply, he₁, cauchyMatrix, Matrix.of_apply,
        Matrix.fromBlocks_apply₂₂, D, Function.comp_apply]
  let row (i : Fin n) := (y i.succ - y 0)/(x 0 - y i.succ)
  let col (j : Fin n) := (x 0 - x j.succ)/(x j.succ - y 0)
  have hSchur : D - C * ⅟ A * B = diagonal row * D * diagonal col := by
    ext i j : 1
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    simp only [hInv, Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_one,
      Ainv, Matrix.diagonal_apply_eq, B, C, D, cauchyMatrix, Matrix.of_apply,
      Function.comp_apply, row, col, p]
    have hp₁ := sub_ne_zero.mpr (hn i.succ j.succ)
    have hp₂ := sub_ne_zero.mpr (hn i.succ 0)
    have hp₃ := sub_ne_zero.mpr (hn 0 j.succ)
    field_simp [hp₁, hp₂, hp₃]
    ring
  rw [← Matrix.det_submatrix_equiv_self e (cauchyMatrix y x), hblock,
    Matrix.det_fromBlocks₁₁, hSchur, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal,
    Matrix.det_diagonal, Matrix.det_diagonal, Fin.prod_univ_one]
  change p⁻¹ * (((∏ i, row i) * D.det) * ∏ j, col j) = _
  ring

/-- The determinant squared equals the product of the two directed difference
products divided by the square of the denominator product. -/
theorem cauchyMatrix_det_sq {n : ℕ} (y x : Fin n → K) (hn : ∀ i j, x j ≠ y i) :
    (cauchyMatrix y x).det ^ 2 =
      directedNodeDifferences y * directedNodeDifferences x / cauchyDenominator y x ^ 2 := by
  induction n with
  | zero => simp [directedNodeDifferences, cauchyDenominator]
  | succ n ih =>
      let X := x ∘ Fin.succ
      let Y := y ∘ Fin.succ
      let a := x 0 - y 0
      let b := ∏ j : Fin n, (x j.succ - y 0)
      let c := ∏ i : Fin n, (x 0 - y i.succ)
      let d := cauchyDenominator Y X
      let s := ∏ i : Fin n, (y i.succ - y 0)
      let t := ∏ j : Fin n, (x 0 - x j.succ)
      have ha : a ≠ 0 := sub_ne_zero.mpr (hn 0 0)
      have hb : b ≠ 0 := Finset.prod_ne_zero_iff.mpr fun j _ => sub_ne_zero.mpr (hn 0 j.succ)
      have hc : c ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => sub_ne_zero.mpr (hn i.succ 0)
      have hd : d ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ =>
        Finset.prod_ne_zero_iff.mpr fun j _ => sub_ne_zero.mpr (hn i.succ j.succ)
      have hdet : (cauchyMatrix y x).det = a⁻¹ * (s/c) * (t/b) * (cauchyMatrix Y X).det := by
        rw [cauchy_schur_det y x hn, Finset.prod_div_distrib, Finset.prod_div_distrib]
      have hpair : (∏ i : Fin n, (y 0-y i.succ)) * (∏ i : Fin n, (y i.succ-y 0)) *
            ((∏ j : Fin n, (x 0-x j.succ)) * (∏ j : Fin n, (x j.succ-x 0))) = s^2 * t^2 := by
        calc
          _ = ∏ i : Fin n, (y 0-y i.succ) * (y i.succ-y 0) *
                ((x 0-x i.succ) * (x i.succ-x 0)) := by
            simp only [Finset.prod_mul_distrib]
          _ = ∏ i : Fin n, (y i.succ-y 0)^2 * (x 0-x i.succ)^2 := by
            apply Finset.prod_congr rfl
            intro i _
            ring
          _ = _ := by simp only [Finset.prod_mul_distrib, Finset.prod_pow, s, t]
      rw [hdet, mul_pow, mul_pow, mul_pow, ih Y X (fun i j => hn i.succ j.succ),
        directedNodeDifferences_succ y, directedNodeDifferences_succ x,
        cauchyDenominator_succ y x]
      change (a⁻¹) ^ 2 * (s/c)^2 * (t/b)^2 *
          (directedNodeDifferences Y * directedNodeDifferences X / d^2) = _
      have hproduct :
          ((∏ i : Fin n, (y 0-y i.succ)) * s * directedNodeDifferences Y) *
            (t*(∏ j : Fin n, (x j.succ-x 0))*directedNodeDifferences X) =
              s^2*t^2*directedNodeDifferences Y*directedNodeDifferences X := by
        calc
          _ = ((∏ i : Fin n, (y 0-y i.succ)) * s *
            (t * ∏ j : Fin n, (x j.succ-x 0))) *
              (directedNodeDifferences Y * directedNodeDifferences X) := by ring
          _ = _ := by rw [hpair]; ring
      rw [hproduct]
      change _ = _ / (a*b*c*d)^2
      field_simp [ha, hb, hc, hd]
      ring


end

end MOC
