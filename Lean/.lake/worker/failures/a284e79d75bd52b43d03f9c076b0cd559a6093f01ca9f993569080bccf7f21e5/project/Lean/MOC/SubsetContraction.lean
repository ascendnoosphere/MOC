import Mathlib.Algebra.BigOperators.Fin
import Mathlib.LinearAlgebra.Matrix.PosDef

/-! The squared-norm bound for deleting a coordinate from exterior coefficients.
The recursive blocks record whether the first coordinate is present. -/

open BigOperators Matrix
open scoped ComplexOrder

namespace MOC

noncomputable section

/-- Subsets of the first (n) coordinates in two branches at each coordinate. -/
def SubsetCube : ℕ → Type
  | 0 => Unit
  | n + 1 => SubsetCube n ⊕ SubsetCube n

instance subsetCubeFintype (n : ℕ) : Fintype (SubsetCube n) :=
  match n with
  | 0 => inferInstanceAs (Fintype Unit)
  | n + 1 =>
    letI : Fintype (SubsetCube n) := subsetCubeFintype n
    inferInstanceAs (Fintype (SubsetCube n ⊕ SubsetCube n))

instance subsetCubeDecidableEq (n : ℕ) : DecidableEq (SubsetCube n) :=
  match n with
  | 0 => inferInstanceAs (DecidableEq Unit)
  | n + 1 =>
    letI : DecidableEq (SubsetCube n) := subsetCubeDecidableEq n
    inferInstanceAs (DecidableEq (SubsetCube n ⊕ SubsetCube n))

/-- Coefficient matrix of contraction by a vector in coordinate order. -/
def subsetContraction : (n : ℕ) → (Fin n → ℂ) → Matrix (SubsetCube n) (SubsetCube n) ℂ
  | 0, _ => 0
  | n + 1, u =>
    let C := subsetContraction n (fun j => u j.succ)
    fromBlocks C ((star (u 0)) • 1) 0 (-C)

private theorem contractionBlock_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C : Matrix ι ι ℂ) (u : ℂ) :
    let A := fromBlocks C (star u • (1 : Matrix ι ι ℂ)) 0 (-C)
    let D := C * Cᴴ + Cᴴ * C + (Complex.normSq u : ℂ) • (1 : Matrix ι ι ℂ)
    A * Aᴴ + Aᴴ * A = fromBlocks D 0 0 D := by
  dsimp only
  have hu : u * star u = (Complex.normSq u : ℂ) := Complex.mul_conj u
  have hu' : star u * u = (Complex.normSq u : ℂ) := by rw [mul_comm, hu]
  simp only [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, Matrix.fromBlocks_add,
    Matrix.conjTranspose_zero, Matrix.conjTranspose_smul, Matrix.conjTranspose_one, star_star,
    Matrix.conjTranspose_neg, Matrix.mul_zero, Matrix.zero_mul, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.one_mul, Matrix.mul_one, smul_smul, hu, hu', zero_add, add_zero, neg_mul, mul_neg,
    neg_neg, smul_neg, neg_add_cancel, add_neg_cancel]
  congr 1 <;> abel

/-- The two Gram matrices add to a scalar identity, giving the contraction bound. -/
theorem subsetContraction_anticommutator (n : ℕ) (u : Fin n → ℂ) :
    let C := subsetContraction n u
    C * Cᴴ + Cᴴ * C = (∑ j, (Complex.normSq (u j) : ℂ)) • (1 : Matrix _ _ ℂ) := by
  induction n with
  | zero => simp [subsetContraction]
  | succ n ih =>
    let D := subsetContraction n (fun j => u j.succ)
    let q := ∑ j : Fin n, (Complex.normSq (u j.succ) : ℂ)
    have hD : D * Dᴴ + Dᴴ * D = q • (1 : Matrix (SubsetCube n) (SubsetCube n) ℂ) :=
      ih (fun j => u j.succ)
    let z := (Complex.normSq (u 0) : ℂ)
    have hstep : D * Dᴴ + Dᴴ * D + z • (1 : Matrix (SubsetCube n) (SubsetCube n) ℂ) =
        (z + q) • (1 : Matrix (SubsetCube n) (SubsetCube n) ℂ) := by
      rw [hD, add_smul, add_comm]
    have hone : (1 : Matrix (SubsetCube n ⊕ SubsetCube n) (SubsetCube n ⊕ SubsetCube n) ℂ) =
        fromBlocks (1 : Matrix (SubsetCube n) (SubsetCube n) ℂ) 0 0 1 := by
      ext (i | i) (j | j) : 1 <;> simp [Matrix.one_apply]
    change (fromBlocks D (star (u 0) • 1) 0 (-D)) *
        (fromBlocks D (star (u 0) • 1) 0 (-D))ᴴ +
      (fromBlocks D (star (u 0) • 1) 0 (-D))ᴴ *
        (fromBlocks D (star (u 0) • 1) 0 (-D)) = _
    rw [contractionBlock_eq, hstep, Fin.sum_univ_succ, hone, Matrix.fromBlocks_smul,
      smul_zero, smul_zero]

private theorem complex_sum_normSq {ι : Type*} [Fintype ι] (v : ι → ℂ) :
    (((∑ j, Complex.normSq (v j)) : ℝ) : ℂ) = star v ⬝ᵥ v := by
  rw [Complex.ofReal_sum]
  unfold dotProduct
  apply Finset.sum_congr rfl
  intro j _
  simpa only [Pi.star_apply, mul_comm] using (Complex.mul_conj (v j)).symm

/-- Contraction by a unit vector cannot increase the total squared coefficient mass. -/
theorem subsetContraction_normSq_bound (n : ℕ) (u : Fin n → ℂ) (v : SubsetCube n → ℂ) :
    ∑ j, Complex.normSq ((subsetContraction n u *ᵥ v) j) ≤
      (∑ j, Complex.normSq (u j)) * ∑ j, Complex.normSq (v j) := by
  let C := subsetContraction n u
  have hpositive := (Matrix.posSemidef_self_mul_conjTranspose C).2 v
  have hle : star (C *ᵥ v) ⬝ᵥ (C *ᵥ v) ≤
      (∑ j, (Complex.normSq (u j) : ℂ)) * (star v ⬝ᵥ v) := calc
    _ = star v ⬝ᵥ ((Cᴴ * C) *ᵥ v) := by
      simp only [Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul]
    _ ≤ star v ⬝ᵥ ((C * Cᴴ + Cᴴ * C) *ᵥ v) := by
      rw [Matrix.add_mulVec, dotProduct_add]
      exact le_add_of_nonneg_left hpositive
    _ = _ := by
      rw [subsetContraction_anticommutator n u, Matrix.smul_mulVec_assoc, Matrix.one_mulVec,
        dotProduct_smul, smul_eq_mul]
  rw [← complex_sum_normSq (C *ᵥ v), ← complex_sum_normSq v, ← Complex.ofReal_sum,
    ← Complex.ofReal_mul] at hle
  exact Complex.ofReal_le_real.mp hle

end

end MOC
