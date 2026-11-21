import MOC.Geometry
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.Tactic.LinearCombination

/-! An exact determinant reduction at a pole of the common Möbius change. -/

open BigOperators Matrix

namespace MOC

noncomputable section

variable {n : ℕ}

/-- The principal compression of the unitary conjugate of the shifted reciprocal spectrum. -/
def poleCompression (a b : Fin (n + 1) → ℂ) (U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (i : Fin (n + 1)) : Matrix (Fin n) (Fin n) ℂ :=
  (U * diagonal (fun j => (b j + a i)⁻¹) * Uᴴ).submatrix i.succAbove i.succAbove

/-- The matching product of shifted reciprocals after dropping the pole row and its match. -/
def poleMatchingProduct (a b : Fin (n + 1) → ℂ) (i : Fin (n + 1))
    (σ : Equiv.Perm (Fin (n + 1))) : ℂ :=
  ∏ k : Fin n, ((a (i.succAbove k) - a i)⁻¹ + (b (σ.symm (i.succAbove k)) + a i)⁻¹)

/-- The common factor in the determinant and all matching products at the pole. -/
def poleFactor (a b : Fin (n + 1) → ℂ) (i : Fin (n + 1)) : ℂ :=
  (∏ k : Fin n, (a (i.succAbove k) - a i)) * ∏ j, (b j + a i)

theorem determinantValue_pole (a b : Fin (n + 1) → ℂ)
    (U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (hU : IsUnitary U) (i : Fin (n + 1))
    (ha : ∀ k ≠ i, a k - a i ≠ 0) (hb : ∀ j, b j + a i ≠ 0) :
    determinantValue a b U = poleFactor a b i *
      (diagonal (fun k => (a (i.succAbove k) - a i)⁻¹) + poleCompression a b U i).det := by
  let α : Fin (n + 1) → ℂ := fun k => a k - a i
  let β : Fin (n + 1) → ℂ := fun j => b j + a i
  let B := U * diagonal β * Uᴴ
  let Bi := U * diagonal (fun j => (β j)⁻¹) * Uᴴ
  let L := 1 + diagonal α * Bi
  have hshift : determinantValue α β U = determinantValue a b U := by
    simpa only [α, β, sub_eq_add_neg, neg_neg] using determinantValue_shift a b hU (-a i)
  have hdiag : diagonal (fun j => (β j)⁻¹) * diagonal β = 1 := by
    simp [β, Matrix.diagonal_mul_diagonal, inv_mul_cancel₀, hb]
  have hBi : Bi * B = 1 := by
    calc
      _ = U * (diagonal (fun j => (β j)⁻¹) * (Uᴴ * U) * diagonal β) * Uᴴ := by
        simp only [Bi, B, Matrix.mul_assoc]
      _ = 1 := by rw [hU.2, Matrix.mul_one, hdiag, Matrix.mul_one, hU.1]
  have hBdet : B.det = ∏ j, β j := by
    rw [show B = U * diagonal β * Uᴴ from rfl, det_unitary_conjugation U _ hU,
      Matrix.det_diagonal]
  have hfactor : diagonal α + B = L * B := by
    symm
    rw [show L = 1 + diagonal α * Bi from rfl, Matrix.add_mul, Matrix.one_mul,
      Matrix.mul_assoc, hBi, Matrix.mul_one]
    exact add_comm B (diagonal α)
  have hrow (j : Fin (n + 1)) : L i j = (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) i j := by
    simp [L, Matrix.diagonal_mul, α]
  have hsign : (-1 : ℂ) ^ (i + i : ℕ) = 1 := by
    have hdouble : (i : ℕ) + (i : ℕ) = 2 * (i : ℕ) := by omega
    rw [hdouble, pow_mul (-1 : ℂ) 2 (i : ℕ), neg_one_sq, one_pow]
  have hLaplace : L.det = (L.submatrix i.succAbove i.succAbove).det := by
    rw [Matrix.det_succ_row L i, Finset.sum_eq_single i]
    · simp only [hrow, Matrix.one_apply_eq, hsign, one_mul]
    · intro j _ hj
      rw [hrow, Matrix.one_apply_ne hj.symm, mul_zero, zero_mul]
    · simp
  have hblock : L.submatrix i.succAbove i.succAbove =
      1 + diagonal (α ∘ i.succAbove) * poleCompression a b U i := by
    ext r s : 1
    simp only [L, Bi, β, poleCompression, Matrix.submatrix_apply, Matrix.add_apply,
      Matrix.diagonal_mul, Matrix.one_apply, Fin.succAbove_right_inj, Function.comp_apply]
  have hsmallDiag : diagonal (α ∘ i.succAbove) *
      diagonal (fun k => (α (i.succAbove k))⁻¹) = 1 := by
    have hne (k : Fin n) : α (i.succAbove k) ≠ 0 := ha _ (i.succAbove_ne k)
    simp [Matrix.diagonal_mul_diagonal, Function.comp_apply, mul_inv_cancel₀, hne]
  have hsmall : diagonal (α ∘ i.succAbove) *
      (diagonal (fun k => (α (i.succAbove k))⁻¹) + poleCompression a b U i) =
      1 + diagonal (α ∘ i.succAbove) * poleCompression a b U i := by
    rw [Matrix.mul_add, hsmallDiag]
  rw [← hshift]
  change (diagonal α + B).det = _
  rw [hfactor, Matrix.det_mul, hLaplace, hblock, ← hsmall, Matrix.det_mul,
    Matrix.det_diagonal, hBdet]
  unfold poleFactor
  change ((∏ k : Fin n, α (i.succAbove k)) *
      (diagonal (fun k => (α (i.succAbove k))⁻¹) + poleCompression a b U i).det) *
        (∏ j, β j) = _
  ring

theorem matchingProduct_pole (a b : Fin (n + 1) → ℂ) (i : Fin (n + 1))
    (σ : Equiv.Perm (Fin (n + 1))) (ha : ∀ k ≠ i, a k - a i ≠ 0)
    (hb : ∀ j, b j + a i ≠ 0) :
    matchingProduct a b σ = poleFactor a b i * poleMatchingProduct a b i σ := by
  let α : Fin (n + 1) → ℂ := fun k => a k - a i
  let β : Fin (n + 1) → ℂ := fun j => b j + a i
  have hshift : matchingProduct α β σ = matchingProduct a b σ := by
    simpa only [α, β, sub_eq_add_neg, neg_neg] using matchingProduct_shift a b (-a i) σ
  have hmatch : matchingProduct α β σ = ∏ k, (α k + β (σ.symm k)) := by
    simpa only [Equiv.symm_symm] using matchingProduct_inverse α β σ.symm
  have hβ : (∏ j, β j) = β (σ.symm i) * ∏ k : Fin n, β (σ.symm (i.succAbove k)) := by
    calc
      _ = ∏ k, β (σ.symm k) := (Equiv.prod_comp σ.symm β).symm
      _ = _ := Fin.prod_univ_succAbove (fun k => β (σ.symm k)) i
  have hterm (k : Fin n) : α (i.succAbove k) + β (σ.symm (i.succAbove k)) =
      (α (i.succAbove k) * β (σ.symm (i.succAbove k))) *
        ((α (i.succAbove k))⁻¹ + (β (σ.symm (i.succAbove k)))⁻¹) := by
    have ha' : α (i.succAbove k) ≠ 0 := ha _ (i.succAbove_ne k)
    have hb' : β (σ.symm (i.succAbove k)) ≠ 0 := hb _
    field_simp [ha', hb']
    ring
  rw [← hshift, hmatch, Fin.prod_univ_succAbove _ i]
  change (α i + β (σ.symm i)) * (∏ k : Fin n, (α (i.succAbove k) + β (σ.symm (i.succAbove k)))) =
    ((∏ k : Fin n, α (i.succAbove k)) * ∏ j, β j) *
      ∏ k : Fin n, ((α (i.succAbove k))⁻¹ + (β (σ.symm (i.succAbove k)))⁻¹)
  rw [show α i = 0 from sub_self _, zero_add, hβ]
  simp_rw [hterm, Finset.prod_mul_distrib]
  ring

/-- The full-order hull inclusion is equivalent to the pole-compressed determinant inclusion. -/
theorem holds_iff_poleCompression (a b : Fin (n + 1) → ℂ)
    (U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (hU : IsUnitary U) (i : Fin (n + 1))
    (ha : ∀ k ≠ i, a k - a i ≠ 0) (hb : ∀ j, b j + a i ≠ 0) :
    Holds a b U ↔
      (diagonal (fun k => (a (i.succAbove k) - a i)⁻¹) + poleCompression a b U i).det ∈
        convexHull ℝ (Set.range (poleMatchingProduct a b i)) := by
  have hk : poleFactor a b i ≠ 0 := by
    exact mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun k _ => ha _ (i.succAbove_ne k))
      (Finset.prod_ne_zero_iff.mpr fun j _ => hb j)
  exact hull_common_factor_iff hk (determinantValue_pole a b U hU i ha hb)
    (fun σ => matchingProduct_pole a b i σ ha hb)

/-- Deleting one index of a normal matrix leaves a self-commutator given by two outer products. -/
theorem principalCompression_self_commutator (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (i : Fin (n + 1)) (hM : M * Mᴴ = Mᴴ * M) :
    let C := M.submatrix i.succAbove i.succAbove
    C * Cᴴ - Cᴴ * C =
      vecMulVec (fun r => star (M i (i.succAbove r))) (fun s => M i (i.succAbove s)) +
      vecMulVec (fun r => -M (i.succAbove r) i) (fun s => star (M (i.succAbove s) i)) := by
  intro C
  ext r s : 1
  have h := congrArg (fun W : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ =>
    W (i.succAbove r) (i.succAbove s)) hM
  change (M * Mᴴ) (i.succAbove r) (i.succAbove s) =
    (Mᴴ * M) (i.succAbove r) (i.succAbove s) at h
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply] at h
  rw [Fin.sum_univ_succAbove _ i, Fin.sum_univ_succAbove _ i] at h
  simp only [C, Matrix.sub_apply, Matrix.add_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.submatrix_apply, Matrix.vecMulVec_apply, neg_mul]
  linear_combination h

/-- The self-commutator of a principal codimension-one compression of a normal matrix
has rank at most two. -/
theorem principalCompression_self_commutator_rank_le_two
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (i : Fin (n + 1))
    (hM : M * Mᴴ = Mᴴ * M) :
    let C := M.submatrix i.succAbove i.succAbove
    (C * Cᴴ - Cᴴ * C).toLin'.rank ≤ 2 := by
  dsimp only
  rw [principalCompression_self_commutator M i hM, map_add]
  refine (LinearMap.rank_add_le _ _).trans ?_
  rw [← one_add_one_eq_two]
  exact add_le_add (Matrix.rank_vecMulVec _ _) (Matrix.rank_vecMulVec _ _)

end

end MOC
