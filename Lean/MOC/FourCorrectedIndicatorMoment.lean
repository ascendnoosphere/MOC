import MOC.FourMatchingCellMoment
import MOC.FourSubsetIndicatorCoordinates
import MOC.OrthogonalSignedWeightTransport
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Data.Real.StarOrdered

/-! The corrected moment on fourteen subset-image indicator columns. -/

open Matrix BigOperators

namespace MOC

private abbrev FourReal := Matrix (Fin 4) (Fin 4) ℝ

def fourIndicatorRowSet (i : Fin 14) : Finset (Fin 4) := fourIndicatorMask (fourIndicatorBasisMasks i).1

def fourIndicatorColSet (i : Fin 14) : Finset (Fin 4) := fourIndicatorMask (fourIndicatorBasisMasks i).2

/-- A permutation is compatible with two selected indicators if it maps both
row sets to the respective column sets. -/
def FourIndicatorCompatible (σ : FourPerm) (i j : Fin 14) : Prop :=
  (fourIndicatorRowSet i).map σ.toEmbedding = fourIndicatorColSet i ∧ (fourIndicatorRowSet j).map σ.toEmbedding = fourIndicatorColSet j

private instance (σ : FourPerm) (i j : Fin 14) : Decidable (FourIndicatorCompatible σ i j) :=
  inferInstanceAs (Decidable ((_ = _) ∧ (_ = _)))

private theorem map_perm_eq_iff (σ : FourPerm) (I J : Finset (Fin 4)) :
    I.map σ.toEmbedding = J ↔ ∀ a, a ∈ I ↔ σ a ∈ J := by
  constructor
  · intro h a
    rw [← h]
    simp only [Finset.mem_map, Equiv.toEmbedding_apply, σ.injective.eq_iff]
    simp
  · intro h
    ext b
    constructor
    · rintro hb
      obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hb
      exact (h a).mp ha
    · intro hb
      refine Finset.mem_map.mpr ⟨σ.symm b, ?_, σ.apply_symm_apply b⟩
      apply (h _).mpr
      rwa [σ.apply_symm_apply]

private theorem cellLabel_iff (σ : FourPerm) (i j : Fin 14) :
    FourIndicatorCompatible σ i j ↔ ∀ a,
      fourMatchingCell (fourIndicatorRowSet i) (fourIndicatorRowSet j) a = fourMatchingCell (fourIndicatorColSet i) (fourIndicatorColSet j) (σ a) := by
  have hpoint (a : Fin 4) :
      fourMatchingCell (fourIndicatorRowSet i) (fourIndicatorRowSet j) a = fourMatchingCell (fourIndicatorColSet i) (fourIndicatorColSet j) (σ a) ↔
        (a ∈ fourIndicatorRowSet i ↔ σ a ∈ fourIndicatorColSet i) ∧ (a ∈ fourIndicatorRowSet j ↔ σ a ∈ fourIndicatorColSet j) := by
    by_cases h₁ : a ∈ fourIndicatorRowSet i <;> by_cases h₂ : a ∈ fourIndicatorRowSet j <;>
      by_cases h₃ : σ a ∈ fourIndicatorColSet i <;> by_cases h₄ : σ a ∈ fourIndicatorColSet j <;>
      simp (disch := decide) [fourMatchingCell, h₁, h₂, h₃, h₄]
  simp only [FourIndicatorCompatible, map_perm_eq_iff, hpoint, forall_and]

private theorem basis_product (p : Fin 24) (i j : Fin 14) :
    fourIndicatorBasis p i * fourIndicatorBasis p j =
      if FourIndicatorCompatible (fourPerm p) i j then 1 else 0 := by
  classical
  change (↑(if (fourIndicatorRowSet i).map (fourPerm p).toEmbedding = fourIndicatorColSet i then 1 else (0 : ℤ)) : ℝ) *
      (↑(if (fourIndicatorRowSet j).map (fourPerm p).toEmbedding = fourIndicatorColSet j then 1 else (0 : ℤ)) : ℝ) = _
  unfold FourIndicatorCompatible
  by_cases h₁ : (fourIndicatorRowSet i).map (fourPerm p).toEmbedding = fourIndicatorColSet i <;>
    by_cases h₂ : (fourIndicatorRowSet j).map (fourPerm p).toEmbedding = fourIndicatorColSet j <;>
    simp [h₁, h₂]

private def pivotSet (a : Fin 6) : Finset (Fin 4) := fourIndicatorMask (a.castLE (by decide))

private theorem fourIndicatorRowSet_small : ∀ i : Fin 14, ∃ a : Fin 6, fourIndicatorRowSet i = pivotSet a := by
  decide +kernel

private theorem pivotSet_dispatch : ∀ a b : Fin 6,
    if Function.Injective (fourMatchingCell (pivotSet a) (pivotSet b)) then
      (a = 3 ∧ b = 5) ∨ (a = 5 ∧ b = 3)
    else pivotSet a ∩ pivotSet b = ∅ ∨ pivotSet a \ pivotSet b = ∅ ∨
      pivotSet b \ pivotSet a = ∅ ∨ (pivotSet a ∪ pivotSet b)ᶜ = ∅ := by
  decide +kernel

private theorem principalGram_basis (A : FourReal) (hA : A * Aᵀ = 1) (i j : Fin 14) :
    fourPrincipalGram A (fourIndicatorRowSet i) (fourIndicatorRowSet j) =
      A.det * (fourPrincipalCellProduct A (fourIndicatorRowSet i) (fourIndicatorRowSet j) +
        if Function.Injective (fourMatchingCell (fourIndicatorRowSet i) (fourIndicatorRowSet j)) then
          fourMatchingCorrectionCandidate A else 0) := by
  obtain ⟨a, ha⟩ := fourIndicatorRowSet_small i
  obtain ⟨b, hb⟩ := fourIndicatorRowSet_small j
  rw [ha, hb]
  have hd := pivotSet_dispatch a b
  by_cases h : Function.Injective (fourMatchingCell (pivotSet a) (pivotSet b))
  · rw [if_pos h] at hd ⊢
    have h₃ : pivotSet 3 = {0,1} := by decide
    have h₅ : pivotSet 5 = {0,2} := by decide
    rcases hd with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · rw [h₃, h₅]
      exact fourPrincipalGram_crossing A hA
    · rw [h₃, h₅, principalGram_comm A {0,2} {0,1}, principalCellProduct_comm A {0,2} {0,1}]
      exact fourPrincipalGram_crossing A hA
  · rw [if_neg h] at hd ⊢
    rw [add_zero]
    exact fourPrincipalGram_eq_cellProduct_of_empty A hA _ _ hd

/-- The signed determinant coefficient plus the alternating correction. -/
noncomputable def fourCorrectedIndicatorWeight (A : FourReal) (σ : FourPerm) : ℝ :=
  A.det * ((Equiv.Perm.sign σ : ℤ) : ℝ) * (∏ i, A i (σ i)) +
    (A.det * fourMatchingCorrectionCandidate A) * ((Equiv.Perm.sign σ : ℤ) : ℝ)

private theorem shifted_indicatorCellSum (A : FourReal) (i j : Fin 14) :
    (∑ τ : FourPerm, fourCorrectedIndicatorWeight A τ *
      (if ∀ a, fourMatchingCell (fourIndicatorRowSet i) (fourIndicatorRowSet j) a =
        fourMatchingCell (fourIndicatorRowSet i) (fourIndicatorRowSet j) (τ a) then 1 else 0)) =
      A.det * (fourPrincipalCellProduct A (fourIndicatorRowSet i) (fourIndicatorRowSet j) +
        if Function.Injective (fourMatchingCell (fourIndicatorRowSet i) (fourIndicatorRowSet j)) then
          fourMatchingCorrectionCandidate A else 0) := by
  let l := fourMatchingCell (fourIndicatorRowSet i) (fourIndicatorRowSet j)
  change (∑ τ : FourPerm, fourCorrectedIndicatorWeight A τ *
    (if ∀ a, l a = l (τ a) then 1 else 0)) = _
  have he := det_labelledMatrix_eq_signed_matching A l l
  have hs := signed_sum_matchingCell l
  calc
    _ = A.det * ((∑ τ : FourPerm, ((Equiv.Perm.sign τ : ℤ) : ℝ) *
        (if ∀ a, l a = l (τ a) then ∏ a, A a (τ a) else 0)) +
      fourMatchingCorrectionCandidate A * (∑ τ : FourPerm, ((Equiv.Perm.sign τ : ℤ) : ℝ) *
        (if ∀ a, l a = l (τ a) then 1 else 0))) := by
      simp only [mul_add, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro τ _
      by_cases h : ∀ a, l a = l (τ a)
      · simp only [fourCorrectedIndicatorWeight, if_pos h, mul_one]; ring
      · simp only [fourCorrectedIndicatorWeight, if_neg h, mul_zero, add_zero]
    _ = _ := by
      have hcell : (∑ τ : FourPerm, ((Equiv.Perm.sign τ : ℤ) : ℝ) *
            (if ∀ a, l a = l (τ a) then ∏ a, A a (τ a) else 0)) =
          fourPrincipalCellProduct A (fourIndicatorRowSet i) (fourIndicatorRowSet j) := by
        calc
          _ = (labelledMatrix A l l).det := by
            convert he.symm using 1
            apply Finset.sum_congr rfl
            intro τ _
            by_cases h : ∀ a, l a = l (τ a)
            · simp only [if_pos h]
            · simp only [if_neg h]
          _ = _ := det_labelledMatrix_fourMatchingCell A (fourIndicatorRowSet i) (fourIndicatorRowSet j)
      rw [hcell, hs]
      change A.det * (_ + fourMatchingCorrectionCandidate A * (if Function.Injective l then 1 else 0)) =
        A.det * (_ + if Function.Injective l then fourMatchingCorrectionCandidate A else 0)
      split_ifs <;> ring

/-- The basis moment entry aligned by a compatible permutation. -/
theorem correctedIndicatorMoment_entry (O : FourReal) (hO : O * Oᵀ = 1)
    (i j : Fin 14) (σ : FourPerm) (hσ : FourIndicatorCompatible σ i j) :
    (∑ p : Fin 24, fourCorrectedIndicatorWeight O (fourPerm p) *
      (fourIndicatorBasis p i * fourIndicatorBasis p j)) =
      fourPrincipalGram (O.submatrix id σ) (fourIndicatorRowSet i) (fourIndicatorRowSet j) := by
  classical
  let A := O.submatrix id σ
  let l := fourMatchingCell (fourIndicatorRowSet i) (fourIndicatorRowSet j)
  let r := fourMatchingCell (fourIndicatorColSet i) (fourIndicatorColSet j)
  have ha : A * Aᵀ = 1 := submatrix_mul_transpose_of_orthogonal O hO 1 σ
  have hσl : ∀ a, l a = r (σ a) := (cellLabel_iff σ i j).mp hσ
  have hshift (τ : FourPerm) : fourCorrectedIndicatorWeight O (σ * τ) =
      fourCorrectedIndicatorWeight A τ := by
    have h := correctedWeight_submatrix_cols O σ τ (fourMatchingCorrectionCandidate O)
    have hc := fourMatchingCorrectionCandidate_permute O hO σ
    rw [fourCorrectedIndicatorWeight]
    rw [h]
    rw [fourCorrectedIndicatorWeight, hc]
  simp only [basis_product, cellLabel_iff]
  change (∑ p : Fin 24, fourCorrectedIndicatorWeight O (fourPermEquiv p) *
    (if ∀ a, l a = r (fourPermEquiv p a) then 1 else 0)) = _
  rw [Equiv.sum_comp fourPermEquiv (fun τ => fourCorrectedIndicatorWeight O τ *
    (if ∀ a, l a = r (τ a) then 1 else 0))]
  rw [← Equiv.sum_comp (Equiv.mulLeft σ) (fun τ => fourCorrectedIndicatorWeight O τ *
    (if ∀ a, l a = r (τ a) then 1 else 0))]
  change (∑ τ : FourPerm, fourCorrectedIndicatorWeight O (σ * τ) *
    (if ∀ a, l a = r ((σ * τ) a) then 1 else 0)) = _
  simp only [hshift, Equiv.Perm.mul_apply, ← hσl]
  rw [shifted_indicatorCellSum, principalGram_basis A ha]

private theorem trace_gram_posSemidef (B : Fin 14 → Matrix (Fin 16) (Fin 16) ℝ) :
    (Matrix.of fun i j => ((B i)ᵀ * B j).trace / 16).PosSemidef := by
  let L : Matrix (Fin 16 × Fin 16) (Fin 14) ℝ :=
    Matrix.of fun x i => B i x.1 x.2 / 4
  have h : (Matrix.of fun i j => ((B i)ᵀ * B j).trace / 16) = Lᴴ * L := by
    ext i j
    simp only [Matrix.of_apply, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
      Matrix.transpose_apply, Matrix.conjTranspose_apply, L, star_trivial, Fintype.sum_prod_type]
    rw [Finset.sum_comm (f := fun a b => B i b a * B j b a), Finset.sum_div]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro b _
    ring
  rw [h]
  exact Matrix.posSemidef_conjTranspose_mul_self L

/-- A family with the aligned principal Gram entries gives a positive
corrected moment on the full indicator basis. -/
theorem correctedIndicatorMoment_posSemidef_of_trace_gram (O : FourReal) (hO : O * Oᵀ = 1)
    (B : Fin 14 → Matrix (Fin 16) (Fin 16) ℝ)
    (hAlign : ∀ (i j : Fin 14) (σ : FourPerm), FourIndicatorCompatible σ i j →
      ((B i)ᵀ * B j).trace / 16 =
        fourPrincipalGram (O.submatrix id σ) (fourIndicatorRowSet i) (fourIndicatorRowSet j))
    (hEmpty : ∀ i j : Fin 14, (¬ ∃ σ : FourPerm, FourIndicatorCompatible σ i j) →
      ((B i)ᵀ * B j).trace / 16 = 0) :
    (fourIndicatorBasisᵀ * Matrix.diagonal (fun p => fourCorrectedIndicatorWeight O (fourPerm p)) *
      fourIndicatorBasis).PosSemidef := by
  have hEq : (fourIndicatorBasisᵀ * Matrix.diagonal (fun p => fourCorrectedIndicatorWeight O (fourPerm p)) *
      fourIndicatorBasis) = (Matrix.of fun i j => ((B i)ᵀ * B j).trace / 16) := by
    ext i j
    rw [Matrix.mul_assoc, Matrix.mul_apply]
    simp only [Matrix.transpose_apply, Matrix.diagonal_mul, Matrix.of_apply]
    rw [show (∑ p, fourIndicatorBasis p i *
        (fourCorrectedIndicatorWeight O (fourPerm p) * fourIndicatorBasis p j)) =
      ∑ p, fourCorrectedIndicatorWeight O (fourPerm p) *
        (fourIndicatorBasis p i * fourIndicatorBasis p j) from
        Finset.sum_congr rfl fun p _ => mul_left_comm _ _ _]
    by_cases h : ∃ σ : FourPerm, FourIndicatorCompatible σ i j
    · obtain ⟨σ, hσ⟩ := h
      rw [correctedIndicatorMoment_entry O hO i j σ hσ, hAlign i j σ hσ]
    · rw [hEmpty i j h]
      apply Finset.sum_eq_zero
      intro p _
      rw [basis_product, if_neg (fun hp => h ⟨_, hp⟩), mul_zero]
  rw [hEq]
  exact trace_gram_posSemidef B

end MOC
