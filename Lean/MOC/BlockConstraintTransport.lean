import MOC.FiniteMinorLaw
import MOC.SpectralMinorDecomposition
import Mathlib.Data.Matrix.Block

/-! Squared minors and permutation constraints for diagonal blocks. -/

open BigOperators Matrix

namespace MOC

noncomputable section

variable {κ : Type*} {ι : κ → Type*}
variable [Fintype κ] [DecidableEq κ] [∀ k, Fintype (ι k)] [∀ k, DecidableEq (ι k)]

/-- A block diagonal matrix with unitary blocks is unitary. -/
theorem blockDiagonal'_isUnitary (U : ∀ k, Matrix (ι k) (ι k) ℂ)
    (hU : ∀ k, IsUnitary (U k)) : IsUnitary (Matrix.blockDiagonal' U) := by
  have h₁ : (fun k => U k * (U k)ᴴ) = 1 := funext fun k => (hU k).1
  have h₂ : (fun k => (U k)ᴴ * U k) = 1 := funext fun k => (hU k).2
  constructor <;> simp only [Matrix.blockDiagonal'_conjTranspose, ← Matrix.blockDiagonal'_mul,
    h₁, h₂, Matrix.blockDiagonal'_one]

private def finsetMapEquiv {α β : Type*} (e : α ↪ β) (s : Finset α) : s ≃ s.map e :=
  Equiv.ofBijective (fun i : s => ⟨e i.val, Finset.apply_coe_mem_map e s i⟩) (by
    constructor
    · intro i j hij
      exact Subtype.ext (e.injective (congrArg Subtype.val hij))
    · intro j
      obtain ⟨i, hi, hij⟩ := Finset.mem_map.mp j.property
      exact ⟨⟨i, hi⟩, Subtype.ext hij⟩)

/-- Row and column subsets in the same block give its local squared minor. -/
theorem subsetMinorSq_blockDiagonal'_map (U : ∀ k, Matrix (ι k) (ι k) ℂ)
    (hU : ∀ k, IsUnitary (U k)) (k : κ) (I J : Finset (ι k)) :
    subsetMinorSq (Matrix.blockDiagonal' U) (I.map (Function.Embedding.sigmaMk k))
      (J.map (Function.Embedding.sigmaMk k)) = subsetMinorSq (U k) I J := by
  let emb : ι k ↪ (Σ l, ι l) := Function.Embedding.sigmaMk k
  change subsetMinorSq (Matrix.blockDiagonal' U) (I.map emb) (J.map emb) =
    subsetMinorSq (U k) I J
  by_cases hc : I.card = J.card
  · let e : I ≃ J := Fintype.equivOfCardEq (by simpa using hc)
    let eI := finsetMapEquiv emb I
    let eJ := e.trans (finsetMapEquiv emb J)
    rw [subsetMinorSq_eq_normSq_det_submatrix _ (blockDiagonal'_isUnitary U hU) _ _ eI eJ,
      subsetMinorSq_eq_normSq_det_submatrix _ (hU k) _ _ (Equiv.refl I) e]
    have hSubmatrix : (Matrix.blockDiagonal' U).submatrix (Subtype.val ∘ eI) (Subtype.val ∘ eJ) =
        (U k).submatrix (Subtype.val ∘ Equiv.refl I) (Subtype.val ∘ e) := by
      apply Matrix.ext
      intro i j
      change Matrix.blockDiagonal' U ⟨k, i.val⟩ ⟨k, (e j).val⟩ = U k i.val (e j).val
      exact Matrix.blockDiagonal'_apply_eq U k i.val (e j).val
    rw [hSubmatrix]
  · have hm : (I.map emb).card ≠ (J.map emb).card := by
      simpa only [Finset.card_map] using hc
    simp only [subsetMinorSq, dif_neg hc, dif_neg hm]

/-- A singleton row and a singleton column in different blocks give zero. -/
theorem subsetMinorSq_blockDiagonal'_singleton_cross (U : ∀ k, Matrix (ι k) (ι k) ℂ)
    (hU : ∀ k, IsUnitary (U k)) (i j : Σ k, ι k) (hij : i.1 ≠ j.1) :
    subsetMinorSq (Matrix.blockDiagonal' U) {i} {j} = 0 := by
  rcases i with ⟨k, i⟩
  rcases j with ⟨l, j⟩
  rw [subsetMinorSq_singleton _ (blockDiagonal'_isUnitary U hU),
    Matrix.blockDiagonal'_apply_ne U i j hij, Complex.normSq_zero]

private def blockPermutationValue (σ : Equiv.Perm (Σ k, ι k))
    (h : ∀ a, (σ a).1 = a.1) (k : κ) (i : ι k) : ι k :=
  cast (congrArg ι (h ⟨k, i⟩)) (σ ⟨k, i⟩).2

private theorem blockPermutationValue_spec (σ : Equiv.Perm (Σ k, ι k))
    (h : ∀ a, (σ a).1 = a.1) (k : κ) (i : ι k) :
    σ ⟨k, i⟩ = ⟨k, blockPermutationValue σ h k i⟩ :=
  Sigma.ext (h ⟨k, i⟩) (cast_heq (congrArg ι (h ⟨k, i⟩)) (σ ⟨k, i⟩).2).symm

private theorem blockPermutationValue_bijective (σ : Equiv.Perm (Σ k, ι k))
    (h : ∀ a, (σ a).1 = a.1) (k : κ) : Function.Bijective (blockPermutationValue σ h k) := by
  have hi : Function.Injective (blockPermutationValue σ h k) := by
    intro i j hij
    have he : σ ⟨k, i⟩ = σ ⟨k, j⟩ :=
      (blockPermutationValue_spec σ h k i).trans
        ((congrArg (Sigma.mk k) hij).trans (blockPermutationValue_spec σ h k j).symm)
    exact (Function.Embedding.sigmaMk k).injective (σ.injective he)
  exact ⟨hi, Finite.injective_iff_surjective.mp hi⟩

/-- Restrict a block-preserving permutation to each block. -/
def blockPermutationRestriction (σ : Equiv.Perm (Σ k, ι k))
    (h : ∀ a, (σ a).1 = a.1) (k : κ) : Equiv.Perm (ι k) :=
  Equiv.ofBijective (blockPermutationValue σ h k) (blockPermutationValue_bijective σ h k)

/-- The family of restrictions recovers the original permutation. -/
theorem sigmaCongrRight_blockPermutationRestriction (σ : Equiv.Perm (Σ k, ι k))
    (h : ∀ a, (σ a).1 = a.1) : Equiv.sigmaCongrRight (blockPermutationRestriction σ h) = σ := by
  apply Equiv.ext
  rintro ⟨k, i⟩
  exact (blockPermutationValue_spec σ h k i).symm

/-- If every cross-block assignment has zero probability, a permutation
with nonzero weight preserves the block of every index. -/
theorem blockPreserving_of_crossBlockAssignment_zero {α : Type*} [Fintype α]
    (p : α → Equiv.Perm (Σ k, ι k)) (w : α → ℝ) (hw : ∀ a, 0 ≤ w a)
    (hcross : ∀ i j : Σ k, ι k, i.1 ≠ j.1 →
      (∑ a, w a * subsetImageEvent {i} {j} (p a)) = 0)
    (a : α) (ha : w a ≠ 0) (j : Σ k, ι k) : (p a j).1 = j.1 := by
  by_contra hij
  have hsum := hcross (p a j) j hij
  have hn (b : α) : 0 ≤ w b * subsetImageEvent {p a j} {j} (p b) := by
    apply mul_nonneg (hw b)
    unfold subsetImageEvent
    split
    · exact zero_le_one
    · exact le_rfl
  have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun b _ => hn b)).mp hsum a (Finset.mem_univ a)
  have he : subsetImageEvent {p a j} {j} (p a) = 1 := by
    rw [subsetImageEvent, Finset.map_singleton, Equiv.toEmbedding_apply, if_pos rfl]
  rw [he, mul_one] at hz
  exact ha hz

/-- A nonnegative indexed law with zero cross-block probabilities can be
written using families of block permutations on all indices of nonzero weight. -/
theorem exists_blockPermutationLaw_of_crossBlockAssignment_zero {α : Type*} [Fintype α]
    (p : α → Equiv.Perm (Σ k, ι k)) (w : α → ℝ) (hw : ∀ a, 0 ≤ w a)
    (hcross : ∀ i j : Σ k, ι k, i.1 ≠ j.1 →
      (∑ a, w a * subsetImageEvent {i} {j} (p a)) = 0) :
    ∃ ρ : α → ∀ k, Equiv.Perm (ι k),
      ∀ a, w a ≠ 0 → Equiv.sigmaCongrRight (ρ a) = p a := by
  classical
  let h (a : α) (ha : w a ≠ 0) := blockPreserving_of_crossBlockAssignment_zero p w hw hcross a ha
  let ρ (a : α) : ∀ k, Equiv.Perm (ι k) :=
    if ha : w a ≠ 0 then blockPermutationRestriction (p a) (h a ha) else fun k => Equiv.refl (ι k)
  refine ⟨ρ, fun a ha => ?_⟩
  rw [show ρ a = blockPermutationRestriction (p a) (h a ha) from dif_pos ha]
  exact sigmaCongrRight_blockPermutationRestriction (p a) (h a ha)

/-- Matching the cross-block singleton minors of a block diagonal unitary
forces the law to be a law on families of block permutations. -/
theorem exists_blockPermutationLaw_of_blockDiagonal'_singleton_law {α : Type*} [Fintype α]
    (U : ∀ k, Matrix (ι k) (ι k) ℂ) (hU : ∀ k, IsUnitary (U k))
    (p : α → Equiv.Perm (Σ k, ι k)) (w : α → ℝ) (hw : ∀ a, 0 ≤ w a)
    (hm : ∀ i j : Σ k, ι k, i.1 ≠ j.1 →
      (∑ a, w a * subsetImageEvent {i} {j} (p a)) = subsetMinorSq (Matrix.blockDiagonal' U) {i} {j}) :
    ∃ ρ : α → ∀ k, Equiv.Perm (ι k),
      ∀ a, w a ≠ 0 → Equiv.sigmaCongrRight (ρ a) = p a := by
  apply exists_blockPermutationLaw_of_crossBlockAssignment_zero p w hw
  intro i j hij
  rw [hm i j hij, subsetMinorSq_blockDiagonal'_singleton_cross U hU i j hij]

end

end MOC
