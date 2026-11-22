import MOC.Small
import Mathlib.Logic.Equiv.Sum

open Matrix

namespace MOC

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- An identity block on the complement of `S` preserves a determinant-hull
inclusion on `S`. The complement can have arbitrary cardinality. -/
theorem holds_of_identity_outside (a b : ι → ℂ) {U : Matrix ι ι ℂ}
    (hU : IsUnitary U) (S : Finset ι) (hsmall : Conjecture S)
    (hout : ∀ i j, i ∉ S ∨ j ∉ S → U i j = (1 : Matrix ι ι ℂ) i j) :
    Holds a b U := by
  classical
  let T := {i : ι // i ∉ S}
  let e : S ⊕ T ≃ ι := Equiv.sumCompl (fun i => i ∈ S)
  let V : Matrix S S ℂ := U.submatrix Subtype.val Subtype.val
  have hblock : U.submatrix e e = fromBlocks V 0 0 (1 : Matrix T T ℂ) := by
    ext i j : 1
    rcases i with i | i <;> rcases j with j | j
    · rfl
    · change U (i : ι) (j : ι) = 0
      rw [hout _ _ (Or.inr j.property)]
      exact Matrix.one_apply_ne (fun h : (i : ι) = (j : ι) => j.property (h ▸ i.property))
    · change U (i : ι) (j : ι) = 0
      rw [hout _ _ (Or.inl i.property)]
      exact Matrix.one_apply_ne (fun h : (i : ι) = (j : ι) => i.property (h.symm ▸ j.property))
    · change U (i : ι) (j : ι) = (1 : Matrix T T ℂ) i j
      rw [hout _ _ (Or.inl i.property)]
      by_cases hij : i = j
      · subst j
        simp only [Matrix.one_apply_eq]
      · have hval : (i : ι) ≠ (j : ι) := fun h => hij (Subtype.ext h)
        rw [Matrix.one_apply_ne hval, Matrix.one_apply_ne hij]
  have hVU : IsUnitary V := by
    have he := unitary_reindex e e hU
    rw [hblock] at he
    exact (unitary_directSum_iff.mp he).1
  have hsplit (f : ι → ℂ) : Sum.elim (fun i : S => f i) (fun j : T => f j) = f ∘ e := by
    funext x
    cases x <;> rfl
  apply (holds_reindex_iff e e a b U).mp
  rw [hblock, ← hsplit a, ← hsplit b]
  exact holds_directSum _ _ _ _ _ _ (hsmall _ _ V hVU) (holds_identity _ _)

/-- A unitary perturbation of the identity supported on at most `k` indices
is covered by the finite-order conjectures through `k`. -/
theorem holds_of_supported_unitary_perturbation {k : ℕ}
    (hsmall : ∀ m : ℕ, m ≤ k → Conjecture (Fin m))
    (a b : ι → ℂ) (M : Matrix ι ι ℂ) (S : Finset ι) (hcard : S.card ≤ k)
    (hU : IsUnitary (1 + M)) (hM : ∀ i j, i ∉ S ∨ j ∉ S → M i j = 0) :
    Holds a b (1 + M) := by
  have hS : Conjecture S := (conjecture_reindex_iff S.equivFin).mpr (hsmall S.card hcard)
  apply holds_of_identity_outside a b hU S hS
  intro i j hij
  simp only [Matrix.add_apply, hM i j hij, add_zero]

end

end MOC
