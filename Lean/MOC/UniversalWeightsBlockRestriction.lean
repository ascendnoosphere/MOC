import MOC.PairedBlockUniversalWeights
import MOC.SubsetMarkerTest

/-! A universal law restricts to a diagonal block of a unitary matrix. -/

open BigOperators Finset Matrix

namespace MOC

noncomputable section

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- Nonnegative universal weights for the direct sum restrict to the left block. -/
theorem universal_matching_weights_left_of_directSum {U : Matrix ι ι ℂ} {V : Matrix κ κ ℂ}
    (hU : IsUnitary U) (hV : IsUnitary V)
    (h : HasUniversalMatchingWeights (fromBlocks U 0 0 V)) : HasUniversalMatchingWeights U := by
  classical
  obtain ⟨w, hw, hs, hd⟩ := h
  let W : Matrix (ι ⊕ κ) (ι ⊕ κ) ℂ := fromBlocks U 0 0 V
  have hW : IsUnitary W := unitary_directSum hU hV
  have hcross (σ : Equiv.Perm (ι ⊕ κ)) (i : ι) (j : κ)
      (hσ : σ (.inl i) = .inr j) : w σ = 0 := by
    let I : Finset (ι ⊕ κ) := {.inr j}
    let J : Finset (ι ⊕ κ) := {.inl i}
    have he := hd (fun x => if x ∈ I then 0 else 1) (fun x => if x ∈ J then 1 else 0)
    change determinantValue _ _ W = _ at he
    rw [determinantValue_subset_marker _ hW I J (by simp [I, J]),
      weightedMatchingValue_subset_marker w I J (by simp [I, J])] at he
    have hz : subsetMinorSq W I J = 0 := by
      rw [show I = {.inr j} from rfl, show J = {.inl i} from rfl,
        subsetMinorSq_singleton _ hW]
      change Complex.normSq (0 : ℂ) = 0
      simp
    rw [hz, Complex.ofReal_zero] at he
    have hs₀ := Complex.ofReal_injective (he.symm.trans Complex.ofReal_zero.symm)
    exact (sum_eq_zero_iff_of_nonneg (fun τ _ => hw τ)).mp hs₀ σ (by simp [I, J, hσ])
  have hleft (σ : Equiv.Perm (ι ⊕ κ)) (hσ : w σ ≠ 0) (i : ι) :
      ∃ j : ι, σ (.inl i) = .inl j := by
    cases hsi : σ (.inl i) with
    | inl j => exact ⟨j, rfl⟩
    | inr j => exact False.elim (hσ (hcross σ i j hsi))
  let f (σ : Equiv.Perm (ι ⊕ κ)) (hσ : w σ ≠ 0) (i : ι) : ι :=
    Classical.choose (hleft σ hσ i)
  have hf (σ : Equiv.Perm (ι ⊕ κ)) (hσ : w σ ≠ 0) (i : ι) :
      σ (.inl i) = .inl (f σ hσ i) := Classical.choose_spec (hleft σ hσ i)
  have hf_inj (σ : Equiv.Perm (ι ⊕ κ)) (hσ : w σ ≠ 0) :
      Function.Injective (f σ hσ) := by
    intro i j hij
    exact Sum.inl_injective (σ.injective ((hf σ hσ i).trans (hij ▸ (hf σ hσ j).symm)))
  let p (σ : Equiv.Perm (ι ⊕ κ)) : Equiv.Perm ι :=
    if hσ : w σ ≠ 0 then
      Equiv.ofBijective (f σ hσ) ⟨hf_inj σ hσ, Finite.injective_iff_surjective.mp (hf_inj σ hσ)⟩
    else Equiv.refl _
  have hp (σ : Equiv.Perm (ι ⊕ κ)) (hσ : w σ ≠ 0) (i : ι) :
      σ (.inl i) = .inl (p σ i) := by
    dsimp only [p]
    rw [dif_pos hσ]
    exact hf σ hσ i
  have hr (σ : Equiv.Perm (ι ⊕ κ)) (hσ : w σ ≠ 0) (j : κ) :
      ∃ k : κ, σ (.inr j) = .inr k := by
    cases hsj : σ (.inr j) with
    | inl i =>
      obtain ⟨k, hk⟩ := (p σ).surjective i
      rw [← hk, ← hp σ hσ k] at hsj
      exact False.elim (Sum.inr_ne_inl (σ.injective hsj))
    | inr k => exact ⟨k, rfl⟩
  apply universalMatchingWeights_of_indexed p w hw hs
  intro a b
  let a' : ι ⊕ κ → ℂ := Sum.elim a 1
  let b' : ι ⊕ κ → ℂ := Sum.elim b 0
  have hdet : determinantValue a' b' W = determinantValue a b U := by
    unfold a' b' W determinantValue
    rw [← Matrix.fromBlocks_diagonal, ← Matrix.fromBlocks_diagonal,
      Matrix.fromBlocks_conjTranspose]
    simp only [Matrix.fromBlocks_multiply, Matrix.fromBlocks_add, Matrix.det_fromBlocks_zero₂₁,
      Matrix.conjTranspose_zero, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add,
      Pi.one_def, Pi.zero_def, Matrix.diagonal_one, Matrix.diagonal_zero, Matrix.det_one, mul_one]
  rw [← hdet]
  change determinantValue a' b' (fromBlocks U 0 0 V) = _
  rw [hd, weightedMatchingValue]
  apply sum_congr rfl
  intro σ _
  by_cases hσ : w σ ≠ 0
  · congr 1
    rw [matchingProduct, Fintype.prod_sum_type, matchingProduct]
    rw [show (∏ j : κ, (a' (σ (.inr j)) + b' (.inr j))) = 1 by
      apply Finset.prod_eq_one
      intro j _
      obtain ⟨k, hk⟩ := hr σ hσ j
      rw [hk]
      simp [a', b']]
    simp [hp σ hσ, a', b']
  · simp [not_not.mp hσ]

end

end MOC
