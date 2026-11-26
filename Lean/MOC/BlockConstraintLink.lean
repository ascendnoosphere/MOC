import MOC.BlockConstraintFeasibility
import MOC.BlockConstraintHomology
import MOC.BlockConstraintTransport
import MOC.FourConstraintNerve

/-! The constraint link of a direct sum is the join of the block
constraint nerves. Cross-block singleton constraints specify the link. -/

open BigOperators Finset Matrix

namespace MOC

noncomputable section

private theorem finiteLaw_pushforward_expectation {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq β] (p : α → β) (w : α → ℝ) (F : β → ℝ) :
    (∑ b, (∑ a, if p a = b then w a else 0) * F b) = ∑ a, w a * F (p a) := by
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp [ite_mul]

variable {κ : Type*} {ι : κ → Type*} [Fintype κ] [DecidableEq κ]
  [∀ k, Fintype (ι k)] [∀ k, DecidableEq (ι k)]

/-- Feasibility after imposing every cross-block singleton constraint. -/
def BlockMinorLinkFeasible {C : κ → Type*} (U : ∀ k, Matrix (ι k) (ι k) ℂ)
    (selected : ∀ k, Finset (C k)) (I J : ∀ k, C k → Finset (ι k)) : Prop :=
  ∃ w : Equiv.Perm (Σ k, ι k) → ℝ, (∀ σ, 0 ≤ w σ) ∧ (∑ σ, w σ) = 1 ∧
    (∀ i j : Σ k, ι k, i.1 ≠ j.1 →
      (∑ σ, w σ * subsetImageEvent {i} {j} σ) = 0) ∧
    ∀ k c ∈ selected k,
      let I' := (I k c).map (Function.Embedding.sigmaMk k)
      let J' := (J k c).map (Function.Embedding.sigmaMk k)
      (∑ σ, w σ * subsetImageEvent I' J' σ) =
        subsetMinorSq (Matrix.blockDiagonal' U) I' J'

/-- A face in the direct-sum link is feasible exactly when its selected
observations in each block are feasible. -/
theorem blockMinorLinkFeasible_iff {C : κ → Type*} (U : ∀ k, Matrix (ι k) (ι k) ℂ)
    (hU : ∀ k, IsUnitary (U k)) (selected : ∀ k, Finset (C k))
    (I J : ∀ k, C k → Finset (ι k)) :
    BlockMinorLinkFeasible U selected I J ↔
      ∀ k, ∃ w : Equiv.Perm (ι k) → ℝ, (∀ σ, 0 ≤ w σ) ∧ (∑ σ, w σ) = 1 ∧
        ∀ c ∈ selected k, (∑ σ, w σ * subsetImageEvent (I k c) (J k c) σ) =
          subsetMinorSq (U k) (I k c) (J k c) := by
  classical
  let target := fun k c => subsetMinorSq (U k) (I k c) (J k c)
  rw [← block_subsetImage_feasible_iff selected I J target]
  constructor
  · rintro ⟨w, hw, hm, hcross, hobs⟩
    obtain ⟨ρ, hρ⟩ := exists_blockPermutationLaw_of_crossBlockAssignment_zero
      (fun σ => σ) w hw hcross
    let W (p : ∀ k, Equiv.Perm (ι k)) := ∑ σ, if ρ σ = p then w σ else 0
    have hW (p) : 0 ≤ W p := Finset.sum_nonneg fun σ _ => by
      dsimp only [W]
      split
      · exact hw σ
      · exact le_rfl
    have hmass : ∑ p, W p = 1 := by
      simpa only [W, mul_one, hm] using
        finiteLaw_pushforward_expectation ρ w (fun _ => 1)
    refine ⟨W, hW, hmass, fun k c hc => ?_⟩
    let I' := (I k c).map (Function.Embedding.sigmaMk k)
    let J' := (J k c).map (Function.Embedding.sigmaMk k)
    change (∑ p, W p * subsetImageEvent I' J' (Equiv.sigmaCongrRight p)) = target k c
    rw [W, finiteLaw_pushforward_expectation]
    have he : (∑ σ, w σ * subsetImageEvent I' J' (Equiv.sigmaCongrRight (ρ σ))) =
        ∑ σ, w σ * subsetImageEvent I' J' σ := by
      apply Finset.sum_congr rfl
      intro σ _
      by_cases h : w σ = 0
      · simp only [h, zero_mul]
      · rw [hρ σ h]
    rw [he, hobs k c hc, subsetMinorSq_blockDiagonal'_map U hU k]
  · rintro ⟨W, hW, hm, hobs⟩
    let p (ρ : ∀ k, Equiv.Perm (ι k)) := Equiv.sigmaCongrRight ρ
    let w (σ : Equiv.Perm (Σ k, ι k)) := ∑ ρ, if p ρ = σ then W ρ else 0
    have hw (σ) : 0 ≤ w σ := Finset.sum_nonneg fun ρ _ => by
      dsimp only [w]
      split
      · exact hW ρ
      · exact le_rfl
    have hmass : ∑ σ, w σ = 1 := by
      simpa only [w, mul_one, hm] using
        finiteLaw_pushforward_expectation p W (fun _ => 1)
    refine ⟨w, hw, hmass, ?_, ?_⟩
    · intro i j hij
      rw [w, finiteLaw_pushforward_expectation]
      apply Finset.sum_eq_zero
      intro ρ _
      have he : ({j} : Finset (Σ k, ι k)).map (p ρ).toEmbedding ≠ {i} := by
        simp only [Finset.map_singleton, Equiv.toEmbedding_apply, Finset.singleton_inj]
        intro h
        exact hij ((congrArg Sigma.fst h).symm)
      simp only [subsetImageEvent, he, if_false, mul_zero]
    · intro k c hc
      dsimp only
      rw [w, finiteLaw_pushforward_expectation, subsetMinorSq_blockDiagonal'_map U hU k]
      exact hobs k c hc

theorem fourConstraintFeasible_subsetImage_iff (s : Finset (Fin 13)) :
    FourConstraintFeasible s ↔
      ∃ w : Equiv.Perm (Fin 4) → ℝ, (∀ σ, 0 ≤ w σ) ∧ (∑ σ, w σ) = 1 ∧
        ∀ k ∈ s, (∑ σ, w σ * subsetImageEvent (ordinaryCostRows (fourConstraintRay k))
          (ordinaryCostColumns (fourConstraintRay k)) σ) =
          subsetMinorSq fourMarginalMixer (ordinaryCostRows (fourConstraintRay k))
            (ordinaryCostColumns (fourConstraintRay k)) := by
  classical
  let e : Fin 24 ≃ Equiv.Perm (Fin 4) := fourPermEquiv.trans (Equiv.inv _)
  have he (r : Fin 34) (p : Fin 24) :
      ordinaryCostRay r p = subsetImageEvent (ordinaryCostRows r) (ordinaryCostColumns r) (e p) := by
    unfold ordinaryCostRay subsetImageEvent
    rw [ordinaryCostRayInt_indicator]
    change ((if (ordinaryCostColumns r).map (fourPerm p).symm.toEmbedding = ordinaryCostRows r
        then (1 : ℤ) else 0) : ℝ) = _
    rw [show e p = (fourPerm p).symm from rfl]
    split <;> norm_num
  constructor
  · rintro ⟨w, hw, hm, hobs⟩
    let v (σ : Equiv.Perm (Fin 4)) := w (e.symm σ)
    refine ⟨v, fun σ => hw _, ?_, fun k hk => ?_⟩
    · rw [← Equiv.sum_comp e v]
      simpa only [v, Equiv.symm_apply_apply] using hm
    · rw [← Equiv.sum_comp e]
      simpa only [v, Equiv.symm_apply_apply, ← he] using hobs k hk
  · rintro ⟨w, hw, hm, hobs⟩
    refine ⟨fun p => w (e p), fun p => hw _, (Equiv.sum_comp e w).trans hm, fun k hk => ?_⟩
    simp only [he]
    rw [Equiv.sum_comp e]
    exact hobs k hk

/-- For any number of copies of the order-four obstruction, the induced
link contains exactly the selections that omit a probe in every block. -/
theorem fourBlockConstraintLinkFeasible_iff {k : ℕ} (selected : Fin k → Finset (Fin 13)) :
    BlockMinorLinkFeasible (fun _ : Fin k => fourMarginalMixer) selected
      (fun _ c => ordinaryCostRows (fourConstraintRay c))
      (fun _ c => ordinaryCostColumns (fourConstraintRay c)) ↔ ∀ j, selected j ≠ univ := by
  rw [blockMinorLinkFeasible_iff _ (fun _ => fourMarginalMixer_unitary)]
  simp only [← fourConstraintFeasible_subsetImage_iff, fourConstraintFeasible_iff]

/-- The induced link on the thirteen observations per block is the
join of the corresponding simplex boundaries. -/
theorem fourBlockConstraintLinkFeasible_iff_joinFace {k : ℕ}
    (selected : BlockJoinTuple k) :
    BlockMinorLinkFeasible (fun _ : Fin k => fourMarginalMixer) selected
      (fun _ c => ordinaryCostRows (fourConstraintRay c))
      (fun _ c => ordinaryCostColumns (fourConstraintRay c)) ↔
      blockJoinVertices selected ∈ blockJoinFaces k := by
  exact (fourBlockConstraintLinkFeasible_iff selected).trans (blockJoinVertices_mem_faces selected).symm

/-- The induced link has a nonzero top cycle with integral coefficients.
The grading counts vertices and includes the empty face. -/
theorem fourBlockConstraintLink_top_cycle (k : ℕ) :
    ∃ c : BlockJoinTuple k → ℤ,
      (∀ s, c s ≠ 0 → BlockMinorLinkFeasible (fun _ : Fin k => fourMarginalMixer) s
        (fun _ i => ordinaryCostRows (fourConstraintRay i))
        (fun _ i => ordinaryCostColumns (fourConstraintRay i)) ∧ blockJoinCard s = 12 * k) ∧
      c ≠ 0 ∧ blockJoinBoundary c = 0 ∧
      ∀ d : BlockJoinTuple k → ℤ,
        (∀ s, d s ≠ 0 → BlockMinorLinkFeasible (fun _ : Fin k => fourMarginalMixer) s
          (fun _ i => ordinaryCostRows (fourConstraintRay i))
          (fun _ i => ordinaryCostColumns (fourConstraintRay i)) ∧ blockJoinCard s = 12 * k + 1) →
        blockJoinBoundary d ≠ c := by
  obtain ⟨c, hc, hn, hz, hb⟩ := blockJoin_top_cycle_witness (R := ℤ) k
  refine ⟨c, ?_, hn, hz, ?_⟩
  · intro s hs
    obtain ⟨hf, hd⟩ := hc s hs
    exact ⟨(fourBlockConstraintLinkFeasible_iff s).mpr hf, hd⟩
  · intro d hd
    apply hb d
    intro s hs
    obtain ⟨hf, hn⟩ := hd s hs
    exact ⟨(fourBlockConstraintLinkFeasible_iff s).mp hf, hn⟩

end

end MOC
