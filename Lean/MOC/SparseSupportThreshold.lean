import MOC.OrderFourThreeZeroMinorObstruction
import MOC.SparseUnitaryUniversalWeights
import MOC.UniversalWeightsBlockRestriction

/-! Identity padding of the order-four obstruction to a universal law. -/

open Matrix BigOperators

namespace MOC

private theorem supportEntryCount_eq_sum_indicators {ι : Type*} [Fintype ι]
    (U : Matrix ι ι ℂ) :
    supportEntryCount U = ∑ i, ∑ j, if U i j ≠ 0 then 1 else 0 := by
  classical
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_boole]
  congr 1
  ext j
  simp [supportColumns]

/-- Block diagonal matrices have additive support counts. -/
theorem supportEntryCount_directSum {ι κ : Type*} [Fintype ι] [Fintype κ]
    (U : Matrix ι ι ℂ) (V : Matrix κ κ ℂ) :
    supportEntryCount (fromBlocks U 0 0 V) = supportEntryCount U + supportEntryCount V := by
  simp [supportEntryCount_eq_sum_indicators, Fintype.sum_sum_type, Matrix.fromBlocks]

/-- Relabeling the rows and columns preserves the number of nonzero entries. -/
theorem supportEntryCount_reindex {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e f : κ ≃ ι) (U : Matrix ι ι ℂ) :
    supportEntryCount (U.submatrix e f) = supportEntryCount U := by
  simp only [supportEntryCount_eq_sum_indicators, Matrix.submatrix_apply]
  calc
    _ = ∑ i, ∑ j, if U (e i) j ≠ 0 then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      exact Equiv.sum_comp f (fun j => if U (e i) j ≠ 0 then (1 : ℕ) else 0)
    _ = _ := Equiv.sum_comp e (fun i => ∑ j, if U i j ≠ 0 then (1 : ℕ) else 0)

theorem supportEntryCount_fourThreeZeroMixer : supportEntryCount fourThreeZeroMixer = 13 := by
  rw [supportEntryCount_eq_sum_indicators]
  simp only [ne_eq, fourThreeZeroMixer_entry_eq_zero]
  decide

theorem supportEntryCount_identity {ι : Type*} [Fintype ι] [DecidableEq ι] :
    supportEntryCount (1 : Matrix ι ι ℂ) = Fintype.card ι := by
  simp [supportEntryCount_eq_sum_indicators, Matrix.one_apply]

/-- Pad the thirteen-entry obstruction with an identity block. -/
noncomputable def paddedThreeZeroMixer (k : ℕ) : Matrix (Fin 4 ⊕ Fin k) (Fin 4 ⊕ Fin k) ℂ :=
  fromBlocks fourThreeZeroMixer 0 0 (1 : Matrix (Fin k) (Fin k) ℂ)

theorem paddedThreeZeroMixer_unitary (k : ℕ) : IsUnitary (paddedThreeZeroMixer k) :=
  unitary_directSum fourThreeZeroMixer_unitary (by constructor <;> simp)

theorem paddedThreeZeroMixer_supportEntryCount (k : ℕ) :
    supportEntryCount (paddedThreeZeroMixer k) = (4 + k) + 9 := by
  rw [paddedThreeZeroMixer, supportEntryCount_directSum, supportEntryCount_fourThreeZeroMixer,
    supportEntryCount_identity, Fintype.card_fin]
  omega

/-- The padded unitary has no spectrum-independent probability law. -/
theorem paddedThreeZeroMixer_no_universalMatchingWeights (k : ℕ) :
    ¬ HasUniversalMatchingWeights (paddedThreeZeroMixer k) := by
  intro hw
  exact fourThreeZeroMixer_no_universalMatchingWeights
    (universal_matching_weights_left_of_directSum fourThreeZeroMixer_unitary
      (show IsUnitary (1 : Matrix (Fin k) (Fin k) ℂ) by constructor <;> simp) hw)

/-- Every order of at least four has a unitary with exactly nine nonzero
entries in excess of the order that admits no universal matching law. -/
theorem exists_no_universalMatchingWeights_supportEntryCount_eq_card_add_nine
    {ι : Type*} [Fintype ι] [DecidableEq ι] (hn : 4 ≤ Fintype.card ι) :
    ∃ U : Matrix ι ι ℂ, IsUnitary U ∧ supportEntryCount U = Fintype.card ι + 9 ∧
      ¬ HasUniversalMatchingWeights U := by
  classical
  let k := Fintype.card ι - 4
  have hk : 4 + k = Fintype.card ι := by dsimp [k]; omega
  let e : ι ≃ Fin 4 ⊕ Fin k := Fintype.equivOfCardEq (by simp [hk])
  refine ⟨(paddedThreeZeroMixer k).submatrix e e,
    unitary_reindex e e (paddedThreeZeroMixer_unitary k), ?_, ?_⟩
  · rw [supportEntryCount_reindex, paddedThreeZeroMixer_supportEntryCount, hk]
  · intro hw
    exact paddedThreeZeroMixer_no_universalMatchingWeights k
      ((hasUniversalMatchingWeights_reindex_iff e e _).mp hw)

/-- In every order of at least four some unitary has no probability law
that gives all squared minors as subset-image probabilities. -/
theorem exists_no_common_squared_minor_law_of_card_ge_four
    {ι : Type*} [Fintype ι] [DecidableEq ι] (hn : 4 ≤ Fintype.card ι) :
    ∃ U : Matrix ι ι ℂ, IsUnitary U ∧
      ¬ ∃ w : Equiv.Perm ι → ℝ, (∀ σ, 0 ≤ w σ) ∧ (∑ σ, w σ = 1) ∧
        ∀ I J : Finset ι, subsetMinorSq U I J =
          ∑ σ ∈ Finset.univ.filter (fun σ : Equiv.Perm ι => J.map σ.toEmbedding = I), w σ := by
  obtain ⟨U, hU, _, hfail⟩ :=
    exists_no_universalMatchingWeights_supportEntryCount_eq_card_add_nine hn
  refine ⟨U, hU, ?_⟩
  rintro ⟨w, hnonnegative, hmass, hminor⟩
  apply hfail
  refine ⟨w, hnonnegative, hmass, fun a b => ?_⟩
  simpa only [weightedMatchingValue, id_eq] using
    determinantValue_eq_sum_of_indexed_minor_law a b U hU id w hminor

/-- For each order of at least four, the largest total support bound
that guarantees universal matching weights is the order plus eight. -/
theorem universalMatchingWeights_supportEntryCount_threshold
    {ι : Type*} [Fintype ι] [DecidableEq ι] (hn : 4 ≤ Fintype.card ι) (t : ℕ) :
    (∀ U : Matrix ι ι ℂ, IsUnitary U → supportEntryCount U ≤ t →
      HasUniversalMatchingWeights U) ↔ t ≤ Fintype.card ι + 8 := by
  constructor
  · intro hall
    obtain ⟨U, hU, hc, hfail⟩ :=
      exists_no_universalMatchingWeights_supportEntryCount_eq_card_add_nine hn
    by_contra! ht
    exact hfail (hall U hU (by omega))
  · intro ht U hU hc
    exact hasUniversalMatchingWeights_of_supportEntryCount_le_card_add_eight hU (hc.trans ht)

end MOC
