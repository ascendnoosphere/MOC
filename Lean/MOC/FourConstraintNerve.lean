import MOC.FourMatchingMarginalObstructions
import MOC.FourSupportCostProfiles

/-! A minimally inconsistent family of thirteen squared-minor constraints
for one rational order-four mixer. -/

open BigOperators Finset Matrix

namespace MOC

/-- The thirteen singleton and pair constraints in the order-four certificate. -/
def fourConstraintRay : Fin 13 → Fin 34 := ![1, 3, 6, 7, 9, 12, 13, 16, 18, 25, 28, 30, 33]

private def fourConstraintTargetNumerator : Fin 13 → ℕ :=
  ![197136, 102400, 250000, 90000, 85264, 160000, 90000, 18225, 11664, 90000,
    90000, 34225, 32400]

private def fourConstraintEvent (k : Fin 13) (p : Fin 24) : ℤ :=
  ordinaryCostRayInt (fourConstraintRay k) p

private theorem fourConstraintTarget_eq (k : Fin 13) :
    subsetMinorSq fourMarginalMixer (ordinaryCostRows (fourConstraintRay k))
      (ordinaryCostColumns (fourConstraintRay k)) = (fourConstraintTargetNumerator k : ℝ) / 390625 := by
  fin_cases k <;>
    norm_num [fourConstraintRay, ordinaryCostRows, ordinaryCostColumns, fourCostPair,
      fourConstraintTargetNumerator, Matrix.cons_val]
  all_goals
    first
    | rw [subsetMinorSq_singleton _ fourMarginalMixer_unitary]
    | rw [subsetMinorSq_pair _ fourMarginalMixer_unitary (by decide) (by decide)]
    norm_num [marginalMixer_entry, marginalMixerNumerator, Matrix.cons_val,
      GaussianInt.toComplex_def₂, Complex.normSq, Complex.mul_re, Complex.mul_im,
      Complex.sub_re, Complex.sub_im, Complex.inv_re, Complex.inv_im]

private def fourConstraintSeparator : Fin 13 → ℤ := ![-1, 1, -2, -1, 1, -2, -2, -1, -2, -1, 2, -1, -3]

private theorem fourConstraintSeparator_nonnegative (p : Fin 24) :
    0 ≤ 3 + ∑ k, fourConstraintSeparator k * fourConstraintEvent k p :=
  (by decide +kernel : ∀ p : Fin 24,
    0 ≤ 3 + ∑ k, fourConstraintSeparator k * fourConstraintEvent k p) p

private theorem fourConstraintSeparator_target :
    3 * 390625 + ∑ k, fourConstraintSeparator k * (fourConstraintTargetNumerator k : ℤ) = -10575 := by
  decide +kernel

/-- Each row gives the numerators of a law after omitting its corresponding
constraint. The common denominator is `1562500`. -/
private def fourConstraintDeletionWeights : Fin 13 → Fin 24 → ℕ := ![
  ![40644, 0, 0, 0, 0, 46656, 32256, 0, 360000, 230400, 0, 82944, 14400, 0, 115200, 0, 0, 230400, 0, 0, 0, 0, 313344, 96256],
  ![0, 0, 0, 0, 0, 4356, 72900, 0, 360000, 230400, 0, 125244, 14400, 0, 72900, 0, 82944, 147456, 42300, 0, 0, 0, 272700, 136900],
  ![0, 0, 4356, 0, 0, 0, 72900, 0, 199800, 303300, 155844, 56700, 82944, 129600, 0, 0, 0, 147456, 46656, 0, 0, 72900, 230400, 59644],
  ![0, 0, 4356, 0, 0, 0, 72900, 0, 355644, 349956, 0, 10044, 129600, 82944, 0, 0, 0, 147456, 0, 46656, 0, 72900, 230400, 59644],
  ![0, 0, 4356, 0, 0, 0, 72900, 0, 355644, 290178, 0, 69822, 69822, 0, 0, 0, 142722, 147456, 46656, 0, 13122, 0, 217278, 132544],
  ![0, 0, 136900, 69956, 0, 0, 72900, 0, 342656, 160444, 82944, 129600, 10044, 0, 0, 0, 0, 147456, 46656, 0, 72900, 0, 290044, 0],
  ![72900, 0, 14400, 0, 0, 0, 0, 0, 428544, 230400, 0, 129600, 0, 0, 46656, 0, 0, 230400, 46656, 0, 36288, 0, 277056, 49600],
  ![0, 0, 4356, 0, 0, 0, 0, 0, 428544, 230400, 0, 129600, 82944, 0, 46656, 0, 82944, 147456, 0, 46656, 0, 26244, 230400, 106300],
  ![4356, 0, 0, 0, 0, 0, 68544, 0, 360000, 277056, 0, 82944, 61056, 0, 21888, 0, 129600, 147456, 0, 0, 46656, 0, 230400, 132544],
  ![0, 0, 4356, 0, 0, 0, 72900, 0, 345600, 360000, 10044, 0, 10044, 0, 0, 0, 202500, 147456, 46656, 0, 72900, 0, 157500, 132544],
  ![0, 69956, 136900, 0, 0, 0, 2944, 0, 140156, 362944, 82944, 199556, 80000, 0, 0, 0, 0, 77500, 46656, 0, 2944, 0, 360000, 0],
  ![4356, 0, 0, 0, 0, 0, 68544, 0, 345600, 360000, 14400, 0, 14400, 0, 0, 0, 68544, 277056, 46656, 0, 68544, 0, 291456, 2944],
  ![0, 20803, 84803, 0, 0, 0, 52097, 0, 296000, 308350, 80447, 51650, 28350, 2497, 0, 0, 0, 227903, 0, 46656, 0, 52097, 310847, 0]]

set_option maxRecDepth 2048 in
private theorem fourConstraintDeletionWeights_sum (omitted : Fin 13) :
    (∑ p, fourConstraintDeletionWeights omitted p) = 1562500 :=
  (by decide +kernel : ∀ omitted : Fin 13,
    (∑ p, fourConstraintDeletionWeights omitted p) = 1562500) omitted

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
private theorem fourConstraintDeletionWeights_event (omitted k : Fin 13) (hk : k ≠ omitted) :
    (∑ p, (fourConstraintDeletionWeights omitted p : ℤ) * fourConstraintEvent k p) =
      4 * (fourConstraintTargetNumerator k : ℤ) := by
  have h : ∀ (i j : Fin 13), j ≠ i →
      (∑ p, (fourConstraintDeletionWeights i p : ℤ) * fourConstraintEvent j p) =
        4 * (fourConstraintTargetNumerator j : ℤ) := by
    intro i
    fin_cases i <;> decide +kernel
  exact h omitted k hk

noncomputable section

/-- A face of this constraint nerve is a set of probes with one common
probability law on the twenty-four permutations. -/
def FourConstraintFeasible (s : Finset (Fin 13)) : Prop :=
  ∃ w : Fin 24 → ℝ, (∀ p, 0 ≤ w p) ∧ (∑ p, w p) = 1 ∧
    ∀ k ∈ s, (∑ p, w p * ordinaryCostRay (fourConstraintRay k) p) =
      subsetMinorSq fourMarginalMixer (ordinaryCostRows (fourConstraintRay k))
        (ordinaryCostColumns (fourConstraintRay k))

private theorem not_fourConstraintFeasible_univ : ¬ FourConstraintFeasible univ := by
  rintro ⟨w, hw, hsum, htarget⟩
  have he (k : Fin 13) : (∑ p, w p * (fourConstraintEvent k p : ℝ)) =
      (fourConstraintTargetNumerator k : ℝ) / 390625 := by
    have h := htarget k (Finset.mem_univ k)
    rw [fourConstraintTarget_eq] at h
    exact h
  have hp (p : Fin 24) : 0 ≤ (3 : ℝ) +
      ∑ k, (fourConstraintSeparator k : ℝ) * (fourConstraintEvent k p : ℝ) := by
    exact_mod_cast fourConstraintSeparator_nonnegative p
  have hn := Finset.sum_nonneg (fun p (_ : p ∈ (univ : Finset (Fin 24))) => mul_nonneg (hw p) (hp p))
  simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum] at hn
  rw [← Finset.sum_mul, hsum, one_mul, Finset.sum_comm] at hn
  have ht (k : Fin 13) :
      (∑ p, w p * ((fourConstraintSeparator k : ℝ) * (fourConstraintEvent k p : ℝ))) =
        (fourConstraintSeparator k : ℝ) * ((fourConstraintTargetNumerator k : ℝ) / 390625) := by
    rw [← he, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p _
    ring
  simp only [ht] at hn
  have hs : (3 : ℝ) * 390625 +
      ∑ k, (fourConstraintSeparator k : ℝ) * (fourConstraintTargetNumerator k : ℝ) = -10575 := by
    exact_mod_cast fourConstraintSeparator_target
  simp_rw [← mul_div_assoc, ← Finset.sum_div] at hn
  linarith

/-- Every proper subfamily of the thirteen probes has a common law, and
the full family has none. These are exactly the faces of a simplex boundary. -/
theorem fourConstraintFeasible_iff (s : Finset (Fin 13)) : FourConstraintFeasible s ↔ s ≠ univ := by
  constructor
  · intro h hs
    subst s
    exact not_fourConstraintFeasible_univ h
  · intro hs
    obtain ⟨omitted, ho⟩ : ∃ k : Fin 13, k ∉ s := by
      by_contra! h
      exact hs (Finset.eq_univ_iff_forall.mpr h)
    let w (p : Fin 24) : ℝ := (fourConstraintDeletionWeights omitted p : ℝ) / 1562500
    refine ⟨w, fun p => div_nonneg (Nat.cast_nonneg _) (by norm_num), ?_, ?_⟩
    · have h : (∑ p, (fourConstraintDeletionWeights omitted p : ℝ)) = 1562500 := by
        exact_mod_cast fourConstraintDeletionWeights_sum omitted
      simp only [w, ← Finset.sum_div, h]
      norm_num
    · intro k hk
      have hko : k ≠ omitted := fun h => ho (h ▸ hk)
      have h : (∑ p, (fourConstraintDeletionWeights omitted p : ℝ) *
          (fourConstraintEvent k p : ℝ)) = 4 * (fourConstraintTargetNumerator k : ℝ) := by
        exact_mod_cast fourConstraintDeletionWeights_event omitted k hko
      rw [fourConstraintTarget_eq]
      calc
        _ = (∑ p, (fourConstraintDeletionWeights omitted p : ℝ) *
            (fourConstraintEvent k p : ℝ)) / 1562500 := by
          rw [Finset.sum_div]
          apply Finset.sum_congr rfl
          intro p _
          change (_ / 1562500) * (_ : ℝ) = _
          ring
        _ = _ := by rw [h]; ring

end

private def extensionEmbedding : Fin 4 ↪ Fin 5 := Fin.castLEEmb (by decide)

private def extensionPermutationImage : Fin 13 → Fin 5 → Fin 5 := ![
  ![0, 1, 2, 3, 4], ![1, 0, 2, 3, 4], ![1, 2, 0, 3, 4], ![1, 2, 3, 0, 4],
  ![1, 3, 2, 0, 4], ![2, 0, 1, 3, 4], ![2, 3, 0, 1, 4], ![2, 3, 1, 0, 4],
  ![3, 0, 1, 2, 4], ![3, 1, 0, 2, 4], ![3, 2, 0, 1, 4], ![3, 2, 1, 0, 4],
  ![3, 2, 4, 0, 1]]

private def extensionWeight : Fin 13 → ℕ :=
  ![1089, 17136, 90000, 72000, 18000, 18000, 35136, 36864, 11664, 2736, 54864,
    18736, 14400]

private theorem extensionPermutation_bijective (p : Fin 13) :
    Function.Bijective (extensionPermutationImage p) :=
  (by decide +kernel : ∀ p : Fin 13, Function.Bijective (extensionPermutationImage p)) p

private noncomputable def extensionPermutation (p : Fin 13) : Equiv.Perm (Fin 5) :=
  Equiv.ofBijective (extensionPermutationImage p) (extensionPermutation_bijective p)

private def extensionEvent (k : Fin 13) (p : Fin 5 → Fin 5) : Prop :=
  (ordinaryCostRows (fourConstraintRay k)).image (p ∘ extensionEmbedding) =
    (ordinaryCostColumns (fourConstraintRay k)).map extensionEmbedding

private instance (k : Fin 13) (p : Fin 5 → Fin 5) : Decidable (extensionEvent k p) := by
  unfold extensionEvent
  infer_instance

private theorem extensionWeight_sum : (∑ p, extensionWeight p) = 390625 := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem extensionWeight_event (k : Fin 13) :
    (∑ p, if extensionEvent k (extensionPermutationImage p) then extensionWeight p else 0) =
      fourConstraintTargetNumerator k :=
  (by decide +kernel : ∀ k : Fin 13,
    (∑ p, if extensionEvent k (extensionPermutationImage p) then extensionWeight p else 0) =
      fourConstraintTargetNumerator k) k

noncomputable section

private abbrev paddedMixerLabels : Fin 5 ≃ Fin 4 ⊕ Fin 1 := finSumFinEquiv.symm

/-- The rational mixer with a fifth coordinate fixed. -/
def fiveConstraintMixer : Matrix (Fin 5) (Fin 5) ℂ :=
  (fromBlocks fourMarginalMixer 0 0 (1 : Matrix (Fin 1) (Fin 1) ℂ)).submatrix
    paddedMixerLabels paddedMixerLabels

theorem fiveConstraintMixer_unitary : IsUnitary fiveConstraintMixer :=
  unitary_reindex paddedMixerLabels paddedMixerLabels
    (unitary_directSum fourMarginalMixer_unitary isUnitary_one)

private theorem fiveConstraintMixer_entry (i j : Fin 4) :
    fiveConstraintMixer (extensionEmbedding i) (extensionEmbedding j) = fourMarginalMixer i j := by
  change (fromBlocks fourMarginalMixer 0 0 (1 : Matrix (Fin 1) (Fin 1) ℂ))
    (finSumFinEquiv.symm (Fin.castAdd 1 i)) (finSumFinEquiv.symm (Fin.castAdd 1 j)) = _
  rw [finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_castAdd]
  rfl

private theorem fiveConstraintMixer_minor (k : Fin 13) :
    subsetMinorSq fiveConstraintMixer ((ordinaryCostRows (fourConstraintRay k)).map extensionEmbedding)
        ((ordinaryCostColumns (fourConstraintRay k)).map extensionEmbedding) =
      subsetMinorSq fourMarginalMixer (ordinaryCostRows (fourConstraintRay k))
        (ordinaryCostColumns (fourConstraintRay k)) := by
  fin_cases k <;>
    norm_num [fourConstraintRay, ordinaryCostRows, ordinaryCostColumns, fourCostPair, Matrix.cons_val]
  all_goals
    first
    | rw [subsetMinorSq_singleton _ fiveConstraintMixer_unitary,
        subsetMinorSq_singleton _ fourMarginalMixer_unitary]
    | rw [subsetMinorSq_pair _ fiveConstraintMixer_unitary
          (extensionEmbedding.injective.ne (by decide)) (extensionEmbedding.injective.ne (by decide)),
        subsetMinorSq_pair _ fourMarginalMixer_unitary (by decide) (by decide)]
    simp only [fiveConstraintMixer_entry]

/-- The thirteen probes have a common law in the padded dimension when
the law is allowed to move the added label. -/
theorem fiveConstraintMixer_extension_law :
    ∃ (p : Fin 13 → Equiv.Perm (Fin 5)) (w : Fin 13 → ℝ),
      (∀ t, 0 ≤ w t) ∧ (∑ t, w t) = 1 ∧ ∀ k : Fin 13,
        (∑ t, if extensionEvent k (p t) then w t else 0) =
          subsetMinorSq fiveConstraintMixer
            ((ordinaryCostRows (fourConstraintRay k)).map extensionEmbedding)
            ((ordinaryCostColumns (fourConstraintRay k)).map extensionEmbedding) := by
  let w (p : Fin 13) : ℝ := (extensionWeight p : ℝ) / 390625
  refine ⟨extensionPermutation, w, fun p => div_nonneg (Nat.cast_nonneg _) (by norm_num), ?_, ?_⟩
  · have h : (∑ p, (extensionWeight p : ℝ)) = 390625 := by
      exact_mod_cast extensionWeight_sum
    simp only [w, ← Finset.sum_div, h]
    norm_num
  · intro k
    rw [fiveConstraintMixer_minor, fourConstraintTarget_eq]
    have h : (∑ p, if extensionEvent k (extensionPermutationImage p) then
        (extensionWeight p : ℝ) else 0) = (fourConstraintTargetNumerator k : ℝ) := by
      exact_mod_cast extensionWeight_event k
    calc
      _ = (∑ p, if extensionEvent k (extensionPermutationImage p) then
          (extensionWeight p : ℝ) else 0) / 390625 := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro p _
        change (if extensionEvent k (extensionPermutationImage p) then w p else 0) = _
        split_ifs <;> simp [w]
      _ = _ := by rw [h]

end

end MOC
