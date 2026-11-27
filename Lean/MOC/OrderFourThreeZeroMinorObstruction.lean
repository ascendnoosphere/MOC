import MOC.SubsetMarkerTest
import MOC.UniversalMatchingWeights

/-! A real unitary with three zeros for which no positive common minor law exists. -/

open BigOperators Finset Matrix

namespace MOC

noncomputable section

private def threeZeroScale : ℝ := (Real.sqrt 21)⁻¹

private theorem threeZeroScale_sq : threeZeroScale ^ 2 = 1 / 21 := by
  rw [threeZeroScale, inv_pow, Real.sq_sqrt (by norm_num : 0 ≤ (21 : ℝ))]
  norm_num

/-- An order-four matrix with three zero entries and no positive common minor law. -/
def fourThreeZeroMixer : Matrix (Fin 4) (Fin 4) ℂ :=
  Complex.ofRealHom.mapMatrix (threeZeroScale •
    (!![0, 4, -1, 2; -1, 0, 4, 2; 4, -1, 0, 2; 2, 2, 2, -3] :
      Matrix (Fin 4) (Fin 4) ℝ))

private theorem fourThreeZeroMixer_mul_adjoint :
    fourThreeZeroMixer * fourThreeZeroMixerᴴ = 1 := by
  have hs : (threeZeroScale : ℂ) ^ 2 = 1 / 21 := by
    rw [← Complex.ofReal_pow, threeZeroScale_sq]
    norm_num [Complex.ofReal_div]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [fourThreeZeroMixer, Matrix.mul_apply, Fin.sum_univ_four,
      Matrix.conjTranspose_apply, Matrix.one_apply, Complex.star_def,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail] <;>
    ring_nf <;> rw [hs] <;> norm_num

theorem fourThreeZeroMixer_unitary : IsUnitary fourThreeZeroMixer :=
  ⟨fourThreeZeroMixer_mul_adjoint, mul_eq_one_comm.mp fourThreeZeroMixer_mul_adjoint⟩

/-- The zero entries are precisely the first three diagonal positions. -/
theorem fourThreeZeroMixer_entry_eq_zero (i j : Fin 4) :
    fourThreeZeroMixer i j = 0 ↔ i = j ∧ i ≠ 3 := by
  have hs : (threeZeroScale : ℂ) ≠ 0 := by
    exact_mod_cast (inv_ne_zero (Real.sqrt_ne_zero'.mpr (by norm_num : 0 < (21 : ℝ))))
  fin_cases i <;> fin_cases j <;> norm_num [fourThreeZeroMixer, mul_eq_zero, hs] <;> decide

private theorem fourThreeZeroMixer_minorA :
    subsetMinorSq fourThreeZeroMixer {0, 1} {0, 2} = 1 / 441 := by
  rw [subsetMinorSq_pair _ fourThreeZeroMixer_unitary (by decide) (by decide)]
  norm_num [fourThreeZeroMixer, ← Complex.ofReal_mul, ← Complex.ofReal_sub,
    Complex.normSq_ofReal, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail]
  ring_nf
  rw [show threeZeroScale ^ 4 = (threeZeroScale ^ 2) ^ 2 by ring, threeZeroScale_sq]
  norm_num

private theorem fourThreeZeroMixer_minorB :
    subsetMinorSq fourThreeZeroMixer {0, 2} {2, 3} = 4 / 441 := by
  rw [subsetMinorSq_pair _ fourThreeZeroMixer_unitary (by decide) (by decide)]
  norm_num [fourThreeZeroMixer, ← Complex.ofReal_mul, ← Complex.ofReal_sub,
    Complex.normSq_ofReal, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail]
  ring_nf
  rw [show threeZeroScale ^ 4 = (threeZeroScale ^ 2) ^ 2 by ring, threeZeroScale_sq]
  norm_num

/-- No nonnegative weights on permutations can give all squared minors of this matrix. -/
theorem fourThreeZeroMixer_no_positive_minor_law :
    ¬ ∃ w : Equiv.Perm (Fin 4) → ℝ, (∀ σ, 0 ≤ w σ) ∧
      ∀ I J : Finset (Fin 4),
        (∑ σ ∈ univ.filter (fun σ : Equiv.Perm (Fin 4) => J.map σ.toEmbedding = I), w σ) =
          subsetMinorSq fourThreeZeroMixer I J := by
  classical
  rintro ⟨w, hw, hm⟩
  have hfix (σ : Equiv.Perm (Fin 4)) (i : Fin 4) (hi : i ≠ 3) (hσ : σ i = i) :
      w σ = 0 := by
    have h := hm {i} {i}
    rw [subsetMinorSq_singleton _ fourThreeZeroMixer_unitary,
      (fourThreeZeroMixer_entry_eq_zero i i).mpr ⟨rfl, hi⟩, map_zero] at h
    exact (sum_eq_zero_iff_of_nonneg (fun τ _ => hw τ)).mp h σ (by simp [hσ])
  let A := univ.filter (fun σ : Equiv.Perm (Fin 4) => ({0, 2} : Finset (Fin 4)).map σ.toEmbedding = {0, 1})
  let B := univ.filter (fun σ : Equiv.Perm (Fin 4) => ({2, 3} : Finset (Fin 4)).map σ.toEmbedding = {0, 2})
  have hAB : ∀ σ : Equiv.Perm (Fin 4), σ 0 ≠ 0 → σ 1 ≠ 1 → σ 2 ≠ 2 →
      σ ∈ B → σ ∈ A := by
    change ∀ σ : Equiv.Perm (Fin 4), σ 0 ≠ 0 → σ 1 ≠ 1 → σ 2 ≠ 2 →
      σ ∈ univ.filter _ → σ ∈ univ.filter _
    decide +kernel
  have hle : ∑ σ ∈ B, w σ ≤ ∑ σ ∈ A, w σ := by
    simp only [A, B, Finset.sum_filter]
    apply Finset.sum_le_sum
    intro σ _
    by_cases hb : ({2, 3} : Finset (Fin 4)).map σ.toEmbedding = {0, 2}
    · rw [if_pos hb]
      by_cases hf : σ 0 ≠ 0 ∧ σ 1 ≠ 1 ∧ σ 2 ≠ 2
      · have ha := hAB σ hf.1 hf.2.1 hf.2.2 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb⟩)
        have ha' : ({0, 2} : Finset (Fin 4)).map σ.toEmbedding = {0, 1} :=
          (Finset.mem_filter.mp ha).2
        rw [if_pos ha']
      · push_neg at hf
        by_cases h0 : σ 0 = 0
        · simp [hfix σ 0 (by decide) h0]
        by_cases h1 : σ 1 = 1
        · simp [hfix σ 1 (by decide) h1]
        · simp [hfix σ 2 (by decide) (hf h0 h1)]
    · rw [if_neg hb]
      split_ifs
      · exact hw σ
      · exact le_rfl
  have ha : (∑ σ ∈ A, w σ) = 1 / 441 :=
    (hm {0, 1} {0, 2}).trans fourThreeZeroMixer_minorA
  have hb : (∑ σ ∈ B, w σ) = 4 / 441 :=
    (hm {0, 2} {2, 3}).trans fourThreeZeroMixer_minorB
  rw [ha, hb] at hle
  norm_num at hle

/-- The three-zero mixer has no nonnegative law independent of both spectra. -/
theorem fourThreeZeroMixer_no_universalMatchingWeights :
    ¬ HasUniversalMatchingWeights fourThreeZeroMixer := by
  classical
  rintro ⟨w, hw, _, hd⟩
  apply fourThreeZeroMixer_no_positive_minor_law
  refine ⟨w, hw, fun I J => ?_⟩
  symm
  apply indexed_minor_law_of_small _ fourThreeZeroMixer_unitary id w
  intro I' J' hc _
  have h := hd (fun i => if i ∈ I' then 0 else 1) (fun j => if j ∈ J' then 1 else 0)
  rw [determinantValue_subset_marker _ fourThreeZeroMixer_unitary I' J' hc,
    weightedMatchingValue_subset_marker w I' J' hc] at h
  exact Complex.ofReal_injective h

end

end MOC
