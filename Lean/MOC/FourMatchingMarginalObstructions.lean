import MOC.SubsetMarkerTest
import MOC.UniversalWeightsBlockRestriction
import MOC.Support
import Mathlib.NumberTheory.Zsqrtd.GaussianInt

/-! One rational orthogonal mixer separates three matching-law assertions. -/

open BigOperators Finset Matrix

namespace MOC

/-- The integer numerator of the rational orthogonal mixer. -/
def marginalMixerNumerator : Matrix (Fin 4) (Fin 4) GaussianInt :=
  !![33, 444, -300, -320; -180, 135, 500, -300;
    444, 292, 225, 240; -400, 300, 0, 375]

noncomputable section

/-- A rational orthogonal matrix with denominator 625. -/
def fourMarginalMixer : Matrix (Fin 4) (Fin 4) ℂ :=
  (625 : ℂ)⁻¹ • marginalMixerNumerator.map GaussianInt.toComplex

theorem marginalMixer_entry (i j : Fin 4) :
    fourMarginalMixer i j = (625 : ℂ)⁻¹ * GaussianInt.toComplex (marginalMixerNumerator i j) :=
  rfl

theorem fourMarginalMixer_unitary : IsUnitary fourMarginalMixer := by
  let g := GaussianInt.toComplex
  let W := marginalMixerNumerator.map g
  have hInt : marginalMixerNumeratorᴴ * marginalMixerNumerator =
      (390625 : GaussianInt) • 1 := by
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  have hstar := Matrix.conjTranspose_map (A := marginalMixerNumerator) g GaussianInt.toComplex_star
  have hW : Wᴴ * W = (390625 : ℂ) • 1 := by
    simpa only [W, Matrix.map_mul, hstar, Matrix.map_smul' g _ _ (map_mul g), map_ofNat,
      Matrix.map_one g (map_zero g) (map_one g)] using
      congrArg (fun M : Matrix (Fin 4) (Fin 4) GaussianInt => M.map g) hInt
  have hc : star ((625 : ℂ)⁻¹) = (625 : ℂ)⁻¹ := by
    rw [star_inv₀, star_ofNat]
  have hu : fourMarginalMixerᴴ * fourMarginalMixer = 1 := by
    change (((625 : ℂ)⁻¹ • W)ᴴ * ((625 : ℂ)⁻¹ • W)) = 1
    rw [Matrix.conjTranspose_smul, hc, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      hW, smul_smul]
    norm_num
  exact ⟨Matrix.mul_eq_one_comm.mp hu, hu⟩

private def marginalEventMass (w : Equiv.Perm (Fin 4) → ℝ)
    (I J : Finset (Fin 4)) : ℝ :=
  ∑ σ ∈ univ.filter (fun σ : Equiv.Perm (Fin 4) => J.map σ.toEmbedding = I), w σ

private theorem marginalEventCover (σ : Equiv.Perm (Fin 4)) :
    ({0, 3} : Finset (Fin 4)).map σ.toEmbedding = {0, 1} →
    σ 0 = 0 ∨ σ 2 = 3 ∨ ({2, 3} : Finset (Fin 4)).map σ.toEmbedding = {0, 2} := by
  have h : ∀ p : Equiv.Perm (Fin 4),
      ({0, 3} : Finset (Fin 4)).map p.toEmbedding = {0, 1} →
      p 0 = 0 ∨ p 2 = 3 ∨ ({2, 3} : Finset (Fin 4)).map p.toEmbedding = {0, 2} := by
    decide +kernel
  exact h σ

private theorem marginalEventMass_bound (w : Equiv.Perm (Fin 4) → ℝ)
    (hw : ∀ σ, 0 ≤ w σ) :
    marginalEventMass w {0, 1} {0, 3} ≤ marginalEventMass w {0} {0} +
      marginalEventMass w {3} {2} + marginalEventMass w {0, 2} {2, 3} := by
  classical
  unfold marginalEventMass
  simp only [Finset.sum_filter, ← Finset.sum_add_distrib, Finset.map_singleton,
    Finset.singleton_inj, Equiv.toEmbedding_apply]
  apply Finset.sum_le_sum
  intro σ _
  by_cases hp : ({0, 3} : Finset (Fin 4)).map σ.toEmbedding = {0, 1}
  · rcases marginalEventCover σ hp with h | h | h
    · simp only [hp, h, if_true]
      split_ifs <;> linarith [hw σ]
    · simp only [hp, h, if_true]
      split_ifs <;> linarith [hw σ]
    · simp only [hp, h, if_true]
      split_ifs <;> linarith [hw σ]
  · simp only [hp, if_false]
    split_ifs <;> linarith [hw σ]

private theorem marginalEventMinor_values :
    subsetMinorSq fourMarginalMixer {0, 1} {0, 3} = 11664 / 390625 ∧
    subsetMinorSq fourMarginalMixer {0} {0} = 1089 / 390625 ∧
    subsetMinorSq fourMarginalMixer {3} {2} = 0 ∧
    subsetMinorSq fourMarginalMixer {0, 2} {2, 3} = 0 := by
  rw [subsetMinorSq_pair _ fourMarginalMixer_unitary (by decide) (by decide),
    subsetMinorSq_singleton _ fourMarginalMixer_unitary,
    subsetMinorSq_singleton _ fourMarginalMixer_unitary,
    subsetMinorSq_pair _ fourMarginalMixer_unitary (by decide) (by decide)]
  norm_num [marginalMixer_entry, marginalMixerNumerator, Matrix.cons_val,
    GaussianInt.toComplex_def₂, Complex.normSq, Complex.mul_re, Complex.mul_im,
    Complex.sub_re, Complex.sub_im, Complex.inv_re, Complex.inv_im]

/-- The explicit mixer has no nonnegative law for its full squared-minor table. -/
theorem fourMarginalMixer_no_minor_law :
    ¬ ∃ w : Equiv.Perm (Fin 4) → ℝ, (∀ σ, 0 ≤ w σ) ∧
      ∀ I J : Finset (Fin 4),
        (∑ σ ∈ univ.filter (fun σ : Equiv.Perm (Fin 4) => J.map σ.toEmbedding = I), w σ) =
          subsetMinorSq fourMarginalMixer I J := by
  rintro ⟨w, hw, hm⟩
  obtain ⟨hA, hB, hC, hD⟩ := marginalEventMinor_values
  have h := marginalEventMass_bound w hw
  unfold marginalEventMass at h
  rw [hm, hm, hm, hm, hA, hB, hC, hD] at h
  norm_num at h

theorem fourMarginalMixer_no_universal_weights :
    ¬ HasUniversalMatchingWeights fourMarginalMixer := by
  classical
  rintro ⟨w, hw, _, hd⟩
  apply fourMarginalMixer_no_minor_law
  refine ⟨w, hw, fun I J => ?_⟩
  symm
  apply indexed_minor_law_of_small _ fourMarginalMixer_unitary id w
  intro I' J' hc _
  have h := hd (fun i => if i ∈ I' then 0 else 1) (fun j => if j ∈ J' then 1 else 0)
  rw [determinantValue_subset_marker _ fourMarginalMixer_unitary I' J' hc,
    weightedMatchingValue_subset_marker w I' J' hc] at h
  exact Complex.ofReal_injective h

/-- Identity padding preserves this failure of common determinant weights. -/
theorem fourMarginalMixer_identityPadding_no_universal_weights
    {κ : Type*} [Fintype κ] [DecidableEq κ] :
    ¬ HasUniversalMatchingWeights (fromBlocks fourMarginalMixer 0 0 (1 : Matrix κ κ ℂ)) := by
  intro h
  apply fourMarginalMixer_no_universal_weights
  exact universal_matching_weights_left_of_directSum fourMarginalMixer_unitary
    isUnitary_one h

end

private def conditionalLeft : Fin 4 → GaussianInt := ![0, ⟨1, 1⟩, ⟨0, -1⟩, 1]
private def conditionalRight : Fin 4 → GaussianInt := ![1, -1, 0, ⟨0, -1⟩]
private def jointLeftFirst : Fin 4 → GaussianInt := ![0, -1, 1, 1]
private def jointRightFirst : Fin 4 → GaussianInt := ![-1, 0, 0, 1]
private def jointLeftSecond : Fin 4 → GaussianInt := ![3, ⟨-1, 2⟩, 3, 0]
private def jointRightSecond : Fin 4 → GaussianInt := ![3, 3, ⟨1, -2⟩, 0]

private def integerMatching (a b : Fin 4 → GaussianInt) (p : Equiv.Perm (Fin 4)) : GaussianInt :=
  ∏ j, (a (p j) + b j)

private def integerEntryMatrix (a b : Fin 4 → GaussianInt) : Matrix (Fin 4) (Fin 4) GaussianInt :=
  Matrix.of fun i j => (a i + b j) * marginalMixerNumerator i j

private def singletonScore (p : Equiv.Perm (Fin 4)) : ℤ :=
  (if p 1 = 0 then 2 else 0) + (if p 0 = 1 then 1 else 0) + (if p 3 = 2 then 2 else 0)

set_option maxRecDepth 4000 in
private theorem conditionalMatching_certificate : ∀ p : Equiv.Perm (Fin 4),
    (integerMatching conditionalLeft conditionalRight p).im ≤ singletonScore p := by
  decide +kernel

set_option maxRecDepth 4000 in
private theorem jointMatching_certificate : ∀ p : Equiv.Perm (Fin 4),
    0 ≤ 54 * (integerMatching jointLeftFirst jointRightFirst p).re +
      (integerMatching jointLeftSecond jointRightSecond p).re := by
  decide +kernel

set_option maxHeartbeats 1200000 in
set_option maxRecDepth 4000 in
private theorem entryDeterminant_certificates :
    marginalMixerNumerator.det = 152587890625 ∧
    (integerEntryMatrix conditionalLeft conditionalRight).det = ⟨-223193359375, 214393359375⟩ ∧
    (integerEntryMatrix jointLeftFirst jointRightFirst).det = -8261718750 ∧
    (integerEntryMatrix jointLeftSecond jointRightSecond).det = ⟨0, 6328125000000⟩ := by
  decide +kernel

noncomputable section

private theorem integerMatching_map (a b : Fin 4 → GaussianInt) (p : Equiv.Perm (Fin 4)) :
    GaussianInt.toComplex (integerMatching a b p) =
      matchingProduct (GaussianInt.toComplex ∘ a) (GaussianInt.toComplex ∘ b) p := by
  simp only [integerMatching, matchingProduct, map_prod, map_add, Function.comp_apply]

private theorem marginalMixer_determinant (a b : Fin 4 → GaussianInt) :
    determinantValue (GaussianInt.toComplex ∘ a) (GaussianInt.toComplex ∘ b) fourMarginalMixer =
      GaussianInt.toComplex (integerEntryMatrix a b).det / 152587890625 := by
  let g := GaussianInt.toComplex
  have hm : Matrix.of (fun i j => (g (a i) + g (b j)) * fourMarginalMixer i j) =
      (625 : ℂ)⁻¹ • (integerEntryMatrix a b).map g := by
    apply Matrix.ext
    intro i j
    simp only [marginalMixer_entry, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul,
      Matrix.map_apply, integerEntryMatrix, map_mul, map_add, g]
    ring
  have hdet (W : Matrix (Fin 4) (Fin 4) GaussianInt) : (W.map g).det = g W.det :=
    (RingHom.map_det g W).symm
  rw [determinantValue_eq_weightedEntryDet_div _ _ _ fourMarginalMixer_unitary]
  change (Matrix.of (fun i j => (g (a i) + g (b j)) * fourMarginalMixer i j)).det /
    fourMarginalMixer.det = _
  rw [hm, fourMarginalMixer, Matrix.det_smul, Matrix.det_smul,
    Fintype.card_fin, hdet, hdet, entryDeterminant_certificates.1, map_ofNat]
  rw [mul_div_mul_left _ _ (by norm_num : ((625 : ℂ)⁻¹)^4 ≠ 0)]

private theorem conditionalMixer_im :
    (determinantValue (GaussianInt.toComplex ∘ conditionalLeft)
      (GaussianInt.toComplex ∘ conditionalRight) fourMarginalMixer).im = 548847 / 390625 := by
  rw [marginalMixer_determinant, entryDeterminant_certificates.2.1]
  norm_num [Complex.div_im, Complex.normSq]

private theorem conditionalSingleton_values :
    2 * Complex.normSq (fourMarginalMixer 0 1) + Complex.normSq (fourMarginalMixer 1 0) +
      2 * Complex.normSq (fourMarginalMixer 2 3) = 541872 / 390625 := by
  norm_num [marginalMixer_entry, marginalMixerNumerator, Matrix.cons_val, GaussianInt.toComplex_def₂,
    Complex.normSq, Complex.mul_re, Complex.mul_im, Complex.inv_re, Complex.inv_im]

/-- For these spectra, no nonnegative determinant law preserves all singleton masses. -/
theorem fourMarginalMixer_no_singleton_preserving_matching :
    ¬ ∃ w : Equiv.Perm (Fin 4) → ℝ, (∀ σ, 0 ≤ w σ) ∧
      (∀ i j, (∑ σ ∈ univ.filter (fun σ : Equiv.Perm (Fin 4) => σ j = i), w σ) =
        Complex.normSq (fourMarginalMixer i j)) ∧
      weightedMatchingValue (GaussianInt.toComplex ∘ conditionalLeft)
        (GaussianInt.toComplex ∘ conditionalRight) w =
      determinantValue (GaussianInt.toComplex ∘ conditionalLeft)
        (GaussianInt.toComplex ∘ conditionalRight) fourMarginalMixer := by
  classical
  rintro ⟨w, hw, hm, hd⟩
  have hvertex (p : Equiv.Perm (Fin 4)) :
      (matchingProduct (GaussianInt.toComplex ∘ conditionalLeft)
        (GaussianInt.toComplex ∘ conditionalRight) p).im ≤ (singletonScore p : ℝ) := by
    rw [← integerMatching_map, ← GaussianInt.to_real_im]
    exact_mod_cast conditionalMatching_certificate p
  have hsum := Finset.sum_le_sum (fun p (_ : p ∈ (univ : Finset (Equiv.Perm (Fin 4)))) =>
    mul_le_mul_of_nonneg_left (hvertex p) (hw p))
  have htarget := congrArg Complex.im hd
  simp only [weightedMatchingValue, Complex.im_sum, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, add_zero, conditionalMixer_im] at htarget
  have hscore : (∑ p, w p * (singletonScore p : ℝ)) = 541872 / 390625 := by
    have he (p : Equiv.Perm (Fin 4)) : w p * (singletonScore p : ℝ) =
        2 * (if p 1 = 0 then w p else 0) + (if p 0 = 1 then w p else 0) +
          2 * (if p 3 = 2 then w p else 0) := by
      unfold singletonScore
      split_ifs <;> push_cast <;> ring
    simp_rw [he, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_filter]
    rw [hm, hm, hm, conditionalSingleton_values]
  rw [htarget, hscore] at hsum
  norm_num at hsum

private theorem jointMixer_separating_value :
    54 * (determinantValue (GaussianInt.toComplex ∘ jointLeftFirst)
      (GaussianInt.toComplex ∘ jointRightFirst) fourMarginalMixer).re +
    (determinantValue (GaussianInt.toComplex ∘ jointLeftSecond)
      (GaussianInt.toComplex ∘ jointRightSecond) fourMarginalMixer).re < 0 := by
  rw [marginalMixer_determinant, marginalMixer_determinant,
    entryDeterminant_certificates.2.2.1, entryDeterminant_certificates.2.2.2]
  norm_num [Complex.div_re, Complex.normSq]

/-- One order-four mixer yields two determinant observations outside their joint matching hull. -/
theorem fourMarginalMixer_two_determinants_outside_joint_hull :
    (determinantValue (GaussianInt.toComplex ∘ jointLeftFirst)
        (GaussianInt.toComplex ∘ jointRightFirst) fourMarginalMixer,
      determinantValue (GaussianInt.toComplex ∘ jointLeftSecond)
        (GaussianInt.toComplex ∘ jointRightSecond) fourMarginalMixer) ∉
    convexHull ℝ (Set.range fun p : Equiv.Perm (Fin 4) =>
      (matchingProduct (GaussianInt.toComplex ∘ jointLeftFirst) (GaussianInt.toComplex ∘ jointRightFirst) p,
        matchingProduct (GaussianInt.toComplex ∘ jointLeftSecond) (GaussianInt.toComplex ∘ jointRightSecond) p)) := by
  let f : (ℂ × ℂ) →ₗ[ℝ] ℝ :=
    (54 : ℝ) • Complex.reLm.comp (LinearMap.fst ℝ ℂ ℂ) +
      Complex.reLm.comp (LinearMap.snd ℝ ℂ ℂ)
  intro h
  have hnonneg : 0 ≤ f _ := by
    apply convexHull_min ?_ (convex_halfSpace_ge f.isLinear 0) h
    rintro _ ⟨p, rfl⟩
    change 0 ≤ 54 * (matchingProduct _ _ p).re + (matchingProduct _ _ p).re
    rw [← integerMatching_map, ← integerMatching_map, ← GaussianInt.to_real_re,
      ← GaussianInt.to_real_re]
    exact_mod_cast jointMatching_certificate p
  exact (not_lt_of_ge hnonneg) jointMixer_separating_value

end

end MOC
