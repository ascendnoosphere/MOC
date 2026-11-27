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
  norm_num [marginalMixer_entry, marginalMixerNumerator, map_neg, map_ofNat,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail,
    Complex.normSq, Complex.mul_re, Complex.mul_im,
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
  norm_num [marginalMixer_entry, marginalMixerNumerator, map_neg, map_ofNat,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail,
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
  norm_num [map_ofNat, Complex.div_re, Complex.normSq]

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
  have hnonneg : 0 ≤ f (determinantValue (GaussianInt.toComplex ∘ jointLeftFirst)
      (GaussianInt.toComplex ∘ jointRightFirst) fourMarginalMixer,
      determinantValue (GaussianInt.toComplex ∘ jointLeftSecond)
        (GaussianInt.toComplex ∘ jointRightSecond) fourMarginalMixer) := by
    apply convexHull_min ?_ (convex_halfSpace_ge f.isLinear 0) h
    rintro _ ⟨p, rfl⟩
    change 0 ≤ 54 * (matchingProduct _ _ p).re + (matchingProduct _ _ p).re
    rw [← integerMatching_map, ← integerMatching_map, ← GaussianInt.to_real_re,
      ← GaussianInt.to_real_re]
    exact_mod_cast jointMatching_certificate p
  exact (not_lt_of_ge hnonneg) jointMixer_separating_value

section Padding

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

private abbrev padZero : Fin 4 ⊕ κ := .inl 0
private abbrev padOne : Fin 4 ⊕ κ := .inl 1
private abbrev padThree : Fin 4 ⊕ κ := .inl 3

private def padFirstLeft (i : Fin 4 ⊕ κ) : ℂ :=
  if i = padZero then 0 else if i = padOne then -1 else 1

private def padFirstRight (j : Fin 4 ⊕ κ) : ℂ :=
  if j = padZero then -1 else if j = padThree then 1 else 0

private def padRatio : ℂ := 1 - 2 * Complex.I

private def padSecondLeft (i : Fin 4 ⊕ κ) : ℂ :=
  if i = padOne then -padRatio else if i = padThree then 0 else 3

private def padSecondRight (j : Fin 4 ⊕ κ) : ℂ :=
  if j = padZero ∨ j = padOne then 3 else if j = padThree then 0 else padRatio

private theorem product_two_exceptions {α : Type*} [Fintype α] [DecidableEq α]
    (g : α → ℂ) {i j : α} (hij : i ≠ j) (h : ∀ k, k ≠ i → k ≠ j → g k = 1) :
    (∏ k, g k) = g i * g j := by
  have hj : j ∈ (Finset.univ : Finset α).erase i := by simp [hij.symm]
  rw [← Finset.prod_erase_mul Finset.univ g (Finset.mem_univ i),
    ← Finset.prod_erase_mul (Finset.univ.erase i) g hj]
  have he : (∏ k ∈ ((Finset.univ : Finset α).erase i).erase j, g k) = 1 := by
    apply Finset.prod_eq_one
    intro k hk
    exact h k (Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).1 (Finset.mem_erase.mp hk).1
  rw [he, one_mul, mul_comm]

private theorem matching_factor_by_columns (a b g : Fin 4 ⊕ κ → ℂ)
    (p : Equiv.Perm (Fin 4 ⊕ κ)) (hg : ∀ j, g j ≠ 0) :
    matchingProduct a b p.symm = (∏ j, g j) * ∏ i, (a i + b (p i)) / g (p i) := by
  rw [matchingProduct_inverse, ← Equiv.prod_comp p g, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  change a i + b (p i) = g (p i) * ((a i + b (p i)) / g (p i))
  field_simp [hg] <;> ring

private theorem pad_first_matching (p : Equiv.Perm (Fin 4 ⊕ κ)) :
    matchingProduct padFirstLeft padFirstRight p.symm =
      if p padZero = padThree ∧ p padOne = padZero then -2
      else if p padZero = padZero ∧ p padOne ≠ padThree then 2 else 0 := by
  let d : Fin 4 ⊕ κ → ℂ := fun j => if j = padThree then 2 else 1
  have hd : ∀ j, d j ≠ 0 := by intro j; by_cases h : j = padThree <;> norm_num [d, h]
  have hprod : (∏ j, d j) = 2 := by
    rw [Finset.prod_eq_single padThree]
    · simp [d]
    · intro j _ hj; simp [d, hj]
    · simp
  let q (i : Fin 4 ⊕ κ) := (padFirstLeft i + padFirstRight (p i)) / d (p i)
  rw [matching_factor_by_columns _ _ d p hd, hprod]
  change 2 * (∏ i, q i) = _
  by_cases hhit : p padZero = padZero ∨ p padOne = padZero
  · have hq (i : Fin 4 ⊕ κ) (h₀ : i ≠ padZero) (h₁ : i ≠ padOne) : q i = 1 := by
      have hp : p i ≠ padZero := by
        intro he
        rcases hhit with h | h
        · exact h₀ (p.injective (he.trans h.symm))
        · exact h₁ (p.injective (he.trans h.symm))
      by_cases ht : p i = padThree <;>
        simp (config := { decide := true }) [q, d, padFirstLeft, padFirstRight, h₀, h₁, hp, ht]
    rw [product_two_exceptions q (by simp) hq]
    have hn : p padZero ≠ p padOne := p.injective.ne (by simp)
    rcases hhit with h | h
    · have hy : p padOne ≠ padZero := fun he => hn (h.trans he.symm)
      by_cases ht : p padOne = padThree <;>
        simp (config := { decide := true }) [q, padFirstLeft, padFirstRight, d, h, hy, ht]
    · have hx : p padZero ≠ padZero := fun he => hn (he.trans h.symm)
      by_cases ht : p padZero = padThree <;>
        simp (config := { decide := true }) [q, padFirstLeft, padFirstRight, d, h, hx, ht] <;>
        norm_num
  · push_neg at hhit
    let i := p.symm padZero
    have hi : p i = padZero := p.apply_symm_apply _
    have h₀ : i ≠ padZero := fun h => hhit.1 (h ▸ hi)
    have h₁ : i ≠ padOne := fun h => hhit.2 (h ▸ hi)
    have hq : q i = 0 := by
      norm_num [q, d, padFirstLeft, padFirstRight, h₀, h₁, hi]
    rw [Finset.prod_eq_zero (Finset.mem_univ i) hq, mul_zero]
    simp [hhit.1, hhit.2]

private theorem padSecondRight_values (j : Fin 4 ⊕ κ) :
    padSecondRight j = 3 ∨ padSecondRight j = padRatio ∨ padSecondRight j = 0 := by
  unfold padSecondRight
  split_ifs <;> simp

private theorem pad_second_matching (p : Equiv.Perm (Fin 4 ⊕ κ)) :
    matchingProduct padSecondLeft padSecondRight p.symm / (3 + padRatio) ^ Fintype.card κ =
      let x := padSecondRight (p padOne)
      let y := padSecondRight (p padThree)
      108 * (3 + padRatio) * ((x - padRatio) / (3 + x) * (y / (3 + y))) := by
  let d (j : Fin 4 ⊕ κ) : ℂ := 3 + padSecondRight j
  have hr : (3 : ℂ) + padRatio ≠ 0 := by
    intro h
    have he := congrArg Complex.re h
    norm_num [padRatio, Complex.add_re, Complex.sub_re, Complex.mul_re] at he
  have hd (j : Fin 4 ⊕ κ) : d j ≠ 0 := by
    rcases padSecondRight_values j with h | h | h <;> norm_num [d, h, hr]
  have hprod : (∏ j, d j) = (108 * (3 + padRatio)) * (3 + padRatio) ^ Fintype.card κ := by
    rw [Fintype.prod_sum_type, Fin.prod_univ_four]
    simp (config := { decide := true }) [d, padSecondRight, padZero, padOne, padThree, Finset.prod_const] <;>
      ring_nf <;> simp
  let q (i : Fin 4 ⊕ κ) := (padSecondLeft i + padSecondRight (p i)) / d (p i)
  have hq (i : Fin 4 ⊕ κ) (h₁ : i ≠ padOne) (h₃ : i ≠ padThree) : q i = 1 := by
    simpa [q, d, padSecondLeft, h₁, h₃] using div_self (hd (p i))
  have hq₁ : q padOne = (padSecondRight (p padOne) - padRatio) / (3 + padSecondRight (p padOne)) := by
    simp [q, d, padSecondLeft, sub_eq_add_neg, add_comm]
  have hq₃ : q padThree = padSecondRight (p padThree) / (3 + padSecondRight (p padThree)) := by
    have hleft : padSecondLeft (padThree : Fin 4 ⊕ κ) = 0 := by
      unfold padSecondLeft
      rw [if_neg (by simp : (padThree : Fin 4 ⊕ κ) ≠ padOne), if_pos rfl]
    simp only [q, d, hleft, zero_add]
  rw [matching_factor_by_columns _ _ d p hd, hprod]
  change ((108 * (3 + padRatio)) * (3 + padRatio) ^ Fintype.card κ) * (∏ i, q i) / _ = _
  rw [product_two_exceptions q (by simp) hq, hq₁, hq₃]
  rw [mul_right_comm, mul_div_cancel_right₀ _ (pow_ne_zero _ hr)]

private theorem pad_second_score (x y : ℂ)
    (hx : x = 3 ∨ x = padRatio ∨ x = 0) (hy : y = 3 ∨ y = padRatio ∨ y = 0) :
    let f := (108 * (3 + padRatio) * ((x - padRatio) / (3 + x) * (y / (3 + y)))).re
    0 ≤ f ∧ (x = 3 → (y = 3 ∨ y = padRatio) → f = 108) := by
  have hr : padRatio ≠ 3 := by
    intro h
    have he := congrArg Complex.re h
    norm_num [padRatio, Complex.sub_re, Complex.mul_re] at he
  have hz : padRatio ≠ 0 := by
    intro h
    have he := congrArg Complex.re h
    norm_num [padRatio, Complex.sub_re, Complex.mul_re] at he
  rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
    simp only [hr, Ne.symm hr, hz, Ne.symm hz, false_implies, true_implies, or_true, true_or, and_true] <;>
    norm_num [padRatio, Complex.div_re, Complex.div_im, Complex.normSq, Complex.mul_re,
      Complex.mul_im, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im]

private theorem padded_vertex_separating_score (p : Equiv.Perm (Fin 4 ⊕ κ)) :
    0 ≤ 54 * (matchingProduct padFirstLeft padFirstRight p.symm).re +
      (matchingProduct padSecondLeft padSecondRight p.symm / (3 + padRatio) ^ Fintype.card κ).re := by
  rw [pad_first_matching, pad_second_matching]
  let x := padSecondRight (p padOne)
  let y := padSecondRight (p padThree)
  have hs := pad_second_score x y (padSecondRight_values _) (padSecondRight_values _)
  by_cases hn : p padZero = padThree ∧ p padOne = padZero
  · rw [if_pos hn]
    have hx : x = 3 := by simp [x, hn.2, padSecondRight]
    have hy₀ : p padThree ≠ padZero := by
      intro he
      exact (by simp : (padThree : Fin 4 ⊕ κ) ≠ padOne) (p.injective (he.trans hn.2.symm))
    have hy₃ : p padThree ≠ padThree := by
      intro he
      exact (by simp : (padThree : Fin 4 ⊕ κ) ≠ padZero) (p.injective (he.trans hn.1.symm))
    have hy : y = 3 ∨ y = padRatio := by
      by_cases h : p padThree = padOne <;> simp [y, padSecondRight, h, hy₀, hy₃]
    have he := hs.2 hx hy
    change 0 ≤ 54 * (-2 : ℂ).re +
      (108 * (3 + padRatio) * ((x - padRatio) / (3 + x) * (y / (3 + y)))).re
    rw [he]
    norm_num
  · rw [if_neg hn]
    split_ifs
    · exact add_nonneg (by norm_num) hs.1
    · simpa only [Complex.zero_re, mul_zero, zero_add] using hs.1

private def padMixer : Matrix (Fin 4 ⊕ κ) (Fin 4 ⊕ κ) ℂ :=
  fromBlocks fourMarginalMixer 0 0 1

private theorem pad_determinant (a b : Fin 4 → ℂ) (s t : ℂ) :
    determinantValue (Sum.elim a (fun _ : κ => s)) (Sum.elim b (fun _ : κ => t)) padMixer =
      determinantValue a b fourMarginalMixer * (s + t) ^ Fintype.card κ := by
  unfold determinantValue padMixer
  rw [← Matrix.fromBlocks_diagonal, ← Matrix.fromBlocks_diagonal,
    Matrix.fromBlocks_conjTranspose]
  simp only [Matrix.fromBlocks_multiply, Matrix.fromBlocks_add, Matrix.det_fromBlocks_zero₂₁,
    Matrix.conjTranspose_zero, Matrix.conjTranspose_one, Matrix.zero_mul, Matrix.mul_zero,
    add_zero, zero_add, Matrix.one_mul, Matrix.mul_one, Matrix.diagonal_add,
    Matrix.det_diagonal, Pi.add_apply, Finset.prod_const, Finset.card_univ]

private theorem padded_determinants_separating_score :
    54 * (determinantValue padFirstLeft padFirstRight (padMixer (κ := κ))).re +
      (determinantValue padSecondLeft padSecondRight (padMixer (κ := κ)) /
        (3 + padRatio) ^ Fintype.card κ).re < 0 := by
  have ha : (padFirstLeft : Fin 4 ⊕ κ → ℂ) =
      Sum.elim (GaussianInt.toComplex ∘ jointLeftFirst) (fun _ => 1) := by
    funext i
    rcases i with i | i
    · fin_cases i <;>
        simp (config := { decide := true }) [padFirstLeft, jointLeftFirst, Matrix.cons_val]
    · simp [padFirstLeft]
  have hb : (padFirstRight : Fin 4 ⊕ κ → ℂ) =
      Sum.elim (GaussianInt.toComplex ∘ jointRightFirst) (fun _ => 0) := by
    funext i
    rcases i with i | i
    · fin_cases i <;>
        simp (config := { decide := true }) [padFirstRight, jointRightFirst, Matrix.cons_val]
    · simp [padFirstRight]
  have hc : (padSecondLeft : Fin 4 ⊕ κ → ℂ) =
      Sum.elim (GaussianInt.toComplex ∘ jointLeftSecond) (fun _ => 3) := by
    funext i
    rcases i with i | i
    · fin_cases i <;> apply Complex.ext <;>
        simp (config := { decide := true }) [padSecondLeft, jointLeftSecond, padRatio, Matrix.cons_val,
          map_ofNat, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im]
    · simp [padSecondLeft]
  have hd : (padSecondRight : Fin 4 ⊕ κ → ℂ) =
      Sum.elim (GaussianInt.toComplex ∘ jointRightSecond) (fun _ => padRatio) := by
    funext i
    rcases i with i | i
    · fin_cases i <;> apply Complex.ext <;>
        simp (config := { decide := true }) [padSecondRight, jointRightSecond, padRatio, Matrix.cons_val,
          map_ofNat, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im]
    · simp [padSecondRight]
  have hr : (3 : ℂ) + padRatio ≠ 0 := by
    intro h
    have he := congrArg Complex.re h
    norm_num [padRatio, Complex.add_re, Complex.sub_re, Complex.mul_re] at he
  rw [ha, hb, hc, hd, pad_determinant, pad_determinant, add_zero, one_pow, mul_one,
    mul_div_cancel_right₀ _ (pow_ne_zero _ hr)]
  exact jointMixer_separating_value

private theorem padded_joint_obstruction :
    (determinantValue padFirstLeft padFirstRight (padMixer (κ := κ)),
      determinantValue padSecondLeft padSecondRight (padMixer (κ := κ))) ∉
    convexHull ℝ (Set.range fun p : Equiv.Perm (Fin 4 ⊕ κ) =>
      (matchingProduct padFirstLeft padFirstRight p, matchingProduct padSecondLeft padSecondRight p)) := by
  let f : (ℂ × ℂ) →ₗ[ℝ] ℝ :=
    (54 : ℝ) • Complex.reLm.comp (LinearMap.fst ℝ ℂ ℂ) +
      Complex.reLm.comp ((LinearMap.mulRight ℝ ((3 + padRatio) ^ Fintype.card κ)⁻¹).comp
        (LinearMap.snd ℝ ℂ ℂ))
  intro h
  have he : 0 ≤ f (determinantValue padFirstLeft padFirstRight (padMixer (κ := κ)),
      determinantValue padSecondLeft padSecondRight (padMixer (κ := κ))) := by
    apply convexHull_min ?_ (convex_halfSpace_ge f.isLinear 0) h
    rintro _ ⟨p, rfl⟩
    simpa only [f, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.comp_apply,
      LinearMap.fst_apply, LinearMap.snd_apply, LinearMap.mulRight_apply,
      Complex.reLm_coe, smul_eq_mul, Equiv.symm_symm, div_eq_mul_inv] using
      padded_vertex_separating_score p.symm
  apply (not_lt_of_ge he)
  simpa only [f, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.comp_apply,
    LinearMap.fst_apply, LinearMap.snd_apply, LinearMap.mulRight_apply,
    Complex.reLm_coe, smul_eq_mul, div_eq_mul_inv] using
    (padded_determinants_separating_score (κ := κ))

end Padding

/-- In every order at least four, two determinant observations at the same
unitary mixer can lie outside the joint matching hull. -/
theorem two_determinants_outside_joint_hull {n : ℕ} (hn : 4 ≤ n) :
    ∃ (U : Matrix (Fin n) (Fin n) ℂ) (a b c d : Fin n → ℂ), IsUnitary U ∧
      (determinantValue a b U, determinantValue c d U) ∉
        convexHull ℝ (Set.range fun p : Equiv.Perm (Fin n) =>
          (matchingProduct a b p, matchingProduct c d p)) := by
  let E : (Fin 4 ⊕ Fin (n - 4)) ≃ Fin n := finSumFinEquiv.trans (finCongr (by omega))
  let e := E.symm
  let U := padMixer (κ := Fin (n - 4))
  have hu : IsUnitary U := unitary_directSum fourMarginalMixer_unitary isUnitary_one
  refine ⟨U.submatrix e e, padFirstLeft ∘ e, padFirstRight ∘ e,
    padSecondLeft ∘ e, padSecondRight ∘ e, unitary_reindex e e hu, ?_⟩
  rw [determinantValue_reindex, determinantValue_reindex]
  intro h
  apply (padded_joint_obstruction (κ := Fin (n - 4)))
  apply convexHull_min ?_ (convex_convexHull ℝ _) h
  rintro _ ⟨p, rfl⟩
  exact subset_convexHull ℝ _ ⟨(e.symm.trans p).trans e,
    Prod.ext (matchingProduct_reindex e e _ _ p).symm (matchingProduct_reindex e e _ _ p).symm⟩

end

end MOC
