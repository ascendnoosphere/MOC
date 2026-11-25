import MOC.CyclicFourier
import MOC.FiniteMinorLaw
import MOC.PositiveWeightMargin
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.GroupWithZero.Units.Equiv
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Data.Fintype.Perm
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

/-! The normalized Fourier matrix in order five admits an affine permutation
law for the joint squared-minor profile. -/

open BigOperators Finset Matrix

namespace MOC

noncomputable section

local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

private theorem character_normSq {n : ℕ} [NeZero n] (x : ZMod n) :
    Complex.normSq (ZMod.stdAddChar x) = 1 := by
  rw [Complex.normSq_eq_norm_sq]
  change ‖(ZMod.toCircle x : ℂ)‖ ^ 2 = 1
  rw [Circle.norm_coe, one_pow]

private def characterChord {n : ℕ} [NeZero n] (x : ZMod n) : ℝ :=
  Complex.normSq (ZMod.stdAddChar x - 1)

private theorem characterChord_neg {n : ℕ} [NeZero n] (x : ZMod n) :
    characterChord (-x) = characterChord x := by
  simp only [characterChord, ← cyclicCharacter_conj]
  simpa only [Complex.star_def, map_sub, map_one] using
    Complex.normSq_conj (ZMod.stdAddChar x - 1)

private theorem cyclicFourier_entry_normSq (n : ℕ) [NeZero n] (i j : ZMod n) :
    Complex.normSq (cyclicFourier n i j) = (n : ℝ)⁻¹ := by
  have h' : ((Real.sqrt (n : ℝ))⁻¹) ^ 2 = (n : ℝ)⁻¹ := by
    rw [inv_pow, Real.sq_sqrt (by positivity)]
  rw [cyclicFourier, Complex.normSq_mul, Complex.normSq_ofReal, character_normSq,
    mul_one, ← pow_two, h']

private theorem cyclicFourier_two_normSq (n : ℕ) [NeZero n] (i k j l : ZMod n) :
    Complex.normSq (cyclicFourier n i j * cyclicFourier n k l -
      cyclicFourier n i l * cyclicFourier n k j) =
      characterChord ((i-k)*(j-l)) / (n : ℝ)^2 := by
  have h (u v w z : ZMod n) : cyclicFourier n u v * cyclicFourier n w z =
      (n : ℂ)⁻¹ * ZMod.stdAddChar (u * v + w * z) := by
    simp only [cyclicFourier, mul_mul_mul_comm, cyclicFourier_scale_mul, AddChar.map_add_eq_mul]
  have hi : i*j+k*l = (i*l+k*j)+(i-k)*(j-l) := by ring
  have he : cyclicFourier n i j * cyclicFourier n k l -
      cyclicFourier n i l * cyclicFourier n k j =
      (n : ℂ)⁻¹ * ZMod.stdAddChar (i*l+k*j) * (ZMod.stdAddChar ((i-k)*(j-l)) - 1) := by
    rw [h, h, hi, AddChar.map_add_eq_mul]
    ring
  rw [he]
  simp only [Complex.normSq_mul, Complex.normSq_inv, Complex.normSq_natCast,
    character_normSq, mul_one, characterChord, div_eq_mul_inv]
  ring

private def affineSlope5 (k : Fin 4) : ZMod 5 := ((k.val + 1 : ℕ) : ZMod 5)

private theorem affineSlope5_ne_zero : ∀ k : Fin 4, affineSlope5 k ≠ 0 := by
  decide +kernel

private def affinePerm5 (k : Fin 4 × Fin 5) : Equiv.Perm (ZMod 5) :=
  (Equiv.mulLeft₀ (affineSlope5 k.1) (affineSlope5_ne_zero k.1)).trans
    (Equiv.addRight (ZMod.finEquiv 5 k.2))

private def firstChord5 (x : ZMod 5) : Prop := x = 1 ∨ x = -1

private instance (x : ZMod 5) : Decidable (firstChord5 x) := by
  unfold firstChord5
  infer_instance

private theorem characterChord_cases5 (x : ZMod 5) (hx : x ≠ 0) :
    characterChord x = if firstChord5 x then characterChord (1 : ZMod 5)
      else characterChord (2 : ZMod 5) := by
  have hc : ∀ y : ZMod 5, y ≠ 0 → y = 1 ∨ y = -1 ∨ y = 2 ∨ y = -2 := by
    decide +kernel
  rcases hc x hx with h | h | h | h <;> subst x
  · rw [if_pos (show firstChord5 1 from Or.inl rfl)]
  · rw [if_pos (show firstChord5 (-1) from Or.inr rfl), characterChord_neg]
  · rw [if_neg (show ¬ firstChord5 2 by decide)]
  · rw [if_neg (show ¬ firstChord5 (-2) by decide), characterChord_neg]

private theorem characterChord_sum5 :
    characterChord (1 : ZMod 5) + characterChord (2 : ZMod 5) = 5 := by
  have hs := AddChar.sum_mulShift (ψ := ZMod.stdAddChar) (1 : ZMod 5)
    (ZMod.isPrimitive_stdAddChar 5)
  have hs' : (∑ x : ZMod 5, ZMod.stdAddChar x) = 0 := by simpa using hs
  rw [← (ZMod.finEquiv 5).toEquiv.sum_comp (fun x => ZMod.stdAddChar x)] at hs'
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Finset.sum_empty, add_zero] at hs'
  change ZMod.stdAddChar (0 : ZMod 5) + (ZMod.stdAddChar (1 : ZMod 5) +
    (ZMod.stdAddChar (2 : ZMod 5) + (ZMod.stdAddChar (3 : ZMod 5) +
      ZMod.stdAddChar (4 : ZMod 5)))) = 0 at hs'
  rw [show (3 : ZMod 5) = -2 by decide, show (4 : ZMod 5) = -1 by decide,
    ← cyclicCharacter_conj, ← cyclicCharacter_conj, AddChar.map_zero_eq_one] at hs'
  have hr := congrArg Complex.re hs'
  simp only [Complex.add_re, Complex.one_re, Complex.zero_re, Complex.star_def,
    Complex.conj_re] at hr
  have he (x : ZMod 5) : characterChord x = 2 - 2 * (ZMod.stdAddChar x).re := by
    rw [characterChord, Complex.normSq_sub, character_normSq, Complex.normSq_one]
    simp <;> ring
  rw [he, he]
  linarith only [hr]

private def affineFilter5 (I J : Finset (ZMod 5)) (first : Bool) : Finset (Fin 4 × Fin 5) :=
  univ.filter fun k => J.map (affinePerm5 k).toEmbedding = I ∧
    decide (firstChord5 (affineSlope5 k.1)) = first

private theorem affine_singleton_counts5 :
    ∀ i j : ZMod 5, (affineFilter5 {i} {j} true).card = 2 ∧
      (affineFilter5 {i} {j} false).card = 2 := by
  decide +kernel

set_option maxHeartbeats 2500000 in
private theorem affine_pair_counts5 :
    ∀ i k j l : ZMod 5, i ≠ k → j ≠ l →
      (affineFilter5 {i,k} {j,l} true).card =
        (if firstChord5 ((i-k)*(j-l)) then 2 else 0) ∧
      (affineFilter5 {i,k} {j,l} false).card =
        (if firstChord5 ((i-k)*(j-l)) then 0 else 2) := by
  decide +kernel

private theorem affine_empty_counts5 :
    (affineFilter5 ∅ ∅ true).card = 10 ∧ (affineFilter5 ∅ ∅ false).card = 10 := by
  decide +kernel

private def affineWeight5 (k : Fin 4 × Fin 5) : ℝ :=
  characterChord (affineSlope5 k.1) / 50

private theorem affine_weighted_count5 (I J : Finset (ZMod 5)) :
    (∑ k ∈ univ.filter (fun k : Fin 4 × Fin 5 => J.map (affinePerm5 k).toEmbedding = I),
      affineWeight5 k) =
      ((affineFilter5 I J true).card : ℝ) * (characterChord (1 : ZMod 5) / 50) +
      ((affineFilter5 I J false).card : ℝ) * (characterChord (2 : ZMod 5) / 50) := by
  simp only [affineWeight5]
  simp_rw [characterChord_cases5 _ (affineSlope5_ne_zero _)]
  have ht (k : Fin 4 × Fin 5) :
      (if J.map (affinePerm5 k).toEmbedding = I then
        (if firstChord5 (affineSlope5 k.1) then characterChord (1 : ZMod 5)
          else characterChord (2 : ZMod 5)) / 50 else 0) =
        (if J.map (affinePerm5 k).toEmbedding = I ∧
          decide (firstChord5 (affineSlope5 k.1)) = true
          then characterChord (1 : ZMod 5) / 50 else 0) +
        (if J.map (affinePerm5 k).toEmbedding = I ∧
          decide (firstChord5 (affineSlope5 k.1)) = false
          then characterChord (2 : ZMod 5) / 50 else 0) := by
    by_cases h : J.map (affinePerm5 k).toEmbedding = I <;>
      by_cases hs : firstChord5 (affineSlope5 k.1) <;> simp [h, hs]
  rw [Finset.sum_filter]
  simp_rw [ht, Finset.sum_add_distrib, ← Finset.sum_filter]
  simp [affineFilter5, nsmul_eq_mul]

private theorem affineWeight5_sum : ∑ k, affineWeight5 k = 1 := by
  have h := affine_weighted_count5 ∅ ∅
  rw [affine_empty_counts5.1, affine_empty_counts5.2] at h
  simpa using h.trans (by push_cast; linarith only [characterChord_sum5])

private theorem affine_minor_law_small5 (I J : Finset (ZMod 5))
    (hcard : I.card = J.card) (hsmall : I.card ≤ 2) :
    subsetMinorSq (cyclicFourier 5) I J =
      ∑ k ∈ univ.filter (fun k : Fin 4 × Fin 5 => J.map (affinePerm5 k).toEmbedding = I),
        affineWeight5 k := by
  have hU := cyclicFourier_unitary 5
  rw [affine_weighted_count5]
  by_cases h0 : I.card = 0
  · obtain rfl := Finset.card_eq_zero.mp h0
    obtain rfl := Finset.card_eq_zero.mp (hcard.symm.trans h0)
    have he : subsetMinorSq (cyclicFourier 5) ∅ ∅ = 1 := by
      apply Complex.ofReal_injective
      rw [← sum_signedWeight_image_eq_subsetMinorSq _ hU ∅ ∅, Complex.ofReal_one]
      simpa using sum_signedWeight (cyclicFourier 5) (det_ne_zero_of_unitary hU)
    rw [he, affine_empty_counts5.1, affine_empty_counts5.2]
    push_cast
    linarith only [characterChord_sum5]
  by_cases h1 : I.card = 1
  · obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp h1
    obtain ⟨j, rfl⟩ := Finset.card_eq_one.mp (hcard.symm.trans h1)
    rw [subsetMinorSq_singleton _ hU, cyclicFourier_entry_normSq,
      (affine_singleton_counts5 i j).1, (affine_singleton_counts5 i j).2]
    push_cast
    linarith only [characterChord_sum5]
  have h2 : I.card = 2 := by omega
  obtain ⟨i,k,hik,rfl⟩ := Finset.card_eq_two.mp h2
  obtain ⟨j,l,hjl,rfl⟩ := Finset.card_eq_two.mp (hcard.symm.trans h2)
  rw [subsetMinorSq_pair _ hU hik hjl, cyclicFourier_two_normSq,
    (affine_pair_counts5 i k j l hik hjl).1, (affine_pair_counts5 i k j l hik hjl).2]
  rw [characterChord_cases5 _ (mul_ne_zero (sub_ne_zero.mpr hik) (sub_ne_zero.mpr hjl))]
  split_ifs <;> push_cast <;> ring

/-- One common affine permutation law realizes every squared minor of the
order-five Fourier matrix. It gives each affine map of slope `m` weight
`|stdAddChar m - 1|² / 50`. -/
theorem cyclicFourier_five_minor_law :
    ∃ (p : Fin 4 × Fin 5 → Equiv.Perm (ZMod 5)) (w : Fin 4 × Fin 5 → ℝ),
      (∀ k, 0 ≤ w k) ∧ (∑ k, w k) = 1 ∧
      ∀ I J : Finset (ZMod 5), subsetMinorSq (cyclicFourier 5) I J =
        ∑ k ∈ univ.filter (fun k => J.map (p k).toEmbedding = I), w k := by
  refine ⟨affinePerm5, affineWeight5, ?_, affineWeight5_sum, ?_⟩
  · intro k
    exact div_nonneg (Complex.normSq_nonneg _) (by norm_num)
  · apply indexed_minor_law_of_small _ (cyclicFourier_unitary 5) affinePerm5 affineWeight5
    intro I J hc hs
    exact affine_minor_law_small5 I J hc (by simpa [ZMod.card] using hs)

/-- All complex spectra satisfy Marcus–de Oliveira with the order-five
Fourier relative eigenbasis. -/
theorem holds_cyclicFourier_five (a b : ZMod 5 → ℂ) : Holds a b (cyclicFourier 5) := by
  obtain ⟨p,w,hw,hs,hm⟩ := cyclicFourier_five_minor_law
  exact holds_of_indexed_minor_law a b _ (cyclicFourier_unitary 5) p w hw hs hm

private def fullFilter5 (I J : Finset (ZMod 5)) : Finset (Equiv.Perm (ZMod 5)) :=
  univ.filter (fun σ => J.map σ.toEmbedding = I)

private theorem fullFilter5_card_map (I J : Finset (ZMod 5))
    (σ τ : Equiv.Perm (ZMod 5)) :
    (fullFilter5 (I.map σ.toEmbedding) (J.map τ.toEmbedding)).card =
      (fullFilter5 I J).card := by
  symm
  apply Finset.card_equiv (τ.equivCongr σ)
  intro p
  have he : (J.map τ.toEmbedding).map ((τ.equivCongr σ) p).toEmbedding =
      (J.map p.toEmbedding).map σ.toEmbedding := by
    rw [Finset.map_map, Finset.map_map]
    congr 1
    ext x
    simp [Function.Embedding.trans_apply]
  simp only [fullFilter5, Finset.mem_filter, Finset.mem_univ, true_and, he,
    (Finset.map_injective σ.toEmbedding).eq_iff]

set_option maxHeartbeats 1000000 in
private theorem fullFilter5_base_counts :
    (fullFilter5 ∅ ∅).card = 120 ∧ (fullFilter5 {0} {0}).card = 24 ∧
      (fullFilter5 {0,1} {0,1}).card = 12 := by
  have e : (univ : Finset (Equiv.Perm (ZMod 5))) =
      @Finset.univ _ (@fintypePerm (ZMod 5) _ _) :=
    congrArg (fun f => @Finset.univ (Equiv.Perm (ZMod 5)) f) (Subsingleton.elim _ _)
  unfold fullFilter5
  rw [e]
  decide +kernel

private theorem fullFilter5_singleton_counts (i j : ZMod 5) :
    (fullFilter5 {i} {j}).card = 24 := by
  simpa [Equiv.addRight] using
    (fullFilter5_card_map {0} {0} (Equiv.addRight i) (Equiv.addRight j)).trans
      fullFilter5_base_counts.2.1

private theorem fullFilter5_pair_counts (i k j l : ZMod 5) (hik : i ≠ k) (hjl : j ≠ l) :
    (fullFilter5 {i,k} {j,l}).card = 12 := by
  let σ := (Equiv.mulLeft₀ (k-i) (sub_ne_zero.mpr (Ne.symm hik))).trans (Equiv.addRight i)
  let τ := (Equiv.mulLeft₀ (l-j) (sub_ne_zero.mpr (Ne.symm hjl))).trans (Equiv.addRight j)
  have hσ : ({0,1} : Finset (ZMod 5)).map σ.toEmbedding = {i,k} := by
    simp [σ, Finset.map_insert, Equiv.mulLeft₀, sub_add_cancel]
  have hτ : ({0,1} : Finset (ZMod 5)).map τ.toEmbedding = {j,l} := by
    simp [τ, Finset.map_insert, Equiv.mulLeft₀, sub_add_cancel]
  rw [← hσ, ← hτ, fullFilter5_card_map]
  exact fullFilter5_base_counts.2.2

private theorem fullFilter5_six_mul (I J : Finset (ZMod 5))
    (hc : I.card = J.card) (hs : I.card ≤ 2) :
    (fullFilter5 I J).card = 6 * (univ.filter (fun k : Fin 4 × Fin 5 =>
      J.map (affinePerm5 k).toEmbedding = I)).card := by
  have hsplit : (affineFilter5 I J true).card + (affineFilter5 I J false).card =
      (univ.filter (fun k : Fin 4 × Fin 5 => J.map (affinePerm5 k).toEmbedding = I)).card := by
    simpa [affineFilter5, Finset.filter_filter] using
      (Finset.filter_card_add_filter_neg_card_eq_card
        (s := univ.filter (fun k : Fin 4 × Fin 5 => J.map (affinePerm5 k).toEmbedding = I))
        (fun k => firstChord5 (affineSlope5 k.1)))
  rw [← hsplit]
  by_cases h0 : I.card = 0
  · obtain rfl := Finset.card_eq_zero.mp h0
    obtain rfl := Finset.card_eq_zero.mp (hc.symm.trans h0)
    rw [fullFilter5_base_counts.1, affine_empty_counts5.1, affine_empty_counts5.2]
  by_cases h1 : I.card = 1
  · obtain ⟨i,rfl⟩ := Finset.card_eq_one.mp h1
    obtain ⟨j,rfl⟩ := Finset.card_eq_one.mp (hc.symm.trans h1)
    rw [fullFilter5_singleton_counts, (affine_singleton_counts5 i j).1,
      (affine_singleton_counts5 i j).2]
  have h2 : I.card = 2 := by omega
  obtain ⟨i,k,hik,rfl⟩ := Finset.card_eq_two.mp h2
  obtain ⟨j,l,hjl,rfl⟩ := Finset.card_eq_two.mp (hc.symm.trans h2)
  rw [fullFilter5_pair_counts i k j l hik hjl, (affine_pair_counts5 i k j l hik hjl).1,
    (affine_pair_counts5 i k j l hik hjl).2]
  split_ifs <;> decide

/-- The uniform weight guaranteed for every permutation in the Fourier-five law. -/
def fourierFiveWeightFloor : ℝ :=
  min (characterChord (1 : ZMod 5)) (characterChord (2 : ZMod 5)) / 300

theorem fourierFiveWeightFloor_pos : 0 < fourierFiveWeightFloor := by
  have hp (t : ZMod 5) (ht : t ≠ 0) : 0 < characterChord t := by
    refine Complex.normSq_pos.mpr (sub_ne_zero.mpr (fun he => ht ?_))
    exact ZMod.injective_stdAddChar (he.trans ZMod.stdAddChar.map_zero_eq_one.symm)
  exact div_pos (lt_min (hp 1 (by decide)) (hp 2 (by decide))) (by norm_num)

private theorem affineWeight5_floor (k : Fin 4 × Fin 5) :
    6 * fourierFiveWeightFloor ≤ affineWeight5 k := by
  unfold fourierFiveWeightFloor affineWeight5
  rw [characterChord_cases5 _ (affineSlope5_ne_zero _)]
  split_ifs
  · linarith only [min_le_left (characterChord (1 : ZMod 5)) (characterChord (2 : ZMod 5))]
  · linarith only [min_le_right (characterChord (1 : ZMod 5)) (characterChord (2 : ZMod 5))]

/-- All 120 permutations can receive positive mass in a common law for Fourier five. -/
theorem cyclicFourier_five_positive_minor_law :
    ∃ w : Equiv.Perm (ZMod 5) → ℝ, (∀ σ, fourierFiveWeightFloor ≤ w σ) ∧
      (∑ σ, w σ) = 1 ∧
      ∀ I J : Finset (ZMod 5), subsetMinorSq (cyclicFourier 5) I J =
        ∑ σ ∈ fullFilter5 I J, w σ := by
  let μ := fourierFiveWeightFloor
  let r (k : Fin 4 × Fin 5) := affineWeight5 k - 6 * μ
  let w (σ : Equiv.Perm (ZMod 5)) :=
    μ + ∑ k ∈ univ.filter (fun k => affinePerm5 k = σ), r k
  have hw (σ : Equiv.Perm (ZMod 5)) : μ ≤ w σ := by
    exact le_add_of_nonneg_right (Finset.sum_nonneg fun k _ => sub_nonneg.mpr (affineWeight5_floor k))
  have hsmall (I J : Finset (ZMod 5)) (hc : I.card = J.card) (hs : I.card ≤ 2) :
      subsetMinorSq (cyclicFourier 5) I J = ∑ σ ∈ fullFilter5 I J, w σ := by
    rw [affine_minor_law_small5 I J hc hs]
    simp only [w, Finset.sum_add_distrib]
    rw [Finset.sum_fiberwise_eq_sum_filter univ (fullFilter5 I J) affinePerm5 r]
    have hmem (p : Equiv.Perm (ZMod 5)) : p ∈ fullFilter5 I J ↔ J.map p.toEmbedding = I := by
      simp [fullFilter5]
    simp only [hmem, r, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    rw [fullFilter5_six_mul I J hc hs, Nat.cast_mul]
    push_cast
    ring
  refine ⟨w, hw, ?_, ?_⟩
  · have h := hsmall ∅ ∅ rfl (by simp)
    rw [affine_minor_law_small5 ∅ ∅ rfl (by simp)] at h
    simpa [fullFilter5, affineWeight5_sum] using h.symm
  · apply indexed_minor_law_of_small _ (cyclicFourier_unitary 5) id w
    intro I J hc hs
    exact hsmall I J hc (by simpa [ZMod.card] using hs)

/-- A squared directional margin for Fourier five using the variance across all
matching products. The upper support height `h` may be the maximum matching score. -/
theorem cyclicFourier_five_squared_support_margin (a b : ZMod 5 → ℂ) (k : ℂ) (h : ℝ)
    (hh : ∀ σ : Equiv.Perm (ZMod 5), (k * matchingProduct a b σ).re ≤ h) :
    fourierFiveWeightFloor ^ 2 * 120 *
        (∑ σ, ((k * matchingProduct a b σ).re - (∑ τ, (k * matchingProduct a b τ).re) / 120) ^ 2) ≤
      119 * (h - (k * determinantValue a b (cyclicFourier 5)).re) ^ 2 := by
  obtain ⟨w, hw, hs, hm⟩ := cyclicFourier_five_positive_minor_law
  have he := determinantValue_eq_sum_of_indexed_minor_law a b _ (cyclicFourier_unitary 5) id w hm
  have hr := congrArg (fun z : ℂ => (k * z).re) he
  change (k * ∑ σ, (w σ : ℂ) * matchingProduct a b σ).re = _ at hr
  rw [Finset.mul_sum, Complex.re_sum] at hr
  have ht (σ : Equiv.Perm (ZMod 5)) :
      (k * ((w σ : ℂ) * matchingProduct a b σ)).re = w σ * (k * matchingProduct a b σ).re := by
    rw [mul_left_comm]
    simp [Complex.mul_re]
  simp_rw [ht] at hr
  rw [← hr]
  have hcard : Fintype.card (Equiv.Perm (ZMod 5)) = 120 := by
    norm_num [Fintype.card_perm, ZMod.card, Nat.factorial]
  have hmargin := squared_support_margin_of_weight_floor
    (p := fun σ => (k * matchingProduct a b σ).re) (w := w)
    (μ := fourierFiveWeightFloor) (h := h)
    (hμ := le_of_lt fourierFiveWeightFloor_pos) hw hs hh
  have hcardR : (Fintype.card (Equiv.Perm (ZMod 5)) : ℝ) = 120 :=
    congrArg (fun n : ℕ => (n : ℝ)) hcard
  rw [hcardR, show (120 : ℝ) - 1 = 119 by norm_num] at hmargin
  exact hmargin

end

end MOC
