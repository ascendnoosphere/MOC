import MOC.FiniteMinorLaw
import Mathlib.Tactic.NormNum

/-!
# Flat order-four unitary matrices

A unitary matrix of order four with squared entry norms equal to one quarter
has a common permutation law for all squared minors. Complementary pairs
give three partitions. A Birkhoff decomposition on these partitions lifts
to a law on permutations of the four indices.
-/

open BigOperators Finset Matrix

namespace MOC

private def oppositeClass (I : Finset (Fin 4)) : Fin 3 :=
  if I = {0, 1} ∨ I = {2, 3} then 0 else
  if I = {0, 2} ∨ I = {1, 3} then 1 else 2

private def representative (i : Fin 3) : Finset (Fin 4) := {0, i.succ}

private def liftPermutation (s : Equiv.Perm (Fin 3)) : Equiv.Perm (Fin 4) where
  toFun := Fin.cases 0 fun i => (s i).succ
  invFun := Fin.cases 0 fun i => (s.symm i).succ
  left_inv i := by cases i using Fin.cases <;> simp
  right_inv i := by cases i using Fin.cases <;> simp

private def kleinPermutation (i : Fin 4) : Equiv.Perm (Fin 4) :=
  if i = 0 then 1 else
  if i = 1 then Equiv.swap 0 1 * Equiv.swap 2 3 else
  if i = 2 then Equiv.swap 0 2 * Equiv.swap 1 3 else
    Equiv.swap 0 3 * Equiv.swap 1 2

private def liftWithKlein (s : Equiv.Perm (Fin 3)) (k : Fin 4) : Equiv.Perm (Fin 4) :=
  kleinPermutation k * liftPermutation s

private theorem class_count :
    ∀ (I J : Finset (Fin 4)) (s : Equiv.Perm (Fin 3)), I.card = 2 → J.card = 2 →
      ((univ.filter fun k : Fin 4 => J.map (liftWithKlein s k).toEmbedding = I).card) =
        if s (oppositeClass J) = oppositeClass I then 2 else 0 := by decide

private theorem singleton_count :
    ∀ (i j : Fin 4) (s : Equiv.Perm (Fin 3)),
      (univ.filter fun k : Fin 4 => liftWithKlein s k j = i).card = 1 := by decide

private theorem class_characterization :
    ∀ (I J : Finset (Fin 4)), I.card = 2 → J.card = 2 →
      (oppositeClass I = oppositeClass J ↔ I = J ∨ I = Jᶜ) := by decide

private theorem image_class_bijective :
    ∀ (σ : Equiv.Perm (Fin 4)), Function.Bijective
      (fun j : Fin 3 => oppositeClass ((representative j).map σ.toEmbedding)) := by decide

private theorem representative_card :
    ∀ i : Fin 3, (representative i).card = 2 := by decide

private theorem representative_class :
    ∀ i : Fin 3, oppositeClass (representative i) = i := by decide

private theorem representative_ne_compl :
    ∀ i : Fin 3, representative i ≠ (representative i)ᶜ := by decide

noncomputable section
private theorem card_inter_add_complement_indicator :
    ∀ I K : Finset (Fin 4), I.card = 2 → K.card = 2 →
      (I ∩ K).card + (if K = Iᶜ then 1 else 0) = 1 + (if K = I then 1 else 0) := by
  decide +kernel

private theorem flat_four_pair_indicator (I J : Finset (Fin 4))
    (hI : I.card = 2) (hJ : J.card = 2) (σ : Equiv.Perm (Fin 4)) :
    (∑ j ∈ J, ∑ i ∈ I, if σ j = i then (1 : ℂ) else 0) +
      (if J.map σ.toEmbedding = Iᶜ then 1 else 0) =
      1 + (if J.map σ.toEmbedding = I then 1 else 0) := by
  classical
  have h := card_inter_add_complement_indicator I (J.map σ.toEmbedding) hI (by simpa)
  have hsum :
      (∑ j ∈ J, ∑ i ∈ I, if σ j = i then (1 : ℂ) else 0) =
        ((I ∩ J.map σ.toEmbedding).card : ℂ) := by
    simp only [Finset.sum_ite_eq, ← Finset.sum_map]
    rw [inter_comm]
    simp only [Finset.sum_boole, ← Finset.filter_mem_eq_inter, Finset.filter_map,
      Finset.card_map, Function.comp_apply, Equiv.toEmbedding_apply]
    congr 2
  rw [hsum]
  exact_mod_cast h

theorem flat_four_subsetMinorSq_compl_left (U : Matrix (Fin 4) (Fin 4) ℂ)
    (hU : IsUnitary U) (hFlat : ∀ i j, Complex.normSq (U i j) = 1 / 4)
    (I J : Finset (Fin 4)) (hI : I.card = 2) (hJ : J.card = 2) :
    subsetMinorSq U I J = subsetMinorSq U Iᶜ J := by
  classical
  let w := signedWeight U
  have hone (i j : Fin 4) :
      (∑ σ : Equiv.Perm (Fin 4), if σ j = i then w σ else 0) = (1 / 4 : ℂ) := by
    rw [← Finset.sum_filter]
    have hs := sum_signedWeight_image_eq_subsetMinorSq U hU {i} {j}
    rw [subsetMinorSq_singleton U hU, hFlat] at hs
    simpa [w] using hs
  have hpair (K : Finset (Fin 4)) :
      (∑ σ : Equiv.Perm (Fin 4), if J.map σ.toEmbedding = K then w σ else 0) =
        (subsetMinorSq U K J : ℂ) := by
    rw [← Finset.sum_filter]
    exact sum_signedWeight_image_eq_subsetMinorSq U hU K J
  have hsum :
      (∑ σ : Equiv.Perm (Fin 4), ∑ j ∈ J, ∑ i ∈ I,
        if σ j = i then w σ else 0) = 1 := by
    rw [Finset.sum_comm]
    simp_rw [Finset.sum_comm (s := Finset.univ), hone]
    simp [hI, hJ]
    norm_num
  have hh := Finset.sum_congr (rfl : (univ : Finset (Equiv.Perm (Fin 4))) = univ)
    (fun σ _ => congrArg (fun z => w σ * z) (flat_four_pair_indicator I J hI hJ σ))
  simp only [mul_add, Finset.mul_sum, mul_ite, mul_one, mul_zero,
    Finset.sum_add_distrib, hsum, hpair] at hh
  change 1 + (subsetMinorSq U Iᶜ J : ℂ) =
    (∑ σ : Equiv.Perm (Fin 4), signedWeight U σ) + (subsetMinorSq U I J : ℂ) at hh
  rw [sum_signedWeight U (det_ne_zero_of_unitary hU)] at hh
  exact Complex.ofReal_injective (add_left_cancel hh).symm

private theorem signed_minor_fin_four (U : Matrix (Fin 4) (Fin 4) ℂ) (hU : IsUnitary U)
    (I J : Finset (Fin 4)) :
    (∑ σ : Equiv.Perm (Fin 4), if J.map σ.toEmbedding = I then realSignedWeight U σ else 0) =
      subsetMinorSq U I J := by
  have hr := congrArg Complex.re (sum_signedWeight_image_eq_subsetMinorSq U hU I J)
  simpa only [Finset.sum_filter, Complex.re_sum, apply_ite, Complex.zero_re,
    Complex.ofReal_re, realSignedWeight] using hr

private theorem flat_four_law_of_complement (U : Matrix (Fin 4) (Fin 4) ℂ)
    (hU : IsUnitary U) (hFlat : ∀ i j, Complex.normSq (U i j) = 1 / 4)
    (hComp : ∀ (I J : Finset (Fin 4)), I.card = 2 → J.card = 2 →
      subsetMinorSq U I J = subsetMinorSq U Iᶜ J) :
    ∃ w : Equiv.Perm (Fin 3) × Fin 4 → ℝ,
      (∀ x, 0 ≤ w x) ∧ (∑ x, w x = 1) ∧
      ∀ I J : Finset (Fin 4), subsetMinorSq U I J =
        ∑ x ∈ univ.filter (fun x : Equiv.Perm (Fin 3) × Fin 4 =>
          J.map (liftWithKlein x.1 x.2).toEmbedding = I), w x := by
  let P (σ : Equiv.Perm (Fin 4)) : Equiv.Perm (Fin 3) :=
    Equiv.ofBijective _ (image_class_bijective σ)
  let D : Matrix (Fin 3) (Fin 3) ℝ :=
    Matrix.of fun j i => ∑ σ : Equiv.Perm (Fin 4), if P σ j = i then realSignedWeight U σ else 0
  have hD (i j : Fin 3) : D j i =
      2 * subsetMinorSq U (representative i) (representative j) := by
    have hclass (σ : Equiv.Perm (Fin 4)) :
        P σ j = i ↔ (representative j).map σ.toEmbedding = representative i ∨
          (representative j).map σ.toEmbedding = (representative i)ᶜ := by
      change oppositeClass ((representative j).map σ.toEmbedding) = i ↔ _
      simpa only [representative_class i] using
        class_characterization ((representative j).map σ.toEmbedding) (representative i)
          (by simpa only [Finset.card_map] using representative_card j) (representative_card i)
    simp only [D, Matrix.of_apply, hclass]
    calc
      _ = (∑ σ : Equiv.Perm (Fin 4), if (representative j).map σ.toEmbedding =
          representative i then realSignedWeight U σ else 0) +
          (∑ σ : Equiv.Perm (Fin 4), if (representative j).map σ.toEmbedding =
          (representative i)ᶜ then realSignedWeight U σ else 0) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro σ _
        by_cases hi : (representative j).map σ.toEmbedding = representative i
        · have hn : (representative j).map σ.toEmbedding ≠ (representative i)ᶜ :=
            hi ▸ representative_ne_compl i
          simp [hi, hn]
        · simp [hi]
      _ = _ := by
        rw [signed_minor_fin_four U hU, signed_minor_fin_four U hU,
          ← hComp _ _ (representative_card i) (representative_card j), two_mul]
  have hDS : D ∈ doublyStochastic ℝ (Fin 3) := by
    rw [mem_doublyStochastic_iff_sum]
    refine ⟨fun j i => ?_, fun j => ?_, fun i => ?_⟩
    · rw [hD]
      exact mul_nonneg (by norm_num) (subsetMinorSq_nonneg _ _ _)
    · simp only [D, Matrix.of_apply]
      rw [Finset.sum_comm]
      simpa only [Finset.sum_ite_eq, Finset.mem_univ, if_true] using sum_realSignedWeight U hU
    · simp only [D, Matrix.of_apply]
      rw [Finset.sum_comm]
      have he (σ : Equiv.Perm (Fin 4)) (j : Fin 3) :
          P σ j = i ↔ j = (P σ).symm i := (P σ).apply_eq_iff_eq_symm_apply
      simp_rw [he]
      simpa only [Finset.sum_ite_eq', Finset.mem_univ, if_true] using sum_realSignedWeight U hU
  obtain ⟨w, hw, hs, he⟩ := exists_eq_sum_perm_of_mem_doublyStochastic hDS
  have hb (i j : Fin 3) :
      (∑ s : Equiv.Perm (Fin 3), if s j = i then w s else 0) = D j i := by
    have hh := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => M j i) he.symm
    simpa [Matrix.sum_apply, Matrix.smul_apply, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply,
      mul_ite, eq_comm] using hh
  refine ⟨fun x => w x.1 / 4, fun x => div_nonneg (hw x.1) (by norm_num), ?_, ?_⟩
  · rw [Fintype.sum_prod_type]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    calc
      _ = ∑ s, w s := by
        apply Finset.sum_congr rfl
        intro s _
        push_cast
        ring
      _ = 1 := hs
  apply indexed_minor_law_of_small U hU (fun x : Equiv.Perm (Fin 3) × Fin 4 =>
    liftWithKlein x.1 x.2) (fun x => w x.1 / 4)
  intro I J hcard hsmall
  have hf (s : Equiv.Perm (Fin 3)) :
      (∑ k : Fin 4, if J.map (liftWithKlein s k).toEmbedding = I then w s / 4 else 0) =
        ((univ.filter (fun k : Fin 4 => J.map (liftWithKlein s k).toEmbedding = I)).card : ℝ) *
          (w s / 4) := by
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  simp_rw [hf]
  have hle : I.card ≤ 2 := by simpa using hsmall
  rcases (show I.card = 0 ∨ I.card = 1 ∨ I.card = 2 by omega) with h0 | h1 | h2
  · have hJ : J.card = 0 := hcard.symm.trans h0
    obtain rfl := Finset.card_eq_zero.mp h0
    obtain rfl := Finset.card_eq_zero.mp hJ
    rw [← signed_minor_fin_four U hU]
    simp only [Finset.map_empty, if_true]
    rw [sum_realSignedWeight U hU]
    calc
      1 = ∑ s, w s := hs.symm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro s _
        simp
        ring
  · obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp h1
    obtain ⟨j, rfl⟩ := Finset.card_eq_one.mp (hcard.symm.trans h1)
    simp only [subsetMinorSq_singleton _ hU, hFlat, Finset.map_singleton,
      Finset.singleton_inj, Equiv.toEmbedding_apply, singleton_count, Nat.cast_one, one_mul]
    rw [← Finset.sum_div, hs]
  have hJ : J.card = 2 := hcard.symm.trans h2
  have hright : ∀ I J : Finset (Fin 4), I.card = 2 → J.card = 2 →
      subsetMinorSq U I J = subsetMinorSq U I Jᶜ := by
    intro L K hL hK
    have hKc : Kᶜ.card = 2 := by rw [Finset.card_compl, Fintype.card_fin, hK]
    exact (subsetMinorSq_compl _ hU L K).symm.trans (hComp L Kᶜ hL hKc).symm
  let i := oppositeClass I
  let j := oppositeClass J
  have hi : I = representative i ∨ I = (representative i)ᶜ :=
    (class_characterization _ _ h2 (representative_card i)).mp (representative_class i).symm
  have hj : J = representative j ∨ J = (representative j)ᶜ :=
    (class_characterization _ _ hJ (representative_card j)).mp (representative_class j).symm
  have hminor : subsetMinorSq U I J = subsetMinorSq U (representative i) (representative j) := by
    rcases hi with hi | hi <;> rcases hj with hj | hj <;> rw [hi, hj]
    · rw [← hright _ _ (representative_card i) (representative_card j)]
    · rw [← hComp _ _ (representative_card i) (representative_card j)]
    · exact subsetMinorSq_compl _ hU _ _
  simp_rw [class_count _ _ _ h2 hJ]
  have hsum :
      (∑ s : Equiv.Perm (Fin 3), ((if s j = i then 2 else 0 : ℕ) : ℝ) * (w s / 4)) =
        (∑ s : Equiv.Perm (Fin 3), if s j = i then w s else 0) / 2 := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro s _
    split_ifs <;> push_cast <;> ring
  change _ = ∑ s : Equiv.Perm (Fin 3), ((if s j = i then 2 else 0 : ℕ) : ℝ) * (w s / 4)
  rw [hsum, hb, hD, hminor]
  ring

/-- A single probability law on permutations represents every squared minor
of a unitary matrix of order four with squared entry norms one quarter. -/
theorem flat_four_common_minor_law (U : Matrix (Fin 4) (Fin 4) ℂ)
    (hU : IsUnitary U) (hFlat : ∀ i j, Complex.normSq (U i j) = 1 / 4) :
    ∃ (p : Equiv.Perm (Fin 3) × Fin 4 → Equiv.Perm (Fin 4))
      (w : Equiv.Perm (Fin 3) × Fin 4 → ℝ),
      (∀ x, 0 ≤ w x) ∧ (∑ x, w x = 1) ∧
      ∀ I J : Finset (Fin 4), subsetMinorSq U I J =
        ∑ x ∈ univ.filter (fun x => J.map (p x).toEmbedding = I), w x := by
  obtain ⟨w, hw, hs, hm⟩ := flat_four_law_of_complement U hU hFlat
    (flat_four_subsetMinorSq_compl_left U hU hFlat)
  exact ⟨fun x => liftWithKlein x.1 x.2, w, hw, hs, hm⟩

/-- The determinant inclusion holds for every pair of complex spectra at a
unitary mixer of order four with squared entry norms one quarter. -/
theorem holds_flat_four (a b : Fin 4 → ℂ) (U : Matrix (Fin 4) (Fin 4) ℂ)
    (hU : IsUnitary U) (hFlat : ∀ i j, Complex.normSq (U i j) = 1 / 4) :
    Holds a b U := by
  obtain ⟨p, w, hw, hs, hm⟩ := flat_four_common_minor_law U hU hFlat
  exact holds_of_indexed_minor_law a b U hU p w hw hs hm

end

end MOC
