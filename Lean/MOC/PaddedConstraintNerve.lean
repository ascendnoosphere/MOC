import MOC.FourConstraintNerve
import MOC.SpectralMinorDecomposition
import Mathlib.GroupTheory.Perm.ViaEmbedding

/-! A minimal infeasible family for the order-four mixer padded by an identity matrix. -/

open BigOperators Finset Matrix

namespace MOC

noncomputable section

private abbrev originalRows (k : Fin 13) := ordinaryCostRows (fourConstraintRay k)
private abbrev originalColumns (k : Fin 13) := ordinaryCostColumns (fourConstraintRay k)

/-- The order-four mixer with an identity block of order `r`. -/
def paddedConstraintMixer (r : ℕ) : Matrix (Fin 4 ⊕ Fin r) (Fin 4 ⊕ Fin r) ℂ :=
  fromBlocks fourMarginalMixer 0 0 (1 : Matrix (Fin r) (Fin r) ℂ)

theorem paddedConstraintMixer_unitary (r : ℕ) : IsUnitary (paddedConstraintMixer r) :=
  unitary_directSum fourMarginalMixer_unitary isUnitary_one

/-- The thirteen original row subsets and the added singleton row subsets. -/
def paddedConstraintRows (r : ℕ) : Fin 13 ⊕ Fin r → Finset (Fin 4 ⊕ Fin r)
  | .inl k => (originalRows k).map Function.Embedding.inl
  | .inr j => {Sum.inr j}

/-- The thirteen original column subsets and the added singleton column subsets. -/
def paddedConstraintColumns (r : ℕ) : Fin 13 ⊕ Fin r → Finset (Fin 4 ⊕ Fin r)
  | .inl k => (originalColumns k).map Function.Embedding.inl
  | .inr j => {Sum.inr j}

/-- The selected events have a common permutation law with the prescribed squared minors. -/
def PaddedConstraintFeasible (r : ℕ) (s : Finset (Fin 13 ⊕ Fin r)) : Prop :=
  ∃ w : Equiv.Perm (Fin 4 ⊕ Fin r) → ℝ, (∀ σ, 0 ≤ w σ) ∧ (∑ σ, w σ) = 1 ∧
    ∀ k ∈ s, (∑ σ, w σ * subsetImageEvent (paddedConstraintRows r k) (paddedConstraintColumns r k) σ) =
      subsetMinorSq (paddedConstraintMixer r) (paddedConstraintRows r k) (paddedConstraintColumns r k)

private def mappedSubsetEquiv {α β : Type*} (e : α ↪ β) (s : Finset α) : s ≃ s.map e :=
  Equiv.ofBijective (fun x : s => ⟨e x, Finset.apply_coe_mem_map e s x⟩) (by
    constructor
    · intro x y h
      exact Subtype.ext (e.injective (congrArg Subtype.val h))
    · intro y
      obtain ⟨x, hx, he⟩ := Finset.mem_map.mp y.property
      exact ⟨⟨x, hx⟩, Subtype.ext he⟩)

private theorem squaredMinor_on_embedding {α β : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] (U : Matrix α α ℂ) (V : Matrix β β ℂ)
    (hU : IsUnitary U) (hV : IsUnitary V) (e : α ↪ β) (h : ∀ i j, V (e i) (e j) = U i j)
    (I J : Finset α) : subsetMinorSq V (I.map e) (J.map e) = subsetMinorSq U I J := by
  by_cases hc : I.card = J.card
  · let f : I ≃ J := Fintype.equivOfCardEq (by simpa using hc)
    let eI := mappedSubsetEquiv e I
    let eJ := f.trans (mappedSubsetEquiv e J)
    rw [subsetMinorSq_eq_normSq_det_submatrix _ hV _ _ eI eJ,
      subsetMinorSq_eq_normSq_det_submatrix _ hU _ _ (Equiv.refl I) f]
    have hM : V.submatrix (Subtype.val ∘ eI) (Subtype.val ∘ eJ) =
        U.submatrix (Subtype.val ∘ Equiv.refl I) (Subtype.val ∘ f) := by
      apply Matrix.ext
      intro i j
      exact h i (f j)
    rw [hM]
  · have hm : (I.map e).card ≠ (J.map e).card := by simpa only [Finset.card_map] using hc
    simp only [subsetMinorSq, dif_neg hc, dif_neg hm]

private theorem paddedMinor_original (r : ℕ) (k : Fin 13) :
    subsetMinorSq (paddedConstraintMixer r) (paddedConstraintRows r (.inl k))
        (paddedConstraintColumns r (.inl k)) =
      subsetMinorSq fourMarginalMixer (originalRows k) (originalColumns k) :=
  squaredMinor_on_embedding _ _ fourMarginalMixer_unitary (paddedConstraintMixer_unitary r)
    Function.Embedding.inl (fun _ _ => rfl) _ _

private theorem paddedMinor_fixed (r : ℕ) (j : Fin r) :
    subsetMinorSq (paddedConstraintMixer r) (paddedConstraintRows r (.inr j))
      (paddedConstraintColumns r (.inr j)) = 1 := by
  change subsetMinorSq (paddedConstraintMixer r) {Sum.inr j} {Sum.inr j} = 1
  rw [subsetMinorSq_singleton _ (paddedConstraintMixer_unitary r)]
  simp only [paddedConstraintMixer, fromBlocks_apply₂₂, Matrix.one_apply_eq, Complex.normSq_one]

private theorem paddedEvent_fixed {r : ℕ} (j : Fin r) (σ : Equiv.Perm (Fin 4 ⊕ Fin r)) :
    subsetImageEvent (paddedConstraintRows r (.inr j)) (paddedConstraintColumns r (.inr j)) σ =
      if σ (Sum.inr j) = Sum.inr j then 1 else 0 := by
  simp only [paddedConstraintRows, paddedConstraintColumns, subsetImageEvent, Finset.map_singleton,
    Equiv.toEmbedding_apply, Finset.singleton_inj]

private theorem event_on_embedding {α β : Type*} [DecidableEq α] [DecidableEq β]
    (e : α ↪ β) (p : Equiv.Perm α) (σ : Equiv.Perm β) (h : ∀ x, σ (e x) = e (p x))
    (I J : Finset α) :
    subsetImageEvent (I.map e) (J.map e) σ = subsetImageEvent I J p := by
  have hm : (J.map e).map σ.toEmbedding = (J.map p.toEmbedding).map e := Finset.map_comm h
  simp only [subsetImageEvent, hm, Finset.map_inj]

private theorem originalEvent_eq (k : Fin 13) (p : Fin 24) :
    subsetImageEvent (originalRows k) (originalColumns k) (fourPerm p).symm =
      ordinaryCostRay (fourConstraintRay k) p := by
  rw [ordinaryCostRay, ordinaryCostRayInt_indicator]
  unfold subsetImageEvent
  split <;> norm_num

private theorem push_law {α β : Type*} [Fintype α] [Fintype β]
    (f : α → β) (w : α → ℝ) (hw : ∀ a, 0 ≤ w a) (hm : ∑ a, w a = 1) :
    ∃ v : β → ℝ, (∀ b, 0 ≤ v b) ∧ (∑ b, v b) = 1 ∧
      ∀ F : β → ℝ, (∑ b, v b * F b) = ∑ a, w a * F (f a) := by
  classical
  let v (b : β) := ∑ a, if f a = b then w a else 0
  have he (F : β → ℝ) : (∑ b, v b * F b) = ∑ a, w a * F (f a) := by
    simp only [v, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    simp [ite_mul]
  refine ⟨v, fun b => Finset.sum_nonneg (fun a _ => ?_), ?_, he⟩
  · split
    · exact hw a
    · exact le_rfl
  · simpa only [mul_one, hm] using he (fun _ => 1)

private theorem feasible_of_indexed_law {r : ℕ} {s : Finset (Fin 13 ⊕ Fin r)}
    {α : Type*} [Fintype α] (p : α → Equiv.Perm (Fin 4 ⊕ Fin r)) (w : α → ℝ)
    (hw : ∀ a, 0 ≤ w a) (hm : ∑ a, w a = 1)
    (he : ∀ k ∈ s, (∑ a, w a * subsetImageEvent (paddedConstraintRows r k)
      (paddedConstraintColumns r k) (p a)) = subsetMinorSq (paddedConstraintMixer r)
        (paddedConstraintRows r k) (paddedConstraintColumns r k)) : PaddedConstraintFeasible r s := by
  obtain ⟨v, hv, hs, hF⟩ := push_law p w hw hm
  exact ⟨v, hv, hs, fun k hk =>
    (hF (subsetImageEvent (paddedConstraintRows r k) (paddedConstraintColumns r k))).trans (he k hk)⟩

private theorem feasible_omit_original {r : ℕ} {s : Finset (Fin 13 ⊕ Fin r)} (k : Fin 13)
    (hk : Sum.inl k ∉ s) : PaddedConstraintFeasible r s := by
  classical
  let S := Finset.univ.filter (fun i : Fin 13 => Sum.inl i ∈ s)
  have hS : S ≠ Finset.univ := by
    intro h
    have hi : k ∈ S := h.symm ▸ Finset.mem_univ k
    exact hk (Finset.mem_filter.mp hi).2
  obtain ⟨w, hw, hm, ht⟩ := (fourConstraintFeasible_iff S).mpr hS
  let p (a : Fin 24) := Equiv.sumCongr (fourPerm a).symm (Equiv.refl (Fin r))
  apply feasible_of_indexed_law p w hw hm
  rintro (i | j) hi
  · have he (a : Fin 24) : subsetImageEvent (paddedConstraintRows r (.inl i))
        (paddedConstraintColumns r (.inl i)) (p a) = ordinaryCostRay (fourConstraintRay i) a :=
      (event_on_embedding Function.Embedding.inl (fourPerm a).symm (p a)
        (fun _ => rfl) (originalRows i) (originalColumns i)).trans (originalEvent_eq i a)
    simpa only [he, paddedMinor_original] using ht i (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩)
  · have he (a : Fin 24) : p a (Sum.inr j) = Sum.inr j := rfl
    simp only [paddedEvent_fixed, he, if_true, mul_one, hm, paddedMinor_fixed]

private abbrev fiveEmbedding : Fin 4 ↪ Fin 5 := Fin.castLEEmb (by decide)

private theorem five_law_on_originals :
    ∃ (p : Fin 13 → Equiv.Perm (Fin 5)) (w : Fin 13 → ℝ), (∀ a, 0 ≤ w a) ∧
      (∑ a, w a) = 1 ∧ ∀ k : Fin 13, (∑ a, w a * subsetImageEvent
        ((originalRows k).map fiveEmbedding) ((originalColumns k).map fiveEmbedding) (p a)) =
          subsetMinorSq fourMarginalMixer (originalRows k) (originalColumns k) := by
  obtain ⟨q, w, hw, hm, he⟩ := fiveConstraintMixer_extension_law
  refine ⟨fun a => (q a).symm, w, hw, hm, fun k => ?_⟩
  let I := (originalRows k).map fiveEmbedding
  let J := (originalColumns k).map fiveEmbedding
  have hminor : subsetMinorSq fiveConstraintMixer I J =
      subsetMinorSq fourMarginalMixer (originalRows k) (originalColumns k) := by
    apply squaredMinor_on_embedding _ _ fourMarginalMixer_unitary fiveConstraintMixer_unitary fiveEmbedding
    intro i j
    change (fromBlocks fourMarginalMixer 0 0 (1 : Matrix (Fin 1) (Fin 1) ℂ))
      (finSumFinEquiv.symm (Fin.castAdd 1 i)) (finSumFinEquiv.symm (Fin.castAdd 1 j)) = _
    rw [finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_castAdd] <;> rfl
  have hinv (a : Fin 13) : J.map (q a).symm.toEmbedding = I ↔ I.map (q a).toEmbedding = J := by
    constructor
    · intro h
      exact le_antisymm (Finset.subset_map_symm.mp h.ge) (Finset.map_symm_subset.mp h.le)
    · intro h
      exact le_antisymm (Finset.map_symm_subset.mpr h.ge) (Finset.subset_map_symm.mpr h.le)
  have hmap (a : Fin 13) :
      I.map (q a).toEmbedding = (originalRows k).image ((q a) ∘ fiveEmbedding) := by
    rw [show I = (originalRows k).map fiveEmbedding from rfl, Finset.map_map, Finset.map_eq_image] <;> rfl
  have ht := he k
  change (∑ a, if (originalRows k).image ((q a) ∘ fiveEmbedding) = J then w a else 0) =
    subsetMinorSq fiveConstraintMixer I J at ht
  change (∑ a, w a * subsetImageEvent I J (q a).symm) = _
  simpa only [subsetImageEvent, hinv, hmap, mul_ite, mul_one, mul_zero] using ht.trans hminor

private def fiveSlot {r : ℕ} (j : Fin r) : Fin 5 ↪ Fin 4 ⊕ Fin r :=
  (finSumFinEquiv.symm : Fin 5 ≃ Fin 4 ⊕ Fin 1).toEmbedding.trans
    (Function.Embedding.sumMap (Function.Embedding.refl (Fin 4))
      (⟨fun _ : Fin 1 => j, fun _ _ _ => Subsingleton.elim _ _⟩ : Fin 1 ↪ Fin r))

private theorem fiveSlot_original {r : ℕ} (j : Fin r) (i : Fin 4) :
    fiveSlot j (fiveEmbedding i) = Sum.inl i := by
  change Sum.map id (fun _ : Fin 1 => j) (finSumFinEquiv.symm (Fin.castAdd 1 i)) = _
  rw [finSumFinEquiv_symm_apply_castAdd] <;> rfl

private theorem fiveSlot_other {r : ℕ} {j l : Fin r} (hl : l ≠ j) : Sum.inr l ∉ Set.range (fiveSlot j) := by
  rintro ⟨x, hx⟩
  change Sum.map id (fun _ : Fin 1 => j) (finSumFinEquiv.symm x) = Sum.inr l at hx
  cases h : (finSumFinEquiv.symm x : Fin 4 ⊕ Fin 1) with
  | inl i => simp only [h, Sum.map_inl, Sum.inl_ne_inr] at hx
  | inr i =>
    rw [h] at hx
    exact hl (Sum.inr.inj hx).symm

private theorem feasible_omit_fixed {r : ℕ} {s : Finset (Fin 13 ⊕ Fin r)} (j : Fin r)
    (hj : Sum.inr j ∉ s) : PaddedConstraintFeasible r s := by
  obtain ⟨p, w, hw, hm, ht⟩ := five_law_on_originals
  let q (a : Fin 13) := (p a).viaEmbedding (fiveSlot j)
  have hmap (I : Finset (Fin 4)) :
      (I.map fiveEmbedding).map (fiveSlot j) = I.map Function.Embedding.inl := by
    rw [Finset.map_map]
    have he : fiveEmbedding.trans (fiveSlot j) = Function.Embedding.inl :=
      Function.Embedding.ext (fiveSlot_original j)
    rw [he]
  apply feasible_of_indexed_law q w hw hm
  rintro (k | l) hl
  · have he (a : Fin 13) : subsetImageEvent (paddedConstraintRows r (.inl k))
        (paddedConstraintColumns r (.inl k)) (q a) = subsetImageEvent
          ((originalRows k).map fiveEmbedding) ((originalColumns k).map fiveEmbedding) (p a) := by
      simpa only [paddedConstraintRows, paddedConstraintColumns, hmap] using event_on_embedding
        (fiveSlot j) (p a) (q a) ((p a).viaEmbedding_apply (fiveSlot j))
        ((originalRows k).map fiveEmbedding) ((originalColumns k).map fiveEmbedding)
    simpa only [he, paddedMinor_original] using ht k
  · have hlj : l ≠ j := fun h => hj (h ▸ hl)
    have he (a : Fin 13) : q a (Sum.inr l) = Sum.inr l :=
      (p a).viaEmbedding_apply_of_not_mem (fiveSlot j) _ (fiveSlot_other hlj)
    simp only [paddedEvent_fixed, he, if_true, mul_one, hm, paddedMinor_fixed]

private theorem fixed_on_support {α : Type*} [Fintype α] [DecidableEq α]
    (w : Equiv.Perm α → ℝ) (hw : ∀ σ, 0 ≤ w σ) (hm : ∑ σ, w σ = 1)
    (j : α) (hp : (∑ σ, w σ * (if σ j = j then 1 else 0)) = 1)
    (σ : Equiv.Perm α) (hs : w σ ≠ 0) : σ j = j := by
  let E (p : Equiv.Perm α) : ℝ := if p j = j then 1 else 0
  have hn (p : Equiv.Perm α) : 0 ≤ w p - w p * E p := by
    by_cases h : p j = j
    · simp only [E, if_pos h, mul_one, sub_self, le_refl]
    · simpa only [E, if_neg h, mul_zero, sub_zero] using hw p
  have hsum : (∑ p, (w p - w p * E p)) = 0 := by
    rw [Finset.sum_sub_distrib, hm, show (∑ p, w p * E p) = 1 from hp, sub_self]
  have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun p _ => hn p)).mp hsum σ (Finset.mem_univ σ)
  by_contra h
  exact hs (by simpa only [E, if_neg h, mul_zero, sub_zero] using hz)

private theorem exists_original_perm {r : ℕ} (σ : Equiv.Perm (Fin 4 ⊕ Fin r))
    (h : ∀ j, σ (Sum.inr j) = Sum.inr j) :
    ∃ p : Fin 24, ∀ i, σ (Sum.inl i) = Sum.inl ((fourPerm p).symm i) := by
  have himage (i : Fin 4) : ∃ j : Fin 4, σ (Sum.inl i) = Sum.inl j := by
    cases he : σ (Sum.inl i) with
    | inl j => exact ⟨j, rfl⟩
    | inr j => exact (Sum.inl_ne_inr (σ.injective (he.trans (h j).symm))).elim
  choose f hf using himage
  have hi : Function.Injective f := by
    intro i j hij
    have he : σ (Sum.inl i) = σ (Sum.inl j) := by rw [hf i, hf j, hij]
    exact Sum.inl.inj (σ.injective he)
  let e : Equiv.Perm (Fin 4) := Equiv.ofBijective f ⟨hi, Finite.injective_iff_surjective.mp hi⟩
  obtain ⟨p, hp⟩ := fourPerm_surjective e.symm
  refine ⟨p, fun i => ?_⟩
  rw [hp, Equiv.symm_symm]
  exact hf i

private theorem paddedConstraintFeasible_not_univ (r : ℕ) :
    ¬ PaddedConstraintFeasible r Finset.univ := by
  classical
  rintro ⟨w, hw, hm, ht⟩
  have hfix (σ : Equiv.Perm (Fin 4 ⊕ Fin r)) (hs : w σ ≠ 0) (j : Fin r) :
      σ (Sum.inr j) = Sum.inr j := by
    refine fixed_on_support w hw hm (Sum.inr j) ?_ σ hs
    simpa only [paddedEvent_fixed, paddedMinor_fixed] using ht (Sum.inr j) (Finset.mem_univ _)
  let p (σ : Equiv.Perm (Fin 4 ⊕ Fin r)) : Fin 24 :=
    if hs : w σ ≠ 0 then Classical.choose (exists_original_perm σ (hfix σ hs)) else 0
  have hp (σ : Equiv.Perm (Fin 4 ⊕ Fin r)) (hs : w σ ≠ 0) (i : Fin 4) :
      σ (Sum.inl i) = Sum.inl ((fourPerm (p σ)).symm i) := by
    simp only [p, dif_pos hs]
    exact Classical.choose_spec (exists_original_perm σ (hfix σ hs)) i
  obtain ⟨v, hv, hvsum, hF⟩ := push_law p w hw hm
  have horiginal : FourConstraintFeasible Finset.univ := by
    refine ⟨v, hv, hvsum, fun k _ => ?_⟩
    rw [hF]
    have he (σ : Equiv.Perm (Fin 4 ⊕ Fin r)) :
        w σ * ordinaryCostRay (fourConstraintRay k) (p σ) =
        w σ * subsetImageEvent (paddedConstraintRows r (.inl k)) (paddedConstraintColumns r (.inl k)) σ := by
      by_cases hs : w σ = 0
      · simp only [hs, zero_mul]
      · have h := event_on_embedding Function.Embedding.inl (fourPerm (p σ)).symm σ
          (hp σ hs) (originalRows k) (originalColumns k)
        exact congrArg (w σ * ·) (h.trans (originalEvent_eq k (p σ))).symm
    simp only [he]
    simpa only [paddedMinor_original] using ht (Sum.inl k) (Finset.mem_univ _)
  exact (fourConstraintFeasible_iff _).mp horiginal rfl

/-- The thirteen original observations and the `r` fixed-label observations form a minimal
infeasible family for the order-`4 + r` padded mixer. Its feasibility nerve is the boundary
of the simplex on `Fin 13 ⊕ Fin r`. -/
theorem paddedConstraintFeasible_iff (r : ℕ) (s : Finset (Fin 13 ⊕ Fin r)) :
    PaddedConstraintFeasible r s ↔ s ≠ Finset.univ := by
  constructor
  · intro h he
    exact paddedConstraintFeasible_not_univ r (he ▸ h)
  · intro h
    obtain ⟨k, hk⟩ : ∃ k, k ∉ s := by
      by_contra! hall
      exact h (Finset.eq_univ_iff_forall.mpr hall)
    cases k with
    | inl i => exact feasible_omit_original i hk
    | inr j => exact feasible_omit_fixed j hk

end

end MOC
