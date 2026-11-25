import MOC.PolynomialProfileContact
import MOC.ZeroHeightCycleSaturation

/-! Finite connectivity certificates of strict contact sets. The
varying-gap argument starts from Zheng, DOI: 10.13140/RG.2.2.36790.25923.
Contacts here are spectral labels; no orbit-rotation tie is inferred. -/

open Matrix

namespace MOC

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- An edge takes a slot to or from its image under a relative contact
permutation. This is not an assertion that the swap of its endpoints is
itself a contact. -/
def relativeContactEdge (r : Equiv.Perm ι) (T : Finset (Equiv.Perm ι)) (i j : ι) : Prop :=
  ∃ q ∈ T, r.symm (q i) = j ∨ r.symm (q j) = i

/-- At most `n−1` old contact labels witness connectedness of the union
of relative moves of a contact-maximal strict witness. -/
theorem StrictMatchingSupport.exists_spanning_contact_subfamily
    {U : Matrix ι ι ℂ} (hU : IsUnitary U) (w : StrictMatchingSupport U)
    (hmax : ∀ v : StrictMatchingSupport U, v.contacts.card ≤ w.contacts.card) (o : ι) :
    ∃ T ⊆ w.contacts, T.card < Fintype.card ι ∧
      ∀ j, Relation.ReflTransGen (relativeContactEdge w.pivot T) o j := by
  classical
  let R (T : Finset (Equiv.Perm ι)) := Finset.univ.filter fun j =>
    Relation.ReflTransGen (relativeContactEdge w.pivot T) o j
  have ho (T : Finset (Equiv.Perm ι)) : o ∈ R T := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,Relation.ReflTransGen.refl⟩
  have hmem (T : Finset (Equiv.Perm ι)) (j : ι) :
      j ∈ R T ↔ Relation.ReflTransGen (relativeContactEdge w.pivot T) o j := by
    simp [R]
  have hm {T T' : Finset (Equiv.Perm ι)} (hh : T ⊆ T') : R T ⊆ R T' := by
    intro j hj
    refine (hmem _ _).mpr ((hmem _ _).mp hj |>.mono ?_)
    rintro i k ⟨q,hq,hq'⟩
    exact ⟨q,hh hq,hq'⟩
  have hstep (T : Finset (Equiv.Perm ι)) (hT : T ⊆ w.contacts) (j : ι) (hj : j ∉ R T) :
      ∃ q ∈ w.contacts, q ∉ T ∧ R T ⊂ R (insert q T) := by
    obtain ⟨q,hq,k,hcross⟩ := w.contact_crosses_every_nontrivial_cut
      hU hmax (R T) ⟨o,ho _⟩ ⟨j,hj⟩
    have he : ∃ i ∈ R T, ∃ l ∉ R T,
        w.pivot.symm (q i) = l ∨ w.pivot.symm (q l) = i := by
      by_cases hki : k ∈ R T
      · refine ⟨k,hki,w.pivot.symm (q k),?_,Or.inl rfl⟩
        intro hl
        exact hcross ⟨fun _ => hki, fun _ => hl⟩
      · refine ⟨w.pivot.symm (q k),?_,k,hki,Or.inr rfl⟩
        by_contra! hn
        exact hcross ⟨fun h => (hn h).elim,fun h => (hki h).elim⟩
    obtain ⟨i,hi,l,hl,hel⟩ := he
    have hqT : q ∉ T := fun hq' =>
      hl ((hmem T l).mpr (((hmem T i).mp hi).tail ⟨q,hq',hel⟩))
    have hsub : R T ⊆ R (insert q T) := hm (Finset.subset_insert _ _)
    have hlu : l ∈ R (insert q T) := (hmem _ _).mpr
      (((hmem _ _).mp (hsub hi)).tail ⟨q,Finset.mem_insert_self _ _,hel⟩)
    exact ⟨q,hq,hqT,Finset.ssubset_iff_subset_ne.mpr
      ⟨hsub,fun e => hl (e.symm ▸ hlu)⟩⟩
  have go (d : ℕ) (T : Finset (Equiv.Perm ι)) (hT : T ⊆ w.contacts)
      (hcount : T.card < (R T).card) (hd : Fintype.card ι - (R T).card = d) :
      ∃ T ⊆ w.contacts, T.card < Fintype.card ι ∧
        ∀ j, Relation.ReflTransGen (relativeContactEdge w.pivot T) o j := by
    induction d using Nat.strong_induction_on generalizing T with
    | h d ih =>
      by_cases hall : ∀ j, j ∈ R T
      · exact ⟨T,hT,hcount.trans_le (R T).card_le_univ,fun j => (hmem _ _).mp (hall j)⟩
      · push_neg at hall
        obtain ⟨j,hj⟩ := hall
        obtain ⟨q,hq,hnot,hsub⟩ := hstep T hT j hj
        have hlt := Finset.card_lt_card hsub
        have hub : (R (insert q T)).card ≤ Fintype.card ι := (R _).card_le_univ
        apply ih (Fintype.card ι - (R (insert q T)).card) (by omega)
          (insert q T) (Finset.insert_subset_iff.mpr ⟨hq,hT⟩)
        · rw [Finset.card_insert_of_not_mem hnot]
          omega
        · rfl
  exact go _ ∅ (Finset.empty_subset _) (by
    simpa using Finset.card_pos.mpr ⟨o,ho ∅⟩) rfl

/-- Graph of nonvanishing labels joined by right transpositions. -/
def nonzeroTranspositionEdge (a b : ι → ℂ) (r q : Equiv.Perm ι) : Prop :=
  matchingProduct a b r ≠ 0 ∧ matchingProduct a b q ≠ 0 ∧
    ∃ i j : ι, i ≠ j ∧ q = r * Equiv.swap i j

/-- A nonzero contact in a strict zero-height witness is in a component
with a noncontact. In fact it already has a nonzero transposition
neighbor outside the contact set. -/
theorem StrictMatchingSupport.nonzero_contact_component_has_boundary
    {U : Matrix ι ι ℂ} (hU : IsUnitary U) (w : StrictMatchingSupport U)
    (hzero : (w.η * matchingProduct w.a w.b w.pivot).re = 0)
    (r : Equiv.Perm ι) (hr : r ∈ w.contacts)
    (hn : matchingProduct w.a w.b r ≠ 0) :
    ∃ q ∉ w.contacts, nonzeroTranspositionEdge w.a w.b r q := by
  have hη : w.η ≠ 0 := fun h => by simpa [h] using w.strict
  have hbad : ¬ Holds w.a w.b U := fun h => by
    obtain ⟨q,hq⟩ := (holds_iff_directional _ _ _).mp h w.η
    exact (not_lt_of_ge (hq.trans (w.maximal q))) w.strict
  have hrzero : (w.η * matchingProduct w.a w.b r).re = 0 :=
    (Finset.mem_filter.mp hr).2.trans hzero
  obtain ⟨i,j,hij,hs,hns⟩ := exists_nonzero_inactive_swap_of_not_holds_at_zero_height
    w.a w.b w.η r U hU hbad (mul_ne_zero hη hn) hrzero (fun q => (w.maximal q).trans_eq hzero)
  refine ⟨_,fun hx => hs.ne ((Finset.mem_filter.mp hx).2.trans hzero),hn,hns,i,j,hij,rfl⟩

end MOC
