import MOC.ContactAffineRigidity

/-! A strict contact-maximal witness cannot have only one complex value
among its contacts. In particular a zero-height terminal face needs a
nonzero contact, even when it also has any number of zero products. -/

open Matrix

namespace MOC

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem StrictMatchingSupport.exists_more_contacts_of_coincident_contacts
    {U : Matrix ι ι ℂ} (hU : IsUnitary U) (w : StrictMatchingSupport U)
    (hc : ∀ q ∈ w.contacts, matchingProduct w.a w.b q = matchingProduct w.a w.b w.pivot) :
    ∃ v : StrictMatchingSupport U, v.η = w.η ∧ v.pivot = w.pivot ∧
      w.contacts ⊂ v.contacts := by
  let p := matchingProduct w.a w.b
  have hp : p ≠ 0 := by
    intro h
    have hd : determinantValue w.a w.b U = 0 := by
      rw [← real_signed_determinant w.a w.b U hU]
      change (∑ σ, (realSignedWeight U σ : ℂ) * p σ) = 0
      simp [h]
    have hw : matchingProduct w.a w.b w.pivot = 0 := by
      change p w.pivot = 0
      simp [h]
    have hs := w.strict
    simp [hw, hd] at hs
  apply w.exists_more_contacts_on_exact_affine_line hU p hp hc
  intro z
  obtain ⟨c, hc'⟩ := IsAlgClosed.exists_pow_nat_eq (1 + z) (Fintype.card_pos (α := ι))
  refine ⟨fun i => c * w.a i, fun j => c * w.b j, ?_⟩
  funext q
  rw [matchingProduct_scale, hc']
  change (1 + z) * p q = p q + z * p q
  ring

theorem StrictMatchingSupport.exists_distinct_complex_contact_of_maximal_count
    {U : Matrix ι ι ℂ} (hU : IsUnitary U) (w : StrictMatchingSupport U)
    (hmax : ∀ v : StrictMatchingSupport U, v.contacts.card ≤ w.contacts.card) :
    ∃ q ∈ w.contacts, matchingProduct w.a w.b q ≠ matchingProduct w.a w.b w.pivot := by
  by_contra! h
  obtain ⟨v, _, _, hv⟩ := w.exists_more_contacts_of_coincident_contacts hU h
  exact (not_lt_of_ge (hmax v)) (Finset.card_lt_card hv)

theorem StrictMatchingSupport.exists_nonzero_contact_of_maximal_count
    {U : Matrix ι ι ℂ} (hU : IsUnitary U) (w : StrictMatchingSupport U)
    (hmax : ∀ v : StrictMatchingSupport U, v.contacts.card ≤ w.contacts.card) :
    ∃ q ∈ w.contacts, matchingProduct w.a w.b q ≠ 0 := by
  by_contra! h
  have hp : w.pivot ∈ w.contacts := by
    simp [StrictMatchingSupport.contacts]
  obtain ⟨q, hq, hne⟩ := w.exists_distinct_complex_contact_of_maximal_count hU hmax
  exact hne ((h q hq).trans (h _ hp).symm)

end MOC
