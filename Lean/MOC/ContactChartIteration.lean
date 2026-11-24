import MOC.GeneralContactReduction
import MOC.ContactIteration

/-! A contact-raising step that stays in the all-nonzero chart can be
iterated without perturbing any of the contacts that it has already gained. -/

open Matrix

namespace MOC

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A strict support witness cannot have a constant matching profile. -/
theorem StrictMatchingSupport.profile_nonconstant {U : Matrix ι ι ℂ}
    (hU : IsUnitary U) (w : StrictMatchingSupport U) :
    ¬ ∀ q, matchingProduct w.a w.b q = matchingProduct w.a w.b 1 := by
  intro h
  have hp (q : Equiv.Perm ι) : matchingProduct w.a w.b q =
      matchingProduct w.a w.b w.pivot := (h q).trans (h w.pivot).symm
  have hg : matchingProfileDetGap U w.η w.pivot (matchingProduct w.a w.b) = 0 := by
    simp only [matchingProfileDetGap, hp, sub_self, mul_zero, Finset.sum_const_zero]
  rw [matchingProfileDetGap_matchingProduct w.a w.b U hU, mul_sub,
    sub_eq_zero] at hg
  exact w.strict.ne (congrArg Complex.re hg).symm

/-- Within the nonzero matching-profile locus, contact raising reduces
the full conjecture to exclusion of strict witnesses at the threshold.
The reverse implication needs no contact-raising premise. -/
theorem conjecture_iff_no_nonzero_terminal_witness (k : ℕ)
    (step : ∀ (U : Matrix ι ι ℂ), IsUnitary U → ∀ w : StrictMatchingSupport U,
      (∀ q, matchingProduct w.a w.b q ≠ 0) → w.contacts.card < k →
      ∃ v : StrictMatchingSupport U, w.contacts ⊂ v.contacts ∧
        ∀ q, matchingProduct v.a v.b q ≠ 0) :
    Conjecture ι ↔ ¬ ∃ (U : Matrix ι ι ℂ), IsUnitary U ∧
      ∃ w : StrictMatchingSupport U, k ≤ w.contacts.card ∧
        ∀ q, matchingProduct w.a w.b q ≠ 0 := by
  constructor
  · rintro h ⟨U, hU, w, -, -⟩
    obtain ⟨q, hq⟩ := ((holds_iff_directional _ _ _).mp (h w.a w.b U hU)) w.η
    exact (not_lt_of_ge (hq.trans (w.maximal q))) w.strict
  · intro h
    apply conjecture_iff_nonopposite.mpr
    intro a b U hU hnz
    classical
    by_contra hh
    obtain ⟨w, hw, ha⟩ : ∃ w : StrictMatchingSupport U,
        w.a = a ∧ w.b = b := by
      rw [holds_iff_directional, not_forall] at hh
      obtain ⟨η, hη⟩ := hh
      push_neg at hη
      obtain ⟨p, _, hp⟩ := Finset.exists_max_image Finset.univ
        (fun q : Equiv.Perm ι => (η * matchingProduct a b q).re)
        ⟨1, Finset.mem_univ _⟩
      exact ⟨⟨a, b, η, p, fun q => hp q (Finset.mem_univ _), hη p⟩, rfl, rfl⟩
    have hit (d : ℕ) (v : StrictMatchingSupport U)
        (hn : ∀ q, matchingProduct v.a v.b q ≠ 0)
        (hd : k - v.contacts.card = d) : False := by
      induction d using Nat.strong_induction_on generalizing v with
      | h d ih =>
        by_cases hk : k ≤ v.contacts.card
        · exact h ⟨U, hU, v, hk, hn⟩
        · obtain ⟨v', hv', hn'⟩ := step U hU v hn (Nat.lt_of_not_ge hk)
          have hcard := Finset.card_lt_card hv'
          exact ih (k - v'.contacts.card) (by omega) v' hn' rfl
    apply hit _ w _ rfl
    intro q
    rw [hw, ha]
    exact Finset.prod_ne_zero_iff.mpr fun j _ => hnz (q j) j

end MOC
