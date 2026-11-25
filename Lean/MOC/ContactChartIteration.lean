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
    exact w.not_holds (h w.a w.b U hU)
  · intro h
    apply conjecture_iff_nonopposite.mpr
    intro a b U hU hnz
    classical
    by_contra hh
    obtain ⟨w, ha, hb⟩ := exists_strictMatchingSupport_of_failure a b hh
    have hw : ∀ q, matchingProduct w.a w.b q ≠ 0 := by
      intro q
      rw [ha, hb]
      exact Finset.prod_ne_zero_iff.mpr fun j _ => hnz (q j) j
    obtain ⟨v, hv, hvnz⟩ := exists_strictMatchingSupport_at_least_preserving k
      (fun u => ∀ q, matchingProduct u.a u.b q ≠ 0) w hw (fun u hunz hu => by
        obtain ⟨v, hinc, hvnz⟩ := step U hU u hunz hu
        exact ⟨v, hvnz, Finset.card_lt_card hinc⟩)
    exact h ⟨U, hU, v, hv, hvnz⟩

end MOC
