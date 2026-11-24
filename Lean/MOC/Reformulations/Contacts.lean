import MOC.Reformulations.Common
import MOC.Support

namespace MOC.Reformulations

/-- A finite support test for one direction. The contacts count permutation
labels, not distinct matching products. -/
def ContactForm (n k : ℕ) : Prop :=
  ∀ (a b : Fin n → ℂ) (U : Matrix (Fin n) (Fin n) ℂ)
    (η : ℂ) (p : Equiv.Perm (Fin n)), IsUnitary U →
    (∀ q : Equiv.Perm (Fin n),
      (η * matchingProduct a b q).re ≤ (η * matchingProduct a b p).re) →
    k ≤ (Finset.univ.filter fun q : Equiv.Perm (Fin n) =>
      (η * matchingProduct a b q).re = (η * matchingProduct a b p).re).card →
    (η * determinantValue a b U).re ≤ (η * matchingProduct a b p).re

theorem contactForm_of_conjecture {n k : ℕ} (h : Conjecture (Fin n)) :
    ContactForm n k := by
  intro a b U η p hU hp _
  obtain ⟨q, hq⟩ := (holds_iff_directional a b U).mp (h a b U hU) η
  exact hq.trans (hp q)

theorem not_moc_of_not_contactForm {n k : ℕ} (h : ¬ ContactForm n k) :
    ¬ MOCIsTrue :=
  fun hm => h (contactForm_of_conjecture (hm n))

/-- The reverse implication in OrderFiveContactReduction.md is not proved by
the two theorems above. It requires the contact-transfer existence theorem. -/
def AllOrderContactTarget : Prop :=
  ∀ n : ℕ, 2 ≤ n → ContactForm n (2 * n - 2)

theorem allOrderContactTarget_of_moc (h : MOCIsTrue) : AllOrderContactTarget :=
  fun n _ => contactForm_of_conjecture (h n)

/-- The seven-contact threshold in the proposed order-four reduction. -/
def SevenContactTarget : Prop := ContactForm 4 7

theorem sevenContactTarget_of_moc (h : MOCIsTrue) : SevenContactTarget :=
  contactForm_of_conjecture (h 4)

end MOC.Reformulations
