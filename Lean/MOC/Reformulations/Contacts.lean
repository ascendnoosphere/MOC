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

end MOC.Reformulations
