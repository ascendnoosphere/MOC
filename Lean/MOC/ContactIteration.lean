import MOC.Support

/-! Strict support witnesses and finite iteration of contact transfer. -/

open Matrix

namespace MOC

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A separating direction and a maximum matching value in that direction.
The mixer is fixed across all witnesses of this type. -/
structure StrictMatchingSupport (U : Matrix ι ι ℂ) where
  a : ι → ℂ
  b : ι → ℂ
  η : ℂ
  pivot : Equiv.Perm ι
  maximal : ∀ q, (η * matchingProduct a b q).re ≤ (η * matchingProduct a b pivot).re
  strict : (η * matchingProduct a b pivot).re < (η * determinantValue a b U).re

noncomputable def StrictMatchingSupport.contacts {U : Matrix ι ι ℂ}
    (w : StrictMatchingSupport U) : Finset (Equiv.Perm ι) := by
  classical
  exact Finset.univ.filter fun q =>
    (w.η * matchingProduct w.a w.b q).re = (w.η * matchingProduct w.a w.b w.pivot).re

/-- Failure of the hull inclusion gives a strict support witness. -/
theorem nonempty_strictMatchingSupport_of_failure {U : Matrix ι ι ℂ}
    (a b : ι → ℂ) (h : ¬ Holds a b U) : Nonempty (StrictMatchingSupport U) := by
  classical
  rw [holds_iff_directional] at h
  push_neg at h
  obtain ⟨η, hη⟩ := h
  obtain ⟨p, _, hp⟩ := Finset.exists_max_image Finset.univ
    (fun q : Equiv.Perm ι => (η * matchingProduct a b q).re)
    ⟨Equiv.refl ι, Finset.mem_univ _⟩
  exact ⟨⟨a, b, η, p, fun q => hp q (Finset.mem_univ _), hη p⟩⟩

/-- A strict increase at each step is enough to reach the threshold.
The induction takes place on the number of contacts still needed. -/
theorem exists_strictMatchingSupport_at_least {U : Matrix ι ι ℂ} (k : ℕ)
    (w : StrictMatchingSupport U)
    (step : ∀ v : StrictMatchingSupport U, v.contacts.card < k →
      ∃ v' : StrictMatchingSupport U, v.contacts.card < v'.contacts.card) :
    ∃ v : StrictMatchingSupport U, k ≤ v.contacts.card := by
  let P (d : ℕ) := ∀ v : StrictMatchingSupport U, k - v.contacts.card = d →
    ∃ v' : StrictMatchingSupport U, k ≤ v'.contacts.card
  have h (d : ℕ) : P d := by
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro v hv
      by_cases hk : k ≤ v.contacts.card
      · exact ⟨v, hk⟩
      · obtain ⟨v', hlt⟩ := step v (by omega)
        exact ih (k - v'.contacts.card) (by omega) v' rfl
  exact h _ w rfl

end MOC
