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

theorem StrictMatchingSupport.not_holds {U : Matrix ι ι ℂ}
    (w : StrictMatchingSupport U) : ¬ Holds w.a w.b U := by
  intro h
  obtain ⟨q, hq⟩ := (holds_iff_directional w.a w.b U).mp h w.η
  exact (not_lt_of_ge (hq.trans (w.maximal q))) w.strict

/-- Failure of the hull inclusion gives a strict support witness at the original spectra. -/
theorem exists_strictMatchingSupport_of_failure {U : Matrix ι ι ℂ}
    (a b : ι → ℂ) (h : ¬ Holds a b U) :
    ∃ w : StrictMatchingSupport U, w.a = a ∧ w.b = b := by
  classical
  rw [holds_iff_directional] at h
  push_neg at h
  obtain ⟨η, hη⟩ := h
  obtain ⟨p, _, hp⟩ := Finset.exists_max_image Finset.univ
    (fun q : Equiv.Perm ι => (η * matchingProduct a b q).re)
    ⟨Equiv.refl ι, Finset.mem_univ _⟩
  exact ⟨⟨a, b, η, p, fun q => hp q (Finset.mem_univ q), hη p⟩, rfl, rfl⟩

theorem nonempty_strictMatchingSupport_of_failure {U : Matrix ι ι ℂ}
    (a b : ι → ℂ) (h : ¬ Holds a b U) : Nonempty (StrictMatchingSupport U) := by
  obtain ⟨w, _, _⟩ := exists_strictMatchingSupport_of_failure a b h
  exact ⟨w⟩

/-- A contact increase that preserves a witness condition reaches the threshold
without leaving that condition. -/
theorem exists_strictMatchingSupport_at_least_preserving {U : Matrix ι ι ℂ} (k : ℕ)
    (P : StrictMatchingSupport U → Prop) (w : StrictMatchingSupport U) (hw : P w)
    (step : ∀ v : StrictMatchingSupport U, P v → v.contacts.card < k →
      ∃ v' : StrictMatchingSupport U, P v' ∧ v.contacts.card < v'.contacts.card) :
    ∃ v : StrictMatchingSupport U, k ≤ v.contacts.card ∧ P v := by
  let Reach (d : ℕ) := ∀ v : StrictMatchingSupport U, P v → k - v.contacts.card = d →
    ∃ v' : StrictMatchingSupport U, k ≤ v'.contacts.card ∧ P v'
  have reach (d : ℕ) : Reach d := by
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro v hv hd
      by_cases hk : k ≤ v.contacts.card
      · exact ⟨v, hk, hv⟩
      · have hbelow : v.contacts.card < k := Nat.lt_of_not_ge hk
        obtain ⟨v', hv', hlt⟩ := step v hv hbelow
        have hdecrease : k - v'.contacts.card < d := by
          rw [← hd]
          exact Nat.sub_lt_sub_left hbelow hlt
        exact ih (k - v'.contacts.card) hdecrease v' hv' rfl
  exact reach (k - w.contacts.card) w hw rfl

/-- A strict increase at each step is enough to reach the threshold. -/
theorem exists_strictMatchingSupport_at_least {U : Matrix ι ι ℂ} (k : ℕ)
    (w : StrictMatchingSupport U)
    (step : ∀ v : StrictMatchingSupport U, v.contacts.card < k →
      ∃ v' : StrictMatchingSupport U, v.contacts.card < v'.contacts.card) :
    ∃ v : StrictMatchingSupport U, k ≤ v.contacts.card := by
  obtain ⟨v, hv, _⟩ :=
    exists_strictMatchingSupport_at_least_preserving k (fun _ => True) w True.intro
      (fun u _ hu => by
        obtain ⟨v', hlt⟩ := step u hu
        exact ⟨v', True.intro, hlt⟩)
  exact ⟨v, hv⟩

end MOC
