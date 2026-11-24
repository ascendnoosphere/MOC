import MOC.GlobalContactSlice
import MOC.MatchingTriangle

/-! A contact slice spends dimension on controlling equations, not on the
number of labels those equations determine. The fixed-gap method follows
Zheng, DOI: 10.13140/RG.2.2.36790.25923. -/

open BigOperators Matrix MvPolynomial

namespace MOC

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A strict witness can be chosen with a contact set that admits no cheaper
control by complex polynomial observables. This gives a terminal condition
in terms of equations on exact profiles instead of a label count. -/
theorem global_exists_contact_equation_saturated {U : Matrix ι ι ℂ}
    (hU : IsUnitary U) (w : StrictMatchingSupport U) :
    ∃ v : StrictMatchingSupport U, w.PreservesContactData v ∧
      ∀ (E : Finset (ProfileRing ι)),
      (∀ a b : ι → ℂ,
        (∀ p ∈ E, eval (matchingProduct a b) p = eval (matchingProduct v.a v.b) p) →
        (∀ q ∈ v.contacts, matchingProduct a b v.pivot - matchingProduct a b q =
          matchingProduct v.a v.b v.pivot - matchingProduct v.a v.b q) ∧
        matchingProfileDetGap U v.η v.pivot (matchingProduct a b) =
          matchingProfileDetGap U v.η v.pivot (matchingProduct v.a v.b)) →
      2 * Fintype.card ι - 2 ≤ E.card := by
  classical
  let M := (Fintype.card (Equiv.Perm ι))
  let P (u : StrictMatchingSupport U) := w.PreservesContactData u
  let S := (Finset.univ : Finset (Fin (M + 1))).filter fun m =>
    ∃ u : StrictMatchingSupport U, P u ∧ u.contacts.card = m.val
  have hle (u : StrictMatchingSupport U) : u.contacts.card ≤ M :=
    u.contacts.card_le_univ
  let m : Fin (M + 1) := ⟨w.contacts.card, Nat.lt_succ_of_le (hle w)⟩
  have hm : m ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, w, .refl w, rfl⟩
  obtain ⟨r, hr, hrmax⟩ := Finset.exists_max_image S Fin.val ⟨m, hm⟩
  obtain ⟨v, hv, hvr⟩ := (Finset.mem_filter.mp hr).2
  refine ⟨v,hv,fun E hdet => ?_⟩
  by_contra! hsmall
  obtain ⟨u, hvu, hdata, _⟩ :=
    global_contact_transfer_of_controlling_observables hU v E hsmall hdet
  let ru : Fin (M + 1) := ⟨u.contacts.card, Nat.lt_succ_of_le (hle u)⟩
  have hru : ru ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, u, hv.trans hdata, rfl⟩
  have hcard := Finset.card_lt_card hvu
  have hbound := hrmax ru hru
  exact (not_lt_of_ge (hvr ▸ hbound)) hcard

/-- A three-column fibre can be controlled by four contact differences:
the alternating identity recovers the fifth. Thus, in order at least four,
a strict witness whose contacts lie in one such fibre can grow its contact
set, even if all six labels of the fibre are already contacts. -/
theorem global_contact_transfer_of_contacts_in_triangle_fibre
    {U : Matrix ι ι ℂ} (hU : IsUnitary U) (w : StrictMatchingSupport U)
    (hn : 4 ≤ Fintype.card ι) (i j k : ι) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hfibre : w.contacts ⊆ ({w.pivot, w.pivot * Equiv.swap i j * Equiv.swap j k,
      w.pivot * Equiv.swap j k * Equiv.swap i j, w.pivot * Equiv.swap i j,
      w.pivot * Equiv.swap i k, w.pivot * Equiv.swap j k} : Finset (Equiv.Perm ι))) :
    ∃ v : StrictMatchingSupport U, w.contacts ⊂ v.contacts ∧ w.PreservesContactData v := by
  classical
  let r := w.pivot
  let c₁ := r * Equiv.swap i j * Equiv.swap j k
  let c₂ := r * Equiv.swap j k * Equiv.swap i j
  let s₁ := r * Equiv.swap i j
  let s₂ := r * Equiv.swap i k
  let s₃ := r * Equiv.swap j k
  let T : Finset (Equiv.Perm ι) := {c₁, s₁, s₂, s₃}
  let diff (q : Equiv.Perm ι) : ProfileRing ι := X r - X q
  let gap : ProfileRing ι := ∑ q, C (realSignedWeight U q : ℂ) *
    (C w.η * (X q - X r))
  let E := insert gap (T.image diff)
  have hT : T.card ≤ 4 := by
    have h := Finset.card_insert_le c₁ ({s₁, s₂, s₃} : Finset (Equiv.Perm ι))
    have h₁ := Finset.card_insert_le s₁ ({s₂, s₃} : Finset (Equiv.Perm ι))
    have h₂ := Finset.card_insert_le s₂ ({s₃} : Finset (Equiv.Perm ι))
    rw [Finset.card_singleton] at h₂
    change T.card ≤ _ at h
    omega
  have hE : E.card < 2 * Fintype.card ι - 2 := by
    have h := Finset.card_insert_le gap (T.image diff)
    have hh := Finset.card_image_le (s := T) (f := diff)
    change E.card ≤ _ at h
    omega
  have hGap (x : Equiv.Perm ι → ℂ) : eval x gap = matchingProfileDetGap U w.η r x := by
    simp only [gap, map_sum, map_mul, eval_C, map_sub, eval_X, matchingProfileDetGap]
  have hdet (a b : ι → ℂ)
      (h : ∀ p ∈ E, eval (matchingProduct a b) p = eval (matchingProduct w.a w.b) p) :
      (∀ q ∈ w.contacts, matchingProduct a b r - matchingProduct a b q =
        matchingProduct w.a w.b r - matchingProduct w.a w.b q) ∧
      matchingProfileDetGap U w.η r (matchingProduct a b) =
        matchingProfileDetGap U w.η r (matchingProduct w.a w.b) := by
    refine ⟨?_, ?_⟩
    · let d (a b : ι → ℂ) (q : Equiv.Perm ι) :=
        matchingProduct a b r - matchingProduct a b q
      have hs (q) (hq : q ∈ T) : d a b q = d w.a w.b q := by
        have hh := h (diff q) (Finset.mem_insert_of_mem (Finset.mem_image_of_mem diff hq))
        simpa only [diff, map_sub, eval_X, d] using hh
      have hc (a b : ι → ℂ) : d a b c₂ = d a b s₁ + d a b s₂ + d a b s₃ - d a b c₁ := by
        have htri := matchingProduct_triangle_identity a b r i j k hij hik hjk
        change matchingProduct a b r + matchingProduct a b c₁ + matchingProduct a b c₂ =
          matchingProduct a b s₁ + matchingProduct a b s₂ + matchingProduct a b s₃ at htri
        unfold d
        linear_combination -htri
      have hc₂ : d a b c₂ = d w.a w.b c₂ := by
        rw [hc a b, hc w.a w.b, hs s₁ (by simp [T]), hs s₂ (by simp [T]),
          hs s₃ (by simp [T]), hs c₁ (by simp [T])]
      intro q hq
      change d a b q = d w.a w.b q
      have hq' : q ∈ ({r, c₁, c₂, s₁, s₂, s₃} : Finset (Equiv.Perm ι)) := hfibre hq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hq'
      rcases hq' with hq' | hq' | hq' | hq' | hq' | hq'
      · subst q
        simp [d]
      · exact hs q (by simp [T, hq'])
      · exact hq' ▸ hc₂
      · exact hs q (by simp [T, hq'])
      · exact hs q (by simp [T, hq'])
      · exact hs q (by simp [T, hq'])
    · rw [← hGap, ← hGap]
      exact h gap (Finset.mem_insert_self ..)
  obtain ⟨v, hv, hd, _⟩ := global_contact_transfer_of_controlling_observables hU w E hE hdet
  exact ⟨v,hv,hd⟩

end MOC
