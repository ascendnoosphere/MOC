import MOC.ThreeSharedRepeatedFive
import MOC.Small
import MOC.SpectralZeroPadding

open Matrix

namespace MOC.ThreeSharedRepeatedFive

private theorem holds_left_of_three_pairs {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a b : ι → ℂ) (e f : Fin 5 ≃ ι)
    (hp : ∀ j : Fin 3, a (e j.castSucc.castSucc) + b (f j.castSucc.castSucc) = 0)
    (hr : a (e 3) = a (e 4))
    (U : Matrix ι ι ℂ) (hU : IsUnitary U) : Holds a b U := by
  let z : Fin 6 → ℂ := ![a (e 0), a (e 1), a (e 2), a (e 3), -b (f 3), -b (f 4)]
  have ha : a ∘ e = left z := by
    funext i
    fin_cases i
    · rfl
    · rfl
    · rfl
    · rfl
    · exact hr.symm
  have hb : b ∘ f = right z := by
    funext i
    fin_cases i
    · change b (f 0) = -a (e 0)
      have h : a (e 0) + b (f 0) = 0 := hp 0
      linear_combination h
    · change b (f 1) = -a (e 1)
      have h : a (e 1) + b (f 1) = 0 := hp 1
      linear_combination h
    · change b (f 2) = -a (e 2)
      have h : a (e 2) + b (f 2) = 0 := hp 2
      linear_combination h
    · change b (f 3) = - -b (f 3)
      simp
    · change b (f 4) = - -b (f 4)
      simp
  apply (holds_reindex_iff e f a b U).mp
  rw [ha, hb]
  exact holds z _ (unitary_reindex e f hU)

/-- Three disjoint opposite pairs suffice when the two unmatched entries on either side agree. -/
theorem holds_of_three_pairs {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a b : ι → ℂ) (e f : Fin 5 ≃ ι)
    (hp : ∀ j : Fin 3, a (e j.castSucc.castSucc) + b (f j.castSucc.castSucc) = 0)
    (hr : a (e 3) = a (e 4) ∨ b (f 3) = b (f 4))
    (U : Matrix ι ι ℂ) (hU : IsUnitary U) : Holds a b U := by
  rcases hr with ha | hb
  · exact holds_left_of_three_pairs a b e f hp ha U hU
  · apply (holds_swap_iff a b hU).mp
    refine holds_left_of_three_pairs b a f e ?_ hb Uᴴ ?_
    · exact fun j => (add_comm _ _).trans (hp j)
    · exact ⟨by simpa using hU.2, by simpa using hU.1⟩

/-- Repeat any one of the three shared marks at every larger order. -/
theorem holds_padded (z : Fin 6 → ℂ) (r : Fin 3) (m : ℕ)
    (U : Matrix (Fin (5 + m)) (Fin (5 + m)) ℂ) (hU : IsUnitary U) :
    Holds (padSpectrumWithValue (left z) (z r.castSucc.castSucc.castSucc) m)
      (padSpectrumWithValue (right z) (-z r.castSucc.castSucc.castSucc) m) U := by
  refine holds_all_shared_value_paddings_five _ _ _ r.castSucc.castSucc r.castSucc.castSucc
    ?_ ?_ (holds z) m U hU
  · fin_cases r <;> rfl
  · fin_cases r <;> rfl

end MOC.ThreeSharedRepeatedFive
