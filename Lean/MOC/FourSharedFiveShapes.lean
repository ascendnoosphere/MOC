import MOC.FourSharedFive
import MOC.SpectralZeroPadding

/-! Independently order the spectra. Any one of the four shared marks can be repeated. -/

open Matrix

namespace MOC.FourSharedFive

/-- Four pairs of entries have opposite values. Both label maps may be chosen independently. -/
theorem holds_of_four_pairs {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a b : ι → ℂ) (e f : Fin 5 ≃ ι)
    (hp : ∀ j : Fin 4, a (e j.castSucc) + b (f j.castSucc) = 0)
    (U : Matrix ι ι ℂ) (hU : IsUnitary U) : Holds a b U := by
  let z : Fin 6 → ℂ := ![a (e 0), a (e 1), a (e 2), a (e 3), a (e 4), -b (f 4)]
  have ha : a ∘ e = left z := by
    funext i
    fin_cases i <;> rfl
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
    · change b (f 3) = -a (e 3)
      have h : a (e 3) + b (f 3) = 0 := hp 3
      linear_combination h
    · change b (f 4) = - -b (f 4)
      simp
  apply (holds_reindex_iff e f a b U).mp
  rw [ha, hb]
  exact holds z _ (unitary_reindex e f hU)

/-- Repeat one chosen shared mark on both signed lists any number of times. -/
theorem holds_padded (z : Fin 6 → ℂ) (r : Fin 4) (m : ℕ)
    (U : Matrix (Fin (5 + m)) (Fin (5 + m)) ℂ) (hU : IsUnitary U) :
    Holds (padSpectrumWithValue (left z) (z r.castSucc.castSucc) m)
      (padSpectrumWithValue (right z) (-z r.castSucc.castSucc) m) U := by
  refine holds_all_shared_value_paddings_five _ _ _ r.castSucc r.castSucc ?_ ?_
    (holds z) m U hU
  · fin_cases r <;> rfl
  · fin_cases r <;> rfl

end MOC.FourSharedFive
