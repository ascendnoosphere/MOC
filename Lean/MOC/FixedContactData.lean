import MOC.ContactIteration
import MOC.GeneralContactReduction

open Matrix

namespace MOC

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
/-- The phase, pivot, old complex differences, and complex determinant gap
travel with the same mixer through repeated contact transfer. -/
structure StrictMatchingSupport.PreservesContactData {U : Matrix ι ι ℂ}
    (w v : StrictMatchingSupport U) : Prop where
  phase : v.η = w.η
  anchor : v.pivot = w.pivot
  contacts : w.contacts ⊆ v.contacts
  differences : ∀ q ∈ w.contacts,
    matchingProduct v.a v.b v.pivot - matchingProduct v.a v.b q =
      matchingProduct w.a w.b w.pivot - matchingProduct w.a w.b q
  gap : matchingProfileDetGap U v.η v.pivot (matchingProduct v.a v.b) =
    matchingProfileDetGap U w.η w.pivot (matchingProduct w.a w.b)

theorem StrictMatchingSupport.PreservesContactData.refl {U : Matrix ι ι ℂ}
    (w : StrictMatchingSupport U) : w.PreservesContactData w :=
  ⟨rfl, rfl, fun _ h => h, fun _ _ => rfl, rfl⟩

theorem StrictMatchingSupport.PreservesContactData.trans {U : Matrix ι ι ℂ}
    {u v w : StrictMatchingSupport U} (h : u.PreservesContactData v)
    (k : v.PreservesContactData w) : u.PreservesContactData w :=
  ⟨k.phase.trans h.phase, k.anchor.trans h.anchor, fun _ hq => k.contacts (h.contacts hq),
    fun q hq => (k.differences q (h.contacts hq)).trans (h.differences q hq),
    k.gap.trans h.gap⟩

end MOC
