import MOC.ContactCensus
import MOC.TriangleRectangleContact

/-! The six prescribed T15 contacts force two additional contacts at
regular spectra. Indices are the lexicographic permutation labels. -/

namespace MOC

/-- The exact six-contact T15 configuration is impossible when the
matching products are distinct and nonzero. -/
theorem fourT15_not_exact_regular_contacts (a b : Fin 4 → ℂ) (η : ℂ) (hη : η ≠ 0)
    (H : ℝ) (hinj : Function.Injective (matchingProduct a b))
    (hnz : ∀ σ, matchingProduct a b σ ≠ 0) :
    ¬ (∀ i : Fin 24, (η * matchingProduct a b (fourPerm i)).re = H ↔
      i ∈ ({1, 2, 3, 4, 6, 7} : Finset (Fin 24))) := by
  intro hexact
  let r : FourPerm := 1
  let T : Finset FourPerm := {r * Equiv.swap 2 3, r * Equiv.swap 1 2,
    r * Equiv.swap 1 2 * Equiv.swap 2 3, r * Equiv.swap 2 3 * Equiv.swap 1 2,
    r * Equiv.swap 0 1, r * Equiv.swap 0 1 * Equiv.swap 2 3}
  have hset : T = {fourPerm 1, fourPerm 2, fourPerm 3, fourPerm 4, fourPerm 6, fourPerm 7} := by
    decide
  have hT : ∀ σ ∈ T, (η * matchingProduct a b σ).re = H := by
    intro σ hσ
    rw [hset] at hσ
    simp only [Finset.mem_insert, Finset.mem_singleton] at hσ
    rcases hσ with rfl | rfl | rfl | rfl | rfl | rfl
    · exact (hexact 1).mpr (by decide)
    · exact (hexact 2).mpr (by decide)
    · exact (hexact 3).mpr (by decide)
    · exact (hexact 4).mpr (by decide)
    · exact (hexact 6).mpr (by decide)
    · exact (hexact 7).mpr (by decide)
  obtain ⟨hH, hbase, _⟩ := matchingProduct_triangle_rectangle_complete_contacts
    a b r 0 1 2 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    η hη H hinj hnz hT
  have hr : r = fourPerm 0 := by decide
  rw [hr] at hbase
  exact (by decide : (0 : Fin 24) ∉ ({1, 2, 3, 4, 6, 7} : Finset (Fin 24)))
    ((hexact 0).mp (hbase.trans hH.symm))

end MOC
