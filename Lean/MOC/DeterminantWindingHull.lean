import MOC.TranspositionWinding

/-! The hull uses closed walks in the transposition graph. A statement about
arbitrary graph homology classes also requires the cycle decomposition. -/

open scoped unitInterval

namespace MOC

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Every point on a transposition edge is an attained determinant. -/
theorem straightSegmentPoint_mem_determinantRange_of_transpositionEdge
    (a b : ι → ℂ) {p q : Equiv.Perm ι} (hpq : TranspositionEdge p q) (t : I) :
    straightSegmentPoint (matchingProduct a b p) (matchingProduct a b q) t ∈ determinantRange a b := by
  obtain ⟨i, j, hij, rfl⟩ := hpq
  obtain ⟨F, _, hF, hside, _, _, _⟩ := transposition_square_in_determinant_range a b p i j i j hij hij
  rw [← hside t]
  exact hF (0, t)

/-- The graph image, together with points of nonzero winding for a closed walk. -/
def determinantWindingHull (a b : ι → ℂ) : Set ℂ :=
  (Set.range (matchingProduct a b) ∪
    {z | ∃ (p q : Equiv.Perm ι) (t : I), TranspositionEdge p q ∧
        z = straightSegmentPoint (matchingProduct a b p) (matchingProduct a b q) t}) ∪
    {z | ∃ (m : ℕ) (p : ℕ → Equiv.Perm ι), p m = p 0 ∧
        (∀ k < m, TranspositionEdge (p k) (p (k + 1))) ∧
        transpositionWindingAngle a b z m p ≠ 0}

/-- The winding hull gives an unconditional inner bound. -/
theorem determinantWindingHull_subset_determinantRange (a b : ι → ℂ) :
    determinantWindingHull a b ⊆ determinantRange a b := by
  rintro z ((⟨p, rfl⟩ | ⟨p, q, t, hpq, rfl⟩) | ⟨m, p, hp, hwalk, hw⟩)
  · exact matchingProduct_mem_determinantRange a b p
  · exact straightSegmentPoint_mem_determinantRange_of_transpositionEdge a b hpq t
  · exact mem_determinantRange_of_transposition_winding_ne_zero a b z m p hp hwalk hw

/-- The conjecture supplies the other inclusion in the winding enclosure. -/
theorem winding_enclosure_of_conjecture (h : Conjecture ι) (a b : ι → ℂ) :
    determinantWindingHull a b ⊆ determinantRange a b ∧
      determinantRange a b ⊆ convexHull ℝ (Set.range (matchingProduct a b)) := by
  refine ⟨determinantWindingHull_subset_determinantRange a b, ?_⟩
  rintro z ⟨U, hU, rfl⟩
  exact h a b U hU

end

end MOC
