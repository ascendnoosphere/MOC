import MOC.FixedMassGroupedSupport

/-! Exact elimination of two unequal partner labels from the grouped
one-entry coefficient conditions. This is a coordinate reduction of
feasibility, not a fixed-mass certificate. -/

open scoped BigOperators

namespace MOC

/-- Solve the two complex moment equations by eliminating the two
coordinates with different spectral values. -/
theorem grouped_moment_two_pivot_elimination
    {I : Type*} [Fintype I] [DecidableEq I] (a w : I → ℂ) (A B : ℂ)
    (p q : I) (h : a p ≠ a q) :
    let R := (Finset.univ.erase p).erase q
    let S := A - ∑ i ∈ R, w i
    let T := B - ∑ i ∈ R, a i * w i
    ((∑ i, w i) = A ∧ (∑ i, a i * w i) = B) ↔
      w p = (T - a q * S) / (a p - a q) ∧
      w q = (a p * S - T) / (a p - a q) := by
  intro R S T
  have hpq : p ≠ q := fun hh => h (congrArg a hh)
  have hq : q ∈ (Finset.univ : Finset I).erase p := by simp [hpq.symm]
  have split (f : I → ℂ) : (∑ i, f i) = (∑ i ∈ R, f i) + f q + f p := by
    rw [Finset.sum_erase_add _ f hq,Finset.sum_erase_add _ f (Finset.mem_univ p)]
  rw [split w,split (fun i => a i * w i)]
  have hn := sub_ne_zero.mpr h
  constructor
  · rintro ⟨hA,hB⟩
    dsimp only [S,T]
    constructor <;> apply (eq_div_iff hn).mpr
    · linear_combination hB - a q * hA
    · linear_combination a p * hA - hB
  · rintro ⟨hp,hq⟩
    have hp' := (eq_div_iff hn).mp hp
    have hq' := (eq_div_iff hn).mp hq
    dsimp only [S,T] at hp' hq'
    constructor <;> apply mul_right_cancel₀ hn
    · linear_combination hp' + hq'
    · linear_combination a p * hp' + a q * hq'

end MOC
