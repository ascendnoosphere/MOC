import MOC.TwoFreeEntries

/-! With real fixed entries, conjugation reduces the four corner tests to two. -/

open BigOperators Matrix
open scoped ComplexConjugate

namespace MOC

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem weightedMatchingValue_conj_both (a b : ι → ℂ) (w : Equiv.Perm ι → ℝ) :
    weightedMatchingValue (fun k => conj (a k)) (fun k => conj (b k)) w =
      conj (weightedMatchingValue a b w) := by
  simp only [weightedMatchingValue, matchingProduct, map_sum, map_prod, map_mul, map_add,
    Complex.conj_ofReal]

private theorem weight_agreement_conj_both (a b : ι → ℂ) (U : Matrix ι ι ℂ)
    (hU : IsUnitary U) (w : Equiv.Perm ι → ℝ)
    (h : weightedMatchingValue a b w = determinantValue a b U) :
    weightedMatchingValue (fun k => conj (a k)) (fun k => conj (b k)) w =
      determinantValue (fun k => conj (a k)) (fun k => conj (b k)) U := by
  have hr (c d : ι → ℂ) :
      weightedMatchingValue c d (realSignedWeight U) = determinantValue c d U :=
    real_signed_determinant c d U hU
  rw [← hr, weightedMatchingValue_conj_both, weightedMatchingValue_conj_both, hr, h]

private theorem conj_update_real_anchor (a : ι → ℝ) (i : ι) (z : ℂ) :
    (fun k => conj (Function.update (fun l => (a l : ℂ)) i z k)) =
      Function.update (fun l => (a l : ℂ)) i (conj z) := by
  funext k
  by_cases hk : k = i
  · subst k
    simp
  · simp [Function.update_of_ne hk]

private theorem ne_conj_of_nonreal {z : ℂ} (hz : z.im ≠ 0) : z ≠ conj z := by
  intro he
  have him := congrArg Complex.im he
  rw [Complex.conj_im] at him
  exact hz (by linarith)

/-- Fix real anchors on both sides and choose two nonreal values. For one free
entry on each side, it suffices to test the two pairs (s,u) and (s,conj u).
The same real weights must pass both tests. -/
theorem weightedMatchingValue_eq_iff_two_conjugate_tests (a b : ι → ℝ)
    (U : Matrix ι ι ℂ) (hU : IsUnitary U) (w : Equiv.Perm ι → ℝ) (i j : ι)
    {s u : ℂ} (hs : s.im ≠ 0) (hu : u.im ≠ 0) :
    let A (z : ℂ) := Function.update (fun k => (a k : ℂ)) i z
    let B (z : ℂ) := Function.update (fun k => (b k : ℂ)) j z
    (∀ x y : ℂ, weightedMatchingValue (A x) (B y) w = determinantValue (A x) (B y) U) ↔
    ∀ y ∈ ({u, conj u} : Set ℂ),
      weightedMatchingValue (A s) (B y) w = determinantValue (A s) (B y) U := by
  dsimp only
  let A (z : ℂ) := Function.update (fun k => (a k : ℂ)) i z
  let B (z : ℂ) := Function.update (fun k => (b k : ℂ)) j z
  let Good (x y : ℂ) := weightedMatchingValue (A x) (B y) w = determinantValue (A x) (B y) U
  change (∀ x y, Good x y) ↔ ∀ y ∈ ({u, conj u} : Set ℂ), Good s y
  constructor
  · exact fun h y _ => h s y
  · intro h
    have hc (x y : ℂ) (hxy : Good x y) : Good (conj x) (conj y) := by
      simpa only [Good, A, B, conj_update_real_anchor] using
        weight_agreement_conj_both (A x) (B y) U hU w hxy
    apply (weightedMatchingValue_eq_iff_four_corners _ _ U hU w i j
      (ne_conj_of_nonreal hs) (ne_conj_of_nonreal hu)).mpr
    intro x hx y hy
    rcases Set.mem_insert_iff.mp hx with rfl | hx
    · exact h y hy
    · have hxs : x = conj s := Set.mem_singleton_iff.mp hx
      subst x
      have hy' : conj y ∈ ({u, conj u} : Set ℂ) := by
        rcases Set.mem_insert_iff.mp hy with rfl | hy
        · simp
        · have hyu : y = conj u := Set.mem_singleton_iff.mp hy
          rw [hyu]
          simp
      simpa [Good, A, B] using hc s (conj y) (h _ hy')

end

end MOC
