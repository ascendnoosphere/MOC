import MOC.GroupedPencil
import MOC.SupportedCompressionReduction
import Mathlib.Topology.Algebra.Module.Cardinality

/-! If the free column meets at most two first-summand spectral values,
the smaller-order conjecture gives a common law for the entire pencil. -/

open Matrix

namespace MOC

noncomputable section

private theorem isClosed_free_partner_holds
    {I : Type*} [Fintype I] [DecidableEq I]
    (a b : I → ℂ) (U : Matrix I I ℂ) (hU : IsUnitary U) (j : I) :
    IsClosed {v : ℂ | Holds a (Function.update b j v) U} := by
  let D (z : ℂ) := determinantValue a (Function.update b j z) U
  let P (q : Equiv.Perm I) (z : ℂ) := matchingProduct a (Function.update b j z) q
  have hD : Continuous D := by
    rw [show D = (fun z : ℂ => D 0 + (D 1 - D 0) * z) from
      funext (determinant_update_interp a b j U hU)]
    exact continuous_const.add (continuous_const.mul continuous_id)
  have hP (q : Equiv.Perm I) : Continuous (P q) := by
    rw [show P q = (fun z : ℂ => P q 0 + (P q 1 - P q 0) * z) from
      funext (matching_update_interp a b j q)]
    exact continuous_const.add (continuous_const.mul continuous_id)
  rw [show {z : ℂ | Holds a (Function.update b j z) U} =
    ⋂ η : ℂ, ⋃ q : Equiv.Perm I, {z : ℂ | (η * D z).re ≤ (η * P q z).re} from by
      ext z
      simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_iUnion]
      exact holds_iff_directional a (Function.update b j z) U]
  exact isClosed_iInter fun η => isClosed_iUnion_of_finite fun q =>
    isClosed_le (Complex.continuous_re.comp (continuous_const.mul hD))
      (Complex.continuous_re.comp (continuous_const.mul (hP q)))

/-- A column can have any number of nonzero entries. If the corresponding
first-summand labels take at most two values, every value of the free partner
label reduces to the smaller-order conjecture. -/
theorem holds_free_partner_of_two_supported_values {n : ℕ}
    (hSmall : Conjecture (Fin n)) (a b : Fin (n + 1) → ℂ)
    (U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (hU : IsUnitary U)
    (j : Fin (n + 1)) (x y : ℂ) (hvalues : ∀ i, U i j ≠ 0 → a i = x ∨ a i = y) :
    ∀ z : ℂ, Holds a (Function.update b j z) U := by
  classical
  let bad : Set ℂ := Set.range (fun i => -a i) ∪ Set.range (fun i : {i // i ≠ j} => b i)
  have hbad : bad.Finite := (Set.finite_range _).union (Set.finite_range _)
  have hdense : Dense badᶜ := hbad.countable.dense_compl ℂ
  have hregular : badᶜ ⊆ {z : ℂ | Holds a (Function.update b j z) U} := by
    intro z hz
    let B := Function.update b j z
    have hBj : B j = z := Function.update_self j z b
    have hp (k : Fin (n + 1)) (hk : k ≠ j) : B k - B j ≠ 0 := by
      rw [hBj, show B k = b k from Function.update_of_ne hk z b, sub_ne_zero]
      intro he
      exact hz (Or.inr ⟨⟨k, hk⟩, he⟩)
    have hab (i : Fin (n + 1)) : a i + B j ≠ 0 := by
      rw [hBj]
      intro he
      exact hz (Or.inl ⟨i, by linear_combination -he⟩)
    have hU' : IsUnitary Uᴴ :=
      ⟨by simpa only [Matrix.conjTranspose_conjTranspose] using hU.2,
        by simpa only [Matrix.conjTranspose_conjTranspose] using hU.1⟩
    let β (i : Fin (n + 1)) := (a i + B j)⁻¹
    let c := (x + B j)⁻¹
    let d := (y + B j)⁻¹ - c
    let t (i : Fin (n + 1)) : ℝ := if a i = x then 0 else 1
    have hline (i : Fin (n + 1)) (hi : Uᴴ j i ≠ 0) :
        β i = c + d * (t i : ℂ) := by
      have hne : U i j ≠ 0 := by
        intro he
        exact hi (by simp only [Matrix.conjTranspose_apply, he, star_zero])
      by_cases hx : a i = x
      · simp only [β, c, t, hx, if_true, Complex.ofReal_zero, mul_zero, add_zero]
      · have hy : a i = y := (hvalues i hne).resolve_left hx
        simp only [β, d, t, hx, if_false, Complex.ofReal_one, mul_one]
        rw [hy]
        ring
    have hnormal : IsStarNormal (poleCompression B a Uᴴ j) :=
      normalCompression_of_spectral_line_on_support β Uᴴ hU' j c d t hline
    exact (holds_swap_iff a B hU).mp
      (holds_of_normal_poleCompression hSmall B a Uᴴ hU' j hp hab hnormal)
  intro z
  exact closure_minimal hregular (isClosed_free_partner_holds a b U hU j) (hdense z)

/-- With a column that meets at most two spectral values, the same convex
weights work for every free partner entry. -/
theorem one_free_partner_law_of_two_supported_values {n : ℕ}
    (hSmall : Conjecture (Fin n)) (a b : Fin (n + 1) → ℂ)
    (U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (hU : IsUnitary U)
    (j : Fin (n + 1)) (x y : ℂ) (hvalues : ∀ i, U i j ≠ 0 → a i = x ∨ a i = y) :
    ∃ k : ℕ, k ≤ 5 ∧ ∃ (p : Fin k → Equiv.Perm (Fin (n + 1))) (w : Fin k → ℝ),
      (∀ i, 0 ≤ w i) ∧ (∑ i, w i) = 1 ∧ ∀ z : ℂ,
        (∑ i, (w i : ℂ) * matchingProduct a (Function.update b j z) (p i)) =
          determinantValue a (Function.update b j z) U :=
  (one_free_partner_entry_iff_common_law a b j U hU).mp
    (holds_free_partner_of_two_supported_values hSmall a b U hU j x y hvalues)

end
end MOC
