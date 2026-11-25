import MOC.Core
import MOC.DuplicatedAssignment

/-! A matching product on two copies of each label factors into two
matching products on the original labels. -/

open BigOperators

namespace MOC

private def doubledSlots (ι : Type*) : (ι ⊕ ι) ≃ ι × Bool where
  toFun
    | .inl j => (j, false)
    | .inr j => (j, true)
  invFun
    | (j, false) => .inl j
    | (j, true) => .inr j
  left_inv := by
    intro x
    cases x <;> rfl
  right_inv := by
    rintro ⟨j, b⟩
    cases b <;> rfl

/-- Every matching product after duplication of all labels is a product
of two matching products on the original labels. -/
theorem doubled_matching_factorization {ι : Type*} [Fintype ι] (a b : ι → ℂ)
    (τ : Equiv.Perm (ι ⊕ ι)) :
    ∃ p q : Equiv.Perm ι,
      matchingProduct (a ∘ Sum.elim id id) (b ∘ Sum.elim id id) τ =
        matchingProduct a b p * matchingProduct a b q := by
  let e := doubledSlots ι
  let s : Equiv.Perm (ι × Bool) := (e.symm.trans τ).trans e
  have he (x : ι ⊕ ι) : (e x).1 = Sum.elim id id x := by cases x <;> rfl
  have hs (x : ι ⊕ ι) : s (e x) = e (τ x) := by simp [s]
  obtain ⟨p, q, hpq⟩ := two_slot_assignments s (fun k j => a k + b j)
  refine ⟨p, q, ?_⟩
  calc
    matchingProduct (a ∘ Sum.elim id id) (b ∘ Sum.elim id id) τ =
        ∏ x : ι × Bool, (a (s x).1 + b x.1) := by
      unfold matchingProduct
      apply Fintype.prod_equiv e
      intro x
      rw [hs, he, he]
      rfl
    _ = matchingProduct a b p * matchingProduct a b q := hpq

end MOC
