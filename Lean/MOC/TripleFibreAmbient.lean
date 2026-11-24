import MOC.TripleFibreContact

/-! Restrict to a fibre with all assignments but three fixed. The complement
contributes one common factor; no ambient permutation list is required. -/

open BigOperators

namespace MOC
noncomputable section

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- Vary the three selected assignments, retaining the complete complementary
matching encoded by the two coordinate equivalences. -/
def tripleFibrePerm (eRow eCol : Fin 3 ⊕ κ ≃ ι) (σ : Equiv.Perm (Fin 3)) : Equiv.Perm ι :=
  eCol.symm.trans ((Equiv.sumCongr σ (Equiv.refl κ)).trans eRow)

/-- The outside factors of all matching values in this fibre are identical. -/
theorem matchingProduct_tripleFibrePerm (a b : ι → ℂ) (eRow eCol : Fin 3 ⊕ κ ≃ ι)
    (σ : Equiv.Perm (Fin 3)) :
    matchingProduct a b (tripleFibrePerm eRow eCol σ) =
      matchingProduct (fun i => a (eRow (.inl i))) (fun j => b (eCol (.inl j))) σ *
        ∏ k : κ, (a (eRow (.inr k)) + b (eCol (.inr k))) := by
  unfold matchingProduct
  rw [← Equiv.prod_comp eCol (fun k => a (tripleFibrePerm eRow eCol σ k) + b k),
    Fintype.prod_sum_type]
  simp [tripleFibrePerm]

/-- For any finite order and any fixed assignment of all but three columns,
the fibre contains at most four active matchings at nonzero support height
if both spectra are simple. In order five the complement has two labels. -/
theorem card_ambient_tripleFibre_contacts_le_four (a b : ι → ℂ)
    (ha : Function.Injective a) (hb : Function.Injective b) (eRow eCol : Fin 3 ⊕ κ ≃ ι)
    (η : ℂ) (H : ℝ) (hH : H ≠ 0)
    (hs : ∀ τ : Equiv.Perm ι, (η * matchingProduct a b τ).re ≤ H) :
    (Finset.univ.filter (fun σ : Equiv.Perm (Fin 3) =>
      (η * matchingProduct a b (tripleFibrePerm eRow eCol σ)).re = H)).card ≤ 4 := by
  classical
  let A (i : Fin 3) := a (eRow (.inl i))
  let B (j : Fin 3) := b (eCol (.inl j))
  let d : ℂ := η * ∏ k : κ, (a (eRow (.inr k)) + b (eCol (.inr k)))
  have he (σ : Equiv.Perm (Fin 3)) :
      η * matchingProduct a b (tripleFibrePerm eRow eCol σ) = d * matchingProduct A B σ := by
    rw [matchingProduct_tripleFibrePerm]
    change η * (matchingProduct A B σ * _) = (η * _) * matchingProduct A B σ
    ring
  simp only [he]
  apply card_triangle_fibre_contacts_le_four A B
    (ha.comp (eRow.injective.comp Sum.inl_injective))
    (hb.comp (eCol.injective.comp Sum.inl_injective)) d H hH
  intro σ
  rw [← he]
  exact hs _

end
end MOC
