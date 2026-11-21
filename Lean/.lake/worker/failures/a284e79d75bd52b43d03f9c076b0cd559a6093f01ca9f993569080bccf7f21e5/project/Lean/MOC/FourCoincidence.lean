import MOC.TwoValues

/-! Zheng's opposite-eigenvalue case in order four. The involution
exchanges the two assignments that are disjoint from the zero label.
After this exchange, the relevant signed masses are singleton marginals. -/

open BigOperators Matrix Finset

namespace MOC

noncomputable section

private abbrev Perm4 := Equiv.Perm (Fin 4)

private def anchorColumns (σ : Perm4) : Perm4 :=
  Equiv.swap 1 (σ.symm 0)

private def anchoredTwist (σ : Perm4) : Perm4 :=
  if σ 0 = 0 then σ else
    σ * anchorColumns σ * Equiv.swap 2 3 * (anchorColumns σ).symm

private theorem anchoredTwist_involutive : Function.Involutive anchoredTwist := by
  decide

private def twistEquiv : Perm4 ≃ Perm4 :=
  ⟨anchoredTwist, anchoredTwist, anchoredTwist_involutive, anchoredTwist_involutive⟩

private theorem anchoredTwist_apply_zero : ∀ σ : Perm4, anchoredTwist σ 0 = σ 0 := by
  decide

private theorem anchoredTwist_zero_image :
    ∀ (σ : Perm4) (j : Fin 4), anchoredTwist σ j = 0 ↔ σ j = 0 := by
  decide

private theorem anchoredTwist_fibre :
    ∀ (σ : Perm4) (i j : Fin 4), i ≠ 0 → j ≠ 0 →
      (σ 0 ≠ 0 ∧ σ j = i ↔
        ({0, j} : Finset (Fin 4)).map (anchoredTwist σ).toEmbedding = ({0, i} : Finset (Fin 4))ᶜ) := by
  decide

private def anchoredProduct (a : Fin 4 → ℂ) : ℂ :=
  ∏ i, if i = 0 then 1 else a i

private def anchoredExcept (a : Fin 4 → ℂ) (k : Fin 4) : ℂ :=
  ∏ i, if i = 0 ∨ i = k then 1 else a i

private def twistCoefficient (a b : Fin 4 → ℂ) (j i : Fin 4) : ℂ :=
  if j = 0 then anchoredProduct b * a i else
    if i = 0 then anchoredProduct a * b j else anchoredExcept a i * anchoredExcept b j

private theorem anchoredProduct_reindex (a : Fin 4 → ℂ) (e : Perm4) (k : Fin 4)
    (he : e k = 0) :
    anchoredProduct a = ∏ j, if j = k then 1 else a (e j) := by
  unfold anchoredProduct
  rw [← Equiv.prod_comp e (fun j => if j = 0 then (1 : ℂ) else a j)]
  simp [← he, e.injective.eq_iff]

private theorem anchoredExcept_reindex (a : Fin 4 → ℂ) (e : Perm4) (k l : Fin 4)
    (he : e k = 0) :
    anchoredExcept a (e l) = ∏ j, if j = k ∨ j = l then 1 else a (e j) := by
  unfold anchoredExcept
  rw [← Equiv.prod_comp e (fun j => if j = 0 ∨ j = e l then (1 : ℂ) else a j)]
  simp [← he, e.injective.eq_iff]

private theorem matching_twist_expansion (a b : Fin 4 → ℂ) (ha : a 0 = 0) (hb : b 0 = 0)
    (σ : Perm4) (hσ : σ 0 ≠ 0) :
    matchingProduct a b (anchoredTwist σ) = ∑ j, twistCoefficient a b j (σ j) := by
  let e := anchorColumns σ
  let f := σ * e
  have hr : σ.symm 0 ≠ 0 := by
    intro h
    exact hσ (by rw [← h, Equiv.apply_symm_apply])
  have he₀ : e 0 = 0 := by
    simp [e, anchorColumns, Equiv.swap_apply_def, hr.symm]
  have he₁ : e 1 = σ.symm 0 := Equiv.swap_apply_left _ _
  have hf₁ : f 1 = 0 := by
    simp only [f, Equiv.Perm.mul_apply, he₁, Equiv.apply_symm_apply]
  have he₂ : e 2 ≠ 0 := fun h => (by decide : (2 : Fin 4) ≠ 0) (e.injective (h.trans he₀.symm))
  have he₃ : e 3 ≠ 0 := fun h => (by decide : (3 : Fin 4) ≠ 0) (e.injective (h.trans he₀.symm))
  have he₁' : e 1 ≠ 0 := he₁ ▸ hr
  have hf₂ : f 2 ≠ 0 := fun h => (by decide : (2 : Fin 4) ≠ 1) (f.injective (h.trans hf₁.symm))
  have hf₃ : f 3 ≠ 0 := fun h => (by decide : (3 : Fin 4) ≠ 1) (f.injective (h.trans hf₁.symm))
  have htwist (j : Fin 4) :
      anchoredTwist σ (e j) = f (Equiv.swap 2 3 j) := by
    simp only [anchoredTwist, hσ, if_false, Equiv.Perm.mul_apply, f]
    exact congrArg (fun i => σ (e (Equiv.swap 2 3 i))) (e.symm_apply_apply j)
  have hL : matchingProduct a b (anchoredTwist σ) =
      a (f 0) * b (e 1) * (a (f 3) + b (e 2)) * (a (f 2) + b (e 3)) := by
    unfold matchingProduct
    rw [← Equiv.prod_comp e (fun j => a (anchoredTwist σ j) + b j), Fin.prod_univ_four]
    simp only [htwist, show Equiv.swap (2 : Fin 4) 3 0 = 0 by decide,
      show Equiv.swap (2 : Fin 4) 3 1 = 1 by decide, Equiv.swap_apply_left,
      Equiv.swap_apply_right, hf₁, he₀, ha, hb, add_zero, zero_add]
  rw [hL, ← Equiv.sum_comp e (fun j => twistCoefficient a b j (σ j)), Fin.sum_univ_four]
  change _ = twistCoefficient a b (e 0) (f 0) + twistCoefficient a b (e 1) (f 1) +
    twistCoefficient a b (e 2) (f 2) + twistCoefficient a b (e 3) (f 3)
  simp only [twistCoefficient, he₀, if_pos rfl, he₁', he₂, he₃, if_false, hf₁, hf₂, hf₃]
  rw [anchoredProduct_reindex a f 1 hf₁, anchoredProduct_reindex b e 0 he₀,
    anchoredExcept_reindex a f 1 2 hf₁, anchoredExcept_reindex a f 1 3 hf₁,
    anchoredExcept_reindex b e 0 2 he₀, anchoredExcept_reindex b e 0 3 he₀]
  simp only [Fin.prod_univ_four]
  norm_num [Fin.ext_iff]
  ring

end

end MOC
