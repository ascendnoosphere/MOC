import MOC.Geometry
import MOC.CommonWeights

/-! A common fractional-linear map of the two signed spectra preserves
the determinant inclusion and every fixed real permutation law. -/

open BigOperators Matrix

namespace MOC

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The map sends z to (αz+β)/(γz+δ). Apply it to the first spectrum
and to the negative of the second spectrum. -/
def fractionalMap (α β γ δ z : ℂ) : ℂ := (α*z+β)/(γ*z+δ)

private theorem fractional_difference (α β γ δ x y : ℂ)
    (hx : γ*x+δ ≠ 0) (hy : γ*y+δ ≠ 0) :
    fractionalMap α β γ δ x - fractionalMap α β γ δ y =
      ((α*δ-β*γ)*(x-y))/((γ*x+δ)*(γ*y+δ)) := by
  unfold fractionalMap
  field_simp [hx, hy] <;> ring

/-- One nonzero factor scales all matching products and the determinant. -/
theorem exists_fractional_factor (a b : ι → ℂ) (U : Matrix ι ι ℂ) (hU : IsUnitary U)
    (α β γ δ : ℂ) (hdet : α*δ-β*γ ≠ 0)
    (ha : ∀ i, γ*a i+δ ≠ 0) (hb : ∀ j, γ*(-b j)+δ ≠ 0) :
    let f := fractionalMap α β γ δ
    ∃ k : ℂ, k ≠ 0 ∧
      (∀ p, matchingProduct (f ∘ a) (fun j => -f (-b j)) p = k * matchingProduct a b p) ∧
      determinantValue (f ∘ a) (fun j => -f (-b j)) U = k * determinantValue a b U := by
  dsimp only
  let k := (α*δ-β*γ)^Fintype.card ι /
    ((∏ i, (γ*a i+δ)) * ∏ j, (γ*(-b j)+δ))
  have hprod (p : Equiv.Perm ι) :
      matchingProduct (fractionalMap α β γ δ ∘ a) (fun j => -fractionalMap α β γ δ (-b j)) p =
        k * matchingProduct a b p := by
    have ht (j : ι) :
        fractionalMap α β γ δ (a (p j)) + -fractionalMap α β γ δ (-b j) =
          (α*δ-β*γ)*(a (p j)+b j) / ((γ*a (p j)+δ)*(γ*(-b j)+δ)) := by
      simpa only [sub_eq_add_neg, neg_neg] using
        fractional_difference α β γ δ (a (p j)) (-b j) (ha _) (hb _)
    unfold matchingProduct
    simp only [Function.comp_apply, ht, Finset.prod_div_distrib, Finset.prod_mul_distrib,
      Finset.prod_const, Finset.card_univ]
    rw [Equiv.prod_comp p (fun i => γ*a i+δ)]
    dsimp only [k]
    ring
  refine ⟨k, div_ne_zero (pow_ne_zero _ hdet)
    (mul_ne_zero (Finset.prod_ne_zero_iff.mpr (fun i _ => ha i))
      (Finset.prod_ne_zero_iff.mpr (fun j _ => hb j))), hprod, ?_⟩
  rw [← signed_determinant _ _ U hU, ← signed_determinant a b U hU, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  rw [hprod]
  ring

/-- A regular fractional-linear change of the signed spectra preserves MOC. -/
theorem holds_fractional_iff (a b : ι → ℂ) (U : Matrix ι ι ℂ) (hU : IsUnitary U)
    (α β γ δ : ℂ) (hd : α*δ-β*γ ≠ 0)
    (ha : ∀ i, γ*a i+δ ≠ 0) (hb : ∀ j, γ*(-b j)+δ ≠ 0) :
    let f := fractionalMap α β γ δ
    Holds (f ∘ a) (fun j => -f (-b j)) U ↔ Holds a b U := by
  obtain ⟨_, hk, hp, hz⟩ := exists_fractional_factor a b U hU α β γ δ hd ha hb
  exact hull_common_factor_iff hk hz hp

/-- The same real weights represent the determinant after a regular change
of the signed spectra. -/
theorem weight_agreement_fractional (a b : ι → ℂ) (U : Matrix ι ι ℂ) (hU : IsUnitary U)
    (w : Equiv.Perm ι → ℝ) (α β γ δ : ℂ) (hd : α*δ-β*γ ≠ 0)
    (ha : ∀ i, γ*a i+δ ≠ 0) (hb : ∀ j, γ*(-b j)+δ ≠ 0)
    (h : weightedMatchingValue a b w = determinantValue a b U) :
    let f := fractionalMap α β γ δ
    weightedMatchingValue (f ∘ a) (fun j => -f (-b j)) w =
      determinantValue (f ∘ a) (fun j => -f (-b j)) U := by
  obtain ⟨k, _, hp, hz⟩ := exists_fractional_factor a b U hU α β γ δ hd ha hb
  dsimp only
  rw [hz, ← h, weightedMatchingValue, weightedMatchingValue, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  rw [hp]
  ring

theorem fractionalMap_injOn (α β γ δ : ℂ) (hd : α*δ-β*γ ≠ 0) :
    Set.InjOn (fractionalMap α β γ δ) {z | γ*z+δ ≠ 0} := by
  intro x hx y hy he
  have hz := fractional_difference α β γ δ x y hx hy
  rw [he, sub_self] at hz
  have hn := (div_eq_zero_iff.mp hz.symm).resolve_right (mul_ne_zero hx hy)
  exact sub_eq_zero.mp ((mul_eq_zero.mp hn).resolve_left hd)

end

end MOC
