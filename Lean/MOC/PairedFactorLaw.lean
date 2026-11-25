import MOC.Blocks

/-! A product of independently interpolated opposite-pair factors is a
convex combination of matchings. -/

open BigOperators Finset

namespace MOC

noncomputable section

private def pairPermutation {κ : Type*} [DecidableEq κ] (S : Finset κ) : Equiv.Perm (κ × Bool) where
  toFun p := (p.1, if p.1 ∈ S then p.2 else !p.2)
  invFun p := (p.1, if p.1 ∈ S then p.2 else !p.2)
  left_inv := by rintro ⟨i,b⟩; by_cases h : i ∈ S <;> simp [h]
  right_inv := by rintro ⟨i,b⟩; by_cases h : i ∈ S <;> simp [h]

/-- A probability blend of the two matching factors in each pair can be
multiplied across the pairs, while extra labels use their identity matching. -/
theorem paired_factor_product_mem_matching_hull
    {κ ι : Type*} [Fintype κ] [DecidableEq κ] [Fintype ι] [DecidableEq ι]
    (a b : κ × Bool → ℂ) (c d : ι → ℂ) (t : κ → ℝ)
    (ht0 : ∀ i, 0 ≤ t i) (ht1 : ∀ i, t i ≤ 1) :
    (∏ i, ((t i : ℂ) * ((a (i,true) + b (i,true)) * (a (i,false) + b (i,false))) +
        ((1 - t i : ℝ) : ℂ) * ((a (i,false) + b (i,true)) * (a (i,true) + b (i,false))))) *
        matchingProduct c d (Equiv.refl ι) ∈
      convexHull ℝ (Set.range (matchingProduct (Sum.elim a c) (Sum.elim b d))) := by
  let P (i : κ) := (a (i,true) + b (i,true)) * (a (i,false) + b (i,false))
  let Q (i : κ) := (a (i,false) + b (i,true)) * (a (i,true) + b (i,false))
  let w (S : Finset κ) := (∏ i ∈ S, t i) * ∏ i ∈ Sᶜ, (1 - t i)
  have hmatch (S : Finset κ) : matchingProduct a b (pairPermutation S) =
      (∏ i ∈ S, P i) * ∏ i ∈ Sᶜ, Q i := by
    unfold matchingProduct
    rw [Fintype.prod_prod_type]
    simp_rw [Fintype.prod_bool]
    have he (i : κ) : (a (pairPermutation S (i,true)) + b (i,true)) *
        (a (pairPermutation S (i,false)) + b (i,false)) = if i ∈ S then P i else Q i := by
      by_cases h : i ∈ S <;> simp [pairPermutation, h, P, Q]
    simp_rw [he, Finset.prod_ite]
    have h₁ : (univ.filter fun i : κ => i ∈ S) = S := by ext; simp
    have h₂ : (univ.filter fun i : κ => i ∉ S) = Sᶜ := by ext; simp
    rw [h₁, h₂]
  have hw : ∀ S, 0 ≤ w S := fun S => mul_nonneg
    (Finset.prod_nonneg fun i _ => ht0 i) (Finset.prod_nonneg fun i _ => sub_nonneg.mpr (ht1 i))
  have hs : ∑ S, w S = 1 := by
    have ht (i : κ) : t i + (1 - t i) = 1 := by ring
    simp only [w, ← Fintype.prod_add, ht, Finset.prod_const, one_pow]
  refine mem_convexHull_of_exists_fintype w
    (fun S => matchingProduct (Sum.elim a c) (Sum.elim b d)
      (Equiv.sumCongr (pairPermutation S) (Equiv.refl ι))) hw hs (fun S => ⟨_, rfl⟩) ?_
  change _ = (∏ i, ((t i : ℂ) * P i + ((1 - t i : ℝ) : ℂ) * Q i)) *
    matchingProduct c d (Equiv.refl ι)
  simp_rw [Complex.real_smul, matchingProduct_sum, ← mul_assoc, ← Finset.sum_mul]
  congr 1
  rw [Fintype.prod_add]
  apply Finset.sum_congr rfl
  intro S _
  simp only [w, hmatch, Complex.ofReal_mul, Complex.ofReal_prod, Finset.prod_mul_distrib]
  ring

end

end MOC
