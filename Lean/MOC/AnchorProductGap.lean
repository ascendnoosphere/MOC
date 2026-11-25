import MOC.Weights

/-! Anchored singleton agreement makes the penultimate elementary symmetric
coefficient error divisible by both displacements from the anchor zeroes. -/

open BigOperators Finset

namespace MOC

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def exceptPairProduct (a : ι → ℂ) (i j : ι) : ℂ :=
  ∏ k, if k = i ∨ k = j then 1 else a k

private theorem exceptProduct_shift_at_zero (a : ι → ℂ) (i k : ι) (h : k ≠ i)
    (ha : a i = 0) (v : ℂ) :
    exceptProduct (fun j => a j + v) k = v * exceptPairProduct (fun j => a j + v) i k := by
  unfold exceptProduct exceptPairProduct
  rw [← Finset.mul_prod_erase univ (fun j => if j = k then 1 else a j + v) (Finset.mem_univ i),
    ← Finset.mul_prod_erase univ (fun j => if j = i ∨ j = k then 1 else a j + v) (Finset.mem_univ i)]
  simp only [if_neg h.symm, ha, zero_add, eq_self, true_or, if_true, one_mul]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  simp only [(Finset.mem_erase.mp hj).1, false_or]

/-- The penultimate coefficient of the product matching pencil is a sum of
complementary singleton entries. Matching the row and column through the
two zeroes removes every term independent of either shift. -/
theorem penultimate_product_gap_of_anchor_marginals
    (a b : ι → ℂ) (i₀ j₀ : ι) (ha : a i₀ = 0) (hb : b j₀ = 0)
    (μ : Equiv.Perm ι → ℂ) (hrow : ∀ j, marginal μ i₀ j = 0)
    (hcol : ∀ i, marginal μ i j₀ = 0) (v u : ℂ) :
    let A (i : ι) := a i + v
    let B (j : ι) := b j + u
    (∑ σ, μ σ * ∑ j, exceptProduct A (σ j) * exceptProduct B j) =
      (v * u) * ∑ j, ∑ i, marginal μ i j * (exceptPairProduct A i₀ i * exceptPairProduct B j₀ j) := by
  intro A B
  calc
    _ = ∑ j, ∑ i, marginal μ i j * (exceptProduct A i * exceptProduct B j) := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl
        (fun j _ => sum_weighted_evaluation μ j (fun i => exceptProduct A i * exceptProduct B j))
    _ = _ := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : i = i₀
      · subst i
        simp only [hrow, zero_mul, mul_zero]
      by_cases hj : j = j₀
      · subst j
        simp only [hcol, zero_mul, mul_zero]
      have hA : exceptProduct A i = v * exceptPairProduct A i₀ i :=
        exceptProduct_shift_at_zero a i₀ i hi ha v
      have hB : exceptProduct B j = u * exceptPairProduct B j₀ j :=
        exceptProduct_shift_at_zero b j₀ j hj hb u
      rw [hA, hB]
      ring

end

end MOC
