import MOC.BilinearPencil

/-! On a fixed bilinear anchor, agreement on the anchor row and column
marginals leaves just one constant after division by the squared coefficient determinant. -/

open BigOperators Finset

namespace MOC

noncomputable section

private theorem anchor_product_terms (a b : Fin 4 → ℂ) (ha : a 0 = 0) (hb : b 0 = 0)
    (α β γ : ℂ) (σ : Equiv.Perm (Fin 4)) :
    let A := exceptProduct a 0
    let B := exceptProduct b 0
    let x := a (σ 0)
    let y := b (σ.symm 0)
    bilinearMatchingProduct a b α β γ 0 σ - (β * γ) ^ 2 * matchingProduct a b σ =
      β * γ * (B * x * (γ ^ 2 - β * γ + α * γ * ((∑ i, a i) - x)) +
        A * y * (β ^ 2 - β * γ + α * β * ((∑ j, b j) - y)) +
        if σ 0 = 0 then 0 else α ^ 2 * A * B) := by
  dsimp only
  by_cases hσ : σ 0 = 0
  · have hσs : σ.symm 0 = 0 := calc
      _ = σ.symm (σ 0) := congrArg σ.symm hσ.symm
      _ = _ := σ.symm_apply_apply _
    have hp : bilinearMatchingProduct a b α β γ 0 σ = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ 0)
      simp [bilinearKernel, hσ, ha, hb]
    have hq : matchingProduct a b σ = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ 0)
      simp [hσ, ha, hb]
    simp [hp, hq, hσ, hσs, ha, hb]
  · have hσs : σ.symm 0 ≠ 0 := fun h => hσ (calc
      _ = σ (σ.symm 0) := congrArg σ h.symm
      _ = _ := σ.apply_symm_apply _)
    let e := Equiv.swap (1 : Fin 4) (σ.symm 0)
    let f := σ * e
    have he₀ : e 0 = 0 := by
      simp [e, Equiv.swap_apply_def, hσs.symm]
    have he₁ : e 1 = σ.symm 0 := Equiv.swap_apply_left _ _
    have hf₀ : f 0 = σ 0 := by simp only [f, Equiv.Perm.mul_apply, he₀]
    have hf₁ : f 1 = 0 := by simp only [f, Equiv.Perm.mul_apply, he₁, Equiv.apply_symm_apply]
    have h01 : (0 : Fin 4) ≠ 1 := by decide
    have h02 : (0 : Fin 4) ≠ 2 := by decide
    have h03 : (0 : Fin 4) ≠ 3 := by decide
    have h12 : (1 : Fin 4) ≠ 2 := by decide
    have h13 : (1 : Fin 4) ≠ 3 := by decide
    have hA : exceptProduct a 0 = a (f 0) * a (f 2) * a (f 3) := by
      rw [show exceptProduct a 0 = exceptProduct (a ∘ f) 1 by rw [exceptProduct_comp, hf₁]]
      simp only [exceptProduct, Fin.prod_univ_four, Function.comp_apply, h01, h12.symm,
        h13.symm, if_false, eq_self, if_true, mul_one]
    have hB : exceptProduct b 0 = b (e 1) * b (e 2) * b (e 3) := by
      rw [show exceptProduct b 0 = exceptProduct (b ∘ e) 0 by rw [exceptProduct_comp, he₀]]
      simp only [exceptProduct, Fin.prod_univ_four, Function.comp_apply, h01.symm,
        h02.symm, h03.symm, if_false, eq_self, if_true, one_mul]
    have hsA : (∑ i, a i) = a (f 0) + a (f 2) + a (f 3) := by
      rw [← Equiv.sum_comp f a, Fin.sum_univ_four, hf₁, ha, add_zero]
    have hsB : (∑ j, b j) = b (e 1) + b (e 2) + b (e 3) := by
      rw [← Equiv.sum_comp e b, Fin.sum_univ_four, he₀, hb, zero_add]
    unfold bilinearMatchingProduct matchingProduct
    rw [← Equiv.prod_comp e (fun j => bilinearKernel α β γ 0 (a (σ j)) (b j)),
      ← Equiv.prod_comp e (fun j => a (σ j) + b j), Fin.prod_univ_four, Fin.prod_univ_four]
    change bilinearKernel α β γ 0 (a (f 0)) (b (e 0)) *
          bilinearKernel α β γ 0 (a (f 1)) (b (e 1)) *
          bilinearKernel α β γ 0 (a (f 2)) (b (e 2)) *
          bilinearKernel α β γ 0 (a (f 3)) (b (e 3)) -
        (β * γ) ^ 2 * ((a (f 0) + b (e 0)) * (a (f 1) + b (e 1)) *
          (a (f 2) + b (e 2)) * (a (f 3) + b (e 3))) = _
    simp only [hσ, if_false]
    rw [hA, hB, hsA, hsB, ← hf₀, ← he₁]
    simp only [he₀, hf₁, ha, hb, bilinearKernel]
    ring

/-- On the zero-edge hyperplane, any law difference with zero anchor row
and column marginals has a constant normalized determinant error. -/
theorem weighted_bilinear_gap_of_anchor_marginals (a b : Fin 4 → ℂ) (ha : a 0 = 0) (hb : b 0 = 0)
    (μ : Equiv.Perm (Fin 4) → ℂ) (hμ : ∑ σ, μ σ = 0)
    (hrow : ∀ j, marginal μ 0 j = 0) (hcol : ∀ i, marginal μ i 0 = 0) (α β γ : ℂ) :
    (∑ σ, μ σ * bilinearMatchingProduct a b α β γ 0 σ) =
      (β * γ) ^ 2 * ∑ σ, μ σ * matchingProduct a b σ := by
  let A := exceptProduct a 0
  let B := exceptProduct b 0
  let F (i : Fin 4) := B * a i * (γ ^ 2 - β * γ + α * γ * ((∑ k, a k) - a i))
  let G (j : Fin 4) := A * b j * (β ^ 2 - β * γ + α * β * ((∑ k, b k) - b j))
  let C := α ^ 2 * A * B
  have hF : (∑ σ, μ σ * F (σ 0)) = 0 := by
    rw [sum_weighted_evaluation μ 0 F]
    simp only [hcol, zero_mul, Finset.sum_const_zero]
  have hG : (∑ σ, μ σ * G (σ.symm 0)) = 0 := by
    have hsum (σ : Equiv.Perm (Fin 4)) : ∑ j, (if σ j = 0 then μ σ * G j else 0) =
        μ σ * G (σ.symm 0) := by
      simp only [(show ∀ j, σ j = 0 ↔ j = σ.symm 0 from fun j => σ.eq_symm_apply.symm),
        Finset.sum_ite_eq', Finset.mem_univ, if_true]
    calc
      _ = ∑ j, ∑ σ, if σ j = 0 then μ σ * G j else 0 := by
        simp_rw [← hsum]
        rw [Finset.sum_comm]
      _ = ∑ j, marginal μ 0 j * G j := by
        simp only [marginal, Finset.sum_mul, ite_mul, zero_mul]
      _ = _ := by simp only [hrow, zero_mul, Finset.sum_const_zero]
  have hC : (∑ σ, μ σ * (if σ 0 = 0 then 0 else C)) = 0 := calc
    _ = ∑ σ, (μ σ * C - (if σ 0 = 0 then μ σ * C else 0)) := by
      apply Finset.sum_congr rfl
      intro σ _
      split_ifs <;> simp
    _ = _ := by
      have he : (∑ σ, if σ 0 = 0 then μ σ * C else 0) = marginal μ 0 0 * C := by
        simp only [marginal, Finset.sum_mul, ite_mul, zero_mul]
      rw [Finset.sum_sub_distrib, ← Finset.sum_mul, he, hμ, hrow]
      simp
  have hterm (σ : Equiv.Perm (Fin 4)) :
      μ σ * bilinearMatchingProduct a b α β γ 0 σ =
        (β * γ) ^ 2 * (μ σ * matchingProduct a b σ) +
          (β * γ) * (μ σ * F (σ 0) + μ σ * G (σ.symm 0) + μ σ * (if σ 0 = 0 then 0 else C)) := by
    have he := anchor_product_terms a b ha hb α β γ σ
    change _ = (β * γ) * (F (σ 0) + G (σ.symm 0) + if σ 0 = 0 then 0 else C) at he
    linear_combination μ σ * he
  simp only [hterm, Finset.sum_add_distrib, ← Finset.mul_sum, hF, hG, hC, add_zero, mul_zero]

end

end MOC
