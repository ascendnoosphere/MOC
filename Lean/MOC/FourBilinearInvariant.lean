import MOC.BilinearPencil
import MOC.FourAnchorInterpolation

/-! The part of an order-four matching evaluation invisible to singleton
marginals changes by exactly the squared coefficient determinant. -/

open BigOperators Finset

namespace MOC

noncomputable section

private theorem exceptProduct_mul_four (x y : Fin 4 → ℂ) (j : Fin 4) :
    exceptProduct (fun k => x k * y k) j = exceptProduct x j * exceptProduct y j := by
  unfold exceptProduct
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro k _
  by_cases h : k = j <;> simp [h]

/-- A mass-zero law difference with vanishing singleton marginals defines
an order-four bilinear gap equal to its additive gap times `det(H)²`. -/
theorem four_bilinear_gap_of_singleton_marginals (a b : Fin 4 → ℂ)
    (μ : Equiv.Perm (Fin 4) → ℂ) (hμ : ∑ σ, μ σ = 0)
    (hm : ∀ i j, marginal μ i j = 0) (α β γ δ : ℂ) :
    (∑ σ, μ σ * bilinearMatchingProduct a b α β γ δ σ) =
      (α * δ - β * γ) ^ 2 * ∑ σ, μ σ * matchingProduct a b σ := by
  let A (i j : Fin 4) := ∑ σ, μ σ * (a (σ i) * a (σ j))
  have moment (j : Fin 4) (g : Fin 4 → ℂ) : (∑ σ, μ σ * g (σ j)) = 0 := by
    rw [sum_weighted_evaluation μ j g]
    simp only [hm, zero_mul, Finset.sum_const_zero]
  have hpart (e : Equiv.Perm (Fin 4)) : A (e 0) (e 1) = A (e 2) (e 3) := by
    have hσ (σ : Equiv.Perm (Fin 4)) :
        (∑ i, a i) = a (σ (e 0)) + a (σ (e 1)) + a (σ (e 2)) + a (σ (e 3)) := by
      rw [← Equiv.sum_comp (e.trans σ) a, Fin.sum_univ_four]
      rfl
    have hp (σ : Equiv.Perm (Fin 4)) :
        2 * (μ σ * (a (σ (e 0)) * a (σ (e 1)))) -
          2 * (μ σ * (a (σ (e 2)) * a (σ (e 3)))) =
        (∑ i, a i) * (μ σ * a (σ (e 0)) + μ σ * a (σ (e 1)) -
          (μ σ * a (σ (e 2)) + μ σ * a (σ (e 3)))) -
        (μ σ * a (σ (e 0)) ^ 2 + μ σ * a (σ (e 1)) ^ 2 -
          (μ σ * a (σ (e 2)) ^ 2 + μ σ * a (σ (e 3)) ^ 2)) := by
      rw [hσ]
      ring
    have h := Finset.sum_congr rfl (fun σ (_ : σ ∈ Finset.univ) => hp σ)
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
      moment (e 0) a, moment (e 1) a, moment (e 2) a, moment (e 3) a,
      moment (e 0) (fun i => a i ^ 2), moment (e 1) (fun i => a i ^ 2),
      moment (e 2) (fun i => a i ^ 2), moment (e 3) (fun i => a i ^ 2),
      add_zero, sub_zero, mul_zero] at h
    change 2 * A (e 0) (e 1) - 2 * A (e 2) (e 3) = 0 at h
    linear_combination h / 2
  have h₁ : A 0 1 = A 2 3 := hpart 1
  have h₂ : A 0 2 = A 1 3 := hpart (Equiv.swap 1 2)
  have h₃ : A 0 3 = A 1 2 := by
    have h := hpart (Equiv.swap 1 3)
    change A 0 3 = A 2 1 at h
    simpa only [A, mul_comm] using h
  have hAtotal : A 0 1 + A 0 2 + A 0 3 = 0 := by
    have hσ (σ : Equiv.Perm (Fin 4)) :
        ∑ i, a i = a (σ 0) + a (σ 1) + a (σ 2) + a (σ 3) := by
      rw [← Equiv.sum_comp σ a, Fin.sum_univ_four]
    calc
      _ = ∑ σ, μ σ * (a (σ 0) * ((∑ i, a i) - a (σ 0))) := by
        simp only [A, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro σ _
        rw [hσ]
        ring
      _ = _ := moment 0 (fun i => a i * ((∑ i, a i) - a i))
  let S (p q : Fin 4 → ℂ) (i j k l : Fin 4) :=
    (p i * p j) * (q k * q l) + (p k * p l) * (q i * q j)
  have hgap (p q : Fin 4 → ℂ) :
      (∑ σ, μ σ * ∏ j, (a (σ j) * p j + q j)) =
        A 0 1 * S p q 0 1 2 3 + A 0 2 * S p q 0 2 1 3 + A 0 3 * S p q 0 3 1 2 := by
    let x (σ : Equiv.Perm (Fin 4)) (j : Fin 4) := a (σ j) * p j
    have hx (σ : Equiv.Perm (Fin 4)) (j : Fin 4) :
        exceptProduct (x σ) j = exceptProduct a (σ j) * exceptProduct p j := by
      rw [show x σ = fun k => (a ∘ σ) k * p k from rfl, exceptProduct_mul_four, exceptProduct_comp]
    have ht (σ : Equiv.Perm (Fin 4)) :
        (∏ j, (x σ j + q j)) =
          ((∏ j, a j) * ∏ j, p j) + (∏ j, q j) +
          (∑ j, exceptProduct a (σ j) * (exceptProduct p j * q j)) + twoTwoTerm (x σ) q +
          (∑ j, a (σ j) * (p j * exceptProduct q j)) := by
      have he (j : Fin 4) : x σ j * exceptProduct q j = a (σ j) * (p j * exceptProduct q j) := by
        simp only [x, mul_assoc]
      have hprod : (∏ j, x σ j) = (∏ j, a j) * ∏ j, p j := by
        simp only [x, Finset.prod_mul_distrib, Equiv.prod_comp σ a]
      simpa only [one_mul, one_pow, hx, mul_assoc, he, hprod] using four_scaled_product (x σ) q 1
    have hs₃ (j : Fin 4) :
        (∑ σ, μ σ * (exceptProduct a (σ j) * (exceptProduct p j * q j))) = 0 :=
      moment j (fun i => exceptProduct a i * (exceptProduct p j * q j))
    have hs₁ (j : Fin 4) : (∑ σ, μ σ * (a (σ j) * (p j * exceptProduct q j))) = 0 :=
      moment j (fun i => a i * (p j * exceptProduct q j))
    have hpair (i j k l : Fin 4) :
        (∑ σ, μ σ * (x σ i * x σ j * q k * q l)) = A i j * (p i * p j * q k * q l) := by
      dsimp only [A]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro σ _
      simp only [x]
      ring
    change (∑ σ, μ σ * ∏ j, (x σ j + q j)) = _
    simp_rw [ht, mul_add]
    simp only [Finset.sum_add_distrib, ← Finset.sum_mul, hμ, zero_mul, zero_add]
    have hzero₃ : (∑ σ, μ σ * ∑ j, exceptProduct a (σ j) * (exceptProduct p j * q j)) = 0 := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      simp only [hs₃, Finset.sum_const_zero]
    have hzero₁ : (∑ σ, μ σ * ∑ j, a (σ j) * (p j * exceptProduct q j)) = 0 := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      simp only [hs₁, Finset.sum_const_zero]
    simp only [hzero₃, hzero₁, zero_add, add_zero, twoTwoTerm, mul_add, Finset.sum_add_distrib, hpair]
    rw [← h₁, ← h₂, ← h₃]
    dsimp only [S]
    ring
  let p (j : Fin 4) := α * b j + β
  let q (j : Fin 4) := γ * b j + δ
  let d := α * δ - β * γ
  let c := S p q 0 1 2 3 - d ^ 2 * S (fun _ => 1) b 0 1 2 3
  have hS₁ : S p q 0 1 2 3 = d ^ 2 * S (fun _ => 1) b 0 1 2 3 + c := by
    dsimp only [c]
    ring
  have hS₂ : S p q 0 2 1 3 = d ^ 2 * S (fun _ => 1) b 0 2 1 3 + c := by
    dsimp only [S, p, q, d, c]
    ring
  have hS₃ : S p q 0 3 1 2 = d ^ 2 * S (fun _ => 1) b 0 3 1 2 + c := by
    dsimp only [S, p, q, d, c]
    ring
  have hbilinear (σ : Equiv.Perm (Fin 4)) : bilinearMatchingProduct a b α β γ δ σ =
      ∏ j, (a (σ j) * p j + q j) := by
    unfold bilinearMatchingProduct
    apply Finset.prod_congr rfl
    intro j _
    dsimp only [p, q, bilinearKernel]
    ring
  have hadd : (∑ σ, μ σ * matchingProduct a b σ) =
      A 0 1 * S (fun _ => 1) b 0 1 2 3 + A 0 2 * S (fun _ => 1) b 0 2 1 3 +
        A 0 3 * S (fun _ => 1) b 0 3 1 2 := by
    simpa only [mul_one, matchingProduct] using hgap (fun _ => 1) b
  simp only [hbilinear, hgap p q, hadd, hS₁, hS₂, hS₃]
  change _ = d ^ 2 * _
  linear_combination c * hAtotal

end

end MOC
