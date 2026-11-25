import MOC.Weights

/-! One value at a zero spectral edge determines the balanced mixed term
in order four because the two remaining mixed terms have singleton marginals. -/

open BigOperators Matrix

namespace MOC

noncomputable section

def twoTwoTerm (x y : Fin 4 → ℂ) : ℂ :=
  x 0 * x 1 * y 2 * y 3 + x 0 * x 2 * y 1 * y 3 + x 0 * x 3 * y 1 * y 2 +
    x 1 * x 2 * y 0 * y 3 + x 1 * x 3 * y 0 * y 2 + x 2 * x 3 * y 0 * y 1

theorem four_scaled_product (x y : Fin 4 → ℂ) (t : ℂ) :
    (∏ j, (t * x j + y j)) =
      t ^ 4 * (∏ j, x j) + (∏ j, y j) + t ^ 3 * (∑ j, exceptProduct x j * y j) +
        t ^ 2 * twoTwoTerm x y + t * (∑ j, x j * exceptProduct y j) := by
  have h01 : (0 : Fin 4) ≠ 1 := by decide
  have h02 : (0 : Fin 4) ≠ 2 := by decide
  have h03 : (0 : Fin 4) ≠ 3 := by decide
  have h12 : (1 : Fin 4) ≠ 2 := by decide
  have h13 : (1 : Fin 4) ≠ 3 := by decide
  have h23 : (2 : Fin 4) ≠ 3 := by decide
  simp only [Fin.prod_univ_four, Fin.sum_univ_four, exceptProduct, twoTwoTerm,
    h01, h02, h03, h12, h13, h23, h01.symm, h02.symm, h03.symm, h12.symm, h13.symm, h23.symm,
    eq_self, if_false, if_true, one_mul, mul_one]
  ring

/-- If a signed difference of weights has total mass zero and agrees at the
scale that creates one zero spectral edge, its unscaled difference is an
explicit combination of the two singleton coefficient differences. -/
theorem four_matching_gap_from_anchored_scale (μ : Equiv.Perm (Fin 4) → ℂ)
    (hmass : ∑ σ, μ σ = 0) (a b : Fin 4 → ℂ) (t : ℂ) (ht : t ≠ 0)
    (hanchor : ∑ σ, μ σ * matchingProduct (fun i => t * a i) b σ = 0) :
    (∑ σ, μ σ * matchingProduct a b σ) =
      (1 - t) * (∑ j, ∑ i, marginal μ i j * (exceptProduct a i * b j)) +
        (1 - t⁻¹) * (∑ j, ∑ i, marginal μ i j * (a i * exceptProduct b j)) := by
  classical
  let c₃₁ (σ : Equiv.Perm (Fin 4)) := ∑ j, exceptProduct a (σ j) * b j
  let c₂₂ (σ : Equiv.Perm (Fin 4)) := twoTwoTerm (a ∘ σ) b
  let c₁₃ (σ : Equiv.Perm (Fin 4)) := ∑ j, a (σ j) * exceptProduct b j
  let C₃₁ := ∑ j, ∑ i, marginal μ i j * (exceptProduct a i * b j)
  let C₂₂ := ∑ σ, μ σ * c₂₂ σ
  let C₁₃ := ∑ j, ∑ i, marginal μ i j * (a i * exceptProduct b j)
  have h₃₁ : (∑ σ, μ σ * c₃₁ σ) = C₃₁ := by
    simp only [c₃₁, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun j _ => sum_weighted_evaluation μ j (fun i => exceptProduct a i * b j))
  have h₁₃ : (∑ σ, μ σ * c₁₃ σ) = C₁₃ := by
    simp only [c₁₃, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun j _ => sum_weighted_evaluation μ j (fun i => a i * exceptProduct b j))
  have hp (z : ℂ) (σ : Equiv.Perm (Fin 4)) :
      matchingProduct (fun i => z * a i) b σ =
        z ^ 4 * (∏ j, a j) + (∏ j, b j) + z ^ 3 * c₃₁ σ + z ^ 2 * c₂₂ σ + z * c₁₃ σ := by
    simpa only [matchingProduct, c₃₁, c₂₂, c₁₃, Function.comp_apply, Equiv.prod_comp σ a,
      exceptProduct_comp] using four_scaled_product (a ∘ σ) b z
  have hsum (z : ℂ) : (∑ σ, μ σ * matchingProduct (fun i => z * a i) b σ) =
      z ^ 3 * C₃₁ + z ^ 2 * C₂₂ + z * C₁₃ := by
    have hterm (σ : Equiv.Perm (Fin 4)) : μ σ * matchingProduct (fun i => z * a i) b σ =
        (z ^ 4 * (∏ j, a j) + ∏ j, b j) * μ σ + z ^ 3 * (μ σ * c₃₁ σ) +
          z ^ 2 * (μ σ * c₂₂ σ) + z * (μ σ * c₁₃ σ) := by
      rw [hp]
      ring
    simp only [hterm, Finset.sum_add_distrib, ← Finset.mul_sum, hmass, h₃₁, h₁₃, mul_zero,
      zero_add, C₂₂]
  have htzero : t ^ 3 * C₃₁ + t ^ 2 * C₂₂ + t * C₁₃ = 0 := (hsum t).symm.trans hanchor
  have hfactor : t ^ 2 * (t * C₃₁ + C₂₂ + t⁻¹ * C₁₃) = 0 := calc
    _ = t ^ 3 * C₃₁ + t ^ 2 * C₂₂ + t * C₁₃ := by
      field_simp [ht]
      ring
    _ = 0 := htzero
  have hc : t * C₃₁ + C₂₂ + t⁻¹ * C₁₃ = 0 := (mul_eq_zero.mp hfactor).resolve_left (pow_ne_zero _ ht)
  have h₁ : (∑ σ, μ σ * matchingProduct a b σ) = C₃₁ + C₂₂ + C₁₃ := by
    simpa only [one_mul, one_pow] using hsum 1
  change _ = (1 - t) * C₃₁ + (1 - t⁻¹) * C₁₃
  rw [h₁]
  linear_combination hc

end

end MOC
