import MOC.Core
import Mathlib.Tactic.LinearCombination

/-! Disjoint swaps in order four give four products of two independent
two-factor choices. A full rectangle at one common height is constrained
by the multiplicative identity between its diagonal pairs. -/

namespace MOC

/-- Three contacts determine the fourth real gap up to the squared
modulus of the opposite corner. The identity also holds at zero height. -/
theorem rectangle_fourth_gap {z₀₀ z₀₁ z₁₀ z₁₁ : ℂ} {H : ℝ}
    (hdiag : z₀₀ * z₁₁ = z₀₁ * z₁₀)
    (h₀₀ : z₀₀.re = H) (h₀₁ : z₀₁.re = H) (h₁₀ : z₁₀.re = H) :
    (H - z₁₁.re) * (H ^ 2 + z₀₀.im ^ 2) =
      H * (z₀₁.im - z₀₀.im) * (z₁₀.im - z₀₀.im) := by
  have hre := congrArg Complex.re hdiag
  have him := congrArg Complex.im hdiag
  simp only [Complex.mul_re, h₀₀, h₀₁, h₁₀] at hre
  simp only [Complex.mul_im, h₀₀, h₀₁, h₁₀] at him
  linear_combination -H * hre - z₀₀.im * him

/-- If four products have the same nonzero real part, one of the two
choices of factor is constant. -/
theorem rectangle_factors_eq_of_nonzero_height {x x' y y' : ℂ} {H : ℝ}
    (hH : H ≠ 0) (hxy : (x * y).re = H) (hx'y : (x' * y).re = H)
    (hxy' : (x * y').re = H) (hx'y' : (x' * y').re = H) :
    x = x' ∨ y = y' := by
  have hcross : (x' * y - x * y) * (x * y') = (x' * y' - x * y') * (x * y) := by ring
  have him := congrArg Complex.im hcross
  simp only [Complex.mul_im, Complex.sub_re, hxy, hx'y, hxy', hx'y',
    sub_self, zero_mul, zero_add] at him
  have hdiff : x' * y - x * y = x' * y' - x * y' := by
    apply Complex.ext
    · simp only [Complex.sub_re, hxy, hx'y, hxy', hx'y', sub_self]
    · exact mul_right_cancel₀ hH him
  rw [← sub_mul, ← sub_mul] at hdiff
  have hzero : (x' - x) * (y - y') = 0 := by rw [mul_sub, hdiff, sub_self]
  rcases mul_eq_zero.mp hzero with h | h
  · exact Or.inl (sub_eq_zero.mp h).symm
  · exact Or.inr (sub_eq_zero.mp h)

/-- A two-factor product changes by the product of the two spectral
differences when its assignments are swapped. -/
theorem matching_pair_sub_swap (a₀ a₁ b₀ b₁ : ℂ) :
    (a₀ + b₀) * (a₁ + b₁) - (a₀ + b₁) * (a₁ + b₀) =
      (a₀ - a₁) * (b₁ - b₀) := by ring

/-- For simple spectra in order four, the identity and the two disjoint
swaps and their product can share a support line only at height zero.
The factors are ordered by columns, as in `matchingProduct`. -/
theorem matchingProduct_swap_rectangle_height_zero
    {a b : Fin 4 → ℂ} {η : ℂ} {H : ℝ}
    (ha : Function.Injective a) (hb : Function.Injective b) (hη : η ≠ 0)
    (hid : (η * matchingProduct a b 1).re = H)
    (hs : (η * matchingProduct a b (Equiv.swap 0 1)).re = H)
    (ht : (η * matchingProduct a b (Equiv.swap 2 3)).re = H)
    (hst : (η * matchingProduct a b (Equiv.swap 0 1 * Equiv.swap 2 3)).re = H) :
    H = 0 := by
  let x := (a 0 + b 0) * (a 1 + b 1)
  let x' := (a 0 + b 1) * (a 1 + b 0)
  let y := (a 2 + b 2) * (a 3 + b 3)
  let y' := (a 2 + b 3) * (a 3 + b 2)
  have hx : x ≠ x' := by
    apply sub_ne_zero.mp
    change (a 0 + b 0) * (a 1 + b 1) - (a 0 + b 1) * (a 1 + b 0) ≠ 0
    rw [matching_pair_sub_swap]
    exact mul_ne_zero (sub_ne_zero.mpr (ha.ne (by decide))) (sub_ne_zero.mpr (hb.ne (by decide)))
  have hy : y ≠ y' := by
    apply sub_ne_zero.mp
    change (a 2 + b 2) * (a 3 + b 3) - (a 2 + b 3) * (a 3 + b 2) ≠ 0
    rw [matching_pair_sub_swap]
    exact mul_ne_zero (sub_ne_zero.mpr (ha.ne (by decide))) (sub_ne_zero.mpr (hb.ne (by decide)))
  simp only [matchingProduct, Fin.prod_univ_four] at hid hs ht hst
  change (η * ((a 0 + b 0) * (a 1 + b 1) * (a 2 + b 2) * (a 3 + b 3))).re = H at hid
  change (η * ((a 1 + b 0) * (a 0 + b 1) * (a 2 + b 2) * (a 3 + b 3))).re = H at hs
  change (η * ((a 0 + b 0) * (a 1 + b 1) * (a 3 + b 2) * (a 2 + b 3))).re = H at ht
  change (η * ((a 1 + b 0) * (a 0 + b 1) * (a 3 + b 2) * (a 2 + b 3))).re = H at hst
  have hxy : (η * x * y).re = H := by
    convert hid using 2
    dsimp [x, y]
    ring
  have hx'y : (η * x' * y).re = H := by
    convert hs using 2
    dsimp [x', y]
    ring
  have hxy' : (η * x * y').re = H := by
    convert ht using 2
    dsimp [x, y']
    ring
  have hx'y' : (η * x' * y').re = H := by
    convert hst using 2
    dsimp [x', y']
    ring
  by_contra h
  rcases rectangle_factors_eq_of_nonzero_height h hxy hx'y hxy' hx'y' with he | he
  · exact hx (mul_left_cancel₀ hη he)
  · exact hy he

end MOC
