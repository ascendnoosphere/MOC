import MOC.MatchingTriangle
import Mathlib.Tactic.LinearCombination

/-! Three even and three odd matchings of a triangle have the same product
as well as the same sum. A common nonzero height would make the two triples
the roots of one real cubic. -/

open BigOperators

namespace MOC

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Each side uses each of the nine entries on the three selected labels
once, and outside entries three times. -/
theorem matchingProduct_triangle_product_identity
    (a b : ι → ℂ) (σ : Equiv.Perm ι) (i j k : ι)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    matchingProduct a b σ *
      matchingProduct a b (σ * Equiv.swap i j * Equiv.swap j k) *
      matchingProduct a b (σ * Equiv.swap j k * Equiv.swap i j) =
    matchingProduct a b (σ * Equiv.swap i j) *
      matchingProduct a b (σ * Equiv.swap i k) *
      matchingProduct a b (σ * Equiv.swap j k) := by
  simp only [matchingProduct, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro l _
  simp only [Equiv.Perm.mul_apply]
  rcases eq_or_ne l i with rfl | hli
  · simp only [Equiv.swap_apply_left, Equiv.swap_apply_right,
      Equiv.swap_apply_of_ne_of_ne hij hik] <;> ac_rfl
  rcases eq_or_ne l j with rfl | hlj
  · simp only [Equiv.swap_apply_left, Equiv.swap_apply_right,
      Equiv.swap_apply_of_ne_of_ne hij hik,
      Equiv.swap_apply_of_ne_of_ne hij.symm hjk,
      Equiv.swap_apply_of_ne_of_ne hik.symm hjk.symm] <;> ac_rfl
  rcases eq_or_ne l k with rfl | hlk
  · simp only [Equiv.swap_apply_left, Equiv.swap_apply_right,
      Equiv.swap_apply_of_ne_of_ne hik.symm hjk.symm] <;> ac_rfl
  · simp only [Equiv.swap_apply_of_ne_of_ne hli hlj,
      Equiv.swap_apply_of_ne_of_ne hli hlk, Equiv.swap_apply_of_ne_of_ne hlj hlk]

private theorem common_height_eq_zero_of_triple_sum_product
    {p₀ p₁ p₂ q₀ q₁ q₂ : ℂ} {H : ℝ}
    (hp₀ : p₀.re = H) (hp₁ : p₁.re = H) (hp₂ : p₂.re = H)
    (hq₀ : q₀.re = H) (hq₁ : q₁.re = H) (hq₂ : q₂.re = H)
    (hdis : p₀ ≠ q₀ ∧ p₀ ≠ q₁ ∧ p₀ ≠ q₂)
    (hsum : p₀ + p₁ + p₂ = q₀ + q₁ + q₂)
    (hprod : p₀ * p₁ * p₂ = q₀ * q₁ * q₂) : H = 0 := by
  by_contra hH
  have h₁ := congrArg Complex.im hsum
  simp only [Complex.add_im] at h₁
  have hre := congrArg Complex.re hprod
  have him := congrArg Complex.im hprod
  simp only [Complex.mul_re, Complex.mul_im, hp₀, hp₁, hp₂, hq₀, hq₁, hq₂] at hre him
  have h₂mul : H * (p₀.im * p₁.im + p₀.im * p₂.im + p₁.im * p₂.im) =
      H * (q₀.im * q₁.im + q₀.im * q₂.im + q₁.im * q₂.im) := by
    linear_combination -hre
  have h₂ := mul_left_cancel₀ hH h₂mul
  have h₃ : p₀.im * p₁.im * p₂.im = q₀.im * q₁.im * q₂.im := by
    linear_combination H ^ 2 * h₁ - him
  have hv : (p₀.im - q₀.im) * (p₀.im - q₁.im) * (p₀.im - q₂.im) = 0 := calc
    _ = (p₀.im - p₀.im) * (p₀.im - p₁.im) * (p₀.im - p₂.im) := by
      linear_combination p₀.im ^ 2 * h₁ - p₀.im * h₂ + h₃
    _ = 0 := by simp
  have heq {q : ℂ} (hr : q.re = H) (hi : p₀.im - q.im = 0) : p₀ = q :=
    Complex.ext (hp₀.trans hr.symm) (sub_eq_zero.mp hi)
  rcases mul_eq_zero.mp hv with h | h
  · rcases mul_eq_zero.mp h with h | h
    · exact hdis.1 (heq hq₀ h)
    · exact hdis.2.1 (heq hq₁ h)
  · exact hdis.2.2 (heq hq₂ h)

/-- Four zero-height entries, two from each triple, force the remaining two
to have zero height when the two triple sums and products agree. -/
theorem zero_height_of_two_pairs_of_triple_sum_product
    {p₀ p₁ p₂ q₀ q₁ q₂ : ℂ}
    (hp₀ : p₀.re = 0) (hp₁ : p₁.re = 0) (hq₀ : q₀.re = 0) (hq₁ : q₁.re = 0)
    (hp₀nz : p₀ ≠ 0) (hp₁nz : p₁ ≠ 0) (hne : p₂ ≠ q₂)
    (hsum : p₀ + p₁ + p₂ = q₀ + q₁ + q₂)
    (hprod : p₀ * p₁ * p₂ = q₀ * q₁ * q₂) : p₂.re = 0 ∧ q₂.re = 0 := by
  have hre : p₂.re = q₂.re := by
    simpa only [Complex.add_re, hp₀, hp₁, hq₀, hq₁, zero_add] using congrArg Complex.re hsum
  by_cases hz : q₂.re = 0
  · exact ⟨hre.trans hz, hz⟩
  exfalso
  have he := congrArg Complex.re hprod
  have hi := congrArg Complex.im hprod
  simp only [Complex.mul_re, Complex.mul_im, hp₀, hp₁, hq₀, hq₁, zero_mul, mul_zero,
    zero_add, add_zero, sub_zero, zero_sub] at he hi
  rw [hre] at he
  have hpair := mul_right_cancel₀ hz he
  rw [← hpair] at hi
  have hpinz : -(p₀.im * p₁.im) ≠ 0 :=
    neg_ne_zero.mpr (mul_ne_zero
      (fun h => hp₀nz (Complex.ext hp₀ h)) (fun h => hp₁nz (Complex.ext hp₁ h)))
  exact hne (Complex.ext hre (mul_left_cancel₀ hpinz hi))

/-- In a three-label triangle, two even and two odd zero-height contacts
force the last even and odd labels to become contacts. -/
theorem matchingProduct_triangle_complete_zero_height
    (a b : ι → ℂ) (σ : Equiv.Perm ι) (i j k : ι)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (η : ℂ) (hη : η ≠ 0) (hdistinct : Function.Injective (matchingProduct a b))
    (hnz : ∀ τ, matchingProduct a b τ ≠ 0)
    (hbase : (η * matchingProduct a b σ).re = 0)
    (hcycle : (η * matchingProduct a b (σ * Equiv.swap i j * Equiv.swap j k)).re = 0)
    (hswap₁ : (η * matchingProduct a b (σ * Equiv.swap i j)).re = 0)
    (hswap₂ : (η * matchingProduct a b (σ * Equiv.swap i k)).re = 0) :
    (η * matchingProduct a b (σ * Equiv.swap j k * Equiv.swap i j)).re = 0 ∧
      (η * matchingProduct a b (σ * Equiv.swap j k)).re = 0 := by
  refine zero_height_of_two_pairs_of_triple_sum_product hbase hcycle hswap₁ hswap₂
    (mul_ne_zero hη (hnz _)) (mul_ne_zero hη (hnz _)) ?_ ?_ ?_
  · intro h
    have he := congrArg (fun τ : Equiv.Perm ι => τ i) (hdistinct (mul_left_cancel₀ hη h))
    simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_left,
      Equiv.swap_apply_of_ne_of_ne hij hik] at he
    exact hik (σ.injective he.symm)
  · simpa only [mul_add] using congrArg (η * ·)
      (matchingProduct_triangle_identity a b σ i j k hij hik hjk)
  · have h := matchingProduct_triangle_product_identity a b σ i j k hij hik hjk
    linear_combination η ^ 3 * h

/-- Six matchings obtained by permuting three labels can have a common
projected height only at zero if the matching products are distinct. -/
theorem matchingProduct_triangle_height_eq_zero
    (a b : ι → ℂ) (σ : Equiv.Perm ι) (i j k : ι)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (η : ℂ) (hη : η ≠ 0) (H : ℝ) (hdistinct : Function.Injective (matchingProduct a b))
    (hc : ∀ τ ∈ ({σ, σ * Equiv.swap i j, σ * Equiv.swap i k, σ * Equiv.swap j k,
      σ * Equiv.swap i j * Equiv.swap j k, σ * Equiv.swap j k * Equiv.swap i j} :
      Finset (Equiv.Perm ι)), (η * matchingProduct a b τ).re = H) : H = 0 := by
  have hseparate {i j : ι} (hne : i ≠ j) :
      η * matchingProduct a b σ ≠ η * matchingProduct a b (σ * Equiv.swap i j) := by
    intro h
    have he := congrArg (fun τ : Equiv.Perm ι => τ i) (hdistinct (mul_left_cancel₀ hη h))
    simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_left] at he
    exact hne (σ.injective he)
  refine common_height_eq_zero_of_triple_sum_product (hc σ (by simp))
    (hc (σ * Equiv.swap i j * Equiv.swap j k) (by simp))
    (hc (σ * Equiv.swap j k * Equiv.swap i j) (by simp))
    (hc (σ * Equiv.swap i j) (by simp)) (hc (σ * Equiv.swap i k) (by simp))
    (hc (σ * Equiv.swap j k) (by simp))
    ⟨hseparate hij, hseparate hik, hseparate hjk⟩ ?_ ?_
  · simpa only [mul_add] using congrArg (η * ·)
      (matchingProduct_triangle_identity a b σ i j k hij hik hjk)
  · have h := matchingProduct_triangle_product_identity a b σ i j k hij hik hjk
    linear_combination η ^ 3 * h

end MOC
