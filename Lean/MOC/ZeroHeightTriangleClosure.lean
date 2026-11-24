import MOC.ContactCrossRatios
import MOC.MatchingTriangleHeight

/-! Zero-height triangle saturation should require only local spectral
simplicity and the two nonzero known products that enter the phase law. -/

namespace MOC

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Four indicated zero-height contacts on three labels force both remaining
contacts. Unlike global product injectivity, simple spectra suffice, and
zero products in the ambient profile are permitted. Only the two indicated
even contact values are assumed nonzero. -/
theorem matchingProduct_triangle_complete_zero_height_of_simple
    (a b : ι → ℂ) (ha : Function.Injective a) (hb : Function.Injective b)
    (r : Equiv.Perm ι) (i j k : ι) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (η : ℂ) (hη : η ≠ 0)
    (hbaseNZ : matchingProduct a b r ≠ 0)
    (hcycleNZ : matchingProduct a b (r * Equiv.swap i j * Equiv.swap j k) ≠ 0)
    (hbase : (η * matchingProduct a b r).re = 0)
    (hcycle : (η * matchingProduct a b (r * Equiv.swap i j * Equiv.swap j k)).re = 0)
    (hswap₁ : (η * matchingProduct a b (r * Equiv.swap i j)).re = 0)
    (hswap₂ : (η * matchingProduct a b (r * Equiv.swap i k)).re = 0) :
    (η * matchingProduct a b (r * Equiv.swap j k * Equiv.swap i j)).re = 0 ∧
      (η * matchingProduct a b (r * Equiv.swap j k)).re = 0 := by
  let z (σ : Equiv.Perm ι) := η * matchingProduct a b σ
  let p := r * Equiv.swap j k * Equiv.swap i j
  let q := r * Equiv.swap j k
  change (z r).re = 0 at hbase
  change (z (r * Equiv.swap i j * Equiv.swap j k)).re = 0 at hcycle
  change (z (r * Equiv.swap i j)).re = 0 at hswap₁
  change (z (r * Equiv.swap i k)).re = 0 at hswap₂
  have hsum : z r + z (r * Equiv.swap i j * Equiv.swap j k) + z p =
      z (r * Equiv.swap i j) + z (r * Equiv.swap i k) + z q := by
    simpa only [z, p, q, mul_add] using congrArg (η * ·)
      (matchingProduct_triangle_identity a b r i j k hij hik hjk)
  change (z p).re = 0 ∧ (z q).re = 0
  by_cases hq : matchingProduct a b q = 0
  · have hqr : (z q).re = 0 := by simp [z, hq]
    have hre := congrArg Complex.re hsum
    simp only [Complex.add_re, hbase, hcycle, hswap₁, hswap₂, zero_add] at hre
    exact ⟨hre.trans hqr, hqr⟩
  · have hprod : z r * z (r * Equiv.swap i j * Equiv.swap j k) * z p =
        z (r * Equiv.swap i j) * z (r * Equiv.swap i k) * z q := by
      have h := matchingProduct_triangle_product_identity a b r i j k hij hik hjk
      dsimp only [z, p, q]
      linear_combination η ^ 3 * h
    have hne : z p ≠ z q := by
      intro he
      have hz := matchingProduct_swap_gap_ne_of_simple a b ha hb q hq i j hij
      apply hz
      exact sub_eq_zero.mpr (mul_left_cancel₀ hη he).symm
    exact zero_height_of_two_pairs_of_triple_sum_product hbase hcycle hswap₁ hswap₂
      (mul_ne_zero hη hbaseNZ) (mul_ne_zero hη hcycleNZ) hne hsum hprod

end MOC
