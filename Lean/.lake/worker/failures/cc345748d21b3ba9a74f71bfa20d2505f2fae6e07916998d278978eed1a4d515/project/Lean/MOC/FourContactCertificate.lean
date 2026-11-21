import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! Radial and Gram inequalities for the contact set `T34` in Zheng's
order-four determinant argument. The radial formulas use the coefficients of
the eight source profiles in the order `p, r, a, b, c, q, d, s`. -/

namespace MOC

noncomputable section

/-- The coefficient of the common support height in the restricted cubic for `T34`. -/
def t34RadialQ (a b c d r s : ℝ) : ℝ :=
  (a - (d + r + s)) * (b + c) - d * (d + r + s)

/-- The zero-height part of the restricted cubic for `T34`. -/
def t34RadialC (p r a b c q d s : ℝ) : ℝ :=
  b * c * (a - (d + r + s)) - b * (d + r) * (d + q + s) -
    c * (d + s) * (d + p + r) - d * (d + p + r) * (d + q + s)

/-- The exact polynomial identity used to exclude a zero height coefficient. -/
theorem t34_radial_identity (p r a b c q d s : ℝ) :
    b * c * t34RadialQ a b c d r s - (b + c) * t34RadialC p r a b c q d s =
      d * (d + r + s) * (b ^ 2 + b * c + c ^ 2) +
        (b + c) * (b * (d * q + r * s + r * q) +
          c * (d * p + p * s + r * s) + d * (d + p + r) * (d + q + s)) := by
  unfold t34RadialQ t34RadialC
  ring

/-- A positive mixed coefficient and the height equation force a nonzero
height coefficient. This justifies division by `Q` in the `T34` radial reduction. -/
theorem t34_radialQ_ne_zero_of_height {p r a b c q d s h : ℝ}
    (hp : 0 ≤ p) (hr : 0 ≤ r) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hq : 0 ≤ q) (hd : 0 < d) (hs : 0 ≤ s)
    (hheight : t34RadialC p r a b c q d s + h * t34RadialQ a b c d r s = 0) :
    t34RadialQ a b c d r s ≠ 0 := by
  intro hQ
  have hU : 0 < d + r + s := add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg hd hr) hs
  by_cases hM : b + c = 0
  · unfold t34RadialQ at hQ
    rw [hM, mul_zero, zero_sub] at hQ
    exact (ne_of_lt (neg_neg_of_pos (mul_pos hd hU))) hQ
  have hC : t34RadialC p r a b c q d s = 0 := by simpa [hQ] using hheight
  have hleft := mul_nonneg (mul_nonneg hd.le hU.le)
    (add_nonneg (add_nonneg (sq_nonneg b) (mul_nonneg hb hc)) (sq_nonneg c))
  have hb' := mul_nonneg hb
    (add_nonneg (add_nonneg (mul_nonneg hd.le hq) (mul_nonneg hr hs)) (mul_nonneg hr hq))
  have hc' := mul_nonneg hc
    (add_nonneg (add_nonneg (mul_nonneg hd.le hp) (mul_nonneg hp hs)) (mul_nonneg hr hs))
  have hd' := mul_pos (mul_pos hd (add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg hd hp) hr))
    (add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg hd hq) hs)
  have hright := mul_pos (lt_of_le_of_ne (add_nonneg hb hc) (Ne.symm hM))
    (add_pos_of_nonneg_of_pos (add_nonneg hb' hc') hd')
  have he := t34_radial_identity p r a b c q d s
  simp only [hQ, hC, mul_zero, sub_self] at he
  exact (ne_of_gt (add_pos_of_nonneg_of_pos hleft hright)) he.symm

/-- Completing two squares proves the three-vertex Gram criterion used in
the `(PB)` and `(CQ)` branches of `T34`. -/
theorem contact_three_vertex_gram_nonneg {p a q d₁ d₂ : ℝ}
    (hp : 0 < p) (hq : 0 < q) (ha : d₁ ^ 2 / p + d₂ ^ 2 / q ≤ a)
    (x y z : ℝ) :
    0 ≤ p * x ^ 2 + a * y ^ 2 + q * z ^ 2 - 2 * d₁ * x * y - 2 * d₂ * y * z := by
  have he :
      p * x ^ 2 + a * y ^ 2 + q * z ^ 2 - 2 * d₁ * x * y - 2 * d₂ * y * z =
        p * (x - d₁ / p * y) ^ 2 + q * (z - d₂ / q * y) ^ 2 +
          (a - (d₁ ^ 2 / p + d₂ ^ 2 / q)) * y ^ 2 := by
    field_simp [ne_of_gt hp, ne_of_gt hq]
    <;> ring
  rw [he]
  exact add_nonneg (add_nonneg (mul_nonneg hp.le (sq_nonneg _)) (mul_nonneg hq.le (sq_nonneg _)))
    (mul_nonneg (sub_nonneg.mpr ha) (sq_nonneg _))

/-- Nonnegative Bernstein coefficients and a positive constant coefficient
exclude a root of the radial quadratic below the selected Gram threshold. -/
theorem contact_bernstein_threshold_le_of_root {a A k₀ k₁ k₂ : ℝ}
    (ha : 0 ≤ a) (hk₀ : 0 < k₀) (hmiddle : 0 ≤ 2 * k₀ + k₁ * A)
    (hend : 0 ≤ k₂ * A ^ 2 + k₁ * A + k₀)
    (hroot : k₂ * a ^ 2 + k₁ * a + k₀ = 0) :
    A ≤ a := by
  by_contra h
  have hlt : a < A := lt_of_not_ge h
  have hpositive := mul_pos hk₀ (pow_pos (sub_pos.mpr hlt) 2)
  have hmiddle' := mul_nonneg (mul_nonneg hmiddle ha) (sub_nonneg.mpr hlt.le)
  have hend' := mul_nonneg hend (sq_nonneg a)
  have he : A ^ 2 * (k₂ * a ^ 2 + k₁ * a + k₀) =
      k₀ * (A - a) ^ 2 + (2 * k₀ + k₁ * A) * a * (A - a) +
        (k₂ * A ^ 2 + k₁ * A + k₀) * a ^ 2 := by ring
  rw [hroot, mul_zero] at he
  exact (ne_of_gt (add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg hpositive hmiddle') hend')) he.symm

end

end MOC
