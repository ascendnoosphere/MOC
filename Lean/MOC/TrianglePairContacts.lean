import MOC.MatchingTriangleHeight

/-! Two active matchings of each parity in a three-label triangle determine
the sign of the two remaining projected deficits. -/

namespace MOC

/-- Equal triple sums and products give the exact deficit at either missing
entry when two entries of each triple have the common projected height. -/
theorem triangle_pair_contact_gap {a b c d p q : ℂ} {H : ℝ}
    (ha : a.re = H) (hb : b.re = H) (hc : c.re = H) (hd : d.re = H)
    (hsum : p + c + d = q + a + b) (hprod : p * c * d = q * a * b) :
    (H - p.re) * Complex.normSq (a * b - c * d) =
      H * ((a.im - c.im) * (a.im - d.im) * (b.im - c.im) * (b.im - d.im)) := by
  let s := a.im + b.im - c.im - d.im
  let k := c.im * d.im - a.im * b.im
  have hdiff : p - q = a + b - c - d := by linear_combination hsum
  have hp : p * (a * b - c * d) = (a + b - c - d) * (a * b) := by
    linear_combination (a * b) * hdiff - hprod
  have hk : (a * b - c * d).re = k := by
    simp only [k, Complex.sub_re, Complex.mul_re, ha, hb, hc, hd]
    ring
  have hks : (a * b - c * d).im = H * s := by
    simp only [s, Complex.sub_im, Complex.mul_im, ha, hb, hc, hd]
    ring
  have hLre : (a + b - c - d).re = 0 := by
    simp only [Complex.add_re, Complex.sub_re, ha, hb, hc, hd, add_sub_cancel_right,
      sub_self]
  have hLim : (a + b - c - d).im = s := by
    simp only [s, Complex.add_im, Complex.sub_im]
  have hre : p.re * k - p.im * (H * s) = -(s * (H * b.im + a.im * H)) := by
    simpa only [Complex.mul_re, Complex.mul_im, hk, hks, hLre, hLim, ha, hb,
      zero_mul, zero_sub] using congrArg Complex.re hp
  have him : p.re * (H * s) + p.im * k = s * (H * H - a.im * b.im) := by
    simpa only [Complex.mul_im, Complex.mul_re, hk, hks, hLre, hLim, ha, hb,
      zero_mul, zero_add] using congrArg Complex.im hp
  rw [Complex.normSq_apply, hk, hks]
  dsimp only [s, k] at hre him ⊢
  linear_combination -(c.im * d.im - a.im * b.im) * hre -
    H * (a.im + b.im - c.im - d.im) * him

/-- At nonzero upper support height, the product of the four cross-parity
imaginary differences has the sign of the height. At positive height this
excludes alternating parity along the supporting line. -/
theorem triangle_pair_contact_sign {a b c d p q : ℂ} {H : ℝ}
    (ha : a.re = H) (hb : b.re = H) (hc : c.re = H) (hd : d.re = H)
    (hsum : p + c + d = q + a + b) (hprod : p * c * d = q * a * b)
    (hsupport : p.re ≤ H) (hH : H ≠ 0)
    (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) :
    0 < H * ((a.im - c.im) * (a.im - d.im) * (b.im - c.im) * (b.im - d.im)) := by
  have hgap := triangle_pair_contact_gap ha hb hc hd hsum hprod
  have hnonneg : 0 ≤ H * ((a.im - c.im) * (a.im - d.im) *
      (b.im - c.im) * (b.im - d.im)) := by
    rw [← hgap]
    exact mul_nonneg (sub_nonneg.mpr hsupport) (Complex.normSq_nonneg _)
  have hne {u v : ℂ} (hr : u.re = v.re) (hne : u ≠ v) : u.im - v.im ≠ 0 :=
    fun hi => hne (Complex.ext hr (sub_eq_zero.mp hi))
  exact lt_of_le_of_ne hnonneg (Ne.symm (mul_ne_zero hH
    (mul_ne_zero (mul_ne_zero (mul_ne_zero
      (hne (ha.trans hc.symm) hac) (hne (ha.trans hd.symm) had))
      (hne (hb.trans hc.symm) hbc)) (hne (hb.trans hd.symm) hbd))))

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- If two even and two odd matchings of three labels are active, the two
remaining matching deficits satisfy an exact cross-parity formula. -/
theorem matchingProduct_triangle_pair_contact_gap
    (a b : ι → ℂ) (r : Equiv.Perm ι) (i j k : ι)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (η : ℂ) (H : ℝ)
    (ha : (η * matchingProduct a b r).re = H)
    (hb : (η * matchingProduct a b (r * Equiv.swap i j * Equiv.swap j k)).re = H)
    (hc : (η * matchingProduct a b (r * Equiv.swap i j)).re = H)
    (hd : (η * matchingProduct a b (r * Equiv.swap i k)).re = H) :
    let v (σ : Equiv.Perm ι) := η * matchingProduct a b σ
    let x := v r
    let y := v (r * Equiv.swap i j * Equiv.swap j k)
    let u := v (r * Equiv.swap i j)
    let w := v (r * Equiv.swap i k)
    let p := v (r * Equiv.swap j k)
    (H - p.re) * Complex.normSq (x * y - u * w) =
      H * ((x.im - u.im) * (x.im - w.im) * (y.im - u.im) * (y.im - w.im)) := by
  intro v x y u w p
  let q := v (r * Equiv.swap j k * Equiv.swap i j)
  have hs : x + y + q = u + w + p := by
    simpa only [v, x, y, u, w, p, q, mul_add] using
      congrArg (η * ·) (matchingProduct_triangle_identity a b r i j k hij hik hjk)
  have hp : x * y * q = u * w * p := by
    have h := matchingProduct_triangle_product_identity a b r i j k hij hik hjk
    dsimp only [v, x, y, u, w, p, q]
    linear_combination η ^ 3 * h
  apply triangle_pair_contact_gap ha hb hc hd (q := q)
  · linear_combination -hs
  · linear_combination -hp

end MOC
