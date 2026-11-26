import MOC.SpectralTranslationRigidity

/-! A bivariate slice that stays nonzero in the open upper half-planes
has a nonnegative Rayleigh difference at a real boundary value. -/

open Filter Set
open scoped Topology

namespace MOC

private theorem negative_bilinear_root_im (A B C D : ℝ) :
    ((-((A : ℂ) + (B : ℂ) * Complex.I)) /
      ((C : ℂ) + (D : ℂ) * Complex.I)).im =
      (A * D - B * C) / (C^2 + D^2) := by
  have hr : ((C : ℂ) + (D : ℂ) * Complex.I).re = C := by
    simp [Complex.add_re, Complex.mul_re]
  have hi : ((C : ℂ) + (D : ℂ) * Complex.I).im = D := by
    simp [Complex.add_im, Complex.mul_im]
  have ha : (-((A : ℂ) + (B : ℂ) * Complex.I)).re = -A := by
    simp [Complex.add_re, Complex.mul_re]
  have hb : (-((A : ℂ) + (B : ℂ) * Complex.I)).im = -B := by
    simp [Complex.add_im, Complex.mul_im]
  rw [Complex.div_im, Complex.normSq_apply, hr, hi, ha, hb]
  ring

/-- A continuous family of bivariate multi-affine polynomials cannot
approach real boundary coefficients with negative Rayleigh difference.
The proof uses the explicit root in the second variable. -/
theorem rayleigh_nonneg_of_stable_bilinear_boundary
    (A B C D : ℝ → ℂ) (a b c d : ℝ)
    (hA : ContinuousAt A 0) (hB : ContinuousAt B 0)
    (hC : ContinuousAt C 0) (hD : ContinuousAt D 0)
    (ha : A 0 = a) (hb : B 0 = b) (hc : C 0 = c) (hd : D 0 = d)
    (hstable : ∀ ε : ℝ, 0 < ε → ∀ z w : ℂ, 0 < z.im → 0 < w.im →
      A ε + B ε * z + C ε * w + D ε * z * w ≠ 0) :
    0 ≤ b * c - a * d := by
  by_contra! hneg
  have hpos : 0 < a * d - b * c := by linarith only [hneg]
  have hcd : 0 < c^2 + d^2 := by
    by_cases h : c = 0
    · have hn : d ≠ 0 := by
        intro he
        simp only [h, he, mul_zero, sub_self, lt_self_iff_false] at hpos
      rw [h, zero_pow two_ne_zero, zero_add]
      exact sq_pos_of_ne_zero hn
    · exact add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero h) (sq_nonneg _)
  let den (ε : ℝ) := C ε + D ε * Complex.I
  let w (ε : ℝ) := -(A ε + B ε * Complex.I) / den ε
  have hden : den 0 ≠ 0 := by
    intro he
    have hr := congrArg Complex.re he
    have hi := congrArg Complex.im he
    simp [den, hc, hd, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im] at hr hi
    rw [hr, hi] at hcd
    norm_num at hcd
  have hwpos : 0 < (w 0).im := by
    dsimp only [w, den]
    rw [ha, hb, hc, hd, negative_bilinear_root_im]
    exact div_pos hpos hcd
  have hcontDen : ContinuousAt den 0 := hC.add (hD.mul continuousAt_const)
  have hcontW : ContinuousAt w 0 := (hA.add (hB.mul continuousAt_const)).neg.div hcontDen hden
  have hi : ∀ᶠ ε in 𝓝 (0 : ℝ), 0 < (w ε).im :=
    (Complex.continuous_im.continuousAt.comp hcontW).eventually (Ioi_mem_nhds hwpos)
  have hdne : ∀ᶠ ε in 𝓝 (0 : ℝ), den ε ≠ 0 :=
    hcontDen.eventually (isOpen_ne.mem_nhds hden)
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ∈ Ioi (0 : ℝ) ∧ 0 < (w ε).im ∧ den ε ≠ 0 :=
    self_mem_nhdsWithin.and ((hi.and hdne).filter_mono nhdsWithin_le_nhds)
  obtain ⟨ε, hε, hw, hne⟩ := hev.exists
  have hz : den ε * w ε = -(A ε + B ε * Complex.I) := by
    dsimp only [w]
    rw [mul_comm (den ε), div_mul_cancel₀ _ hne]
  apply hstable ε hε Complex.I (w ε) (by rw [Complex.I_im]; exact zero_lt_one) hw
  dsimp only [den] at hz
  linear_combination hz

end MOC
