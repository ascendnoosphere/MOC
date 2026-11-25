import MOC.FourBilinearInvariant

/-! A singleton law with positive weights bounds every projected matching
contrast at a putative order-four bilinear support violation. -/

open BigOperators Matrix Finset

namespace MOC

noncomputable section

/-- For a fixed positive singleton law, the normalized order-four matching
products have bounded spread in every direction that they fail to support. -/
theorem four_bilinear_projected_spread_le (a b : Fin 4 → ℂ)
    (U : Matrix (Fin 4) (Fin 4) ℂ) (hU : IsUnitary U)
    (w : Equiv.Perm (Fin 4) → ℝ) (hs : ∑ σ, w σ = 1)
    (hm : ∀ i j, marginal (fun σ => (w σ : ℂ)) i j = (Complex.normSq (U i j) : ℂ))
    (ε : ℝ) (hε : 0 < ε) (hw : ∀ σ, ε ≤ w σ)
    (α β γ δ η : ℂ) (hH : α * δ - β * γ ≠ 0) (hη : ‖η‖ = 1)
    (hsep : ∀ σ, 0 ≤ (η * ((bilinearPencil a b U α β γ δ).det -
      bilinearMatchingProduct a b α β γ δ σ) / (α * δ - β * γ) ^ 2).re)
    (σ τ : Equiv.Perm (Fin 4)) :
    |(η * (bilinearMatchingProduct a b α β γ δ σ -
      bilinearMatchingProduct a b α β γ δ τ) / (α * δ - β * γ) ^ 2).re| ≤
      ‖∑ r, (signedWeight U r - (w r : ℂ)) * matchingProduct a b r‖ / ε := by
  let μ (r : Equiv.Perm (Fin 4)) := signedWeight U r - (w r : ℂ)
  let e := ∑ r, μ r * matchingProduct a b r
  let d := α * δ - β * γ
  let p := bilinearMatchingProduct a b α β γ δ
  let D := (bilinearPencil a b U α β γ δ).det
  let f (r : Equiv.Perm (Fin 4)) := (η * (D - p r) / d ^ 2).re
  have hμ : ∑ r, μ r = 0 := by
    simp only [μ, Finset.sum_sub_distrib, sum_signedWeight U (det_ne_zero_of_unitary hU),
      ← Complex.ofReal_sum, hs, Complex.ofReal_one, sub_self]
  have hμm (i j : Fin 4) : marginal μ i j = 0 := calc
    _ = marginal (signedWeight U) i j - marginal (fun r => (w r : ℂ)) i j := by
      unfold marginal
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro r _
      dsimp only [μ]
      split_ifs <;> simp
    _ = 0 := by rw [marginal_signedWeight U hU, hm, sub_self]
  have he : D - ∑ r, (w r : ℂ) * p r = d ^ 2 * e := by
    simpa only [μ, sub_mul, Finset.sum_sub_distrib, bilinear_signed_determinant a b U hU,
      D, e, d, p] using four_bilinear_gap_of_singleton_marginals a b μ hμ hμm α β γ δ
  have hproj (r : Equiv.Perm (Fin 4)) :
      w r * f r = ((w r : ℂ) * (η * (D - p r) / d ^ 2)).re := by
    simp [f, Complex.mul_re]
  have hsum : ∑ r, w r * f r = (η * e).re := by
    simp_rw [hproj, ← Complex.re_sum]
    congr 1
    calc
      _ = ∑ r, (η / d ^ 2) * ((w r : ℂ) * (D - p r)) := by
        apply Finset.sum_congr rfl
        intro r _
        ring
      _ = η / d ^ 2 * (D - ∑ r, (w r : ℂ) * p r) := by
        rw [← Finset.mul_sum]
        simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, ← Complex.ofReal_sum,
          hs, Complex.ofReal_one, one_mul]
      _ = η * e := by
        rw [he]
        field_simp [show d ≠ 0 from hH] <;> ring
  have hf (r : Equiv.Perm (Fin 4)) : 0 ≤ f r := hsep r
  have hbound (r : Equiv.Perm (Fin 4)) : f r ≤ ‖e‖ / ε := by
    apply (le_div_iff₀ hε).mpr
    calc
      f r * ε ≤ w r * f r := by
        rw [mul_comm (f r) ε]
        exact mul_le_mul_of_nonneg_right (hw r) (hf r)
      _ ≤ ∑ s, w s * f s := Finset.single_le_sum
        (fun s _ => mul_nonneg (hε.le.trans (hw s)) (hf s)) (Finset.mem_univ r)
      _ = (η * e).re := hsum
      _ ≤ ‖e‖ := by simpa only [Complex.norm_mul, hη, one_mul] using
        Complex.re_le_norm (η * e)
  change |(η * (p σ - p τ) / d ^ 2).re| ≤ ‖e‖ / ε
  have hdiff : (η * (p σ - p τ) / d ^ 2).re = f τ - f σ := by
    dsimp only [f]
    rw [← Complex.sub_re]
    congr 1
    ring
  rw [hdiff, abs_le]
  exact ⟨by linarith [hbound σ, hf τ], by linarith [hbound τ, hf σ]⟩

/-- The normalized contrast of two matchings that swap their first two
columns is a Laurent polynomial of degrees `-1`, `0`, and `1` on a line
between rank-one coefficient matrices. -/
theorem four_bilinear_swap_laurent (a b : Fin 4 → ℂ) (r : Equiv.Perm (Fin 4))
    (α β γ δ t c l₂ l₃ m₂ m₃ : ℂ)
    (hdet : α * δ - β * γ = t * c) (ht : t ≠ 0) (hc : c ≠ 0)
    (h₂ : bilinearKernel α β γ δ (a (r 2)) (b 2) = l₂ + t * m₂)
    (h₃ : bilinearKernel α β γ δ (a (r 3)) (b 3) = l₃ + t * m₃) :
    (bilinearMatchingProduct a b α β γ δ r -
      bilinearMatchingProduct a b α β γ δ (r * Equiv.swap 0 1)) / (α * δ - β * γ) ^ 2 =
      (((a (r 0) - a (r 1)) * (b 0 - b 1)) / c) *
        (l₂ * l₃ / t + l₂ * m₃ + m₂ * l₃ + t * (m₂ * m₃)) := by
  have hswap₂ : Equiv.swap (0 : Fin 4) 1 2 = 2 := by decide
  have hswap₃ : Equiv.swap (0 : Fin 4) 1 3 = 3 := by decide
  have hfactor : bilinearMatchingProduct a b α β γ δ r -
      bilinearMatchingProduct a b α β γ δ (r * Equiv.swap 0 1) =
      (bilinearKernel α β γ δ (a (r 0)) (b 0) *
        bilinearKernel α β γ δ (a (r 1)) (b 1) -
      bilinearKernel α β γ δ (a (r 0)) (b 1) *
        bilinearKernel α β γ δ (a (r 1)) (b 0)) *
      bilinearKernel α β γ δ (a (r 2)) (b 2) *
      bilinearKernel α β γ δ (a (r 3)) (b 3) := by
    simp only [bilinearMatchingProduct, Fin.prod_univ_four, Equiv.Perm.mul_apply,
      Equiv.swap_apply_left, Equiv.swap_apply_right, hswap₂, hswap₃]
    ring
  rw [hfactor, bilinear_kernel_rectangle, hdet, h₂, h₃]
  field_simp [ht, hc]
  <;> ring

private theorem norm_mul_det_le_two_projections (u x y : ℂ) :
    |x.re * y.im - y.re * x.im| * ‖u‖ ≤
      |(u * x).re| * ‖y‖ + |(u * y).re| * ‖x‖ := by
  let d := x.re * y.im - y.re * x.im
  let a : ℂ := ((u * x).re : ℝ)
  let b : ℂ := ((u * y).re : ℝ)
  have hd : (d : ℂ) * u = Complex.I * (a * star y - b * star x) := by
    apply Complex.ext <;>
      simp only [d, a, b, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
        Complex.star_def, Complex.conj_re, Complex.conj_im] <;> ring
  change |d| * ‖u‖ ≤ _
  calc
    _ = ‖(d : ℂ) * u‖ := by rw [Complex.norm_mul, Complex.norm_real, Real.norm_eq_abs]
    _ = ‖a * star y - b * star x‖ := by rw [hd, Complex.norm_mul, Complex.norm_I, one_mul]
    _ ≤ _ := by
      simpa only [a, b, Complex.norm_mul, Complex.norm_real, Real.norm_eq_abs,
        Complex.star_def, Complex.norm_conj] using norm_sub_le (a * star y) (b * star x)

/-- Two bounded projected Laurent contrasts with independent residues force
their parameter away from zero, uniformly over all unit support directions. -/
theorem laurent_contrasts_bound_near_zero (t η a b c a' b' c' : ℂ) (K : ℝ)
    (ht : t ≠ 0) (ht₁ : ‖t‖ ≤ 1) (hη : ‖η‖ = 1)
    (h : |(η * (a / t + b + c * t)).re| ≤ K)
    (h' : |(η * (a' / t + b' + c' * t)).re| ≤ K) :
    |a.re * a'.im - a'.re * a.im| ≤ ‖t‖ *
      ((K + ‖b‖ + ‖c‖) * ‖a'‖ + (K + ‖b'‖ + ‖c'‖) * ‖a‖) := by
  have hrem (x y z : ℂ) (hz : |(η * (x / t + y + z * t)).re| ≤ K) :
      |(η / t * x).re| ≤ K + ‖y‖ + ‖z‖ := by
    have he : (η / t * x).re = (η * (x / t + y + z * t)).re - (η * (y + z * t)).re := by
      rw [← Complex.sub_re]
      congr 1
      ring
    have hy : |(η * (y + z * t)).re| ≤ ‖y‖ + ‖z‖ := calc
      _ ≤ ‖η * (y + z * t)‖ := Complex.abs_re_le_norm _
      _ = ‖y + z * t‖ := by rw [Complex.norm_mul, hη, one_mul]
      _ ≤ ‖y‖ + ‖z * t‖ := norm_add_le _ _
      _ ≤ _ := by
        rw [Complex.norm_mul]
        exact add_le_add_left (mul_le_of_le_one_right (norm_nonneg z) ht₁) _
    rw [he]
    exact ((abs_sub _ _).trans (add_le_add hz hy)).trans_eq (add_assoc K ‖y‖ ‖z‖).symm
  have hdet := (norm_mul_det_le_two_projections (η / t) a a').trans
    (add_le_add (mul_le_mul_of_nonneg_right (hrem a b c h) (norm_nonneg _))
      (mul_le_mul_of_nonneg_right (hrem a' b' c' h') (norm_nonneg _)))
  rw [Complex.norm_div, hη, one_div, ← div_eq_mul_inv] at hdet
  rw [mul_comm ‖t‖]
  exact (div_le_iff₀ (norm_pos_iff.mpr ht)).mp hdet

/-- Independence of the two leading coefficients also bounds the parameter
from above, by applying the small-parameter bound to the reciprocal. -/
theorem laurent_contrasts_bound_near_infinity (t η a b c a' b' c' : ℂ) (K : ℝ)
    (ht₁ : 1 ≤ ‖t‖) (hη : ‖η‖ = 1)
    (h : |(η * (a / t + b + c * t)).re| ≤ K)
    (h' : |(η * (a' / t + b' + c' * t)).re| ≤ K) :
    |c.re * c'.im - c'.re * c.im| * ‖t‖ ≤
      (K + ‖b‖ + ‖a‖) * ‖c'‖ + (K + ‖b'‖ + ‖a'‖) * ‖c‖ := by
  have htpos := lt_of_lt_of_le (zero_lt_one : (0 : ℝ) < 1) ht₁
  have ht : t ≠ 0 := norm_pos_iff.mp htpos
  have hnorm : ‖t⁻¹‖ = ‖t‖⁻¹ := by
    have hone : ‖(1 : ℂ)‖ = 1 := by
      simpa only [Complex.ofReal_one] using Complex.norm_of_nonneg (zero_le_one : (0 : ℝ) ≤ 1)
    simpa only [hone, one_div] using Complex.norm_div (1 : ℂ) t
  have hi : ‖t⁻¹‖ ≤ 1 := by
    rw [hnorm]
    exact inv_le_one_of_one_le₀ ht₁
  have he (x y z : ℂ) : z / t⁻¹ + y + x * t⁻¹ = x / t + y + z * t := by
    simp only [div_eq_mul_inv, inv_inv]
    ring
  have hbound := laurent_contrasts_bound_near_zero t⁻¹ η c b a c' b' a' K
    (inv_ne_zero ht) hi hη (by simpa only [he] using h) (by simpa only [he] using h')
  rw [hnorm, mul_comm (‖t‖⁻¹), ← div_eq_mul_inv] at hbound
  exact (le_div_iff₀ htpos).mp hbound

end

end MOC
