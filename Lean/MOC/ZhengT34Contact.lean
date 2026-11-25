import MOC.FourContactCertificate
import MOC.RealizableContactConsequences
import MOC.MatchingRectangleSupport

/-! Two contact rectangles in the order-four T34 pattern of Zheng
(preprint DOI: 10.13140/RG.2.2.36790.25923, Appendices D and E).
The assignment products below use the paper's one-line labels, with
the two spectra interchanged relative to `matchingProduct`. -/

namespace MOC.ZhengT34Contact

private abbrev P := Equiv.Perm (Fin 4)

def p₂ : P := Equiv.swap 1 2
def p₃ : P := p₂ * Equiv.swap 2 3
def p₅ : P := p₃ * Equiv.swap 1 2
def p₉ : P := p₃ * Equiv.swap 0 3
def p₁₁ : P := p₃ * Equiv.swap 1 2 * Equiv.swap 0 3
def p₁₂ : P := p₂ * Equiv.swap 0 1
def p₁₃ : P := p₂ * Equiv.swap 2 3 * Equiv.swap 0 1

/-- In the zero-height stratum, the contacts at labels 3, 5, 9
force contact 11. This uses only a single disjoint swap rectangle. -/
theorem contact_eleven_of_zero_height
    (a b : Fin 4 → ℂ) (η : ℂ) (hη : η ≠ 0)
    (hn : ∀ σ, matchingProduct b a σ ≠ 0)
    (h₃ : (η * matchingProduct b a p₃).re = 0)
    (h₅ : (η * matchingProduct b a p₅).re = 0)
    (h₉ : (η * matchingProduct b a p₉).re = 0) :
    (η * matchingProduct b a p₁₁).re = 0 :=
  matching_disjoint_swaps_contact_of_zero_height b a η p₃ 1 2 0 3
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (mul_ne_zero hη (hn p₃)) h₃ h₅ h₉

/-- Adding contact 13 to T34 closes the rectangle at labels 2, 3, 12,
13, so that the support height is zero and label 11 is active as well.
In Zheng's retained ray basis, the gap at 11 is the mixed coefficient,
so this eliminates that coefficient on this wall. -/
theorem height_zero_and_contact_eleven
    (a b : Fin 4 → ℂ) (ha : Function.Injective a) (hb : Function.Injective b)
    (η : ℂ) (hη : η ≠ 0) (H : ℝ)
    (hn : ∀ σ, matchingProduct b a σ ≠ 0)
    (h₂ : (η * matchingProduct b a p₂).re = H)
    (h₃ : (η * matchingProduct b a p₃).re = H)
    (h₅ : (η * matchingProduct b a p₅).re = H)
    (h₉ : (η * matchingProduct b a p₉).re = H)
    (h₁₂ : (η * matchingProduct b a p₁₂).re = H)
    (h₁₃ : (η * matchingProduct b a p₁₃).re = H) :
    H = 0 ∧ (η * matchingProduct b a p₁₁).re = 0 := by
  have hd : ∀ i : Fin 4, Equiv.swap 2 3 i = i ∨ Equiv.swap 0 1 i = i := by
    intro i
    fin_cases i <;> decide
  have h0 := matchingProduct_disjoint_swap_rectangle_height_zero_of_simple
    b a hb ha hn p₂ 2 3 0 1 (by decide) (by decide) hd η hη H h₂ h₃ h₁₂ h₁₃
  exact ⟨h0, contact_eleven_of_zero_height a b η hη hn
    (h₃.trans h0) (h₅.trans h0) (h₉.trans h0)⟩

end MOC.ZhengT34Contact

namespace MOC.ZhengT34Contact

noncomputable section

/-- A positive coefficient grouping of the radial equation at the T34
boundary where ordinary coefficient `b` vanishes. The Hessian factorization
that supplies this equation is a separate input, not assumed here. -/
def wallBPolynomial (p c q s a : ℝ) : ℝ :=
  let u := q + s + 1
  let v := s + 1
  let d := (p + 1) * (q + 1) * u + c * v * (p * (q + 1) + 1)
  c * u * a ^ 2 + (d - c * q * (q + s)) * a + d + c * q * (q * s + s + 1)

/-- The `b=0` radial equation forces the two remaining Gram coefficients
to be positive and the central coefficient to reach the reciprocal bound. -/
theorem wallB_reciprocal_threshold
    {p c q s a : ℝ} (hp : 0 ≤ p) (hc : 0 ≤ c) (hq : 0 ≤ q) (hs : 0 ≤ s) (ha : 0 ≤ a)
    (hroot : wallBPolynomial p c q s a = 0) :
    0 < c ∧ 0 < q ∧ 1 / c + 1 / q ≤ a := by
  have hc' : 0 < c := by
    by_contra! hn
    have he : c = 0 := le_antisymm hn hc
    rw [he] at hroot
    have hpos : 0 < wallBPolynomial p 0 q s a := by
      unfold wallBPolynomial
      simp only [zero_mul, zero_add, sub_zero, add_zero]
      positivity
    exact hpos.ne' hroot
  have hq' : 0 < q := by
    by_contra! hn
    have he : q = 0 := le_antisymm hn hq
    rw [he] at hroot
    have hpos : 0 < wallBPolynomial p c 0 s a := by
      unfold wallBPolynomial
      simp only [zero_mul, mul_zero, zero_add, sub_zero, add_zero]
      positivity
    exact hpos.ne' hroot
  refine ⟨hc', hq', ?_⟩
  let u := q + s + 1
  let v := s + 1
  let d := (p + 1) * (q + 1) * u + c * v * (p * (q + 1) + 1)
  let A := 1 / c + 1 / q
  have hu : 0 < u := by dsimp [u]; positivity
  have hd : 0 < d := by dsimp [d,v]; positivity
  have hA : 0 < A := by dsimp [A]; positivity
  have hcq : 0 < c * q ^ 2 := mul_pos hc' (pow_pos hq' _)
  have h₀ : 0 < d + c * q * (q * s + s + 1) := by positivity
  have hdef : (q + 1) * u + c * v ≤ d := by
    dsimp [d]
    nlinarith [mul_nonneg hp (show 0 ≤ (q+1)*u+c*v*(q+1) by
      dsimp [v]; positivity)]
  have h₁ : 0 ≤ 2 * (d + c*q*(q*s+s+1)) + (d-c*q*(q+s))*A := by
    have hdiff : 0 ≤ (q + 1) * u - q * (q + s) := by
      dsimp [u]
      nlinarith
    have hcDiff : 0 ≤ c * (v + 2*q*(q*s+s+1) - (q+s)) := by
      apply mul_nonneg hc
      dsimp [v]
      nlinarith [mul_nonneg (sq_nonneg q) hs, mul_nonneg hq hs]
    have he : c*q*(q+s)*A = c*(q+s)+q*(q+s) := by
      dsimp [A]
      field_simp [hc'.ne',hq'.ne']
      ring
    nlinarith [mul_nonneg hd.le hA.le]
  have h₂ : 0 ≤ c*u*A^2+(d-c*q*(q+s))*A+d+c*q*(q*s+s+1) := by
    have hnonneg : 0 ≤ c*q^2*(d - ((q+1)*u+c*v))*(A+1) :=
      mul_nonneg (mul_nonneg hcq.le (sub_nonneg.mpr hdef))
        (add_nonneg hA.le zero_le_one)
    have he :
        c*q^2*(c*u*A^2+(d-c*q*(q+s))*A+d+c*q*(q*s+s+1)) =
          c*q^2*(d - ((q+1)*u+c*v))*(A+1) +
          c^2*(q+1)^2*(s*((q-1/2)^2+3/4)+1) +
          c*3*q*(q+1)*u + q^2*(q+2)*u := by
      dsimp [u,v,A]
      field_simp [hc'.ne',hq'.ne']
      ring
    apply nonneg_of_mul_nonneg_right _ hcq
    rw [he]
    positivity
  have hroot' : c*u*a^2+(d-c*q*(q+s))*a+(d+c*q*(q*s+s+1)) = 0 := by
    simpa [wallBPolynomial,d,u,v,add_assoc] using hroot
  change A ≤ a
  exact contact_bernstein_threshold_le_of_root ha h₀ h₁ (by simpa only [add_assoc] using h₂) hroot'

end

end MOC.ZhengT34Contact
