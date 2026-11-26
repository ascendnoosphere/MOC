import MOC.GeneralizedSpectralCircles

open Matrix

namespace MOC

noncomputable section

private theorem exists_reciprocal_line_of_circle_equation
    (q u v k : ℝ) (r : ℂ) (h : q ≠ 0 ∨ u ≠ 0 ∨ v ≠ 0)
    (hr : q * Complex.normSq (-r) - 2 * (u * (-r).re + v * (-r).im) + k = 0)
    (hex : ∃ z : ℂ, z + r ≠ 0 ∧ q * Complex.normSq z - 2 * (u * z.re + v * z.im) + k = 0) :
    ∃ c d : ℂ, d ≠ 0 ∧ ∀ z : ℂ, z + r ≠ 0 →
      (q * Complex.normSq z - 2 * (u * z.re + v * z.im) + k = 0 ↔
        ∃ s : ℝ, (z + r)⁻¹ = c + d * (s : ℂ)) := by
  let A := u + q * r.re
  let B := v + q * r.im
  let m : ℂ := ⟨A, B⟩
  have hshift (z : ℂ) :
      q * Complex.normSq (z + r) - 2 * (A * (z + r).re + B * (z + r).im) =
        q * Complex.normSq z - 2 * (u * z.re + v * z.im) + k := by
    dsimp only [A, B]
    simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.neg_re,
      Complex.neg_im] at hr ⊢
    linear_combination -hr
  have hm : m ≠ 0 := by
    intro hzero
    have hA : A = 0 := congrArg Complex.re hzero
    have hB : B = 0 := congrArg Complex.im hzero
    obtain ⟨z, hz, hEq⟩ := hex
    have hs := hshift z
    rw [hEq, hA, hB, zero_mul, zero_mul, add_zero, mul_zero, sub_zero] at hs
    have hq : q = 0 := (mul_eq_zero.mp hs).resolve_right (Complex.normSq_pos.mpr hz).ne'
    have hu : u = 0 := by simpa [A, hq] using hA
    have hv : v = 0 := by simpa [B, hq] using hB
    simp [hq, hu, hv] at h
  let c : ℂ := m⁻¹ * (1 / 2 * (q : ℂ))
  let d : ℂ := m⁻¹ * Complex.I
  have hd : d ≠ 0 := mul_ne_zero (inv_ne_zero hm) Complex.I_ne_zero
  have hrealLine (w : ℂ) : (m * w).re = q / 2 ↔ ∃ s : ℝ, w = c + d * (s : ℂ) := by
    have hcast : ((q / 2 : ℝ) : ℂ) = 1 / 2 * (q : ℂ) := by push_cast; ring
    constructor
    · intro hw
      refine ⟨(m * w).im, ?_⟩
      calc
        w = m⁻¹ * (m * w) := by rw [← mul_assoc, inv_mul_cancel₀ hm, one_mul]
        _ = m⁻¹ * (((m * w).re : ℂ) + ((m * w).im : ℂ) * Complex.I) := by
          rw [Complex.re_add_im]
        _ = _ := by rw [hw, hcast]; dsimp [c, d]; ring
    · rintro ⟨s, rfl⟩
      have hc : m * c = ((q / 2 : ℝ) : ℂ) := by
        rw [show c = m⁻¹ * (1 / 2 * (q : ℂ)) from rfl, ← mul_assoc,
          mul_inv_cancel₀ hm, one_mul, hcast]
      have hmd : m * d = Complex.I := by
        rw [show d = m⁻¹ * Complex.I from rfl, ← mul_assoc, mul_inv_cancel₀ hm, one_mul]
      rw [mul_add, ← mul_assoc m d, hc, hmd, Complex.add_re, Complex.ofReal_re,
        Complex.I_mul_re, Complex.ofReal_im, neg_zero, add_zero]
  refine ⟨c, d, hd, fun z hz => ?_⟩
  rw [← hrealLine, ← hshift]
  let w := z + r
  have hns : Complex.normSq w ≠ 0 := (Complex.normSq_pos.mpr hz).ne'
  have hre : (m * w⁻¹).re = (A * w.re + B * w.im) / Complex.normSq w := by
    change A * (w⁻¹).re - B * (w⁻¹).im = _
    rw [Complex.inv_re, Complex.inv_im]
    field_simp [hns]
  rw [hre, div_eq_iff hns]
  change q * Complex.normSq w - 2 * (A * w.re + B * w.im) = 0 ↔ _
  constructor <;> intro hz'
  · linear_combination (-1 / 2) * hz'
  · linear_combination -2 * hz'

/-- A pole on a generalized circle gives a reciprocal line. Replacement
labels on that line stay on the original circle together with untouched labels. -/
theorem exists_reciprocal_chart_preserving_generalizedCircle {n : ℕ} {κ : Type*}
    (h : Fin (n + 1) → ℂ) (g : κ → ℂ) (r : ℂ)
    (hcircle : SpectrumOnGeneralizedCircle
      (Sum.elim h (Sum.elim g (fun _ : Unit => -r))))
    (hh : ∀ i, h i + r ≠ 0) :
    ∃ c d : ℂ, d ≠ 0 ∧ (∀ i, ∃ s : ℝ, (h i + r)⁻¹ = c + d * (s : ℂ)) ∧
      ∀ {m : ℕ} (a : Fin m → ℂ), (∀ i, a i + r ≠ 0) →
        (∀ i, ∃ s : ℝ, (a i + r)⁻¹ = c + d * (s : ℂ)) →
        SpectrumOnGeneralizedCircle (Sum.elim a g) := by
  obtain ⟨q, u, v, k, hn, hs⟩ := hcircle
  have hEq : ∀ i, q * Complex.normSq (h i) - 2 * (u * (h i).re + v * (h i).im) + k = 0 :=
    fun i => hs (Sum.inl i)
  obtain ⟨c, d, hd, hline⟩ := exists_reciprocal_line_of_circle_equation q u v k r hn
    (hs (Sum.inr (Sum.inr ()))) ⟨h 0, hh 0, hEq 0⟩
  refine ⟨c, d, hd, fun i => (hline (h i) (hh i)).mp (hEq i), ?_⟩
  intro m a ha hline'
  refine ⟨q, u, v, k, hn, ?_⟩
  rintro (i | j)
  · exact (hline (a i) (ha i)).mpr (hline' i)
  · exact hs (Sum.inr (Sum.inl j))

/-- A circle or line through the pole either admits an injective pole path
or places every active label at the pole. -/
theorem exists_generalizedCircle_pole_path_or_constant {n : ℕ} {κ : Type*}
    (h : Fin (n + 1) → ℂ) (g : κ → ℂ) (r : ℂ)
    (hcircle : SpectrumOnGeneralizedCircle
      (Sum.elim h (Sum.elim g (fun _ : Unit => -r)))) :
    (∀ i, h i = -r) ∨
      ∃ P : ℝ → ℂ, Continuous P ∧ Function.Injective P ∧ P 0 = r ∧
        ∀ t : ℝ, SpectrumOnGeneralizedCircle
          (Sum.elim h (Sum.elim g (fun _ : Unit => -P t))) := by
  obtain ⟨q, u, v, k, hn, hs⟩ := hcircle
  let f (z : ℂ) := q * Complex.normSq z - 2 * (u * z.re + v * z.im) + k
  have hEq : ∀ i, f (h i) = 0 := fun i => hs (Sum.inl i)
  have hr : f (-r) = 0 := hs (Sum.inr (Sum.inr ()))
  have hreplace (z : ℂ) (hz : f z = 0) :
      SpectrumOnGeneralizedCircle (Sum.elim h (Sum.elim g (fun _ : Unit => z))) := by
    refine ⟨q, u, v, k, hn, ?_⟩
    rintro (i | j | j)
    · exact hs (Sum.inl i)
    · exact hs (Sum.inr (Sum.inl j))
    · exact hz
  by_cases hq : q = 0
  · let d : ℂ := ⟨v, -u⟩
    have hd : d ≠ 0 := by
      intro hzero
      have hv : v = 0 := congrArg Complex.re hzero
      have hu : u = 0 := neg_eq_zero.mp (congrArg Complex.im hzero)
      simp [hq, hu, hv] at hn
    let P (t : ℝ) := -(-r + d * (t : ℂ))
    have hp : Continuous P :=
      (continuous_const.add (continuous_const.mul Complex.continuous_ofReal)).neg
    have hpinj : Function.Injective P := fun _ _ h =>
      Complex.ofReal_injective (mul_left_cancel₀ hd (add_left_cancel (neg_injective h)))
    refine Or.inr ⟨P, hp, hpinj, by simp [P], fun t => hreplace (-P t) ?_⟩
    change f (-(-(-r + d * (t : ℂ)))) = 0
    rw [neg_neg]
    dsimp only [f] at hr ⊢
    simp only [hq, zero_mul] at hr
    simp only [hq, zero_mul, Complex.add_re, Complex.add_im, Complex.mul_re,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, d]
    linear_combination hr
  · let o : ℂ := ⟨u / q, v / q⟩
    have hform (z : ℂ) :
        f z = q * Complex.normSq (z - o) + k - q * Complex.normSq o := by
      simp only [f, Complex.normSq_apply, Complex.sub_re, Complex.sub_im, o]
      field_simp [hq]
      ring
    by_cases ho : -r - o = 0
    · left
      intro i
      have hi := hEq i
      rw [hform (h i)] at hi
      rw [hform (-r), ho, Complex.normSq_zero, mul_zero, zero_add] at hr
      have hz : q * Complex.normSq (h i - o) = 0 := by linear_combination hi - hr
      have hei := sub_eq_zero.mp (Complex.normSq_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left hq))
      exact hei.trans (sub_eq_zero.mp ho).symm
    · let P (t : ℝ) := -(o + (-r - o) * circleRotation t)
      have hp : Continuous P :=
        (continuous_const.add (continuous_const.mul continuous_circleRotation)).neg
      have hpinj : Function.Injective P := fun _ _ h =>
        circleRotation_injective (mul_left_cancel₀ ho (add_left_cancel (neg_injective h)))
      refine Or.inr ⟨P, hp, hpinj, by simp [P, circleRotation], fun t => hreplace (-P t) ?_⟩
      rw [hform (-P t), show -P t - o = (-r - o) * circleRotation t by simp [P],
        Complex.normSq_mul, circleRotation_normSq, mul_one, ← hform (-r)]
      exact hr

end

end MOC
