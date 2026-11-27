import MOC.ConicSpectralReductions
import MOC.FourMinorTransport
import MOC.HermitianByNormalFourProof

/-! Testing antipodal first spectra suffices for the determinant inclusion in order four.
Two entries can be fixed at `1` and `-1`. The other two are `z` and `-z`, where the
parameter `z` can be restricted to the open upper half of the unit disk. -/

open Matrix

namespace MOC

noncomputable section

/-- Two antipodal pairs with the first pair fixed at `1` and `-1`. -/
def fourAntipodalSpectrum (z : ℂ) : Fin 4 → ℂ := ![1, -1, z, -z]

/-- Every distinct order-four list has an antipodal chart in its original label order.
The two specified pairs of labels stay paired, and the map has no pole on the list. -/
theorem exists_four_fractional_antipodal (a : Fin 4 → ℂ) (ha : Function.Injective a) :
    ∃ α β γ δ z : ℂ, α * δ - β * γ ≠ 0 ∧
      (∀ i, γ * a i + δ ≠ 0) ∧ fractionalMap α β γ δ ∘ a = fourAntipodalSpectrum z := by
  let x (i : Fin 4) := a i - a 0
  let y (i : Fin 4) := a i - a 1
  have hx₀ : x 0 = 0 := sub_self _
  have hy₁ : y 1 = 0 := sub_self _
  have hx (i : Fin 4) (hi : i ≠ 0) : x i ≠ 0 := sub_ne_zero.mpr (ha.ne hi)
  have hy (i : Fin 4) (hi : i ≠ 1) : y i ≠ 0 := sub_ne_zero.mpr (ha.ne hi)
  have hdenom : y 2 * y 3 ≠ 0 := mul_ne_zero (hy 2 (by decide)) (hy 3 (by decide))
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq
    (x 2 * x 3 / (y 2 * y 3)) (n := 2) two_pos
  have hs₀ : s ≠ 0 := by
    intro h
    exact div_ne_zero (mul_ne_zero (hx 2 (by decide)) (hx 3 (by decide))) hdenom
      (by simpa only [h, zero_pow two_ne_zero] using hs.symm)
  have hcross : x 2 * x 3 = s ^ 2 * (y 2 * y 3) := ((eq_div_iff hdenom).mp hs).symm
  have havoid (i j : Fin 4) (hij : i ≠ j) (hi : i ≠ 1)
      (hprod : x i * x j = s ^ 2 * (y i * y j)) : s * y i - x i ≠ 0 := by
    intro he
    have hxi : s * y i = x i := sub_eq_zero.mp he
    have hxj : x j = s * y j := by
      apply mul_left_cancel₀ (mul_ne_zero hs₀ (hy i hi))
      calc
        (s * y i) * x j = x i * x j := by rw [hxi]
        _ = s ^ 2 * (y i * y j) := hprod
        _ = (s * y i) * (s * y j) := by ring
    have hz : (a i - a j) * (a 1 - a 0) = 0 := by
      dsimp only [x, y] at hxi hxj
      linear_combination (a j - a 1) * hxi + (a i - a 1) * hxj
    exact (mul_ne_zero (sub_ne_zero.mpr (ha.ne hij))
      (sub_ne_zero.mpr (ha.ne (show (1 : Fin 4) ≠ 0 by decide)))) hz
  let α := s + 1
  let β := -(s * a 1) - a 0
  let γ := s - 1
  let δ := -(s * a 1) + a 0
  have hnum (i : Fin 4) : α * a i + β = s * y i + x i := by
    dsimp only [α, β, x, y]
    ring
  have hden (i : Fin 4) : γ * a i + δ = s * y i - x i := by
    dsimp only [γ, δ, x, y]
    ring
  have hregular (i : Fin 4) : s * y i - x i ≠ 0 := by
    fin_cases i
    · change s * y 0 - x 0 ≠ 0
      rw [hx₀, sub_zero]
      exact mul_ne_zero hs₀ (hy 0 (by decide))
    · change s * y 1 - x 1 ≠ 0
      rw [hy₁, mul_zero, zero_sub]
      exact neg_ne_zero.mpr (hx 1 (by decide))
    · exact havoid 2 3 (by decide) (by decide) hcross
    · apply havoid 3 2 (by decide) (by decide)
      simpa only [mul_comm (x 3) (x 2), mul_comm (y 3) (y 2)] using hcross
  have hdet : α * δ - β * γ ≠ 0 := by
    rw [show α * δ - β * γ = 2 * s * (a 0 - a 1) by
      dsimp only [α, β, γ, δ]
      ring]
    exact mul_ne_zero (mul_ne_zero (by norm_num) hs₀)
      (sub_ne_zero.mpr (ha.ne (show (0 : Fin 4) ≠ 1 by decide)))
  have hf (i : Fin 4) : fractionalMap α β γ δ (a i) = (s * y i + x i) / (s * y i - x i) := by
    unfold fractionalMap
    rw [hnum, hden]
  have h₀ : fractionalMap α β γ δ (a 0) = 1 := by
    rw [hf, hx₀, add_zero, sub_zero,
      div_self (mul_ne_zero hs₀ (hy 0 (by decide)))]
  have h₁ : fractionalMap α β γ δ (a 1) = -1 := by
    rw [hf, hy₁, mul_zero, zero_add, zero_sub, div_neg, div_self (hx 1 (by decide))]
  have h₂₃ : fractionalMap α β γ δ (a 3) = -fractionalMap α β γ δ (a 2) := by
    apply eq_neg_iff_add_eq_zero.mpr
    rw [hf 3, hf 2]
    field_simp [hregular 3, hregular 2] <;> linear_combination -2 * hcross
  have hreg (i : Fin 4) : γ * a i + δ ≠ 0 := by
    rw [hden]
    exact hregular i
  refine ⟨α, β, γ, δ, fractionalMap α β γ δ (a 2), hdet, hreg, ?_⟩
  funext i
  fin_cases i
  · exact h₀
  · exact h₁
  · rfl
  · exact h₂₃

/-- On the normalized list, the generalized-circle cases are exactly the real axis
and the unit circle of the parameter plane. -/
theorem fourAntipodalSpectrum_generalizedCircle_iff (z : ℂ) :
    SpectrumOnGeneralizedCircle (fourAntipodalSpectrum z) ↔ z.im = 0 ∨ ‖z‖ = 1 := by
  constructor
  · rintro ⟨q, u, v, c, hnonzero, h⟩
    have he (i : Fin 4) (w : ℂ) (hw : fourAntipodalSpectrum z i = w) :
        q * Complex.normSq w - 2 * (u * w.re + v * w.im) + c = 0 := by
      have hi := h i
      rw [hw] at hi
      exact hi
    have h₀ := he 0 1 rfl
    have h₁ := he 1 (-1) rfl
    have h₂ := he 2 z rfl
    have h₃ := he 3 (-z) rfl
    simp only [Complex.normSq_one, Complex.one_re, Complex.one_im,
      mul_one, mul_zero, add_zero] at h₀
    simp only [Complex.normSq_neg, Complex.normSq_one, Complex.neg_re, Complex.neg_im,
      Complex.one_re, Complex.one_im, neg_zero, mul_one, mul_zero, mul_neg, add_zero] at h₁
    simp only [Complex.normSq_neg, Complex.neg_re, Complex.neg_im] at h₃
    have hu : u = 0 := by linarith only [h₀, h₁]
    have hc : c = -q := by linarith only [h₀, hu]
    by_cases hz : z.im = 0
    · exact Or.inl hz
    · right
      have hvprod : v * z.im = 0 := by
        linear_combination (h₃ - h₂) / 4 - z.re * hu
      have hv : v = 0 := (mul_eq_zero.mp hvprod).resolve_right hz
      have hq : q ≠ 0 := by simpa [hu, hv] using hnonzero
      have hnormprod : q * (Complex.normSq z - 1) = 0 := by
        simp only [hu, hv, zero_mul, add_zero, sub_zero, hc] at h₂
        linear_combination h₂
      have hnorm : ‖z‖ ^ 2 = (1 : ℝ) ^ 2 := by
        rw [Complex.sq_norm, one_pow]
        exact sub_eq_zero.mp ((mul_eq_zero.mp hnormprod).resolve_left hq)
      exact le_antisymm ((sq_le_sq₀ (norm_nonneg z) zero_le_one).mp hnorm.le)
        ((sq_le_sq₀ zero_le_one (norm_nonneg z)).mp hnorm.ge)
  · rintro (hz | hz)
    · apply spectrumOnGeneralizedCircle_of_line _ 0 1 0 (Or.inr one_ne_zero)
      intro i
      fin_cases i <;> simp [fourAntipodalSpectrum, hz]
    · apply spectrumOnGeneralizedCircle_of_circle _ 0 1
      intro i
      fin_cases i <;> simp [fourAntipodalSpectrum, ← Complex.sq_norm, hz]

private theorem holds_fourAntipodal_of_halfDisk_test
    (h : ∀ (z : ℂ), 0 < z.im → ‖z‖ < 1 → ∀ (b : Fin 4 → ℂ)
      (U : Matrix (Fin 4) (Fin 4) ℂ), IsUnitary U → Holds (fourAntipodalSpectrum z) b U)
    (z : ℂ) (hz : ‖z‖ < 1) (b : Fin 4 → ℂ) (U : Matrix (Fin 4) (Fin 4) ℂ)
    (hU : IsUnitary U) : Holds (fourAntipodalSpectrum z) b U := by
  rcases lt_trichotomy z.im 0 with hneg | hzero | hpos
  · let e : Equiv.Perm (Fin 4) := Equiv.swap 2 3
    have hA : fourAntipodalSpectrum z ∘ e = fourAntipodalSpectrum (-z) := by
      have h₀ : e 0 = 0 := by decide
      have h₁ : e 1 = 1 := by decide
      have h₂ : e 2 = 3 := by decide
      have h₃ : e 3 = 2 := by decide
      funext i
      fin_cases i <;> simp [Function.comp_apply, h₀, h₁, h₂, h₃, fourAntipodalSpectrum]
    apply (holds_reindex_iff e (Equiv.refl (Fin 4)) _ b U).mp
    rw [hA]
    refine h (-z) ?_ (by rwa [norm_neg]) b _ (unitary_reindex e (Equiv.refl (Fin 4)) hU)
    rwa [Complex.neg_im, neg_pos]
  · exact holds_four_of_generalized_circle _ b U hU
      (Or.inl ((fourAntipodalSpectrum_generalizedCircle_iff z).mpr (Or.inl hzero)))
  · exact h z hpos hz b U hU

/-- For order four, test only the normalized antipodal first lists with the parameter
in the open upper half of the unit disk. The second list remains arbitrary. -/
theorem conjecture_four_iff_antipodal_halfDisk :
    Conjecture (Fin 4) ↔
      ∀ (z : ℂ), 0 < z.im → ‖z‖ < 1 → ∀ (b : Fin 4 → ℂ)
        (U : Matrix (Fin 4) (Fin 4) ℂ), IsUnitary U → Holds (fourAntipodalSpectrum z) b U := by
  constructor
  · exact fun h z _ _ b U hU => h (fourAntipodalSpectrum z) b U hU
  · intro h
    apply conjecture_four_iff_noncircular.mpr
    intro a b U hU ha _ _ _
    obtain ⟨α, β, γ, δ, z, hdet, hreg, hchart⟩ := exists_four_fractional_antipodal a ha
    apply holds_of_fractional_spectral_test a b U hU α β γ δ hdet hreg
    intro c
    rw [hchart]
    rcases lt_trichotomy ‖z‖ 1 with hlt | heq | hgt
    · exact holds_fourAntipodal_of_halfDisk_test h z hlt c U hU
    · exact holds_four_of_generalized_circle _ c U hU
        (Or.inl ((fourAntipodalSpectrum_generalizedCircle_iff z).mpr (Or.inr heq)))
    · have hz : z ≠ 0 := by
        intro hz₀
        rw [hz₀, norm_zero] at hgt
        norm_num at hgt
      let e : Equiv.Perm (Fin 4) := (Equiv.swap 0 2).trans (Equiv.swap 1 3)
      let e' := Equiv.refl (Fin 4)
      let V := U.submatrix e e'
      have hV : IsUnitary V := unitary_reindex e e' hU
      apply (holds_reindex_iff e e' _ c U).mp
      apply (holds_fractional_iff _ _ V hV z⁻¹ 0 0 1
        (by simpa using inv_ne_zero hz) (fun _ => by simp) (fun _ => by simp)).mp
      have hA : fractionalMap z⁻¹ 0 0 1 ∘ (fourAntipodalSpectrum z ∘ e) =
          fourAntipodalSpectrum z⁻¹ := by
        have h₀ : e 0 = 2 := by decide
        have h₁ : e 1 = 3 := by decide
        have h₂ : e 2 = 0 := by decide
        have h₃ : e 3 = 1 := by decide
        funext i
        fin_cases i <;> simp [Function.comp_apply, h₀, h₁, h₂, h₃, fractionalMap,
          fourAntipodalSpectrum, inv_mul_cancel₀ hz]
      rw [hA]
      exact holds_fourAntipodal_of_halfDisk_test h z⁻¹
        (by rw [norm_inv]; exact inv_lt_one_of_one_lt₀ hgt) _ V hV

/-- The normalized half-disk test suffices with real orthogonal mixers. -/
theorem conjecture_four_iff_antipodal_halfDisk_orthogonal :
    Conjecture (Fin 4) ↔
      ∀ (z : ℂ), 0 < z.im → ‖z‖ < 1 → ∀ (b : Fin 4 → ℂ)
        (O : Matrix.orthogonalGroup (Fin 4) ℝ),
        Holds (fourAntipodalSpectrum z) b (Complex.ofRealHom.mapMatrix O.val) := by
  constructor
  · exact fun h z _ _ b O => h (fourAntipodalSpectrum z) b _ (isUnitary_ofReal_orthogonal O)
  · intro h
    apply conjecture_four_iff_antipodal_halfDisk.mpr
    intro z him hnorm b U hU
    obtain ⟨O₀, O₁, θ, hθ, hθ', hm⟩ := four_minor_two_point U hU
    exact holds_of_subsetMinorSq_convex_combination (fourAntipodalSpectrum z) b hU
      (isUnitary_ofReal_orthogonal O₀) (isUnitary_ofReal_orthogonal O₁) θ hθ hθ' hm
      (h z him hnorm b O₀) (h z him hnorm b O₁)

end

end MOC
