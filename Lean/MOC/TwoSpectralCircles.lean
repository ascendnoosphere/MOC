import MOC.ConcentricPerturbation
import MOC.DruryHermitianPencil
import MOC.GeneralizedSpectralCircles

/-! The determinant inclusion for two spectra on arbitrary circles. -/

open Matrix

namespace MOC

private theorem holds_of_normalized_circle_centers {n : ℕ}
    (a b : Fin n → ℂ) (A B : ℝ) (hA : 0 < A) (hB : 0 < B)
    (ha : ∀ i, Complex.normSq (a i) = A) (hb : ∀ i, Complex.normSq (-b i - 1) = B)
    (U : Matrix (Fin n) (Fin n) ℂ) (hU : IsUnitary U) : Holds a b U := by
  let x := (1 + A - B) / 2
  let D := A - x ^ 2
  have hcenter : (x - 1) ^ 2 + D = B := by dsimp only [D, x]; ring
  rcases lt_trichotomy D 0 with hD | hD | hD
  · let r := Real.sqrt A
    let s := Real.sqrt B
    have hr : 0 < r := Real.sqrt_pos_of_pos hA
    have hs : 0 < s := Real.sqrt_pos_of_pos hB
    have hr₂ : r ^ 2 = A := Real.sq_sqrt hA.le
    have hs₂ : s ^ 2 = B := Real.sq_sqrt hB.le
    have hfactor : (1 - (r + s) ^ 2) * (1 - (r - s) ^ 2) = -4 * D := by
      dsimp only [D, x]
      rw [← hr₂, ← hs₂]
      ring
    have hproduct : 0 < (1 - (r + s) ^ 2) * (1 - (r - s) ^ 2) := by rw [hfactor]; linarith
    have hsep : r + s < 1 ∨ 1 < |r - s| := by
      by_cases h : r + s < 1
      · exact Or.inl h
      · have hsum : 1 ≤ (r + s) ^ 2 := by
          simpa only [one_pow] using pow_le_pow_left₀ zero_le_one (le_of_not_gt h) 2
        have hdiff : 1 < (r - s) ^ 2 := sub_neg.mp (neg_of_mul_pos_right hproduct (sub_nonpos.mpr hsum))
        have hdiff' : (1 : ℝ) ^ 2 < (r - s) ^ 2 := by simpa only [one_pow] using hdiff
        exact Or.inr (by simpa only [abs_one] using sq_lt_sq.mp hdiff')
    exact holds_of_disjoint_circles a b U hU 0 1 one_ne_zero r s hr hs hsep
      (fun i => by simpa only [sub_zero, div_one, hr₂] using ha i)
      (fun i => by simpa only [sub_zero, div_one, hs₂] using hb i)
  · have hxA : x ^ 2 = A := by dsimp only [D] at hD; linarith
    have hxB : (x - 1) ^ 2 = B := by rwa [hD, add_zero] at hcenter
    have hx₀ : x ≠ 0 := by intro h; rw [h, zero_pow (by decide : 2 ≠ 0)] at hxA; exact hA.ne' hxA.symm
    have hx₁ : x ≠ 1 := by
      intro h
      rw [h, sub_self, zero_pow (by decide : 2 ≠ 0)] at hxB
      exact hB.ne' hxB.symm
    let p : ℂ := x
    let t := (1 - x) / (-x)
    have hp : p ≠ 0 := Complex.ofReal_ne_zero.mpr hx₀
    have ht : t ≠ 0 := div_ne_zero (sub_ne_zero.mpr hx₁.symm) (neg_ne_zero.mpr hx₀)
    have htv : (t : ℂ) * (-p) = 1 - p := by
      dsimp only [t, p]
      rw [Complex.ofReal_div, Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_neg,
        div_mul_cancel₀ _ (neg_ne_zero.mpr (Complex.ofReal_ne_zero.mpr hx₀))]
    have hpA : Complex.normSq (-p) = A := by
      simpa only [p, Complex.normSq_neg, Complex.normSq_ofReal, ← pow_two] using hxA
    have hpB : Complex.normSq (1 - p) = B := by
      rw [show 1 - p = -((x - 1 : ℝ) : ℂ) by simp [p, neg_sub], Complex.normSq_neg,
        Complex.normSq_ofReal, ← pow_two, hxB]
    apply holds_of_tangent_circles a b p (-p) t (neg_ne_zero.mpr hp) ht _ _ U hU
    · intro i
      rw [show a i - p - -p = a i by ring, hpA]
      exact ha i
    · intro i
      rw [htv, show -b i - p - (1 - p) = -b i - 1 by ring, hpB]
      exact hb i
  · let y := Real.sqrt D
    let p := Complex.mk x y
    let q := Complex.mk x (-y)
    have hy : 0 < y := Real.sqrt_pos_of_pos hD
    have hy₂ : y ^ 2 = D := Real.sq_sqrt hD.le
    have hpq : p ≠ q := by
      intro h
      have him : y = -y := congrArg Complex.im h
      linarith
    have hpA : Complex.normSq p = A := by
      simp only [p, Complex.normSq_apply, ← pow_two, hy₂]
      dsimp only [D]
      ring
    have hqA : Complex.normSq q = A := by
      simp only [q, Complex.normSq_apply, ← pow_two, neg_sq, hy₂]
      dsimp only [D]
      ring
    have hpB : Complex.normSq (p - 1) = B := by
      simpa only [p, Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.one_re,
        Complex.one_im, sub_zero, ← pow_two, hy₂] using hcenter
    have hqB : Complex.normSq (q - 1) = B := by
      simpa only [q, Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.one_re,
        Complex.one_im, sub_zero, ← pow_two, neg_sq, hy₂] using hcenter
    exact holds_of_intersecting_circles_of_lines a b p q 0 1 hpq
      (by simpa only [sub_zero] using hpA.trans hqA.symm) (hpB.trans hqB.symm)
      (fun i => by simpa only [sub_zero, hqA] using ha i)
      (fun i => (hb i).trans hqB.symm) U hU
      (fun x y z w => by simpa only [add_zero] using holds_of_affine_spectral_lines x y z w 0 0 U hU)

/-- If each spectrum lies on a circle, the determinant belongs to the
matching hull. The two signed spectral circles may have independent centers
and radii, and a zero radius is allowed. -/
theorem holds_of_circular_spectra {n : ℕ} (a b : Fin n → ℂ) (u v : ℂ) (A B : ℝ)
    (ha : ∀ i, Complex.normSq (a i - u) = A) (hb : ∀ i, Complex.normSq (-b i - v) = B)
    (U : Matrix (Fin n) (Fin n) ℂ) (hU : IsUnitary U) : Holds a b U := by
  by_cases hn : n ≤ 3
  · exact conjecture_le_three hn a b U hU
  let i₀ : Fin n := ⟨0, by omega⟩
  have hA₀ : 0 ≤ A := ha i₀ ▸ Complex.normSq_nonneg (a i₀ - u)
  have hB₀ : 0 ≤ B := hb i₀ ▸ Complex.normSq_nonneg (-b i₀ - v)
  by_cases hA : A = 0
  · have he : a = fun _ => u := funext fun i =>
      sub_eq_zero.mp (Complex.normSq_eq_zero.mp ((ha i).trans hA))
    apply (holds_swap_iff a b hU).mp
    have hUs : IsUnitary Uᴴ := ⟨by simpa using hU.2, by simpa using hU.1⟩
    exact holds_of_commute b a hUs (by
      rw [he, ← Matrix.scalar_apply]
      exact (Matrix.scalar_commute u (Commute.all u) Uᴴ).symm)
  by_cases hB : B = 0
  · have he : b = fun _ => -v := funext fun i => by
      have hi := sub_eq_zero.mp (Complex.normSq_eq_zero.mp ((hb i).trans hB))
      exact neg_eq_iff_eq_neg.mp hi
    exact holds_of_commute a b hU (by
      rw [he, ← Matrix.scalar_apply]
      exact (Matrix.scalar_commute (-v) (Commute.all (-v)) U).symm)
  have hA' : 0 < A := lt_of_le_of_ne hA₀ (Ne.symm hA)
  have hB' : 0 < B := lt_of_le_of_ne hB₀ (Ne.symm hB)
  let e (i : Fin n) := a i - u
  let f (i : Fin n) := b i + u
  have hc : Holds e f U := by
    by_cases huv : u = v
    · apply holds_of_concentric_circles e f A B ha _ U hU
      intro i
      rw [show f i = -(-b i - v) by dsimp [f]; rw [huv]; ring, Complex.normSq_neg]
      exact hb i
    · let d := v - u
      have hd : d ≠ 0 := sub_ne_zero.mpr (Ne.symm huv)
      have hd' := Complex.normSq_pos.mpr hd
      let x (i : Fin n) := e i / d
      let y (i : Fin n) := f i / d
      have hx (i : Fin n) : Complex.normSq (x i) = A / Complex.normSq d := by
        dsimp only [x, e]
        rw [Complex.normSq_div, ha]
      have hy (i : Fin n) : Complex.normSq (-y i - 1) = B / Complex.normSq d := by
        rw [show -y i - 1 = (-b i - v) / d by dsimp only [y, f, d] at *; field_simp [hd] <;> ring,
          Complex.normSq_div, hb]
      have hh := holds_of_normalized_circle_centers x y _ _ (div_pos hA' hd') (div_pos hB' hd') hx hy U hU
      have hh' := hull_of_common_factor (determinantValue_scale x y U d) (matchingProduct_scale x y d) hh
      have he : (fun i => d * x i) = e := funext fun i => by dsimp only [x]; field_simp [hd] <;> ring
      have hf : (fun i => d * y i) = f := funext fun i => by dsimp only [y]; field_simp [hd] <;> ring
      simpa only [he, hf] using hh'
  apply (holds_shift_iff a b hU (-u)).mp
  simpa only [e, f, sub_eq_add_neg, neg_neg] using hc

/-- Each signed spectrum may independently lie on a line or a circle. -/
theorem holds_of_generalized_circular_spectra {n : ℕ} (a b : Fin n → ℂ)
    (ha : SpectrumOnGeneralizedCircle a) (hb : SpectrumOnGeneralizedCircle (fun i => -b i))
    (U : Matrix (Fin n) (Fin n) ℂ) (hU : IsUnitary U) : Holds a b U :=
  holds_of_generalized_circular_spectra_of_circular a b ha hb U hU
    (fun e f o p r s he hf => holds_of_circular_spectra e f o p r s he hf U hU)

/-- The number of matrix rows is unrestricted when each spectrum has at most
three distinct eigenvalues. -/
theorem holds_of_at_most_three_distinct_eigenvalues {n : ℕ} (a b : Fin n → ℂ)
    (ha : Nat.card (Set.range a) ≤ 3) (hb : Nat.card (Set.range b) ≤ 3)
    (U : Matrix (Fin n) (Fin n) ℂ) (hU : IsUnitary U) : Holds a b U :=
  holds_of_generalized_circular_spectra a b (spectrumOnGeneralizedCircle_of_card_range_le_three a ha)
    (spectrumOnGeneralizedCircle_neg (spectrumOnGeneralizedCircle_of_card_range_le_three b hb)) U hU

end MOC
