import MOC.GeneralizedSpectralCircles
import MOC.Support
import MOC.SupportedCompressionReduction

/-! A row whose supported spectral values share a circle or line with its
negative eigenvalue permits a reduction by one order. -/

open Filter Matrix
open scoped Topology

namespace MOC

noncomputable section

variable {n : ℕ}

private theorem holds_of_regular_pole_line (hSmall : Conjecture (Fin n))
    (a b : Fin (n + 1) → ℂ) (U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (hU : IsUnitary U) (p : Fin (n + 1)) (ha : ∀ k ≠ p, a k - a p ≠ 0)
    (hb : ∀ j, b j + a p ≠ 0) (c d : ℂ)
    (hline : ∀ j, U p j ≠ 0 → ∃ r : ℝ, (b j + a p)⁻¹ = c + d * (r : ℂ)) :
    Holds a b U := by
  classical
  have hknots (j : Fin (n + 1)) :
      ∃ r : ℝ, U p j ≠ 0 → (b j + a p)⁻¹ = c + d * (r : ℂ) := by
    by_cases hj : U p j = 0
    · exact ⟨0, fun hn => (hn hj).elim⟩
    · obtain ⟨r, hr⟩ := hline j hj
      exact ⟨r, fun _ => hr⟩
  choose r hr using hknots
  apply holds_of_normal_poleCompression hSmall a b U hU p ha hb
  exact normalCompression_of_spectral_line_on_support
    (fun j => (b j + a p)⁻¹) U hU p c d r hr

private theorem holds_of_continuous_pole_move
    (a b : Fin (n + 1) → ℂ) (U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (p : Fin (n + 1)) (P : ℝ → ℂ) (hP : Continuous P) (hPinj : Function.Injective P)
    (hP0 : P 0 = -a p)
    (hregular : ∀ t : ℝ, (∀ k ≠ p, a k ≠ -P t) → (∀ j, b j ≠ P t) →
      Holds (Function.update a p (-P t)) b U) : Holds a b U := by
  classical
  let A (t : ℝ) := Function.update a p (-P t)
  have hA : Continuous A := by
    apply continuous_pi
    intro k
    by_cases hk : k = p
    · subst k
      simpa only [A, Function.update_self] using hP.neg
    · simpa only [A, Function.update_of_ne hk] using
        (continuous_const : Continuous (fun _ : ℝ => a k))
  have hA0 : A 0 = a := by
    funext k
    by_cases hk : k = p
    · subst k
      simp only [A, Function.update_self, hP0, neg_neg]
    · simp only [A, Function.update_of_ne hk]
  have hevent (z : ℂ) : ∀ᶠ t in 𝓝[≠] (0 : ℝ), P t ≠ z := by
    by_cases hz : P 0 = z
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact fun he => ht (hPinj (he.trans hz.symm))
    · exact (hP.continuousAt.eventually_ne hz).filter_mono nhdsWithin_le_nhds
  have ha : ∀ᶠ t in 𝓝[≠] (0 : ℝ), ∀ k ≠ p, a k ≠ -P t := by
    apply Filter.eventually_all.mpr
    intro k
    filter_upwards [hevent (-a k)] with t ht
    exact fun _ hk => ht (by rw [hk, neg_neg])
  have hb : ∀ᶠ t in 𝓝[≠] (0 : ℝ), ∀ j, b j ≠ P t := by
    apply Filter.eventually_all.mpr
    intro j
    exact (hevent (b j)).mono fun _ hj => Ne.symm hj
  by_contra h
  rw [holds_iff_directional, not_forall] at h
  obtain ⟨η, hη⟩ := h
  have hd : Continuous (fun t => (η * determinantValue (A t) b U).re) := by
    unfold determinantValue
    fun_prop
  have hs : ∀ᶠ t in 𝓝[≠] (0 : ℝ), ∀ σ : Equiv.Perm (Fin (n + 1)),
      (η * matchingProduct (A t) b σ).re < (η * determinantValue (A t) b U).re := by
    apply Filter.eventually_all.mpr
    intro σ
    have hm : Continuous (fun t => matchingProduct (A t) b σ) := by
      unfold matchingProduct
      exact continuous_finset_prod _ fun j _ =>
        ((continuous_apply (σ j)).comp hA).add continuous_const
    have hproj := Complex.continuous_re.comp (continuous_const.mul hm)
    have hlt : (η * matchingProduct (A 0) b σ).re <
        (η * determinantValue (A 0) b U).re := by
      rw [hA0]
      exact lt_of_not_ge fun hle => hη ⟨σ, hle⟩
    exact (hproj.continuousAt.eventually_lt hd.continuousAt hlt).filter_mono
      nhdsWithin_le_nhds
  obtain ⟨t, ht, hta, htb⟩ := (hs.and (ha.and hb)).exists
  obtain ⟨σ, hσ⟩ := (holds_iff_directional (A t) b U).mp (hregular t hta htb) η
  exact (not_le_of_gt (ht σ)) hσ

/-- A row supported on an affine line through its negative eigenvalue
reduces the determinant inclusion to the preceding order. -/
theorem holds_of_pole_line (hSmall : Conjecture (Fin n))
    (a b : Fin (n + 1) → ℂ) (U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (hU : IsUnitary U) (p : Fin (n + 1)) (d : ℂ) (hd : d ≠ 0)
    (hline : ∀ j, U p j ≠ 0 → ∃ r : ℝ, b j = -a p + d * (r : ℂ)) : Holds a b U := by
  let P (t : ℝ) := -a p + d * (t : ℂ)
  have hP : Continuous P := continuous_const.add (continuous_const.mul Complex.continuous_ofReal)
  have hPinj : Function.Injective P := fun _ _ h =>
    Complex.ofReal_injective (mul_left_cancel₀ hd (add_left_cancel h))
  apply holds_of_continuous_pole_move a b U p P hP hPinj (by simp [P])
  intro t ha hb
  let A := Function.update a p (-P t)
  have hAp : A p = -P t := Function.update_self p _ _
  have ha' (k : Fin (n + 1)) (hk : k ≠ p) : A k - A p ≠ 0 := by
    rw [hAp, show A k = a k by simp only [A, Function.update_of_ne hk]]
    exact sub_ne_zero.mpr (ha k hk)
  have hb' (j : Fin (n + 1)) : b j + A p ≠ 0 := by
    rw [hAp, ← sub_eq_add_neg]
    exact sub_ne_zero.mpr (hb j)
  apply holds_of_regular_pole_line hSmall A b U hU p ha' hb' 0 d⁻¹
  intro j hj
  obtain ⟨r, hr⟩ := hline j hj
  refine ⟨(r - t)⁻¹, ?_⟩
  rw [hAp, show b j + -P t = d * ((r - t : ℝ) : ℂ) by
    rw [hr]; simp only [P, Complex.ofReal_sub]; ring,
    _root_.mul_inv_rev, Complex.ofReal_inv, zero_add]
  exact mul_comm _ _

/-- A row supported on a circle through its negative eigenvalue reduces the
determinant inclusion to the preceding order, even at repeated values. -/
theorem holds_of_pole_circle (hSmall : Conjecture (Fin n))
    (a b : Fin (n + 1) → ℂ) (U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (hU : IsUnitary U) (p : Fin (n + 1)) (o : ℂ)
    (hcircle : ∀ j, U p j ≠ 0 → Complex.normSq (b j - o) = Complex.normSq (-a p - o)) :
    Holds a b U := by
  by_cases ho : -a p - o = 0
  · apply holds_of_pole_line hSmall a b U hU p 1 one_ne_zero
    intro j hj
    have hz := hcircle j hj
    rw [ho, Complex.normSq_zero] at hz
    have he := sub_eq_zero.mp (Complex.normSq_eq_zero.mp hz)
    exact ⟨0, by simpa only [Complex.ofReal_zero, mul_zero, add_zero] using
      he.trans (sub_eq_zero.mp ho).symm⟩
  let P (t : ℝ) := o + (-a p - o) * circleRotation t
  have hP : Continuous P := continuous_const.add (continuous_const.mul continuous_circleRotation)
  have hPinj : Function.Injective P := fun _ _ h =>
    circleRotation_injective (mul_left_cancel₀ ho (add_left_cancel h))
  have hP0 : P 0 = -a p := by simp [P, circleRotation]
  apply holds_of_continuous_pole_move a b U p P hP hPinj hP0
  intro t ha hb
  let A := Function.update a p (-P t)
  have hAp : A p = -P t := Function.update_self p _ _
  have ha' (k : Fin (n + 1)) (hk : k ≠ p) : A k - A p ≠ 0 := by
    rw [hAp, show A k = a k by simp only [A, Function.update_of_ne hk]]
    exact sub_ne_zero.mpr (ha k hk)
  have hb' (j : Fin (n + 1)) : b j + A p ≠ 0 := by
    rw [hAp, ← sub_eq_add_neg]
    exact sub_ne_zero.mpr (hb j)
  let u := o - P t
  have hu : u ≠ 0 := by
    change o - P t ≠ 0
    rw [show o - P t = -((-a p - o) * circleRotation t) by dsimp [P]; ring]
    apply neg_ne_zero.mpr
    refine mul_ne_zero ho fun h => ?_
    have hn := circleRotation_normSq t
    rw [h, Complex.normSq_zero] at hn
    exact zero_ne_one hn
  have hnorm : Complex.normSq u = Complex.normSq (-a p - o) := by
    rw [show u = -((-a p - o) * circleRotation t) by dsimp [u, P]; ring,
      Complex.normSq_neg, Complex.normSq_mul, circleRotation_normSq, mul_one]
  apply holds_of_regular_pole_line hSmall A b U hU p ha' hb' (u⁻¹ * (1 / 2 : ℂ))
    (u⁻¹ * Complex.I)
  intro j hj
  let z := b j + A p
  have hcircle' : Complex.normSq (z - u) = Complex.normSq u := by
    rw [show z - u = b j - o by dsimp [z, u]; rw [hAp]; ring, hcircle j hj, hnorm]
  have hre := re_mul_inv_of_circle u z (hb' j) hcircle'
  refine ⟨(u * z⁻¹).im, ?_⟩
  change z⁻¹ = _
  have hcast : (((1 / 2 : ℝ) : ℂ)) = (1 / 2 : ℂ) := by norm_num
  calc
    z⁻¹ = u⁻¹ * (u * z⁻¹) := by rw [← mul_assoc, inv_mul_cancel₀ hu, one_mul]
    _ = u⁻¹ * (((u * z⁻¹).re : ℂ) + ((u * z⁻¹).im : ℂ) * Complex.I) := by
      rw [Complex.re_add_im]
    _ = _ := by rw [hre, hcast]; ring

/-- For a dense row at a regular pole, normality of the reciprocal
compression implies that the partner spectrum lies on a circle or line. -/
theorem generalizedCircle_of_normal_poleCompression_of_dense_row
    (a b : Fin (n + 1) → ℂ) (U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (hU : IsUnitary U) (p : Fin (n + 1)) (hdense : ∀ j, U p j ≠ 0)
    (hnz : ∀ j, b j + a p ≠ 0) (hC : IsStarNormal (poleCompression a b U p)) :
    SpectrumOnGeneralizedCircle b := by
  let β (j : Fin (n + 1)) := (b j + a p)⁻¹
  let μ := (U * diagonal β * Uᴴ) p p
  obtain ⟨d, hd, hline⟩ := exists_spectral_line_of_normalCompression β U hU p hC
  have hβ : SpectrumOnGeneralizedCircle β := by
    have hd' : d⁻¹ ≠ 0 := inv_ne_zero hd
    have hparts : (d⁻¹).im ≠ 0 ∨ (d⁻¹).re ≠ 0 := by
      by_contra! h
      exact hd' (Complex.ext h.2 h.1)
    apply spectrumOnGeneralizedCircle_of_line β (d⁻¹).im (d⁻¹).re (d⁻¹ * μ).im hparts
    intro j
    change (d⁻¹ * β j).im = (d⁻¹ * μ).im
    obtain ⟨r, hr⟩ := hline j (hdense j)
    rw [hr, mul_add, ← mul_assoc d⁻¹ d (r : ℂ), inv_mul_cancel₀ hd, one_mul, Complex.add_im,
      Complex.ofReal_im, add_zero]
  simpa only [β, inv_inv, add_neg_cancel_right] using
    (hβ.inv_of_ne_zero (fun j => inv_ne_zero (hnz j))).add_const (-a p)

/-- The specified convex quadrilateral gives a nonnormal reciprocal
compression at every dense row whose pole avoids the partner spectrum. -/
theorem not_normal_poleCompression_convexQuadrilateral
    (a : Fin 4 → ℂ) (U : Matrix (Fin 4) (Fin 4) ℂ) (hU : IsUnitary U) (p : Fin 4)
    (hdense : ∀ j, U p j ≠ 0)
    (hnz : ∀ j, ![(0 : ℂ), 1, 1 + Complex.I, 2 * Complex.I] j + a p ≠ 0) :
    ¬ IsStarNormal
      (poleCompression a ![(0 : ℂ), 1, 1 + Complex.I, 2 * Complex.I] U p) := by
  intro hC
  exact not_generalizedCircle_convexQuadrilateral
    (generalizedCircle_of_normal_poleCompression_of_dense_row a _ U hU p hdense hnz hC)

end

end MOC
