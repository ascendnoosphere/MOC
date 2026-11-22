import MOC.ContactRectangle

/-! Independent changes of assignments give multiplicative contact
rectangles, including when a change moves more than two labels. -/

open BigOperators

namespace MOC

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Matching products factor over two independent changes of assignments. -/
theorem matchingProduct_disjoint_perms_identity
    (a b : ι → ℂ) (r s t : Equiv.Perm ι)
    (hst : ∀ i, s i = i ∨ t i = i) :
    matchingProduct a b r * matchingProduct a b (r * s * t) =
      matchingProduct a b (r * s) * matchingProduct a b (r * t) := by
  simp only [matchingProduct, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  by_cases ht : t i = i
  · simp only [Equiv.Perm.mul_apply, ht]
    ac_rfl
  · have hs := (hst i).resolve_right ht
    have ht' : t (t i) ≠ t i := fun he => ht (t.injective he)
    have hs' := (hst (t i)).resolve_right ht'
    simp only [Equiv.Perm.mul_apply, hs, hs']

/-- The support deficit at the fourth corner of an assignment rectangle
is determined by the two imaginary differences from the reference. -/
theorem matchingProduct_disjoint_perms_fourth_gap
    (a b : ι → ℂ) (r s t : Equiv.Perm ι) (hst : ∀ i, s i = i ∨ t i = i)
    (η : ℂ) (H : ℝ)
    (h₀ : (η * matchingProduct a b r).re = H)
    (h₁ : (η * matchingProduct a b (r * s)).re = H)
    (h₂ : (η * matchingProduct a b (r * t)).re = H) :
    let z (q : Equiv.Perm ι) := η * matchingProduct a b q
    (H - (z (r * s * t)).re) * (H ^ 2 + (z r).im ^ 2) =
      H * ((z (r * s)).im - (z r).im) * ((z (r * t)).im - (z r).im) := by
  intro z
  have hdiag : z r * z (r * s * t) = z (r * s) * z (r * t) := by
    have h := matchingProduct_disjoint_perms_identity a b r s t hst
    dsimp only [z]
    linear_combination η ^ 2 * h
  exact rectangle_fourth_gap hdiag h₀ h₁ h₂

private theorem contact_im_sub_ne_zero
    (a b : ι → ℂ) (r s : Equiv.Perm ι) (hs : s ≠ 1)
    (hinj : Function.Injective (matchingProduct a b)) (η : ℂ) (hη : η ≠ 0)
    (h : (η * matchingProduct a b (r * s)).re = (η * matchingProduct a b r).re) :
    (η * matchingProduct a b (r * s)).im - (η * matchingProduct a b r).im ≠ 0 := by
  intro he
  have hz := Complex.ext h (sub_eq_zero.mp he)
  have hp : r * s = r := hinj (mul_left_cancel₀ hη hz)
  exact hs (mul_left_cancel (hp.trans (mul_one r).symm))

/-- At a nonzero projected height, two independently changeable nontrivial
assignments cannot form four contacts with distinct matching products. -/
theorem matchingProduct_disjoint_perms_contact_height_eq_zero
    (a b : ι → ℂ) (r s t : Equiv.Perm ι)
    (hst : ∀ i, s i = i ∨ t i = i) (hs : s ≠ 1) (ht : t ≠ 1)
    (hinj : Function.Injective (matchingProduct a b))
    (η : ℂ) (hη : η ≠ 0) (H : ℝ)
    (h₀ : (η * matchingProduct a b r).re = H)
    (h₁ : (η * matchingProduct a b (r * s)).re = H)
    (h₂ : (η * matchingProduct a b (r * t)).re = H)
    (h₃ : (η * matchingProduct a b (r * s * t)).re = H) : H = 0 := by
  have h := matchingProduct_disjoint_perms_fourth_gap a b r s t hst η H h₀ h₁ h₂
  dsimp only at h
  have hs' := contact_im_sub_ne_zero a b r s hs hinj η hη (h₁.trans h₀.symm)
  have ht' := contact_im_sub_ne_zero a b r t ht hinj η hη (h₂.trans h₀.symm)
  rw [h₃, sub_self, zero_mul, mul_assoc] at h
  exact (mul_eq_zero.mp h.symm).resolve_right (mul_ne_zero hs' ht')

/-- At negative upper support height, the imaginary offsets of two disjoint
active changes are nonzero and have opposite signs. -/
theorem matchingProduct_disjoint_contact_im_mul_neg
    (a b : ι → ℂ) (r s t : Equiv.Perm ι)
    (hst : ∀ i, s i = i ∨ t i = i) (hs : s ≠ 1) (ht : t ≠ 1)
    (hinj : Function.Injective (matchingProduct a b)) (η : ℂ) (hη : η ≠ 0)
    (H : ℝ) (hH : H < 0)
    (h₀ : (η * matchingProduct a b r).re = H)
    (h₁ : (η * matchingProduct a b (r * s)).re = H)
    (h₂ : (η * matchingProduct a b (r * t)).re = H)
    (h₃ : (η * matchingProduct a b (r * s * t)).re ≤ H) :
    let δ (q : Equiv.Perm ι) := (η * matchingProduct a b (r * q)).im -
      (η * matchingProduct a b r).im
    δ s * δ t < 0 := by
  intro δ
  have h := matchingProduct_disjoint_perms_fourth_gap a b r s t hst η H h₀ h₁ h₂
  dsimp only at h
  have hprod : 0 ≤ H * (δ s * δ t) := by
    rw [← mul_assoc, ← h]
    exact mul_nonneg (sub_nonneg.mpr h₃) (add_nonneg (sq_nonneg _) (sq_nonneg _))
  have hne : δ s * δ t ≠ 0 := mul_ne_zero
    (contact_im_sub_ne_zero a b r s hs hinj η hη (h₁.trans h₀.symm))
    (contact_im_sub_ne_zero a b r t ht hinj η hη (h₂.trans h₀.symm))
  apply lt_of_le_of_ne _ hne
  exact le_of_not_gt fun hpos => (mul_neg_of_neg_of_pos hH hpos).not_le hprod

/-- Three nontrivial, pairwise disjoint changes of assignments cannot all
be active at a reference of negative upper support height. -/
theorem no_three_disjoint_active_changes_of_negative_height
    (a b : ι → ℂ) (r : Equiv.Perm ι) (s : Fin 3 → Equiv.Perm ι)
    (hdisj : ∀ i j, i ≠ j → ∀ k, s i k = k ∨ s j k = k)
    (hmove : ∀ i, s i ≠ 1) (hinj : Function.Injective (matchingProduct a b))
    (η : ℂ) (hη : η ≠ 0) (H : ℝ) (hH : H < 0)
    (h₀ : (η * matchingProduct a b r).re = H)
    (hactive : ∀ i, (η * matchingProduct a b (r * s i)).re = H)
    (hsupport : ∀ σ, (η * matchingProduct a b σ).re ≤ H) : False := by
  let δ (i : Fin 3) := (η * matchingProduct a b (r * s i)).im -
    (η * matchingProduct a b r).im
  have hpair (i j : Fin 3) (hij : i ≠ j) : δ i * δ j < 0 :=
    matchingProduct_disjoint_contact_im_mul_neg a b r (s i) (s j) (hdisj i j hij)
      (hmove i) (hmove j) hinj η hη H hH h₀ (hactive i) (hactive j) (hsupport _)
  have hpos := mul_pos_of_neg_of_neg (hpair 0 1 (by decide)) (hpair 0 2 (by decide))
  have hnonpos := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg (δ 0)) (hpair 1 2 (by decide)).le
  exact (not_le_of_gt hpos) (by convert hnonpos using 1 <;> ring)

end MOC
