import MOC.RealizableContactKernels
import MOC.CollinearKernelSupport

/-! Two complete zero-height fibres through the same matching cannot be
a proper face in the simple, nonvanishing chart. Their real pivot blocks
agree on a nonzero rank-one residual direction. -/

open BigOperators Matrix

namespace MOC
noncomputable section

private theorem pure_imaginary_div_im_zero {z w : ℂ} (hz : z.re = 0) (hw : w.re = 0) :
    (z / w).im = 0 := by
  simp [Complex.div_im, Complex.normSq_apply, hz, hw]

/-- If two codimension-one principal blocks of an anchored rank-one
residual are real and overlap in a nonzero diagonal residual, the whole
kernel is real. -/
theorem anchoredKernel_real_of_two_real_blocks {ι : Type*}
    (x y : ι → ℂ) (p q k : ι) (hpq : p ≠ q) (hkp : k ≠ p) (hkq : k ≠ q)
    (hk : anchoredMatchingKernel x y k k - 1 ≠ 0)
    (hp : ∀ i j, i ≠ p → j ≠ p → (anchoredMatchingKernel x y i j).im = 0)
    (hq : ∀ i j, i ≠ q → j ≠ q → (anchoredMatchingKernel x y i j).im = 0) :
    ∀ i j, (anchoredMatchingKernel x y i j).im = 0 := by
  let K := anchoredMatchingKernel x y
  let E (i j : ι) := K i j - 1
  have hcol (i : ι) : (E i k).im = 0 := by
    by_cases he : i = p
    · simpa [E, K, he] using hq p k hpq hkq
    · simpa [E, K] using hp i k he hkp
  have hrow (j : ι) : (E k j).im = 0 := by
    by_cases he : j = p
    · simpa [E, K, he] using hq k p hkq hpq
    · simpa [E, K] using hp k j hkp he
  have hkre : (E k k).re ≠ 0 := fun h =>
    hk (show E k k = 0 from Complex.ext h (hrow k))
  intro i j
  have he : E i j * E k k = E i k * E k j := anchored_residual_cross x y i k j k
  have him := congrArg Complex.im he
  simp only [Complex.mul_im, hrow k, hcol i, hrow j, mul_zero, zero_mul, zero_add,
    add_zero] at him
  have hz := (mul_eq_zero.mp him).resolve_right hkre
  simpa [E, K] using hz

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Two full fixed-label matchings fibres at zero height force every matching
to the imaginary axis in the support coordinates. The four labels are the
two excluded labels, an anchor, and a nonzero overlap direction. -/
theorem matching_line_of_two_zero_height_fibres
    (a b : ι → ℂ) (ha : Function.Injective a) (hb : Function.Injective b)
    (hn : ∀ σ, matchingProduct a b σ ≠ 0) (η : ℂ) (hη : η ≠ 0)
    (p q o k : ι) (hpq : p ≠ q) (hop : o ≠ p) (hoq : o ≠ q)
    (hkp : k ≠ p) (hkq : k ≠ q) (hko : k ≠ o)
    (hp : ∀ σ : Equiv.Perm ι, σ p = p → (η * matchingProduct a b σ).re = 0)
    (hq : ∀ σ : Equiv.Perm ι, σ q = q → (η * matchingProduct a b σ).re = 0) :
    ∀ σ, (η * matchingProduct a b σ).re = 0 := by
  let A : Matrix ι ι ℂ := Matrix.of fun i j => a i + b j
  have hentry : ∀ i j, a i + b j ≠ 0 := kernel_nonzero_of_profile_nonzero A hn
  let x (i : ι) := (a i - a o) / (a i + b o)
  let y (j : ι) := (b o - b j) / (a o + b j)
  let K := anchoredMatchingKernel x y
  let L (i : ι) := (a i + b o) / (a o + b o)
  let R (j : ι) := a o + b j
  let d : ℂ := η * ((∏ i, L i) * ∏ j, R j)
  obtain ⟨hx, hy, hA⟩ := additive_eq_gauged_anchored a b o (hentry o) (fun i => hentry i o)
  have hscale (σ : Equiv.Perm ι) : η * matchingProduct a b σ = d * kernelMatchingProduct K σ := by
    have he : A = Matrix.of fun i j => L i * R j * K i j := by
      ext i j
      exact hA i j
    change η * kernelMatchingProduct A σ = _
    rw [he, gauged_kernelMatchingProduct]
    exact (mul_assoc η _ _).symm
  change x o = 0 at hx
  change y o = 0 at hy
  have hKnz (σ : Equiv.Perm ι) : d * kernelMatchingProduct K σ ≠ 0 := by
    rw [← hscale]
    exact mul_ne_zero hη (hn σ)
  have hblock (t : ι) (hot : o ≠ t)
      (ht : ∀ σ : Equiv.Perm ι, σ t = t → (η * matchingProduct a b σ).re = 0)
      (i j : ι) (hit : i ≠ t) (hjt : j ≠ t) : (K i j).im = 0 := by
    by_cases hio : i = o
    · subst i
      simp [K, anchoredMatchingKernel, hx]
    · by_cases hjo : j = o
      · subst j
        simp [K, anchoredMatchingKernel, hy]
      · let σ : Equiv.Perm ι := Equiv.swap j i
        have hσo : σ o = o := Equiv.swap_apply_of_ne_of_ne (Ne.symm hjo) (Ne.symm hio)
        have hσt : σ t = t := Equiv.swap_apply_of_ne_of_ne (Ne.symm hjt) (Ne.symm hit)
        have hτt : (σ * Equiv.swap o j) t = t := by
          rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne (Ne.symm hot) (Ne.symm hjt), hσt]
        have hEq := anchored_entry_eq_profile_ratio x y o j hjo hx hy σ hσo d (hKnz _)
        change K (σ j) j = _ at hEq
        rw [show σ j = i from Equiv.swap_apply_left j i] at hEq
        rw [hEq, ← hscale σ, ← hscale (σ * Equiv.swap o j)]
        exact pure_imaginary_div_im_zero (ht σ hσt) (ht _ hτt)
  have hk : K k k - 1 ≠ 0 := by
    dsimp only [K, anchoredMatchingKernel, Matrix.of_apply]
    rw [add_comm, add_sub_cancel_right]
    exact mul_ne_zero (div_ne_zero (sub_ne_zero.mpr (ha.ne hko)) (hentry k o))
      (div_ne_zero (sub_ne_zero.mpr (hb.ne (Ne.symm hko))) (hentry o k))
  have hc : ∀ i j, (K i j).im = 0 := anchoredKernel_real_of_two_real_blocks x y p q k hpq hkp hkq hk
    (hblock p hop hp) (hblock q hoq hq)
  have hprod (σ : Equiv.Perm ι) : (kernelMatchingProduct K σ).im = 0 := by
    have hreal (i j : ι) : ((K i j).re : ℂ) = K i j := by
      apply Complex.ext <;> simp [hc i j]
    have e : kernelMatchingProduct K σ = ((∏ j, (K (σ j) j).re : ℝ) : ℂ) := by
      simp only [kernelMatchingProduct, Complex.ofReal_prod, hreal]
    rw [e]
    exact Complex.ofReal_im _
  have hr : (kernelMatchingProduct K 1).re ≠ 0 := fun h => hKnz 1 (by
    have hz : kernelMatchingProduct K 1 = 0 :=
      Complex.ext (by simpa using h) (by simpa using hprod 1)
    simp [hz])
  have hdre : d.re = 0 := by
    have hh := hp 1 rfl
    rw [hscale, Complex.mul_re, hprod, mul_zero, sub_zero] at hh
    exact (mul_eq_zero.mp hh).resolve_right hr
  intro σ
  rw [hscale, Complex.mul_re, hdre, hprod, zero_mul, mul_zero, sub_self]

/-- The same closure holds around any common base matching and provides a
mixer-independent MOC certificate for these spectra. -/
theorem holds_of_two_zero_height_fibres
    (a b : ι → ℂ) (ha : Function.Injective a) (hb : Function.Injective b)
    (hn : ∀ σ, matchingProduct a b σ ≠ 0) (η : ℂ) (hη : η ≠ 0)
    (r : Equiv.Perm ι) (p q o k : ι) (hpq : p ≠ q) (hop : o ≠ p) (hoq : o ≠ q)
    (hkp : k ≠ p) (hkq : k ≠ q) (hko : k ≠ o)
    (hp : ∀ σ : Equiv.Perm ι, σ p = r p → (η * matchingProduct a b σ).re = 0)
    (hq : ∀ σ : Equiv.Perm ι, σ q = r q → (η * matchingProduct a b σ).re = 0)
    (U : Matrix ι ι ℂ) (hU : IsUnitary U) : Holds a b U := by
  let a' := a ∘ r
  have he (σ : Equiv.Perm ι) : matchingProduct a' b σ = matchingProduct a b (r * σ) := rfl
  have hl := matching_line_of_two_zero_height_fibres a' b (ha.comp r.injective) hb
    (fun σ => he σ ▸ hn _) η hη p q o k hpq hop hoq hkp hkq hko
    (fun σ h => he σ ▸ hp (r * σ) (by simp [Equiv.Perm.mul_apply, h]))
    (fun σ h => he σ ▸ hq (r * σ) (by simp [Equiv.Perm.mul_apply, h]))
  letI : Nonempty ι := ⟨p⟩
  apply holds_of_matching_line_through_origin a b η hη _ U hU
  intro σ
  have hh := hl (r⁻¹ * σ)
  simpa only [he, ← mul_assoc, mul_inv_cancel, one_mul] using hh

end
end MOC
