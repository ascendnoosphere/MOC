import MOC.ContactFibreGluing
import MOC.ZeroHeightTriangleClosure
import MOC.MatchingQuartet

/-! A sparse set of terminal contacts that forces the entire profile to
a line, regardless of the relative unitary. -/

open BigOperators Matrix

namespace MOC

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
private theorem star_cycle_rotate (o i j : ι) (hoi : o ≠ i) (hoj : o ≠ j) (hij : i ≠ j) :
    Equiv.swap o i * Equiv.swap o j = Equiv.swap o j * Equiv.swap j i := by
  ext x
  by_cases hxo : x = o
  · subst x
    simp [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne, hoi, hoi.symm, hoj, hoj.symm, hij, hij.symm]
  by_cases hxi : x = i
  · subst x
    simp [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne, hoi, hoi.symm, hoj, hoj.symm, hij, hij.symm]
  by_cases hxj : x = j
  · subst x
    simp [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne, hoi, hoi.symm, hoj, hoj.symm, hij, hij.symm]
  · simp [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne, hxo, hxi, hxj]

omit [Fintype ι] in
private theorem star_cycle_rotate₂ (o i j : ι) (hoi : o ≠ i) (hoj : o ≠ j) (hij : i ≠ j) :
    Equiv.swap i j * Equiv.swap o j = Equiv.swap o i * Equiv.swap i j := by
  ext x
  by_cases hxo : x = o
  · subst x
    simp [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne, hoi, hoi.symm, hoj, hoj.symm, hij, hij.symm]
  by_cases hxi : x = i
  · subst x
    simp [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne, hoi, hoi.symm, hoj, hoj.symm, hij, hij.symm]
  by_cases hxj : x = j
  · subst x
    simp [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne, hoi, hoi.symm, hoj, hoj.symm, hij, hij.symm]
  · simp [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne, hxo, hxi, hxj]

private theorem star_pure_imaginary_ratio {z w : ℂ} (hz : z.re = 0) (hw : w.re = 0) :
    (z / w).im = 0 := by
  simp [Complex.div_im, Complex.normSq_apply, hz, hw]

/-- The identity, all swaps at the anchor, and one of the two 3-cycles on
each triple through two designated labels determine collinearity at height zero. -/
theorem matching_line_of_zero_height_anchored_star
    (a b : ι → ℂ) (ha : Function.Injective a) (hb : Function.Injective b)
    (hn : ∀ σ, matchingProduct a b σ ≠ 0) (η : ℂ) (hη : η ≠ 0)
    (o i : ι) (hoi : o ≠ i)
    (hp : (η * matchingProduct a b 1).re = 0)
    (hs : ∀ j, j ≠ o → (η * matchingProduct a b (Equiv.swap o j)).re = 0)
    (hc : ∀ j, j ≠ o → j ≠ i →
      (η * matchingProduct a b (Equiv.swap o i * Equiv.swap i j)).re = 0 ∨
      (η * matchingProduct a b (Equiv.swap o i * Equiv.swap o j)).re = 0) :
    ∀ σ, (η * matchingProduct a b σ).re = 0 := by
  let z (σ : Equiv.Perm ι) := (η * matchingProduct a b σ).re = 0
  have htri (j : ι) (hjo : j ≠ o) (hji : j ≠ i) :
      z (Equiv.swap i j) ∧ z (Equiv.swap o i * Equiv.swap i j) ∧
      z (Equiv.swap i j * Equiv.swap o i) := by
    rcases hc j hjo hji with h | h
    · have hh := matchingProduct_triangle_complete_zero_height_of_simple a b ha hb 1
        o i j hoi hjo.symm hji.symm η hη (hn 1) (hn _) hp
        (by simpa only [one_mul] using h) (by simpa only [one_mul] using hs i hoi.symm)
        (by simpa only [one_mul] using hs j hjo)
      simpa only [z, one_mul] using And.intro hh.2 (And.intro h hh.1)
    · rw [star_cycle_rotate o i j hoi hjo.symm hji.symm] at h
      have hh := matchingProduct_triangle_complete_zero_height_of_simple a b ha hb 1
        o j i hjo.symm hoi hji η hη (hn 1) (hn _) hp
        (by simpa only [one_mul] using h) (by simpa only [one_mul] using hs j hjo)
        (by simpa only [one_mul] using hs i hoi.symm)
      simp only [one_mul, Equiv.swap_comm j i] at hh h
      refine ⟨hh.2, ?_, ?_⟩
      · have eq := star_cycle_rotate₂ o i j hoi hjo.symm hji.symm
        rw [← eq]
        exact hh.1
      · have eq := star_cycle_rotate₂ o j i hjo.symm hoi hji
        rw [Equiv.swap_comm j i] at eq
        rw [eq]
        exact h
  let A : Matrix ι ι ℂ := Matrix.of fun r s => a r + b s
  have hentry : ∀ r s, a r + b s ≠ 0 := kernel_nonzero_of_profile_nonzero A hn
  let x (r : ι) := (a r - a o) / (a r + b o)
  let y (s : ι) := (b o - b s) / (a o + b s)
  let K := anchoredMatchingKernel x y
  let L (r : ι) := (a r + b o) / (a o + b o)
  let R (s : ι) := a o + b s
  let d : ℂ := η * ((∏ r, L r) * ∏ s, R s)
  obtain ⟨hx, hy, hA⟩ := additive_eq_gauged_anchored a b o (hentry o) (fun r => hentry r o)
  have hscale (σ : Equiv.Perm ι) : η * matchingProduct a b σ = d * kernelMatchingProduct K σ := by
    have he : A = Matrix.of fun r s => L r * R s * K r s := by
      ext r s
      exact hA r s
    change η * kernelMatchingProduct A σ = _
    rw [he, gauged_kernelMatchingProduct]
    exact (mul_assoc η _ _).symm
  change x o = 0 at hx
  change y o = 0 at hy
  have hKnz (σ : Equiv.Perm ι) : d * kernelMatchingProduct K σ ≠ 0 := by
    rw [← hscale]
    exact mul_ne_zero hη (hn σ)
  have hratio {s : ι} (hso : s ≠ o) (σ : Equiv.Perm ι) (hσo : σ o = o)
      (hσ : z σ) (hτ : z (σ * Equiv.swap o s)) : (K (σ s) s).im = 0 := by
    have he := anchored_entry_eq_profile_ratio x y o s hso hx hy σ hσo d (hKnz _)
    change K (σ s) s = _ at he
    rw [he, ← hscale σ, ← hscale (σ * Equiv.swap o s)]
    exact star_pure_imaginary_ratio hσ hτ
  have hdiag (s : ι) (hso : s ≠ o) : (K s s).im = 0 := by
    simpa only [Equiv.Perm.one_apply] using hratio hso 1 rfl hp (by simpa using hs s hso)
  have hrow (s : ι) : (K i s).im = 0 := by
    by_cases hso : s = o
    · subst s
      simp [K, anchoredMatchingKernel, hy]
    by_cases hsi : s = i
    · subst s
      exact hdiag i hso
    let σ := Equiv.swap i s
    have hσo : σ o = o := Equiv.swap_apply_of_ne_of_ne hoi (Ne.symm hso)
    have hs₁ := (htri s hso hsi).1
    have hs₂ : z (σ * Equiv.swap o s) := by
      rw [show σ = Equiv.swap i s from rfl, star_cycle_rotate₂ o i s hoi (Ne.symm hso) (Ne.symm hsi)]
      exact (htri s hso hsi).2.1
    have h := hratio hso σ hσo hs₁ hs₂
    simpa only [σ, Equiv.swap_apply_right] using h
  have hcol (r : ι) : (K r i).im = 0 := by
    by_cases hro : r = o
    · subst r
      simp [K, anchoredMatchingKernel, hx]
    by_cases hri : r = i
    · subst r
      exact hdiag i hro
    let σ := Equiv.swap i r
    have hσo : σ o = o := Equiv.swap_apply_of_ne_of_ne hoi (Ne.symm hro)
    have hr₁ := (htri r hro hri).1
    have hr₂ := (htri r hro hri).2.2
    have h := hratio hoi.symm σ hσo hr₁ hr₂
    simpa only [σ, Equiv.swap_apply_left] using h
  let E (r s : ι) := K r s - 1
  have hE (r s : ι) : (E r s).im = (K r s).im := by simp [E]
  have hii : E i i ≠ 0 := by
    unfold E K anchoredMatchingKernel
    simp only [Matrix.of_apply, add_sub_cancel_left]
    exact mul_ne_zero (div_ne_zero (sub_ne_zero.mpr (ha.ne hoi.symm)) (hentry i o))
      (div_ne_zero (sub_ne_zero.mpr (hb.ne hoi)) (hentry o i))
  have hiire : (E i i).re ≠ 0 := fun h => hii (Complex.ext (by simpa using h)
    (by simpa only [hE, Complex.zero_im] using hrow i))
  have hrealK (r s : ι) : (K r s).im = 0 := by
    have he : E r s * E i i = E r i * E i s := anchored_residual_cross x y r i s i
    have him := congrArg Complex.im he
    simp only [Complex.mul_im, hE, hrow, hcol, mul_zero, zero_mul, zero_add, add_zero] at him
    exact (mul_eq_zero.mp him).resolve_right hiire
  have hprod (σ : Equiv.Perm ι) : (kernelMatchingProduct K σ).im = 0 := by
    have hreal (r s : ι) : ((K r s).re : ℂ) = K r s := by
      apply Complex.ext <;> simp [hrealK r s]
    have e : kernelMatchingProduct K σ = ((∏ s, (K (σ s) s).re : ℝ) : ℂ) := by
      simp only [kernelMatchingProduct, Complex.ofReal_prod, hreal]
    rw [e]
    exact Complex.ofReal_im _
  have hr : (kernelMatchingProduct K 1).re ≠ 0 := fun h => hKnz 1 (by
    have hz : kernelMatchingProduct K 1 = 0 :=
      Complex.ext (by simpa using h) (by simpa using hprod 1)
    simp [hz])
  have hdre : d.re = 0 := by
    rw [hscale, Complex.mul_re, hprod, mul_zero, sub_zero] at hp
    exact (mul_eq_zero.mp hp).resolve_right hr
  intro σ
  rw [hscale, Complex.mul_re, hdre, hprod, zero_mul, mul_zero, sub_self]


/-- A terminal-size sparse contact family gives MOC for every mixer.
Use a base matching, the anchor swaps, one three-cycle from each anchored
triple, and one four-cycle completing a nondegenerate rectangle. -/
theorem holds_of_anchored_star_with_rectangle
    (a b : ι → ℂ) (ha : Function.Injective a) (hb : Function.Injective b)
    (hn : ∀ σ, matchingProduct a b σ ≠ 0)
    (η : ℂ) (hη : η ≠ 0) (H : ℝ) (r : Equiv.Perm ι)
    (o i j k : ι) (hoi : o ≠ i) (hoj : o ≠ j) (hok : o ≠ k)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hp : (η * matchingProduct a b r).re = H)
    (hs : ∀ l, l ≠ o → (η * matchingProduct a b (r * Equiv.swap o l)).re = H)
    (hc : ∀ l, l ≠ o → l ≠ i →
      (η * matchingProduct a b (r * (Equiv.swap o i * Equiv.swap i l))).re = H ∨
      (η * matchingProduct a b (r * (Equiv.swap o i * Equiv.swap o l))).re = H)
    (hj : (η * matchingProduct a b (r * Equiv.swap o i * Equiv.swap o j)).re = H)
    (hk : (η * matchingProduct a b (r * Equiv.swap o i * Equiv.swap i k)).re = H)
    (he : (η * matchingProduct a b
      (r * Equiv.swap o i * Equiv.swap o j * Equiv.swap i k)).re = H)
    (U : Matrix ι ι ℂ) (hU : IsUnitary U) : Holds a b U := by
  let A : Matrix ι ι ℂ := Matrix.of fun l m => a l + b m
  have hentry : ∀ l m, a l + b m ≠ 0 := kernel_nonzero_of_profile_nonzero A hn
  have hH := matchingProduct_disjoint_swaps_common_height_eq_zero a b
    (r * Equiv.swap o i) o j i k hoj hoi hok hij.symm hjk hik ha hb hentry
    hη (hs i hoi.symm) hj hk he
  rw [hH] at hp hs hc
  let a' := a ∘ r
  have hprof (σ : Equiv.Perm ι) :
      matchingProduct a' b σ = matchingProduct a b (r * σ) := rfl
  have hline := matching_line_of_zero_height_anchored_star a' b (ha.comp r.injective) hb
    (fun σ => hprof σ ▸ hn _) η hη o i hoi (by simpa only [hprof, mul_one] using hp)
    (fun l hl => by simpa only [hprof] using hs l hl)
    (fun l h₁ h₂ => by simpa only [hprof] using hc l h₁ h₂)
  letI : Nonempty ι := ⟨o⟩
  apply holds_of_matching_line_through_origin a b η hη _ U hU
  intro σ
  simpa only [hprof, ← mul_assoc, mul_inv_cancel, one_mul] using hline (r⁻¹ * σ)

end

end MOC
