import MOC.RealizableContactKernels
import MOC.CollinearKernelSupport
import MOC.ContactCrossRatios
import MOC.MatchingTriangle

/-! A six-contact pattern excluded for proper zero-height support faces
in order four: a contact plus five of its six transposition neighbors. -/

open BigOperators Matrix

namespace MOC
noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Five active exchanges on four labels imply that the entire profile lies
on the same zero-height line. The common edge of the two active swap
triangles is the real bridge in the rank-one pivot chart. -/
theorem matching_line_of_five_active_swaps_at_zero
    (a b : ι → ℂ) (ha : Function.Injective a) (hb : Function.Injective b)
    (hn : ∀ σ, matchingProduct a b σ ≠ 0) (η : ℂ) (hη : η ≠ 0)
    (o k p q : ι) (hok : o ≠ k)
    (hop : o ≠ p) (hoq : o ≠ q) (hkp : k ≠ p) (hkq : k ≠ q)
    (hcover : ∀ i, i = o ∨ i = k ∨ i = p ∨ i = q)
    (hmax : ∀ σ : Equiv.Perm ι, (η * matchingProduct a b σ).re ≤ 0)
    (hid : (η * matchingProduct a b 1).re = 0)
    (hok' : (η * matchingProduct a b (Equiv.swap o k)).re = 0)
    (hop' : (η * matchingProduct a b (Equiv.swap o p)).re = 0)
    (hoq' : (η * matchingProduct a b (Equiv.swap o q)).re = 0)
    (hkp' : (η * matchingProduct a b (Equiv.swap k p)).re = 0)
    (hkq' : (η * matchingProduct a b (Equiv.swap k q)).re = 0) :
    ∀ σ, (η * matchingProduct a b σ).re = 0 := by
  let P := matchingProduct a b
  let z (σ : Equiv.Perm ι) := η * P σ
  have hb1 : (z 1).re = 0 := hid
  have hcycle (t : ι) (hot : o ≠ t) (hkt : k ≠ t)
      (ha' : (z (Equiv.swap o t)).re = 0) (hb' : (z (Equiv.swap k t)).re = 0) :
      (z (Equiv.swap k t * Equiv.swap o k)).re = 0 ∧
        (z (Equiv.swap k t * Equiv.swap o t)).re = 0 := by
    have hs := congrArg (fun w : ℂ => (η * w).re)
      (matchingProduct_triangle_identity a b 1 o k t hok hot hkt)
    simp only [one_mul, mul_add, Complex.add_re] at hs
    change (z 1).re + (z (Equiv.swap o k * Equiv.swap k t)).re +
      (z (Equiv.swap k t * Equiv.swap o k)).re =
      (z (Equiv.swap o k)).re + (z (Equiv.swap o t)).re + (z (Equiv.swap k t)).re at hs
    have he : Equiv.swap k t * Equiv.swap o t = Equiv.swap o k * Equiv.swap k t := by
      rw [Equiv.mul_swap_eq_swap_mul]
      simp only [Equiv.swap_apply_right,
        Equiv.swap_apply_of_ne_of_ne hok hot]
    rw [he]
    have le₁ := hmax (Equiv.swap k t * Equiv.swap o k)
    have le₂ := hmax (Equiv.swap o k * Equiv.swap k t)
    exact ⟨by linarith only [hs, hb1, hok', ha', hb', le₁, le₂],
      by linarith only [hs, hb1, hok', ha', hb', le₁, le₂]⟩
  obtain ⟨d, hd, x, y, hx, hy, form⟩ :=
    (nonzero_additive_profile_iff_anchored o P hn).mp ⟨a, b, rfl⟩
  let K := anchoredMatchingKernel x y
  have hratio (i j : ι) (hio : i ≠ o) (hjo : j ≠ o) :
      K i j = z (Equiv.swap j i) / z (Equiv.swap j i * Equiv.swap o j) := by
    let s : Equiv.Perm ι := Equiv.swap j i
    have hs : s o = o := Equiv.swap_apply_of_ne_of_ne (Ne.symm hjo) (Ne.symm hio)
    have he (σ : Equiv.Perm ι) : z σ = (η * d) * kernelMatchingProduct K σ := by
      dsimp only [z]
      rw [form σ, mul_assoc]
    have hnz : (η * d) * kernelMatchingProduct K (s * Equiv.swap o j) ≠ 0 := by
      rw [← he]
      exact mul_ne_zero hη (hn _)
    have hf := anchored_entry_eq_profile_ratio x y o j hjo hx hy s hs (η * d) hnz
    change K (s j) j = _ at hf
    rwa [show s j = i from Equiv.swap_apply_left j i, ← he s, ← he (s * Equiv.swap o j)] at hf
  have him {u v : ℂ} (hu : u.re = 0) (hv : v.re = 0) : (u / v).im = 0 := by
    simp [Complex.div_im, hu, hv]
  have hkk : K k k = z 1 / z (Equiv.swap o k) := by
    simpa only [Equiv.swap_self, ← Equiv.Perm.one_def, one_mul] using
      hratio k k hok.symm hok.symm
  have hk : K k k - 1 ≠ 0 := by
    intro h
    have he := sub_eq_zero.mp h
    rw [hkk, div_eq_iff (mul_ne_zero hη (hn _)), one_mul] at he
    exact matchingProduct_swap_gap_ne_of_simple a b ha hb 1 (hn 1) o k hok
      (sub_eq_zero.mpr (mul_left_cancel₀ hη (by simpa only [one_mul] using he)))
  have hbridge (t : ι) (hot : o ≠ t) (hkt : k ≠ t)
      (ht₁ : (z (Equiv.swap o t)).re = 0) (ht₂ : (z (Equiv.swap k t)).re = 0) :
      (K t k).im = 0 ∧ (K k t).im = 0 := by
    obtain ⟨hc₁, hc₂⟩ := hcycle t hot hkt ht₁ ht₂
    constructor
    · rw [hratio t k hot.symm hok.symm]
      exact him ht₂ hc₁
    · rw [hratio k t hok.symm hot.symm, Equiv.swap_comm t k]
      exact him ht₂ hc₂
  obtain ⟨hp₁, hp₂⟩ := hbridge p hop hkp hop' hkp'
  obtain ⟨hq₁, hq₂⟩ := hbridge q hoq hkq hoq' hkq'
  have hone : (K k k).im = 0 := by rw [hkk]; exact him hid hok'
  have hKcol (i : ι) : (K i k).im = 0 := by
    rcases hcover i with rfl | rfl | rfl | rfl
    · simp [K, anchoredMatchingKernel, hx]
    · exact hone
    · exact hp₁
    · exact hq₁
  have hKrow (j : ι) : (K k j).im = 0 := by
    rcases hcover j with rfl | rfl | rfl | rfl
    · simp [K, anchoredMatchingKernel, hy]
    · exact hone
    · exact hp₂
    · exact hq₂
  have hc (i j : ι) : (K i j).im = 0 := by
    have hkre : (K k k - 1).re ≠ 0 := fun h =>
      hk (Complex.ext h (by simpa only [Complex.sub_im, Complex.one_im, sub_zero] using hone))
    have he := congrArg Complex.im (anchored_residual_cross x y i k j k)
    change ((K i j - 1) * (K k k - 1)).im = ((K i k - 1) * (K k j - 1)).im at he
    simp only [Complex.mul_im, Complex.sub_im, Complex.one_im, sub_zero, hone, hKcol i,
      hKrow j, mul_zero, zero_mul, zero_add, add_zero] at he
    exact (mul_eq_zero.mp he).resolve_right hkre
  have hre (σ : Equiv.Perm ι) : (kernelMatchingProduct K σ).im = 0 := by
    have hf (i j : ι) : ((K i j).re : ℂ) = K i j :=
      Complex.ext (Complex.ofReal_re _) (by simpa only [Complex.ofReal_im] using (hc i j).symm)
    have he : kernelMatchingProduct K σ = ((∏ j, (K (σ j) j).re : ℝ) : ℂ) := by
      simp only [kernelMatchingProduct, Complex.ofReal_prod, hf]
    rw [he]
    exact Complex.ofReal_im _
  have hz (σ : Equiv.Perm ι) : z σ = (η * d) * kernelMatchingProduct K σ := by
    dsimp only [z]
    rw [form σ, mul_assoc]
  have hnonzero : (kernelMatchingProduct K 1).re ≠ 0 := by
    intro h
    have hh : kernelMatchingProduct K 1 = 0 := Complex.ext h (hre 1)
    exact mul_ne_zero hη (hn 1) (by change z 1 = 0; rw [hz, hh, mul_zero])
  have hscale : (η * d).re = 0 := by
    rw [hz, Complex.mul_re, hre, mul_zero, sub_zero] at hb1
    exact (mul_eq_zero.mp hb1).resolve_right hnonzero
  intro σ
  change (z σ).re = 0
  rw [hz, Complex.mul_re, hscale, hre, zero_mul, mul_zero, sub_self]

/-- The same configuration can be based at any permutation in order four.
No other contact labels need be specified. -/
theorem holds_of_five_active_swaps_at_zero
    (a b : Fin 4 → ℂ) (ha : Function.Injective a) (hb : Function.Injective b)
    (hn : ∀ σ, matchingProduct a b σ ≠ 0) (η : ℂ) (hη : η ≠ 0)
    (r : Equiv.Perm (Fin 4)) (o k p q : Fin 4) (hok : o ≠ k)
    (hop : o ≠ p) (hoq : o ≠ q) (hkp : k ≠ p) (hkq : k ≠ q) (hpq : p ≠ q)
    (hmax : ∀ σ : Equiv.Perm (Fin 4), (η * matchingProduct a b σ).re ≤ 0)
    (hid : (η * matchingProduct a b r).re = 0)
    (hok' : (η * matchingProduct a b (r * Equiv.swap o k)).re = 0)
    (hop' : (η * matchingProduct a b (r * Equiv.swap o p)).re = 0)
    (hoq' : (η * matchingProduct a b (r * Equiv.swap o q)).re = 0)
    (hkp' : (η * matchingProduct a b (r * Equiv.swap k p)).re = 0)
    (hkq' : (η * matchingProduct a b (r * Equiv.swap k q)).re = 0)
    (U : Matrix (Fin 4) (Fin 4) ℂ) (hU : IsUnitary U) : Holds a b U := by
  let a' := a ∘ r
  have hf (σ : Equiv.Perm (Fin 4)) : matchingProduct a' b σ = matchingProduct a b (r * σ) := rfl
  have hcover (i : Fin 4) : i = o ∨ i = k ∨ i = p ∨ i = q := by
    have he : ({o, k, p, q} : Finset (Fin 4)) = Finset.univ := by
      apply Finset.eq_univ_of_card
      simp [hok, hop, hoq, hkp, hkq, hpq]
    have hh : i ∈ ({o, k, p, q} : Finset (Fin 4)) := he ▸ Finset.mem_univ i
    simpa using hh
  have hline := matching_line_of_five_active_swaps_at_zero a' b (ha.comp r.injective) hb
    (fun σ => hf σ ▸ hn _) η hη o k p q hok hop hoq hkp hkq hcover
    (fun σ => by rw [hf]; exact hmax _) (by simpa only [hf, mul_one] using hid)
    (by rwa [hf]) (by rwa [hf]) (by rwa [hf]) (by rwa [hf]) (by rwa [hf])
  apply holds_of_matching_line_through_origin a b η hη _ U hU
  intro σ
  simpa only [hf, ← mul_assoc, mul_inv_cancel, one_mul] using hline (r⁻¹ * σ)

end
end MOC
