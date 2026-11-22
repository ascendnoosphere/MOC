import MOC.Hermitian
import MOC.CommonWeights

/-! One exceptional spectral value can move off a common line. -/

open BigOperators Matrix Filter
open scoped Topology

namespace MOC

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem projected_update_as_real_test (F : ℂ → ℂ) (η z : ℂ) (hη : η.re ≠ 0)
    (haff : ∀ t, F t = F 0 + (F 1 - F 0) * t) (h₀ : (F 0).im = 0) (h₁ : (F 1).im = 0) :
    (η * F z).re = ((η.re : ℂ) * F (((η * z).re / η.re : ℝ) : ℂ)).re := by
  let r := (η * z).re / η.re
  let c := F 0
  let s := F 1 - F 0
  have hc : c.im = 0 := h₀
  have hs : s.im = 0 := by simp only [s, Complex.sub_im, h₀, h₁, sub_self]
  change (η * F z).re = ((η.re : ℂ) * F (r : ℂ)).re
  rw [haff z, haff (r : ℂ)]
  change (η * (c + s * z)).re = ((η.re : ℂ) * (c + s * (r : ℂ))).re
  rw [mul_add, show η * (s * z) = s * (η * z) by ring, Complex.add_re,
    Complex.mul_re η c, Complex.mul_re s (η * z), hc, hs]
  simp only [Complex.mul_re, Complex.add_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, mul_zero, sub_zero]
  dsimp only [r]
  field_simp [hη] <;> ring

/-- The spectra may have one complex exception to the common real line. -/
theorem holds_of_one_complex_entry (a b : ι → ℝ) (j : ι) (z : ℂ)
    (U : Matrix ι ι ℂ) (hU : IsUnitary U) :
    Holds (fun i => (a i : ℂ)) (Function.update (fun i => (b i : ℂ)) j z) U := by
  let A (i : ι) : ℂ := a i
  let B (i : ι) : ℂ := b i
  let F (t : ℂ) := Function.update B j t
  let d (t : ℂ) := determinantValue A (F t) U
  let m (σ : Equiv.Perm ι) (t : ℂ) := matchingProduct A (F t) σ
  have hF (t : ℝ) : F (t : ℂ) = fun i => ((Function.update b j t i : ℝ) : ℂ) := by
    funext i
    by_cases hi : i = j
    · subst i
      simp [F]
    · simp [F, B, Function.update_of_ne hi]
  have htest (t : ℝ) : Holds A (F (t : ℂ)) U := by
    rw [hF]
    exact holds_of_real_spectra a (Function.update b j t) U hU
  have hm (t : ℝ) (σ : Equiv.Perm ι) : (m σ (t : ℂ)).im = 0 := by
    dsimp only [m, A]
    rw [hF]
    simp only [matchingProduct, ← Complex.ofReal_add, ← Complex.ofReal_prod, Complex.ofReal_im]
  have hd (t : ℝ) : (d (t : ℂ)).im = 0 := by
    obtain ⟨σ, hσ⟩ := (holds_iff_directional A (F (t : ℂ)) U).mp (htest t) Complex.I
    obtain ⟨τ, hτ⟩ := (holds_iff_directional A (F (t : ℂ)) U).mp (htest t) (-Complex.I)
    change (Complex.I * d (t : ℂ)).re ≤ (Complex.I * m σ (t : ℂ)).re at hσ
    change (-Complex.I * d (t : ℂ)).re ≤ (-Complex.I * m τ (t : ℂ)).re at hτ
    simp only [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.neg_re, Complex.neg_im,
      hm, zero_mul, mul_zero, sub_zero, neg_zero, one_mul, zero_sub, neg_one_mul] at hσ hτ
    linarith only [hσ, hτ]
  have hnonzero (η : ℂ) (hη : η.re ≠ 0) : ∃ σ, (η * d z).re ≤ (η * m σ z).re := by
    let r := (η * z).re / η.re
    obtain ⟨σ, hσ⟩ := (holds_iff_directional A (F (r : ℂ)) U).mp (htest r) (η.re : ℂ)
    refine ⟨σ, ?_⟩
    rw [projected_update_as_real_test d η z hη (determinant_update_interp A B j U hU)
        (by simpa only [Complex.ofReal_zero] using hd 0) (by simpa only [Complex.ofReal_one] using hd 1),
      projected_update_as_real_test (m σ) η z hη (matching_update_interp A B j σ)
        (by simpa only [Complex.ofReal_zero] using hm 0 σ) (by simpa only [Complex.ofReal_one] using hm 1 σ)]
    exact hσ
  apply (holds_iff_directional A (F z) U).mpr
  intro η
  change ∃ σ, (η * d z).re ≤ (η * m σ z).re
  by_cases hη : η.re = 0
  · by_contra hbad
    push_neg at hbad
    have hc (v : ℂ) : Continuous (fun t : ℝ => ((η + (t : ℂ)) * v).re) := by fun_prop
    have hevent : ∀ᶠ t : ℝ in 𝓝[≠] (0 : ℝ), ∀ σ, ((η + (t : ℂ)) * m σ z).re <
        ((η + (t : ℂ)) * d z).re := by
      apply Filter.eventually_all.mpr
      intro σ
      have h0 : ((η + ((0 : ℝ) : ℂ)) * m σ z).re < ((η + ((0 : ℝ) : ℂ)) * d z).re := by
        simpa only [Complex.ofReal_zero, add_zero] using hbad σ
      exact ((hc (m σ z)).continuousAt.eventually_lt (hc (d z)).continuousAt h0).filter_mono
        nhdsWithin_le_nhds
    obtain ⟨t, ht, htn⟩ := (hevent.and
      (self_mem_nhdsWithin : ∀ᶠ t in 𝓝[≠] (0 : ℝ), t ≠ 0)).exists
    obtain ⟨σ, hσ⟩ := hnonzero (η + (t : ℂ)) (by simpa only [Complex.add_re, hη,
      Complex.ofReal_re, zero_add] using htn)
    exact (not_le_of_gt (ht σ)) hσ
  · exact hnonzero η hη

end MOC
