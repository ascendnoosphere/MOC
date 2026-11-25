import MOC.Hermitian
import MOC.SpectralMobius

/-! A single complex outlier from common real spectra admits one convex law
for every value of the outlier. -/

open BigOperators Filter Matrix
open scoped Topology

namespace MOC

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The factor paired with the exceptional coordinate is the only complex
factor when the other spectral entries are real. -/
theorem matchingProduct_one_complex_outlier (a b : ι → ℝ) (j : ι) (z : ℂ)
    (σ : Equiv.Perm ι) :
    matchingProduct (fun i => (a i : ℂ)) (Function.update (fun i => (b i : ℂ)) j z) σ =
      ((a (σ j) : ℂ) + z) * ((∏ k ∈ Finset.univ.erase j, a (σ k) + b k : ℝ) : ℂ) := by
  let f (k : ι) := (a (σ k) : ℂ) + Function.update (fun i => (b i : ℂ)) j z k
  change (∏ k, f k) = _
  rw [← Finset.mul_prod_erase Finset.univ f (Finset.mem_univ j)]
  have hhead : f j = (a (σ j) : ℂ) + z := by simp [f]
  have htail : (∏ k ∈ Finset.univ.erase j, f k) =
      ((∏ k ∈ Finset.univ.erase j, a (σ k) + b k : ℝ) : ℂ) := by
    refine Eq.trans (Finset.prod_congr rfl fun k hk => ?_) (Complex.ofReal_prod _).symm
    simp only [f, Function.update_of_ne (Finset.mem_erase.mp hk).1, Complex.ofReal_add]
  rw [hhead, htail]

private def replaceImaginaryUnit (z : ℂ) : ℂ →ₗ[ℝ] ℂ where
  toFun x := (x.re : ℂ) + (x.im : ℂ) * z
  map_add' x y := by
    simp only [Complex.add_re, Complex.add_im, Complex.ofReal_add]
    ring
  map_smul' s x := by
    simp only [Complex.real_smul, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, zero_add, Complex.ofReal_mul]
    ring

private theorem effective_real_projection (η p : ℂ) (hη : η.re ≠ 0) :
    (η * replaceImaginaryUnit ((-η.im / η.re : ℝ) : ℂ) p).re = (η * p).re := by
  change (η * ((p.re : ℂ) + (p.im : ℂ) * ((-η.im / η.re : ℝ) : ℂ))).re = _
  simp only [Complex.mul_re, Complex.add_re, Complex.add_im, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero]
  field_simp [hη] <;> ring

/-- For a single exceptional coordinate, one probability distribution on
permutations gives the determinant for every complex value at that coordinate. -/
theorem exists_common_law_one_complex_outlier (a b : ι → ℝ) (j : ι)
    (U : Matrix ι ι ℂ) (hU : IsUnitary U) :
    ∃ w : Equiv.Perm ι → ℝ, (∀ σ, 0 ≤ w σ) ∧ (∑ σ, w σ) = 1 ∧
      ∀ z : ℂ, ∑ σ, (w σ : ℂ) *
        matchingProduct (fun i => (a i : ℂ)) (Function.update (fun i => (b i : ℂ)) j z) σ =
          determinantValue (fun i => (a i : ℂ)) (Function.update (fun i => (b i : ℂ)) j z) U := by
  classical
  let A (i : ι) : ℂ := a i
  let B (z : ℂ) := Function.update (fun i => (b i : ℂ)) j z
  let P (z : ℂ) (σ : Equiv.Perm ι) := matchingProduct A (B z) σ
  let D (z : ℂ) := determinantValue A (B z) U
  have hP (z : ℂ) (σ : Equiv.Perm ι) :
      replaceImaginaryUnit z (P Complex.I σ) = P z σ := by
    change ((P Complex.I σ).re : ℂ) + ((P Complex.I σ).im : ℂ) * z = P z σ
    dsimp only [P, A, B]
    rw [matchingProduct_one_complex_outlier a b j Complex.I σ,
      matchingProduct_one_complex_outlier a b j z σ]
    simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      zero_mul, mul_zero, sub_zero, add_zero, zero_add, one_mul, Complex.ofReal_mul]
    ring
  have hD (z : ℂ) : replaceImaginaryUnit z (D Complex.I) = D z := by
    change replaceImaginaryUnit z (determinantValue A (B Complex.I) U) =
      determinantValue A (B z) U
    rw [← real_signed_determinant A (B Complex.I) U hU, ← real_signed_determinant A (B z) U hU]
    change replaceImaginaryUnit z (∑ σ, (realSignedWeight U σ : ℂ) * P Complex.I σ) =
      ∑ σ, (realSignedWeight U σ : ℂ) * P z σ
    simp only [map_sum, ← Complex.real_smul, map_smul, hP]
  have hbound (η : ℂ) (hη : η.re ≠ 0) :
      ∃ σ, (η * D Complex.I).re ≤ (η * P Complex.I σ).re := by
    let t : ℝ := -η.im / η.re
    have hB : B (t : ℂ) = fun i => (Function.update b j t i : ℂ) := by
      funext i
      by_cases h : i = j
      · subst i
        simp [B]
      · simp [B, Function.update_of_ne h]
    obtain ⟨σ, hσ⟩ := (holds_iff_directional A (B (t : ℂ)) U).mp
      (by rw [hB]; exact holds_of_real_spectra a (Function.update b j t) U hU) η
    change (η * D (t : ℂ)).re ≤ (η * P (t : ℂ) σ).re at hσ
    rw [← hD (t : ℂ), ← hP (t : ℂ) σ] at hσ
    have hp (p : ℂ) : (η * replaceImaginaryUnit (t : ℂ) p).re = (η * p).re :=
      effective_real_projection η p hη
    exact ⟨σ, by simpa only [hp] using hσ⟩
  have hI : Holds A (B Complex.I) U := by
    by_contra hn
    rw [holds_iff_directional] at hn
    push_neg at hn
    obtain ⟨η, hη⟩ := hn
    change ∀ σ, (η * P Complex.I σ).re < (η * D Complex.I).re at hη
    by_cases hη₀ : η.re = 0
    · let F (σ : Equiv.Perm ι) (t : ℝ) :=
        ((η + (t : ℂ)) * (D Complex.I - P Complex.I σ)).re
      have he (σ : Equiv.Perm ι) : ∀ᶠ t in 𝓝 (0 : ℝ), 0 < F σ t := by
        have hc : Continuous (F σ) := by dsimp only [F]; fun_prop
        exact hc.continuousAt.eventually_mem (Ioi_mem_nhds (by
          simpa only [F, Complex.ofReal_zero, add_zero, mul_sub, Complex.sub_re, sub_pos] using hη σ))
      obtain ⟨t, ht, ht₀⟩ := (((Filter.eventually_all.mpr he).filter_mono
        (nhdsWithin_le_nhds : 𝓝[≠] (0 : ℝ) ≤ 𝓝 0)).and self_mem_nhdsWithin).exists
      change t ≠ 0 at ht₀
      have hne : (η + (t : ℂ)).re ≠ 0 := by
        simpa only [Complex.add_re, Complex.ofReal_re, hη₀, zero_add] using ht₀
      obtain ⟨σ, hσ⟩ := hbound (η + (t : ℂ)) hne
      exact (not_lt_of_ge hσ) (by simpa only [F, mul_sub, Complex.sub_re, sub_pos] using ht σ)
    · obtain ⟨σ, hσ⟩ := hbound η hη₀
      exact (not_lt_of_ge hσ) (hη σ)
  change D Complex.I ∈ convexHull ℝ (Set.range (P Complex.I)) at hI
  rw [convexHull_range_eq_exists_affineCombination, Set.mem_setOf_eq] at hI
  obtain ⟨s, w, hw, hs, hsum⟩ := hI
  rw [Finset.affineCombination_eq_linear_combination _ _ _ hs] at hsum
  let w' (σ : Equiv.Perm ι) := if σ ∈ s then w σ else 0
  have hsum' : ∑ σ, w' σ • P Complex.I σ = D Complex.I := by
    simpa only [w', ite_smul, zero_smul, Fintype.sum_ite_mem] using hsum
  refine ⟨w', fun σ => by by_cases h : σ ∈ s <;> simp [w', h, hw], ?_, fun z => ?_⟩
  · simpa only [w', Fintype.sum_ite_mem] using hs
  · have he : ∑ σ, w' σ • P z σ = D z := by
      simpa only [map_sum, map_smul, hP, hD] using congrArg (replaceImaginaryUnit z) hsum'
    simpa only [Complex.real_smul, P, D, A, B] using he

/-- The same law works on a common affine line in the difference convention,
with one arbitrary eigenvalue of the second summand. -/
theorem exists_common_law_affine_one_complex_outlier (a b : ι → ℝ) (j : ι)
    (c s : ℂ) (hc : c ≠ 0) (U : Matrix ι ι ℂ) (hU : IsUnitary U) :
    let A (i : ι) := c * (a i : ℂ) + s
    let B (i : ι) := c * (b i : ℂ) - s
    ∃ w : Equiv.Perm ι → ℝ, (∀ σ, 0 ≤ w σ) ∧ (∑ σ, w σ) = 1 ∧
      ∀ z : ℂ, ∑ σ, (w σ : ℂ) * matchingProduct A (Function.update B j z) σ =
        determinantValue A (Function.update B j z) U := by
  intro A B
  obtain ⟨w, hw, hs, he⟩ := exists_common_law_one_complex_outlier a b j U hU
  refine ⟨w, hw, hs, fun z => ?_⟩
  let v := (z + s) / c
  let a₀ (i : ι) : ℂ := a i
  let b₀ := Function.update (fun i => (b i : ℂ)) j v
  have hB : Function.update B j z = fun i => c * b₀ i - s := by
    funext i
    by_cases h : i = j
    · subst i
      simp only [b₀, Function.update_self, v]
      rw [mul_comm c, div_mul_cancel₀ _ hc, add_sub_cancel_right]
    · simp only [Function.update_of_ne h, b₀, B]
  have hP (σ : Equiv.Perm ι) : matchingProduct A (Function.update B j z) σ =
      c ^ Fintype.card ι * matchingProduct a₀ b₀ σ := by
    rw [hB]
    exact (matchingProduct_shift (fun i => c * a₀ i) (fun i => c * b₀ i) s σ).trans
      (matchingProduct_scale a₀ b₀ c σ)
  have hD : determinantValue A (Function.update B j z) U =
      c ^ Fintype.card ι * determinantValue a₀ b₀ U := by
    rw [hB]
    exact (determinantValue_shift (fun i => c * a₀ i) (fun i => c * b₀ i) hU s).trans
      (determinantValue_scale a₀ b₀ U c)
  calc
    _ = ∑ σ, c ^ Fintype.card ι * ((w σ : ℂ) * matchingProduct a₀ b₀ σ) := by
      apply Finset.sum_congr rfl
      intro σ _
      rw [hP σ, mul_left_comm (w σ : ℂ)]
    _ = _ := by rw [← Finset.mul_sum, he v, hD]

/-- A pole-free common Möbius change preserves a single law for all outlier
values away from the pole. The fixed transformed entries may lie on any
common affine line in the difference convention. -/
theorem exists_common_law_mobius_one_complex_outlier (a b : ι → ℂ) (j : ι)
    (t c s : ℂ) (hc : c ≠ 0) (α β : ι → ℝ)
    (ha₀ : ∀ i, 1 - t * a i ≠ 0) (hb₀ : ∀ i, i ≠ j → 1 + t * b i ≠ 0)
    (ha : mobiusSpectrum t a = fun i => c * (α i : ℂ) + s)
    (hb : ∀ i, i ≠ j → mobiusSpectrum (-t) b i = c * (β i : ℂ) - s)
    (U : Matrix ι ι ℂ) (hU : IsUnitary U) :
    ∃ w : Equiv.Perm ι → ℝ, (∀ σ, 0 ≤ w σ) ∧ (∑ σ, w σ) = 1 ∧
      ∀ z : ℂ, 1 + t * z ≠ 0 →
        ∑ σ, (w σ : ℂ) * matchingProduct a (Function.update b j z) σ =
          determinantValue a (Function.update b j z) U := by
  obtain ⟨w, hw, hs, he⟩ := exists_common_law_affine_one_complex_outlier α β j c s hc U hU
  refine ⟨w, hw, hs, fun z hz => ?_⟩
  let B := Function.update b j z
  let v := z / (1 + t * z)
  have hB₀ (i : ι) : 1 + t * B i ≠ 0 := by
    by_cases h : i = j
    · subst i
      simpa only [B, Function.update_self] using hz
    · simpa only [B, Function.update_of_ne h] using hb₀ i h
  have hB : mobiusSpectrum (-t) B = Function.update (fun i => c * (β i : ℂ) - s) j v := by
    funext i
    by_cases h : i = j
    · subst i
      simp only [mobiusSpectrum, B, Function.update_self, neg_mul, sub_neg_eq_add, v]
    · simp only [Function.update_of_ne h]
      simpa only [mobiusSpectrum, B, Function.update_of_ne h] using hb i h
  have h := he v
  rw [← ha, ← hB] at h
  simp_rw [matchingProduct_mobius a B t _ ha₀ hB₀,
    determinantValue_mobius a B U hU t ha₀ hB₀, ← mul_div_assoc, ← Finset.sum_div] at h
  have hden : mobiusDenominator a B t ≠ 0 :=
    mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun i _ => ha₀ i)
      (Finset.prod_ne_zero_iff.mpr fun i _ => hB₀ i)
  have hmul := congrArg (fun x : ℂ => x * mobiusDenominator a B t) h
  simpa only [div_mul_cancel₀ _ hden, B] using hmul

/-- At nonzero support height, each possible partner of the outlier accounts
for at most one active label if all complex matching products are distinct. -/
theorem card_contacts_le_of_one_complex_outlier (a b : ι → ℝ) (j : ι) (z η : ℂ) (h : ℝ)
    (h₀ : h ≠ 0)
    (hinj : Function.Injective (matchingProduct (fun i => (a i : ℂ))
      (Function.update (fun i => (b i : ℂ)) j z))) :
    (Finset.univ.filter (fun σ : Equiv.Perm ι =>
      (η * matchingProduct (fun i => (a i : ℂ)) (Function.update (fun i => (b i : ℂ)) j z) σ).re =
        h)).card ≤ Fintype.card ι := by
  let P := matchingProduct (fun i => (a i : ℂ)) (Function.update (fun i => (b i : ℂ)) j z)
  let T := Finset.univ.filter (fun σ : Equiv.Perm ι => (η * P σ).re = h)
  let r (i : ι) := (η * ((a i : ℂ) + z)).re
  let R (σ : Equiv.Perm ι) := ∏ k ∈ Finset.univ.erase j, a (σ k) + b k
  have hP (σ : Equiv.Perm ι) : P σ = ((a (σ j) : ℂ) + z) * (R σ : ℂ) :=
    matchingProduct_one_complex_outlier a b j z σ
  have hr (σ : ↥T) : r (σ.1 j) * R σ.1 = h := by
    have hp := (Finset.mem_filter.mp σ.property).2
    rw [hP, ← mul_assoc] at hp
    simpa only [r, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero] using hp
  have hpartner : Function.Injective (fun σ : ↥T => σ.1 j) := by
    intro σ τ hστ
    change σ.1 j = τ.1 j at hστ
    have hσ := hr σ
    have hτ := hr τ
    rw [← hστ] at hτ
    have hn : r (σ.1 j) ≠ 0 := fun hz => h₀ (by simpa only [hz, zero_mul] using hσ.symm)
    have hR : R σ.1 = R τ.1 := mul_left_cancel₀ hn (hσ.trans hτ.symm)
    apply Subtype.ext
    apply hinj
    change P σ.1 = P τ.1
    rw [hP σ.1, hP τ.1, hστ, hR]
  change T.card ≤ Fintype.card ι
  rw [← Fintype.card_coe T]
  exact Fintype.card_le_of_injective _ hpartner

end

end MOC
