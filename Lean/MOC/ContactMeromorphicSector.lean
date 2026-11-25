import MOC.PositiveLaurentSector
import MOC.ContactAsymptoticObstruction
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Meromorphic.Order

/-! Turn a polynomial-growth bound on an affine curve end into a meromorphic
germ, and then take the ratio with the prescribed pole. The argument
uses removable singularities rather than the Puiseux expansion theorem;
for the latter see Wall, DOI: 10.1017/CBO9780511617560.003. -/

open Filter Set Function
open scoped Topology

namespace MOC

/-- Holomorphic on a punctured disk, with a polynomial-growth bound, implies
meromorphy at the missing center. -/
theorem meromorphicAt_zero_of_eventually_pow_mul_norm_bounded {f : ℂ → ℂ} (N : ℕ)
    (hd : ∀ᶠ z in 𝓝[≠] (0 : ℂ), DifferentiableAt ℂ f z)
    (hb : ∃ C : ℝ, ∀ᶠ z in 𝓝[≠] (0 : ℂ), ‖z‖ ^ N * ‖f z‖ ≤ C) :
    MeromorphicAt f 0 := by
  obtain ⟨C, hC⟩ := hb
  let u : ℂ → ℂ := fun z => z ^ N * f z
  have hdu : ∀ᶠ z in 𝓝[≠] (0 : ℂ), DifferentiableAt ℂ u z := by
    filter_upwards [hd] with z hz
    exact ((differentiableAt_id (𝕜 := ℂ) (x := z)).pow N).mul hz
  have hbu : IsBoundedUnder (· ≤ ·) (𝓝[≠] (0 : ℂ)) (fun z => ‖u z - u 0‖) :=
    ⟨C + ‖u 0‖, eventually_map.2 (hC.mono fun z hz =>
      (norm_sub_le _ _).trans (add_le_add_right (by simpa [u, norm_mul, norm_pow] using hz) _))⟩
  let v := update u 0 (limUnder (𝓝[≠] (0 : ℂ)) u)
  have hlim := Complex.tendsto_limUnder_of_differentiable_on_punctured_nhds_of_bounded_under hdu hbu
  have hv : AnalyticAt ℂ v 0 := by
    apply Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
    · filter_upwards [hdu, self_mem_nhdsWithin (s := ({0} : Set ℂ)ᶜ)] with z hz hne
      apply hz.congr_of_eventuallyEq
      filter_upwards [eventually_ne_nhds hne] with w hw
      simp [v, update_of_ne hw]
    · exact continuousAt_update_same.2 hlim
  apply MeromorphicAt.iff_eventuallyEq_zpow_smul_analyticAt.mpr
  refine ⟨-(N : ℤ), v, hv, ?_⟩
  filter_upwards [self_mem_nhdsWithin (s := ({0} : Set ℂ)ᶜ)] with z hz
  have hne : z ≠ 0 := hz
  simp [v, update_of_ne hne, u, zpow_neg, zpow_natCast, smul_eq_mul, ← mul_assoc, hne]

private noncomputable def meromorphicRay (θ : ℝ) (t : ℝ) : ℂ :=
  (t : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)

private theorem meromorphicRay_tendsto (θ : ℝ) :
    Tendsto (meromorphicRay θ) (𝓝[>] (0 : ℝ)) (𝓝[≠] (0 : ℂ)) := by
  apply tendsto_nhdsWithin_iff.2
  refine ⟨?_, ?_⟩
  · have h : ContinuousAt (meromorphicRay θ) 0 := by unfold meromorphicRay; fun_prop
    simpa [meromorphicRay] using h.continuousWithinAt.tendsto
  · filter_upwards [self_mem_nhdsWithin (s := Ioi (0 : ℝ))] with t ht
    exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt ht)) (Complex.exp_ne_zero _)

private theorem pole_scaled_ray_eq (t θ : ℝ) (k : ℕ) (ht : 0 < t) (w : ℂ) :
    (t : ℂ) ^ k * ((meromorphicRay θ t) ^ (-(k : ℤ)) * w) =
       Complex.exp (-((k : ℝ) * θ : ℝ) * Complex.I) * w := by
  have hne : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  let e := Complex.exp ((θ : ℂ) * Complex.I)
  have he : e ≠ 0 := Complex.exp_ne_zero _
  change (t : ℂ) ^ k * (((t : ℂ) * e) ^ (-(k : ℤ)) * w) = _
  rw [zpow_neg, zpow_natCast, ← mul_assoc, mul_pow]
  have hcancel : (t : ℂ) ^ k * ((t : ℂ) ^ k * e ^ k)⁻¹ = (e ^ k)⁻¹ := by
    field_simp [pow_ne_zero _ hne, pow_ne_zero _ he]
  rw [hcancel]
  dsimp only [e]
  rw [← Complex.exp_nat_mul, ← Complex.exp_neg]
  congr 2
  push_cast
  ring

/-- A meromorphic germ that has nonnegative real part on the rays of the
positive sector of z⁻ᵐ has a finite, nonnegative real limit after division
by z⁻ᵐ. The limit holds through the entire punctured neighborhood. -/
theorem tendsto_pow_mul_of_meromorphic_sector {f : ℂ → ℂ} (hmf : MeromorphicAt f 0)
    {m : ℕ} (hm : 0 < m)
    (hsec : ∀ θ : ℝ, |θ| < Real.pi / (2 * (m : ℝ)) →
      ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ),
        0 ≤ (f ((t : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))).re) :
    ∃ c : ℝ, 0 ≤ c ∧ Tendsto (fun z : ℂ => z ^ m * f z) (𝓝[≠] (0 : ℂ)) (𝓝 (c : ℂ)) := by
  by_cases ht : hmf.order = ⊤
  · refine ⟨0, le_rfl, ?_⟩
    simp only [Complex.ofReal_zero]
    apply tendsto_const_nhds.congr'
    filter_upwards [hmf.order_eq_top_iff.mp ht] with z hz
    simp [hz]
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp ht
  obtain ⟨g, hg, hgn, hfg⟩ := hmf.order_eq_int_iff.mp hn.symm
  have hscaled (hbound : 0 < (m : ℤ) + n) : ∃ c : ℝ, 0 ≤ c ∧
      Tendsto (fun z : ℂ => z ^ m * f z) (𝓝[≠] (0 : ℂ)) (𝓝 (c : ℂ)) := by
    refine ⟨0, le_rfl, ?_⟩
    obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le hbound.le
    have hk' : k ≠ 0 := by omega
    have heq : (fun z : ℂ => z ^ m * f z) =ᶠ[𝓝[≠] (0 : ℂ)]
        (fun z : ℂ => z ^ k * g z) := by
      filter_upwards [hfg, self_mem_nhdsWithin (s := ({0} : Set ℂ)ᶜ)] with z hz hne
      rw [hz, sub_zero, smul_eq_mul, ← mul_assoc, ← zpow_natCast z m,
        ← zpow_add₀ (show z ≠ 0 from hne), hk, zpow_natCast]
    have hc : ContinuousAt (fun z : ℂ => z ^ k * g z) 0 :=
        (continuousAt_id.pow k).mul hg.continuousAt
    simpa [zero_pow hk'] using hc.continuousWithinAt.tendsto.congr' heq.symm
  by_cases hnpos : 0 ≤ n
  · exact hscaled (by omega)
  obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ -n)
  have hkpos : 0 < k := by omega
  have hnk : n = -(k : ℤ) := by omega
  have hangular : ∀ θ : ℝ, |θ| < Real.pi / (2 * (m : ℝ)) →
      0 ≤ (g 0).re * Real.cos ((k : ℝ) * θ) + (g 0).im * Real.sin ((k : ℝ) * θ) := by
    intro θ hθ
    have heq : (fun t : ℝ => (t : ℂ) ^ k * f (meromorphicRay θ t)) =ᶠ[𝓝[>] (0 : ℝ)]
        (fun t : ℝ => Complex.exp (-((k : ℝ) * θ : ℝ) * Complex.I) * g (meromorphicRay θ t)) := by
      filter_upwards [(meromorphicRay_tendsto θ).eventually hfg,
        self_mem_nhdsWithin (s := Ioi (0 : ℝ))] with t ht ht'
      rw [ht, hnk, sub_zero, smul_eq_mul, pole_scaled_ray_eq t θ k ht']
    have hg' : Tendsto (fun t : ℝ => g (meromorphicRay θ t)) (𝓝[>] (0 : ℝ)) (𝓝 (g 0)) :=
      hg.continuousAt.continuousWithinAt.tendsto.comp (meromorphicRay_tendsto θ)
    have hlim := ((tendsto_const_nhds (x := Complex.exp (-((k : ℝ) * θ : ℝ) * Complex.I))).mul hg').congr' heq.symm
    have hlim' := Complex.continuous_re.continuousAt.tendsto.comp hlim
    have hnon : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), 0 ≤ ((t : ℂ) ^ k * f (meromorphicRay θ t)).re := by
      filter_upwards [hsec θ hθ, self_mem_nhdsWithin (s := Ioi (0 : ℝ))] with t ht ht'
      have hpos : 0 ≤ t := le_of_lt ht'
      rw [← Complex.ofReal_pow, Complex.re_ofReal_mul]
      exact mul_nonneg (pow_nonneg hpos _) ht
    have hval := ge_of_tendsto hlim' hnon
    rw [show -((k : ℝ) * θ : ℝ) * Complex.I = ((-((k : ℝ) * θ) : ℝ) : ℂ) * Complex.I by
          push_cast; rfl,
      Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, add_mul] at hval
    simp only [Complex.add_re, mul_assoc, Complex.re_ofReal_mul, Complex.I_mul_re,
      Real.cos_neg, Real.sin_neg, neg_mul_neg] at hval
    simpa only [mul_comm] using hval
  classical
  have hnn : (g 0).re ≠ 0 ∨ (g 0).im ≠ 0 := by
    by_cases hre : (g 0).re = 0
    · right
      intro him
      apply hgn
      exact Complex.ext (by simpa using hre) (by simpa using him)
    · exact Or.inl hre
  obtain ⟨hkm, he⟩ := positive_laurent_sector (m : ℝ) (k : ℝ) (g 0).re (g 0).im
    (by exact_mod_cast hm) (by exact_mod_cast hkpos) hnn hangular
  have hkm' : k ≤ m := by exact_mod_cast hkm
  by_cases heq : k = m
  · obtain ⟨hpos, him⟩ := he (by simp [heq])
    refine ⟨(g 0).re, hpos.le, ?_⟩
    have hgval : ((g 0).re : ℂ) = g 0 := by
      apply Complex.ext <;> simp [him]
    rw [hgval]
    apply hg.continuousAt.continuousWithinAt.tendsto.congr'
    filter_upwards [hfg, self_mem_nhdsWithin (s := ({0} : Set ℂ)ᶜ)] with z hz hne
    have hn' : n = -(m : ℤ) := by omega
    rw [hz, sub_zero, smul_eq_mul, hn', zpow_neg, zpow_natCast, ← mul_assoc,
      mul_inv_cancel₀ (pow_ne_zero _ (show z ≠ 0 from hne)), one_mul]
  · exact hscaled (by omega)


/-- A meromorphic germ either tends to a finite value or its reciprocal
tends to zero through nonzero values. -/
theorem meromorphicAt_zero_tendsto_or_inv {f : ℂ → ℂ} (hf : MeromorphicAt f 0) :
    (∃ c : ℂ, Tendsto f (𝓝[≠] (0 : ℂ)) (𝓝 c)) ∨
      Tendsto (fun z => (f z)⁻¹) (𝓝[≠] (0 : ℂ)) (𝓝[≠] (0 : ℂ)) := by
  rcases le_or_gt 0 hf.order with h | h
  · exact Or.inl (hf.tendsto_nhds_of_order_nonneg h)
  · exact Or.inr (Filter.tendsto_inv₀_cobounded'.comp (hf.tendsto_cobounded_of_order_neg h))

/-- A punctured holomorphic parameter with the prescribed gap pole
cannot remain in the support chamber on its entire positive sector. -/
theorem not_profile_gap_meromorphic_sector
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (U : Matrix ι ι ℂ) (hU : IsUnitary U) (η : ℂ) (hη : η ≠ 0)
    (r : Equiv.Perm ι) (P : ℂ → Equiv.Perm ι → ℂ)
    {m : ℕ} (hm : 0 < m)
    (hex : ∀ᶠ z in 𝓝[≠] (0 : ℂ), ∃ a b : ι → ℂ, matchingProduct a b = P z)
    (hmero : ∀ q, MeromorphicAt (fun z => P z q) 0)
    (hgap : ∀ᶠ z in 𝓝[≠] (0 : ℂ), matchingProfileDetGap U η r (P z) = (z ^ m)⁻¹)
    (hsec : ∀ q (θ : ℝ), |θ| < Real.pi / (2 * (m : ℝ)) →
      ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), 0 ≤
        (η * (P ((t : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) r -
          P ((t : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) q)).re) : False := by
  let D (q : Equiv.Perm ι) (z : ℂ) : ℂ := η * (P z r - P z q)
  have hD (q : Equiv.Perm ι) : MeromorphicAt (D q) 0 :=
    (MeromorphicAt.const η 0).mul ((hmero r).sub (hmero q))
  have hDlim (q : Equiv.Perm ι) : ∃ c : ℝ, 0 ≤ c ∧
      Tendsto (fun z => z ^ m * D q z) (𝓝[≠] (0 : ℂ)) (𝓝 (c : ℂ)) :=
    tendsto_pow_mul_of_meromorphic_sector (hD q) hm (hsec q)
  choose c hc hlim using hDlim
  let d (q : Equiv.Perm ι) : ℂ := -(c q : ℂ) / η
  have hdr : d r = 0 := by
    have hr := hlim r
    simp only [D, sub_self, mul_zero] at hr
    have h : (0 : ℂ) = (c r : ℂ) := tendsto_nhds_unique tendsto_const_nhds hr
    simp [d, ← h]
  have hreal (q : Equiv.Perm ι) : η * (d r - d q) = (c q : ℂ) := by
    rw [hdr]
    dsimp only [d]
    field_simp [hη]
  have hgapne : ∀ᶠ z in 𝓝[≠] (0 : ℂ), matchingProfileDetGap U η r (P z) ≠ 0 := by
    filter_upwards [hgap, self_mem_nhdsWithin (s := ({0} : Set ℂ)ᶜ)] with z hz hne
    rw [hz]
    exact inv_ne_zero (pow_ne_zero _ (show z ≠ 0 from hne))
  have hdlim (q : Equiv.Perm ι) :
      Tendsto (fun z => (P z q - P z r) / matchingProfileDetGap U η r (P z))
        (𝓝[≠] (0 : ℂ)) (𝓝 (d q)) := by
    apply ((hlim q).neg.div_const η).congr'
    filter_upwards [hgap] with z hz
    rw [hz]
    dsimp only [D]
    simp only [div_inv_eq_mul]
    field_simp [hη]
    ring
  refine not_profile_gap_asymptotic U hU η hη r P hex d hdlim hgapne ?_ ?_ ?_
  · intro q
    rw [hreal]
    exact Complex.ofReal_im _
  · intro q
    rw [hreal, Complex.ofReal_re]
    exact hc q
  · have ht : MeromorphicAt (fun z : ℂ => z ^ m * P z r) 0 :=
      ((MeromorphicAt.id (𝕜 := ℂ) 0).pow m).mul (hmero r)
    rcases meromorphicAt_zero_tendsto_or_inv ht with ⟨w, hw⟩ | hw
    · left
      refine ⟨w, hw.congr' ?_⟩
      filter_upwards [hgap] with z hz
      rw [hz, div_inv_eq_mul, mul_comm]
    · right
      refine ⟨(hw.mono_right nhdsWithin_le_nhds).congr' ?_, ?_⟩
      · filter_upwards [hgap] with z hz
        rw [hz, div_eq_mul_inv, mul_inv]
      · filter_upwards [hw.eventually self_mem_nhdsWithin] with z hz
        intro hzero
        apply hz
        simp [hzero]

end MOC
