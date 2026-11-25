import MOC.HalfPlaneContactLimit
import MOC.ContactAsymptoticObstruction

/-! The half-plane sheet needed by the varying-gap contact argument
cannot exist. In contrast to the pole-sector argument, this criterion
does not require a meromorphic expansion of any profile coordinate. -/

open Filter Set Matrix
open scoped Topology

namespace MOC

private theorem complex_ratio_cluster_or_escape {α : Type*} {l : Filter α} [l.NeBot]
    (f : α → ℂ) :
    (∃ L : Ultrafilter α, L ≤ l ∧ ∃ c : ℂ, Tendsto f L (𝓝 c)) ∨
      (Tendsto (fun x => (f x)⁻¹) l (𝓝 0) ∧ ∀ᶠ x in l, f x ≠ 0) := by
  by_cases h : Tendsto (fun x => ‖f x‖) l atTop
  · right
    constructor
    · apply tendsto_iff_norm_sub_tendsto_zero.mpr
      simpa only [sub_zero, norm_inv, Function.comp_apply] using tendsto_inv_atTop_zero.comp h
    · filter_upwards [(tendsto_atTop.mp h) (1 : ℝ)] with x hx
      intro hzero
      exact (not_le_of_gt zero_lt_one) (by simpa [hzero] using hx)
  · left
    rw [tendsto_atTop] at h
    push_neg at h
    obtain ⟨R, hR⟩ := h
    have hsmall : ∃ᶠ x in l, ‖f x‖ < R := by
      simpa only [Filter.Frequently, not_lt] using hR
    have hb : ∃ᶠ x in l, f x ∈ Metric.closedBall (0 : ℂ) R := by
      apply hsmall.mono
      intro x hx
      simpa only [Metric.mem_closedBall, dist_zero_right] using hx.le
    obtain ⟨c, _, hc⟩ := (isCompact_closedBall (0 : ℂ) R).exists_mapClusterPt_of_frequently hb
    obtain ⟨L, hL, hlim⟩ := mapClusterPt_iff_ultrafilter.mp hc
    exact ⟨L, hL, c, hlim⟩

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- Gap-normalized differences alone forbid the asymptotic. No hypothesis
is needed on the common pivot coordinate: pass to a convergent filter or
use escape of its norm. -/
theorem not_profile_gap_asymptotic_of_differences
    {α : Type*} {l : Filter α} [l.NeBot]
    (U : Matrix ι ι ℂ) (hU : IsUnitary U) (η : ℂ) (hη : η ≠ 0) (r : Equiv.Perm ι)
    (P : α → Equiv.Perm ι → ℂ)
    (hex : ∀ᶠ t in l, ∃ a b : ι → ℂ, matchingProduct a b = P t)
    (d : Equiv.Perm ι → ℂ)
    (hlim : ∀ q, Tendsto (fun t => (P t q - P t r) / matchingProfileDetGap U η r (P t)) l (𝓝 (d q)))
    (hgap : ∀ᶠ t in l, matchingProfileDetGap U η r (P t) ≠ 0)
    (hreal : ∀ q, (η * (d r - d q)).im = 0)
    (hpos : ∀ q, 0 ≤ (η * (d r - d q)).re) : False := by
  let f (t : α) := P t r / matchingProfileDetGap U η r (P t)
  rcases complex_ratio_cluster_or_escape (l := l) f with ⟨L, hL, c, hc⟩ | ⟨he, hne⟩
  · exact not_profile_gap_asymptotic U hU η hη r P (hex.filter_mono hL) d
      (fun q => (hlim q).mono_left hL) (hgap.filter_mono hL) hreal hpos (Or.inl ⟨c, hc⟩)
  · exact not_profile_gap_asymptotic U hU η hη r P hex d hlim hgap hreal hpos (Or.inr ⟨by
      simpa only [f, inv_div] using he,
      hne.mono fun t ht hzero => ht (by simp [f, hzero])⟩)

/-- A half-plane section with its affine base parameter equal to the
determinant gap cannot keep all matching deficits nonnegative. The
coordinates only have to be holomorphic on that half-plane. -/
theorem not_exact_profile_halfPlane_section
    (U : Matrix ι ι ℂ) (hU : IsUnitary U) (η : ℂ) (hη : η ≠ 0) (r : Equiv.Perm ι)
    (P : ℂ → Equiv.Perm ι → ℂ) (c : ℝ)
    (hex : ∀ z, 0 < z.re → ∃ a b : ι → ℂ, matchingProduct a b = P z)
    (hhol : ∀ q, DifferentiableOn ℂ (fun z => P z q) {z | 0 < z.re})
    (hgap : ∀ z, 0 < z.re → matchingProfileDetGap U η r (P z) = z + c)
    (hpos : ∀ z, 0 < z.re → ∀ q, 0 ≤ (η * (P z r - P z q)).re) : False := by
  let F (q : Equiv.Perm ι) (z : ℂ) := η * (P z r - P z q)
  have hlim (q : Equiv.Perm ι) :
      ∃ a : ℝ, 0 ≤ a ∧ Tendsto (fun x : ℝ => F q x / (x : ℂ)) atTop (𝓝 (a : ℂ)) :=
    tendsto_nonnegativeReal_div_atTop (F q) ((hhol r).sub (hhol q) |>.const_mul η)
      (fun z hz => hpos z hz q)
  choose a ha hT using hlim
  have ha0 : a r = 0 := by
    have hconst : Tendsto (fun _ : ℝ => (0 : ℂ)) atTop (𝓝 0) := tendsto_const_nhds
    have he := tendsto_nhds_unique (by simpa [F] using hT r) hconst
    exact_mod_cast he
  let d (q : Equiv.Perm ι) := -(a q : ℂ) / η
  have hd (q : Equiv.Perm ι) : η * (d r - d q) = a q := by
    dsimp only [d]
    rw [ha0, Complex.ofReal_zero, neg_zero, zero_div, zero_sub, neg_div, neg_neg]
    exact mul_div_cancel₀ _ hη
  apply not_profile_gap_asymptotic_of_differences (l := atTop) U hU η hη r
    (fun x : ℝ => P (x : ℂ)) _ d _ _ (fun q => by rw [hd]; simp) (fun q => by rw [hd]; exact ha q)
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    exact hex x (by simpa using hx)
  · intro q
    have hc : Tendsto (fun x : ℝ => c / x) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
    have ho : Tendsto (fun x : ℝ => (1 : ℂ) + (c : ℂ) / (x : ℂ)) atTop (𝓝 1) := by
      simpa only [add_zero, Complex.ofReal_zero, Complex.ofReal_div, Function.comp_apply] using
        ((Complex.continuous_ofReal.tendsto 0).comp hc).const_add (1 : ℂ)
    have h := (((hT q).div ho one_ne_zero).neg.div_const η)
    rw [div_one] at h
    apply h.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ), eventually_gt_atTop (-c)] with x hx hxc
    rw [hgap x (by simpa using hx)]
    have hxn : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
    have hsum : (x : ℂ) + c ≠ 0 := by
      rw [← Complex.ofReal_add]
      exact Complex.ofReal_ne_zero.mpr (by linarith)
    have hn : (1 : ℂ) + (c : ℂ) / (x : ℂ) ≠ 0 := by
      rw [← div_self hxn, ← add_div]
      exact div_ne_zero hsum hxn
    dsimp only [F]
    field_simp [hη, hxn, hsum, hn]
    ring
  · filter_upwards [eventually_gt_atTop (0 : ℝ), eventually_gt_atTop (-c)] with x hx hxc
    rw [hgap x (by simpa using hx), ← Complex.ofReal_add]
    exact Complex.ofReal_ne_zero.mpr (by linarith)

end MOC
