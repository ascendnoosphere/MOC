import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Analysis.Complex.OpenMapping
import Mathlib.Analysis.Complex.ReImTopology
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Topology.LocalAtTarget
import Mathlib.Topology.Maps.Proper.CompactlyGenerated

/-! A complex polynomial can reach every target in an open connected strip
without leaving a chosen component of the inverse image. -/

open Bornology Filter Polynomial
open scoped Topology

namespace MOC

/-- Evaluating a nonconstant complex polynomial is both an open and a closed map. -/
theorem polynomial_eval_open_and_closed (p : ℂ[X]) (hp : 0 < p.degree) :
    IsOpenMap (fun z => p.eval z) ∧ IsClosedMap (fun z => p.eval z) := by
  have hnorm : Tendsto (fun z : ℂ => ‖p.eval z‖) (cobounded ℂ) atTop :=
    p.tendsto_norm_atTop hp tendsto_norm_cobounded_atTop
  have ht : Tendsto (fun z => p.eval z) (cobounded ℂ) (cobounded ℂ) :=
    tendsto_norm_atTop_iff_cobounded.mp hnorm
  have hproper : IsProperMap (fun z => p.eval z) :=
    isProperMap_iff_tendsto_cocompact.mpr ⟨p.continuous,
      by simpa only [Metric.cobounded_eq_cocompact] using ht⟩
  refine ⟨?_, hproper.isClosedMap⟩
  have ha : AnalyticOnNhd ℂ (fun z => p.eval z) Set.univ :=
    AnalyticOnNhd.eval_polynomial p
  rcases ha.is_constant_or_isOpen isPreconnected_univ with ⟨w, hw⟩ | ho
  · have he : ∀ᶠ z : ℂ in cobounded ℂ, ‖w‖ < ‖p.eval z‖ :=
      hnorm.eventually (eventually_gt_atTop ‖w‖)
    obtain ⟨z, hz⟩ := he.exists
    rw [hw z (Set.mem_univ z)] at hz
    exact (lt_irrefl _ hz).elim
  · exact fun s hs => ho s (Set.subset_univ s) hs

/-- Starting inside an open set, one can choose an imaginary band for the
polynomial values that avoids all values taken at finitely many excluded points. -/
theorem exists_polynomial_imaginary_band_avoiding_finite
    (p : ℂ[X]) (hp : 0 < p.degree) {W B : Set ℂ} (hW : IsOpen W) (hn : W.Nonempty)
    (hB : B.Finite) :
    ∃ x ∈ W, ∃ r > 0, Metric.ball (p.eval x).im r ⊆
      (((fun z => (p.eval z).im) '' B)ᶜ : Set ℝ) := by
  let f (z : ℂ) := p.eval z
  let D := Complex.im '' (f '' W)
  let R : Set ℝ := (fun z => (f z).im) '' B
  have hD : IsOpen D :=
    Complex.isOpenMap_im _ ((polynomial_eval_open_and_closed p hp).1 W hW)
  have hR : R.Finite := hB.image _
  obtain ⟨x₀, hx₀⟩ := hn
  let m := (f x₀).im
  have hm : m ∈ D := ⟨f x₀, ⟨x₀, hx₀, rfl⟩, rfl⟩
  obtain ⟨s, hs, hsD⟩ := Metric.isOpen_iff.mp hD m hm
  obtain ⟨y, hy, hyR⟩ :=
    (Set.Ioo_infinite (show m < m + s by linarith only [hs])).exists_not_mem_finite hR
  have hyD : y ∈ D := hsD (by
    rw [Metric.mem_ball, Real.dist_eq, abs_of_pos (sub_pos.mpr hy.1)]
    linarith only [hy.2])
  obtain ⟨w, ⟨x, hx, rfl⟩, rfl⟩ := hyD
  obtain ⟨r, hr, hband⟩ := Metric.isOpen_iff.mp hR.isClosed.isOpen_compl (f x).im hyR
  exact ⟨x, hx, r, hr, hband⟩

/-- For a nonconstant complex polynomial, each connected component of the
inverse image of an open connected target set maps onto that target set.
A horizontal strip can therefore keep a determinant projection above its
support level while excluding finitely many collision values. -/
theorem polynomial_component_image_eq (p : ℂ[X]) (hp : 0 < p.degree)
    {V : Set ℂ} (hV : IsOpen V) (hc : IsPreconnected V) {x : ℂ}
    (hx : p.eval x ∈ V) :
    (fun z => p.eval z) '' connectedComponentIn ((fun z => p.eval z) ⁻¹' V) x = V := by
  let f : ℂ → ℂ := fun z => p.eval z
  let X := f ⁻¹' V
  have hx' : x ∈ X := hx
  let x' : X := ⟨x, hx'⟩
  let g := V.restrictPreimage f
  let C := connectedComponent x'
  letI : LocallyConnectedSpace X := (hV.preimage p.continuous).locallyConnectedSpace
  letI : PreconnectedSpace V := isPreconnected_iff_preconnectedSpace.mp hc
  obtain ⟨ho, hc'⟩ := polynomial_eval_open_and_closed p hp
  have hcl : IsClopen (g '' C) := ⟨hc'.restrictPreimage V _ isClosed_connectedComponent,
    ho.restrictPreimage V _ isOpen_connectedComponent⟩
  have hne : (g '' C).Nonempty := ⟨g x', x', mem_connectedComponent, rfl⟩
  have hall : g '' C = Set.univ := (isClopen_iff.mp hcl).resolve_left hne.ne_empty
  change f '' connectedComponentIn X x = V
  apply le_antisymm
  · rintro y ⟨z, hz, rfl⟩
    exact connectedComponentIn_subset X x hz
  · intro y hy
    have hy' : (⟨y, hy⟩ : V) ∈ g '' C := hall.symm ▸ Set.mem_univ _
    obtain ⟨z, hz, hzy⟩ := hy'
    refine ⟨z.val, ?_, congrArg Subtype.val hzy⟩
    rw [connectedComponentIn_eq_image hx']
    exact ⟨z, hz, rfl⟩

/-- Along an escaping polynomial component, every lower-degree error is
negligible compared with the polynomial that defines the component. -/
theorem polynomial_ratio_tendsto_zero (q p : ℂ[X]) (h : q.natDegree < p.natDegree) :
    Tendsto (fun z => q.eval z / p.eval z) (cobounded ℂ) (𝓝 0) := by
  let r := reflect p.natDegree q
  let s := p.reverse
  have hr₀ : r.eval 0 = 0 := by
    rw [← coeff_zero_eq_eval_zero, show r = reflect p.natDegree q from rfl,
      coeff_reflect, revAt_zero, coeff_eq_zero_of_natDegree_lt h]
  have hs₀ : s.eval 0 ≠ 0 := by
    have hp : p ≠ 0 := by
      intro hp
      simp only [hp, natDegree_zero, Nat.not_lt_zero] at h
    rw [← coeff_zero_eq_eval_zero, show s = p.reverse from rfl, coeff_zero_reverse]
    exact leadingCoeff_ne_zero.mpr hp
  have hlim : Tendsto (fun z => r.eval z / s.eval z) (𝓝 (0 : ℂ)) (𝓝 (0 : ℂ)) := by
    simpa only [hr₀, zero_div] using
      (r.continuous.continuousAt.tendsto.div s.continuous.continuousAt.tendsto hs₀)
  have hev : ∀ᶠ z : ℂ in cobounded ℂ, z ≠ 0 :=
    (tendsto_norm_cobounded_atTop.eventually_gt_atTop 0).mono fun _ hz => norm_pos_iff.mp hz
  have hratio : (fun z => q.eval z / p.eval z) =ᶠ[cobounded ℂ]
      fun z => r.eval z⁻¹ / s.eval z⁻¹ := by
    filter_upwards [hev] with z hz
    letI := invertibleOfNonzero hz
    have hq : r.eval z⁻¹ * z ^ p.natDegree = q.eval z := by
      simpa only [invOf_eq_inv] using
        eval₂_reflect_mul_pow (RingHom.id ℂ) z p.natDegree q h.le
    have hp : s.eval z⁻¹ * z ^ p.natDegree = p.eval z := by
      simpa only [invOf_eq_inv] using eval₂_reverse_mul_pow (RingHom.id ℂ) z p
    rw [← hq, ← hp, mul_div_mul_right _ _ (pow_ne_zero _ hz)]
  exact (tendsto_congr' hratio).mpr (hlim.comp tendsto_inv₀_cobounded)

/-- If a competing matching polynomial has a positive real multiple of the
determinant's leading coefficient, its real value becomes arbitrarily large
on any inverse-image component whose target contains an eventual horizontal ray. -/
theorem exists_large_real_part_on_polynomial_component
    (p q : ℂ[X]) (hp : 0 < p.degree) (c : ℝ) (hc : 0 < c)
    (hrem : (q - C (c : ℂ) * p).natDegree < p.natDegree)
    {V : Set ℂ} (hV : IsOpen V) (hVc : IsPreconnected V) {x : ℂ} (hx : p.eval x ∈ V)
    (d T₀ H : ℝ) (hRay : ∀ t ≥ T₀, (t : ℂ) + (d : ℂ) * Complex.I ∈ V) :
    ∃ z ∈ connectedComponentIn ((fun z => p.eval z) ⁻¹' V) x, H < (q.eval z).re := by
  let r := q - C (c : ℂ) * p
  have hr : Tendsto (fun z => ‖r.eval z / p.eval z‖) (cobounded ℂ) (𝓝 0) := by
    simpa only [norm_zero] using (polynomial_ratio_tendsto_zero r p hrem).norm
  have hnear : ∀ᶠ z : ℂ in cobounded ℂ, ‖r.eval z / p.eval z‖ < c / 4 :=
    hr.eventually (Iio_mem_nhds (by positivity))
  obtain ⟨R, -, hR⟩ := (Filter.hasBasis_cobounded_norm.eventually_iff.mp hnear)
  let R' := max R 0
  have hball : (0 : ℂ) ∈ Metric.closedBall 0 R' := by
    rw [Metric.mem_closedBall, dist_self]
    exact le_max_right R 0
  obtain ⟨y, hy, hymax⟩ := (isCompact_closedBall (0 : ℂ) R').exists_isMaxOn
    ⟨0, hball⟩ p.continuous.norm.continuousOn
  obtain ⟨T, hT⟩ := exists_gt (max T₀ (max |d| (max ‖p.eval y‖ (H / (c / 2)))))
  have hT₀ : T₀ ≤ T := (le_max_left _ _).trans hT.le
  have hTd : |d| < T := (le_max_left _ _).trans_lt ((le_max_right T₀ _).trans_lt hT)
  have hTy : ‖p.eval y‖ < T := (le_max_left _ _).trans_lt
    ((le_max_right |d| _).trans_lt ((le_max_right T₀ _).trans_lt hT))
  have hTH : H / (c / 2) < T := (le_max_right _ _).trans_lt
    ((le_max_right |d| _).trans_lt ((le_max_right T₀ _).trans_lt hT))
  have hH : H < c / 2 * T := by
    simpa only [mul_comm] using (div_lt_iff₀ (show 0 < c / 2 by positivity)).mp hTH
  have hTpos : 0 < T := lt_of_le_of_lt (abs_nonneg _) hTd
  obtain ⟨z, hz, hzEval⟩ : (T : ℂ) + (d : ℂ) * Complex.I ∈
      (fun z => p.eval z) '' connectedComponentIn ((fun z => p.eval z) ⁻¹' V) x := by
    rw [polynomial_component_image_eq p hp hV hVc hx]
    exact hRay T hT₀
  change p.eval z = (T : ℂ) + (d : ℂ) * Complex.I at hzEval
  have hre : (p.eval z).re = T := by rw [hzEval]; simp [Complex.mul_re]
  have hnormlo : T ≤ ‖p.eval z‖ := by
    have h := Complex.abs_re_le_norm (p.eval z)
    simpa only [hre, abs_of_pos hTpos] using h
  have hnormhi : ‖p.eval z‖ ≤ T + |d| := by
    rw [hzEval]
    exact (norm_add_le _ _).trans_eq (by
      simp [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hTpos])
  have hzR : R ≤ ‖z‖ := by
    by_contra hn
    have hzball : z ∈ Metric.closedBall 0 R' := by
      rw [Metric.mem_closedBall, dist_zero_right]
      exact (lt_of_not_ge hn).le.trans (le_max_left _ _)
    exact (not_le_of_gt hTy) (hnormlo.trans (hymax hzball))
  have hratio : ‖r.eval z / p.eval z‖ < c / 4 := hR hzR
  have hsmall : ‖r.eval z‖ < c / 2 * T := by
    apply (lt_of_lt_of_le ((div_lt_iff₀ (hTpos.trans_le hnormlo)).mp
      (by simpa only [norm_div] using hratio)))
    have hnorm : ‖p.eval z‖ ≤ 2 * T := by linarith only [hnormhi, hTd]
    nlinarith only [mul_le_mul_of_nonneg_left hnorm (show 0 ≤ c / 4 by positivity)]
  have hreal : -(c / 2 * T) < (r.eval z).re := by
    have h := Complex.abs_re_le_norm (r.eval z)
    linarith only [h, hsmall, neg_abs_le (r.eval z).re]
  have he : (r.eval z).re = (q.eval z).re - c * T := by
    simp only [r, eval_sub, eval_mul, eval_C, Complex.sub_re, Complex.re_ofReal_mul, hre]
  exact ⟨z, hz, by linarith only [hH, hreal, he]⟩

end MOC
