import MOC.TracialLogDerivative
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.Abel

/-! The trace of the operator logarithm under strictly positive conjugation. -/

open Set Filter
open scoped Topology

namespace MOC

noncomputable section

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

private theorem tracial_scalar_map_le {a b : ℝ} (h : a ≤ b) :
    algebraMap ℝ A a ≤ algebraMap ℝ A b := by
  rw [← sub_nonneg, ← map_sub, Algebra.algebraMap_eq_smul_one]
  exact smul_nonneg' (sub_nonneg.mpr h) zero_le_one

private theorem isUnit_of_strict_spectral_gap (X : A) (hX : IsSelfAdjoint X)
    (m : ℝ) (hm : 0 < m) (hg : algebraMap ℝ A m ≤ X) : IsUnit X := by
  apply spectrum.isUnit_of_zero_not_mem ℝ
  intro h
  exact (not_le_of_gt hm) ((algebraMap_le_iff_le_spectrum hX).mp hg 0 h)

private theorem selfAdjoint_path_eventually_strict_gap
    (Y : ℝ → A) (s : ℝ) (hY : ContinuousAt Y s) (hsa : ∀ t, IsSelfAdjoint (Y t))
    (m : ℝ) (hm : 0 < m) (hg : algebraMap ℝ A m ≤ Y s) :
    ∀ᶠ t in 𝓝 s, IsSelfAdjoint (Y t) ∧
      ∃ r : ℝ, 0 < r ∧ algebraMap ℝ A r ≤ Y t := by
  have hcont : ContinuousAt (fun t => ‖Y t - Y s‖) s :=
    (hY.sub continuousAt_const).norm
  have hs : ‖Y s - Y s‖ < m / 2 := by
    simpa only [sub_self, norm_zero] using half_pos hm
  have hnear : ∀ᶠ t in 𝓝 s, ‖Y t - Y s‖ < m / 2 :=
    hcont.eventually (Iio_mem_nhds hs)
  filter_upwards [hnear] with t ht
  have hself : IsSelfAdjoint (Y t - Y s) := (hsa t).sub (hsa s)
  have hscalar : algebraMap ℝ A ‖Y t - Y s‖ ≤ algebraMap ℝ A (m / 2) :=
    tracial_scalar_map_le ht.le
  have hdiff : - (algebraMap ℝ A (m / 2)) ≤ Y t - Y s :=
    (neg_le_neg hscalar).trans hself.neg_algebraMap_norm_le_self
  refine ⟨hsa t, m / 2, half_pos hm, ?_⟩
  calc
    algebraMap ℝ A (m / 2) = algebraMap ℝ A m + - (algebraMap ℝ A (m / 2)) := by
      rw [← map_neg, ← map_add]
      congr 1
      ring
    _ ≤ Y s + (Y t - Y s) := add_le_add hg hdiff
    _ = Y t := by abel

private theorem strict_gap_conjugate
    (W U : A) (hW : IsSelfAdjoint W) (m r : ℝ) (hm : 0 < m) (hr : 0 < r)
    (hmW : algebraMap ℝ A m ≤ W) (hrU : algebraMap ℝ A r ≤ U) :
    algebraMap ℝ A (r * m ^ 2) ≤ W * U * W := by
  have hsm : ∀ x ∈ spectrum ℝ W, m ≤ x := (algebraMap_le_iff_le_spectrum hW).mp hmW
  have hcs : ContinuousOn (fun x : ℝ => x ^ 2) (spectrum ℝ W) :=
    (continuous_id.pow 2).continuousOn
  have hsq : algebraMap ℝ A (m ^ 2) ≤ W * W := by
    rw [← pow_two W, ← cfc_pow_id (R := ℝ) W 2 hW]
    refine (algebraMap_le_cfc_iff _ _ W hcs hW).mpr fun x hx =>
      pow_le_pow_left₀ hm.le (hsm x hx) 2
  have hscale : W * algebraMap ℝ A r * W = r • (W * W) := by
    rw [Algebra.algebraMap_eq_smul_one, mul_smul_comm, mul_one, smul_mul_assoc]
  calc
    algebraMap ℝ A (r * m ^ 2) = r • algebraMap ℝ A (m ^ 2) := by
      rw [Algebra.smul_def, map_mul]
    _ ≤ r • (W * W) := smul_le_smul_of_nonneg_left hsq hr.le
    _ = W * algebraMap ℝ A r * W := hscale.symm
    _ ≤ W * U * W := hW.conjugate_le_conjugate hrU

private theorem trace_log_conjugation_velocity
    (τ : A →L[ℂ] ℂ) (hτ : IsNormalizedTracialState τ) (W U D : A)
    (hW : IsUnit W) (hU : IsUnit U) :
    τ ((D * U * W + W * U * D) * Ring.inverse (W * U * W)) =
      τ (D * Ring.inverse W) + τ (D * Ring.inverse W) := by
  obtain ⟨w, rfl⟩ := hW
  obtain ⟨u, rfl⟩ := hU
  let wi : A := ↑w⁻¹
  let ui : A := ↑u⁻¹
  have hwi : (w : A) * wi = 1 := Units.mul_inv w
  have hiw : wi * (w : A) = 1 := Units.inv_mul w
  have hui : (u : A) * ui = 1 := Units.mul_inv u
  have hiu : ui * (u : A) = 1 := Units.inv_mul u
  have hinv : Ring.inverse ((w : A) * (u : A) * (w : A)) = wi * (ui * wi) := by
    change Ring.inverse (↑(w * u * w) : A) = _
    rw [Ring.inverse_unit, mul_inv_rev, mul_inv_rev, Units.val_mul, Units.val_mul] <;> rfl
  have hfirst : (D * (u : A) * (w : A)) * (wi * (ui * wi)) = D * wi := by
    calc
      _ = D * ((u : A) * (((w : A) * wi) * (ui * wi))) := by simp only [mul_assoc]
      _ = D * wi := by rw [hwi, one_mul, ← mul_assoc (u : A) ui wi, hui, one_mul]
  have hsecond : τ (((w : A) * (u : A) * D) * (wi * (ui * wi))) = τ (D * wi) := by
    calc
      _ = τ (((w : A) * ((u : A) * ((D * wi) * ui))) * wi) := by simp only [mul_assoc]
      _ = τ (wi * ((w : A) * ((u : A) * ((D * wi) * ui)))) := hτ.cyclic _ _
      _ = τ ((u : A) * ((D * wi) * ui)) := by rw [← mul_assoc wi (w : A), hiw, one_mul]
      _ = τ (((D * wi) * ui) * (u : A)) := hτ.cyclic _ _
      _ = τ (D * wi) := by rw [mul_assoc (D * wi) ui (u : A), hiu, mul_one]
  rw [hinv, add_mul, map_add, hfirst, hsecond, Ring.inverse_unit]

/-- Strictly positive conjugation adds twice the trace of the logarithm
of the conjugating operator. -/
theorem tracial_log_conjugation (τ : A →L[ℂ] ℂ) (hτ : IsNormalizedTracialState τ)
    (L U : A) (hL : IsSelfAdjoint L) (hLp : ∀ x ∈ spectrum ℝ L, 0 < x)
    (hU : IsSelfAdjoint U) (hUp : ∀ x ∈ spectrum ℝ U, 0 < x) :
    (τ (CFC.log (L * U * L))).re =
      2 * (τ (CFC.log L)).re + (τ (CFC.log U)).re := by
  have hne : (0 : A) ≠ 1 := by
    intro he
    have h := congrArg τ he
    rw [map_zero, hτ.one] at h
    exact zero_ne_one h
  letI : Nontrivial A := ⟨⟨0, 1, hne⟩⟩
  obtain ⟨rL, hrL, hrLL⟩ := (CFC.exists_pos_algebraMap_le_iff hL).mpr hLp
  obtain ⟨rU, hrU, hrUU⟩ := (CFC.exists_pos_algebraMap_le_iff hU).mpr hUp
  let m := min 1 rL
  have hm : 0 < m := lt_min zero_lt_one hrL
  have hmOne : algebraMap ℝ A m ≤ 1 := by
    simpa only [map_one] using
      (tracial_scalar_map_le (A := A) (min_le_left 1 rL))
  have hmL : algebraMap ℝ A m ≤ L :=
    (tracial_scalar_map_le (min_le_right 1 rL)).trans hrLL
  let D : A := L - 1
  let W (s : ℝ) : A := 1 + s • D
  let V (s : ℝ) : A := W s * U * W s
  let F (s : ℝ) : ℝ := (τ (CFC.log (V s))).re - 2 * (τ (CFC.log (W s))).re
  have hWself (s : ℝ) : IsSelfAdjoint (W s) := by
    change star (1 + s • (L - 1)) = 1 + s • (L - 1)
    simp only [star_add, star_smul, star_trivial, star_sub, hL.star_eq, star_one]
  have hVself (s : ℝ) : IsSelfAdjoint (V s) := by
    change star (W s * U * W s) = W s * U * W s
    simp only [star_mul, (hWself s).star_eq, hU.star_eq, mul_assoc]
  have hWgap (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) : algebraMap ℝ A m ≤ W s := by
    calc
      algebraMap ℝ A m = (1 - s) • algebraMap ℝ A m + s • algebraMap ℝ A m := by
        rw [← add_smul, sub_add_cancel, one_smul]
      _ ≤ (1 - s) • (1 : A) + s • L := add_le_add
        (smul_le_smul_of_nonneg_left hmOne (sub_nonneg.mpr hs.2))
        (smul_le_smul_of_nonneg_left hmL hs.1)
      _ = W s := by
        simp only [W, D, sub_smul, one_smul, smul_sub]
        abel
  have hVgap (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
      algebraMap ℝ A (rU * m ^ 2) ≤ V s :=
    strict_gap_conjugate (W s) U (hWself s) m rU hm hrU (hWgap s hs) hrUU
  have hWdiff : ContDiff ℝ 1 W := by
    unfold W
    fun_prop
  have hVdiff : ContDiff ℝ 1 V := by
    unfold V W
    fun_prop
  have hFs (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) : HasDerivAt F 0 s := by
    have hW' : HasDerivAt W D s := by
      simpa only [W, one_smul] using ((hasDerivAt_id' s).smul_const D).const_add (1 : A)
    have hV' : HasDerivAt V (D * U * W s + W s * U * D) s :=
      (hW'.mul_const U).mul hW'
    have hWpos := selfAdjoint_path_eventually_strict_gap W s hWdiff.continuous.continuousAt
      hWself m hm (hWgap s hs)
    have hVpos := selfAdjoint_path_eventually_strict_gap V s hVdiff.continuous.continuousAt
      hVself (rU * m ^ 2) (mul_pos hrU (pow_pos hm 2)) (hVgap s hs)
    have hWd := tracial_log_hasDerivAt τ hτ W s D hW' hWdiff hWpos
    have hVd := tracial_log_hasDerivAt τ hτ V s
      (D * U * W s + W s * U * D) hV' hVdiff hVpos
    have hunitW := isUnit_of_strict_spectral_gap (W s) (hWself s) m hm (hWgap s hs)
    have hunitU := isUnit_of_strict_spectral_gap U hU rU hrU hrUU
    have htrace := trace_log_conjugation_velocity τ hτ (W s) U D hunitW hunitU
    have hh := hVd.sub (hWd.const_mul 2)
    change HasDerivAt F
      ((τ ((D * U * W s + W s * U * D) * Ring.inverse (V s))).re -
        2 * (τ (D * Ring.inverse (W s))).re) s at hh
    have hz : (τ ((D * U * W s + W s * U * D) * Ring.inverse (V s))).re -
        2 * (τ (D * Ring.inverse (W s))).re = 0 := by
      rw [V, htrace, Complex.add_re]
      ring
    rw [hz] at hh
    exact hh
  have hFc : ContinuousOn F (Icc (0 : ℝ) 1) :=
    fun s hs => (hFs s hs).continuousAt.continuousWithinAt
  obtain ⟨s, _, hmean⟩ := exists_hasDerivAt_eq_slope F (fun _ => 0)
    (show (0 : ℝ) < 1 from zero_lt_one) hFc
    (fun s hs => hFs s ⟨hs.1.le, hs.2.le⟩)
  simp only [sub_zero, div_one] at hmean
  have hconst : F 1 = F 0 := sub_eq_zero.mp hmean.symm
  have hWzero : W 0 = 1 := by simp only [W, zero_smul, add_zero]
  have hWone : W 1 = L := by
    simp only [W, D, one_smul]
    abel
  simp only [F, V, hWzero, hWone, one_mul, mul_one, CFC.log_one, map_zero, Complex.zero_re,
    mul_zero, sub_zero] at hconst
  linarith only [hconst]

/-- Positive invertible scaling adds its trace logarithm on either side
of any operator. The operator being scaled may be singular. -/
theorem fugledeKadisonLog_mul_of_strict_positive
    (τ : A →L[ℂ] ℂ) (hτ : IsNormalizedTracialState τ)
    (L T : A) (hL : IsSelfAdjoint L) (hLp : ∀ x ∈ spectrum ℝ L, 0 < x) :
    fugledeKadisonLog τ (T * L) = fugledeKadisonLog τ T + ((τ (CFC.log L)).re : EReal) ∧
      fugledeKadisonLog τ (L * T) = fugledeKadisonLog τ T + ((τ (CFC.log L)).re : EReal) := by
  have hne : (0 : A) ≠ 1 := by
    intro he
    have hz := congrArg τ he
    rw [map_zero, hτ.one] at hz
    exact zero_ne_one hz
  letI : Nontrivial A := ⟨⟨0, 1, hne⟩⟩
  obtain ⟨m, hm, hmL⟩ := (CFC.exists_pos_algebraMap_le_iff hL).mpr hLp
  have hsq : algebraMap ℝ A (m ^ 2) ≤ L * L := by
    simpa only [one_mul, mul_one] using
      strict_gap_conjugate L 1 hL m 1 hm zero_lt_one hmL (by simp only [map_one, le_refl])
  have hself : IsSelfAdjoint (L * L) := by
    change star (L * L) = L * L
    rw [star_mul, hL.star_eq]
  have hupper : L * L ≤ algebraMap ℝ A (‖L * L‖ + 1) :=
    hself.le_algebraMap_norm_self.trans (tracial_scalar_map_le (le_add_of_nonneg_right zero_le_one))
  exact fugledeKadisonLog_mul_of_strict_conjugation τ hτ L T hL
    (m ^ 2) (‖L * L‖ + 1) (pow_pos hm 2)
    (add_pos_of_nonneg_of_pos (norm_nonneg _) zero_lt_one) hsq hupper
    (fun U hU hUp => tracial_log_conjugation τ hτ L U hL hLp hU hUp)

end

end MOC
