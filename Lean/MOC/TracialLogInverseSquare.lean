import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Integral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Tactic.Linarith

/-! The integral of the squared resolvent on a finite interval and the
positive half-line. -/

open Filter MeasureTheory
open scoped Interval Topology

namespace MOC

noncomputable section

private theorem shifted_inv_sq_primitive (m : ℝ) (hm : 0 < m) (t : ℝ) (ht : 0 ≤ t) :
    HasDerivAt (fun s : ℝ => -(m + s)⁻¹) (((m + t)⁻¹) ^ 2) t := by
  have hadd : HasDerivAt (fun s : ℝ => m + s) 1 t := (hasDerivAt_id' t).const_add m
  have h := (hadd.inv (add_pos_of_pos_of_nonneg hm ht).ne').neg
  simpa only [neg_div, neg_neg, one_div, inv_pow] using h

private theorem neg_shifted_inv_tendsto_zero (m : ℝ) :
    Tendsto (fun t : ℝ => -(m + t)⁻¹) atTop (𝓝 0) := by
  have h : Tendsto (fun t : ℝ => m + t) atTop atTop := by
    refine tendsto_atTop.2 fun y => (eventually_ge_atTop (y - m)).mono ?_
    intro t ht
    linarith only [ht]
  simpa only [Function.comp_apply, neg_zero] using (tendsto_inv_atTop_zero.comp h).neg

/-- A positive shift gives an integrable reciprocal square on the positive half-line. -/
theorem integrableOn_shifted_inv_sq (m : ℝ) (hm : 0 < m) :
    IntegrableOn (fun t : ℝ => ((m + t)⁻¹) ^ 2) (Set.Ioi (0 : ℝ)) :=
  integrableOn_Ioi_deriv_of_nonneg'
    (fun t ht => shifted_inv_sq_primitive m hm t ht)
    (fun t _ => sq_nonneg ((m + t)⁻¹)) (neg_shifted_inv_tendsto_zero m)

/-- The scalar inverse-square integral has value the inverse of the shift. -/
theorem integral_Ioi_shifted_inv_sq (m : ℝ) (hm : 0 < m) :
    (∫ t in Set.Ioi (0 : ℝ), ((m + t)⁻¹) ^ 2) = m⁻¹ := by
  have h := integral_Ioi_of_hasDerivAt_of_tendsto'
    (fun t (ht : t ∈ Set.Ici (0 : ℝ)) => shifted_inv_sq_primitive m hm t ht)
    (integrableOn_shifted_inv_sq m hm) (neg_shifted_inv_tendsto_zero m)
  simpa only [add_zero, sub_neg_eq_add, zero_add] using h

/-- The scalar inverse-square integral on a bounded positive interval. -/
theorem intervalIntegral_shifted_inv_sq (m R : ℝ) (hm : 0 < m) (hR : 0 ≤ R) :
    (∫ t in (0 : ℝ)..R, ((m + t)⁻¹) ^ 2) = m⁻¹ - (m + R)⁻¹ := by
  have hcont : ContinuousOn (fun t : ℝ => ((m + t)⁻¹) ^ 2) (Set.Icc 0 R) := by
    apply ContinuousOn.pow
    exact (continuous_const.add continuous_id).continuousOn.inv₀ (fun t ht =>
      (add_pos_of_pos_of_nonneg hm ht.1).ne')
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => shifted_inv_sq_primitive m hm t ((Set.uIcc_of_le hR ▸ ht).1))
    (hcont.intervalIntegrable_of_Icc hR)
  simpa only [add_zero, neg_sub_neg] using h

variable {A : Type*} [CStarAlgebra A]

private theorem cfc_shifted_inv_sq_on (X : A) (hX : IsSelfAdjoint X)
    (hXp : ∀ x ∈ spectrum ℝ X, 0 < x) (s : Set ℝ)
    (hs : MeasurableSet s) (hs₀ : ∀ t ∈ s, 0 ≤ t)
    (hdom : ∀ m : ℝ, 0 < m → IntegrableOn (fun t : ℝ => ((m + t)⁻¹) ^ 2) s) :
    IntegrableOn (fun t : ℝ => cfc (fun x : ℝ => ((x + t)⁻¹) ^ 2) X) s ∧
      (∫ t in s, cfc (fun x : ℝ => ((x + t)⁻¹) ^ 2) X) =
        cfc (fun x : ℝ => ∫ t in s, ((x + t)⁻¹) ^ 2) X := by
  rcases subsingleton_or_nontrivial A with hA | hA
  · letI := hA
    have hz : (fun t : ℝ => cfc (fun x : ℝ => ((x + t)⁻¹) ^ 2) X) = fun _ => (0 : A) :=
      Subsingleton.elim _ _
    refine ⟨?_, Subsingleton.elim _ _⟩
    rw [hz]
    exact integrable_zero _ _ _
  letI := hA
  let μ : Measure s := Measure.comap Subtype.val volume
  have hcompact : IsCompact (spectrum ℝ X) := isCompact_iff_compactSpace.mpr inferInstance
  obtain ⟨m, hm, hmin⟩ := hcompact.exists_isMinOn hX.spectrum_nonempty continuousOn_id
  have hm₀ := hXp m hm
  let k (t : s) (x : ℝ) : ℝ := ((x + t.val)⁻¹) ^ 2
  let g (t : s) : ℝ := ((m + t.val)⁻¹) ^ 2
  have hmeas : MeasurableEmbedding (Subtype.val : s → ℝ) := MeasurableEmbedding.subtype_coe hs
  have hgi : Integrable g μ := by
    have hi : Integrable (fun t : ℝ => ((m + t)⁻¹) ^ 2) (Measure.map Subtype.val μ) := by
      rw [μ, map_comap_subtype_coe hs]
      exact hdom m hm₀
    exact hmeas.integrable_map_iff.mp hi
  have hpos (t : s) (x : spectrum ℝ X) : 0 < x.val + t.val :=
    add_pos_of_pos_of_nonneg (hXp x.val x.property) (hs₀ t.val t.property)
  have hjoint : Continuous (fun p : s × spectrum ℝ X => k p.1 p.2.val) := by
    apply Continuous.pow
    exact ((continuous_subtype_val.comp continuous_snd).add
      (continuous_subtype_val.comp continuous_fst)).inv₀ (fun p => (hpos p.1 p.2).ne')
  have hbound (t : s) (x : ℝ) (hx : x ∈ spectrum ℝ X) : ‖k t x‖ ≤ ‖g t‖ := by
    have hx₀ := hpos t ⟨x, hx⟩
    have hmt := add_pos_of_pos_of_nonneg hm₀ (hs₀ t.val t.property)
    have hle : m + t.val ≤ x + t.val := add_le_add_right (hmin hx) _
    dsimp only [k, g]
    rw [Real.norm_of_nonneg (sq_nonneg _), Real.norm_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (inv_nonneg.mpr hx₀.le) ((inv_le_inv₀ hx₀ hmt).mpr hle) 2
  let F (t : s) : C(spectrum ℝ X, ℝ) := ⟨fun x => k t x.val, hjoint.uncurry_left t⟩
  have hFc : Continuous F :=
    (ContinuousMap.curry (⟨_, hjoint⟩ : C(s × spectrum ℝ X, ℝ))).continuous
  have hFn (t : s) : ‖F t‖ ≤ ‖g t‖ :=
    (ContinuousMap.norm_le _ (norm_nonneg _)).mpr fun x => hbound t x.val x.property
  have hFi : Integrable F μ := ⟨hFc.aestronglyMeasurable, hgi.hasFiniteIntegral.mono (.of_forall hFn)⟩
  have hL (t : s) : cfcL hX (F t) = cfc (k t) X := by
    rw [cfc_apply (k t) X hX (continuousOn_iff_continuous_restrict.mpr (hjoint.uncurry_left t))]
    rfl
  have hAi : Integrable (fun t : s => cfc (k t) X) μ := by
    simpa only [hL] using (cfcL hX).integrable_comp hFi
  have hint := cfc_integral' (μ := μ) k g X hjoint hbound hgi.hasFiniteIntegral hX
  have hkernel (x : ℝ) : (∫ t : s, k t x ∂μ) = ∫ t in s, ((x + t)⁻¹) ^ 2 := by
    exact integral_subtype_comap hs (fun t : ℝ => ((x + t)⁻¹) ^ 2)
  refine ⟨?_, ?_⟩
  · unfold IntegrableOn
    rw [← map_comap_subtype_coe hs, hmeas.integrable_map_iff]
    exact hAi
  · rw [← integral_subtype_comap hs (fun t : ℝ => cfc (fun x : ℝ => ((x + t)⁻¹) ^ 2) X)]
    change (∫ t : s, cfc (k t) X ∂μ) = _
    rw [← hint]
    exact congrArg (fun f : ℝ → ℝ => cfc f X) (funext hkernel)

/-- The squared resolvent is norm integrable on the positive half-line. -/
theorem integrableOn_cfc_shifted_inv_sq (X : A) (hX : IsSelfAdjoint X)
    (hXp : ∀ x ∈ spectrum ℝ X, 0 < x) :
    IntegrableOn (fun t : ℝ => cfc (fun x : ℝ => ((x + t)⁻¹) ^ 2) X) (Set.Ioi (0 : ℝ)) :=
  (cfc_shifted_inv_sq_on X hX hXp _ measurableSet_Ioi (fun _ ht => ht.le)
    integrableOn_shifted_inv_sq).1

/-- The positive half-line integral of the squared resolvent is the inverse. -/
theorem integral_Ioi_cfc_shifted_inv_sq (X : A) (hX : IsSelfAdjoint X)
    (hXp : ∀ x ∈ spectrum ℝ X, 0 < x) :
    (∫ t in Set.Ioi (0 : ℝ), cfc (fun x : ℝ => ((x + t)⁻¹) ^ 2) X) = Ring.inverse X := by
  rw [(cfc_shifted_inv_sq_on X hX hXp _ measurableSet_Ioi (fun _ ht => ht.le)
    integrableOn_shifted_inv_sq).2]
  rw [cfc_congr (fun x hx => integral_Ioi_shifted_inv_sq x (hXp x hx))]
  rw [cfc_inv (fun x : ℝ => x) X (fun x hx => (hXp x hx).ne') (by fun_prop) hX, cfc_id']

/-- The finite interval integral of the squared resolvent is the difference
of the two endpoint inverses. -/
theorem intervalIntegral_cfc_shifted_inv_sq (X : A) (hX : IsSelfAdjoint X)
    (hXp : ∀ x ∈ spectrum ℝ X, 0 < x) (R : ℝ) (hR : 0 ≤ R) :
    (∫ t in (0 : ℝ)..R, cfc (fun x : ℝ => ((x + t)⁻¹) ^ 2) X) =
      Ring.inverse X - Ring.inverse (X + algebraMap ℝ A R) := by
  have hdom (m : ℝ) (hm : 0 < m) :
      IntegrableOn (fun t : ℝ => ((m + t)⁻¹) ^ 2) (Set.Ioc 0 R) :=
    (integrableOn_shifted_inv_sq m hm).mono_set (fun _ ht => ht.1)
  rw [intervalIntegral.integral_of_le hR]
  rw [(cfc_shifted_inv_sq_on X hX hXp _ measurableSet_Ioc (fun _ ht => ht.1.le) hdom).2]
  rw [cfc_congr (fun x hx => (intervalIntegral.integral_of_le hR).symm.trans
    (intervalIntegral_shifted_inv_sq x R (hXp x hx) hR))]
  have hpos (x : ℝ) (hx : x ∈ spectrum ℝ X) : 0 < x + R :=
    add_pos_of_pos_of_nonneg (hXp x hx) hR
  have h₀ : ContinuousOn (fun x : ℝ => x⁻¹) (spectrum ℝ X) :=
    continuousOn_id.inv₀ fun x hx => (hXp x hx).ne'
  have h₁ : ContinuousOn (fun x : ℝ => (x + R)⁻¹) (spectrum ℝ X) :=
    (continuous_id.add continuous_const).continuousOn.inv₀ fun x hx => (hpos x hx).ne'
  rw [cfc_sub (fun x : ℝ => x⁻¹) (fun x : ℝ => (x + R)⁻¹) X h₀ h₁,
    cfc_inv (fun x : ℝ => x) X (fun x hx => (hXp x hx).ne') (by fun_prop) hX,
    cfc_inv (fun x : ℝ => x + R) X (fun x hx => (hpos x hx).ne') (by fun_prop) hX,
    cfc_add_const R (fun x : ℝ => x) X (by fun_prop) hX, cfc_id']

end

end MOC
