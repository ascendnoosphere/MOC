import MOC.TracialGramSymmetry
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog
import Mathlib.Data.EReal.Operations
import Mathlib.Tactic.Ring

/-! Transport of the analytic logarithm through positive regularization. -/

namespace MOC

noncomputable section

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- Half of the regularized trace logarithm, expressed on a positive
Gram operator directly. -/
def tracialGramLog (τ : A →L[ℂ] ℂ) (X : A) : EReal :=
  ⨅ ε : Set.Ioi (0 : ℝ),
    (((τ (CFC.log (X + algebraMap ℝ A ε.val))).re / 2 : ℝ) : EReal)

private theorem shifted_spectral_log (X : A) (hX : 0 ≤ X) (ε : ℝ) (hε : 0 < ε) :
    cfc (fun t : ℝ => Real.log (t + ε)) X = CFC.log (X + algebraMap ℝ A ε) := by
  have hg : ContinuousOn Real.log ((fun t : ℝ => t + ε) '' spectrum ℝ X) := by
    apply Real.continuousOn_log.mono
    rintro _ ⟨t, ht, rfl⟩
    exact (add_pos_of_nonneg_of_pos (spectrum_nonneg_of_nonneg hX ht) hε).ne'
  rw [cfc_comp' Real.log (fun t : ℝ => t + ε) X hg (by fun_prop) hX.isSelfAdjoint,
    cfc_add_const ε (fun t : ℝ => t) X (by fun_prop) hX.isSelfAdjoint, cfc_id']
  rfl

/-- The regularized Gram formula equals the analytic determinant for
the Gram operator of a bounded element. -/
theorem fugledeKadisonLog_eq_tracialGramLog (τ : A →L[ℂ] ℂ) (T : A) :
    fugledeKadisonLog τ T = tracialGramLog τ (star T * T) := by
  unfold fugledeKadisonLog tracialGramLog
  congr 1
  funext ε
  rw [shifted_spectral_log _ (star_mul_self_nonneg T) ε.val ε.property]

private def positiveMulEquiv (r : ℝ) (hr : 0 < r) :
    Set.Ioi (0 : ℝ) ≃ Set.Ioi (0 : ℝ) where
  toFun x := ⟨x.val * r, mul_pos x.property hr⟩
  invFun x := ⟨x.val / r, div_pos x.property hr⟩
  left_inv x := Subtype.ext (mul_div_cancel_right₀ x.val hr.ne')
  right_inv x := Subtype.ext (div_mul_cancel₀ x.val hr.ne')

private def addRealOrderIso (c : ℝ) : EReal ≃o EReal where
  toFun x := x + (c : EReal)
  invFun x := x - (c : EReal)
  left_inv _ := EReal.add_sub_cancel_right
  right_inv _ := EReal.sub_add_cancel
  map_rel_iff' := (EReal.addLECancellable_coe c).add_le_add_iff_right

private theorem positive_shift_spectrum (X : A) (hX : 0 ≤ X) (ε : ℝ) (hε : 0 < ε) :
    ∀ x ∈ spectrum ℝ (X + algebraMap ℝ A ε), 0 < x := by
  have hsa : IsSelfAdjoint (X + algebraMap ℝ A ε) :=
    hX.isSelfAdjoint.add (IsSelfAdjoint.algebraMap A (.all ε))
  have hlo : algebraMap ℝ A ε ≤ X + algebraMap ℝ A ε := le_add_of_nonneg_left hX
  exact fun x hx => hε.trans_le
    ((algebraMap_le_iff_le_spectrum hsa).mp hlo x hx)

/-- Positive scalar multiplication transports the regularization exactly. -/
theorem tracialGramLog_real_smul (τ : A →L[ℂ] ℂ) (hτ : IsNormalizedTracialState τ)
    (X : A) (hX : 0 ≤ X) (r : ℝ) (hr : 0 < r) :
    tracialGramLog τ (r • X) = tracialGramLog τ X + ((Real.log r / 2 : ℝ) : EReal) := by
  let F (V : A) (ε : Set.Ioi (0 : ℝ)) : EReal :=
    (((τ (CFC.log (V + algebraMap ℝ A ε.val))).re / 2 : ℝ) : EReal)
  have hscalar : (τ (algebraMap ℝ A (Real.log r))).re = Real.log r := by
    rw [Algebra.algebraMap_eq_smul_one, RCLike.real_smul_eq_coe_smul (K := ℂ),
      map_smul, hτ.one, smul_eq_mul, mul_one, Complex.ofReal_re]
  have he (ε : Set.Ioi (0 : ℝ)) :
      F (r • X) (positiveMulEquiv r hr ε) = F X ε + ((Real.log r / 2 : ℝ) : EReal) := by
    have hshift : r • X + algebraMap ℝ A (ε.val * r) =
        r • (X + algebraMap ℝ A ε.val) := by
      rw [smul_add, Algebra.smul_def r (algebraMap ℝ A ε.val), ← map_mul, mul_comm r ε.val]
    dsimp only [F, positiveMulEquiv, Equiv.coe_fn_mk]
    rw [hshift, CFC.log_smul _ (positive_shift_spectrum X hX ε.val ε.property) hr
      (hX.isSelfAdjoint.add (IsSelfAdjoint.algebraMap A (.all ε.val))),
      map_add, Complex.add_re, hscalar, ← EReal.coe_add]
    congr 1 <;> ring
  have hinf := (addRealOrderIso (Real.log r / 2)).map_iInf (F X)
  change (⨅ ε, F X ε) + ((Real.log r / 2 : ℝ) : EReal) =
    ⨅ ε, F X ε + ((Real.log r / 2 : ℝ) : EReal) at hinf
  change (⨅ ε, F (r • X) ε) =
    (⨅ ε, F X ε) + ((Real.log r / 2 : ℝ) : EReal)
  rw [← (positiveMulEquiv r hr).iInf_comp (g := F (r • X)), hinf]
  simp only [he]

/-- Positive scalar multiplication of a bounded element adds the real
logarithm of the scalar to the analytic determinant. -/
theorem fugledeKadisonLog_real_smul (τ : A →L[ℂ] ℂ)
    (hτ : IsNormalizedTracialState τ) (T : A) (r : ℝ) (hr : 0 < r) :
    fugledeKadisonLog τ (r • T) = fugledeKadisonLog τ T + (Real.log r : EReal) := by
  have hT : star (r • T) * (r • T) = (r * r) • (star T * T) := by
    rw [star_smul, star_trivial, smul_mul_smul_comm]
  have hrlog : Real.log (r * r) / 2 = Real.log r := by
    rw [Real.log_mul hr.ne' hr.ne']
    ring
  rw [fugledeKadisonLog_eq_tracialGramLog, fugledeKadisonLog_eq_tracialGramLog, hT,
    tracialGramLog_real_smul τ hτ _ (star_mul_self_nonneg T) _ (mul_pos hr hr), hrlog]

/-- Positive conjugation takes a scalar regularization into the interval
between the two scalar regularizations given by bounds on the square
of the conjugating operator. -/
theorem positive_conjugation_regularization_sandwich (L X : A) (m M ε : ℝ)
    (hε : 0 ≤ ε) (hm : algebraMap ℝ A m ≤ L * L) (hM : L * L ≤ algebraMap ℝ A M) :
    L * X * L + algebraMap ℝ A (ε * m) ≤ L * (X + algebraMap ℝ A ε) * L ∧
      L * (X + algebraMap ℝ A ε) * L ≤ L * X * L + algebraMap ℝ A (ε * M) := by
  have hmiddle : L * (X + algebraMap ℝ A ε) * L =
      L * X * L + ε • (L * L) := by
    rw [mul_add, add_mul, Algebra.algebraMap_eq_smul_one, mul_smul_comm,
      mul_one, smul_mul_assoc]
  have hmap (r : ℝ) : (ε • algebraMap ℝ A r) = algebraMap ℝ A (ε * r) := by
    rw [Algebra.smul_def, map_mul]
  rw [hmiddle, ← hmap, ← hmap]
  exact ⟨add_le_add_left (smul_le_smul_of_nonneg_left hm hε) _,
    add_le_add_left (smul_le_smul_of_nonneg_left hM hε) _⟩

/-- The analytic infimum respects positive conjugation if the two
invertible trace-log results hold. The hypotheses concern only operators
whose spectra are strictly positive. -/
theorem tracialGramLog_conjugation_of_invertible_trace_log
    (τ : A →L[ℂ] ℂ) (L X : A) (hL : IsSelfAdjoint L) (hX : 0 ≤ X)
    (m M : ℝ) (hm : 0 < m) (hM : 0 < M)
    (hmL : algebraMap ℝ A m ≤ L * L) (hML : L * L ≤ algebraMap ℝ A M)
    (hmono : ∀ U V : A, IsSelfAdjoint U → IsSelfAdjoint V → (∀ x ∈ spectrum ℝ U, 0 < x) →
      (∀ x ∈ spectrum ℝ V, 0 < x) → U ≤ V → (τ (CFC.log U)).re ≤ (τ (CFC.log V)).re)
    (hconj : ∀ U : A, IsSelfAdjoint U → (∀ x ∈ spectrum ℝ U, 0 < x) →
      (τ (CFC.log (L * U * L))).re =
        2 * (τ (CFC.log L)).re + (τ (CFC.log U)).re) :
    tracialGramLog τ (L * X * L) = tracialGramLog τ X + ((τ (CFC.log L)).re : EReal) := by
  let Y := L * X * L
  have hY : 0 ≤ Y := hL.conjugate_nonneg hX
  let c := (τ (CFC.log L)).re
  let F (V : A) (ε : Set.Ioi (0 : ℝ)) : EReal :=
    (((τ (CFC.log (V + algebraMap ℝ A ε.val))).re / 2 : ℝ) : EReal)
  have hb (ε : Set.Ioi (0 : ℝ)) :
      F Y (positiveMulEquiv m hm ε) ≤ F X ε + (c : EReal) ∧
      F X ε + (c : EReal) ≤ F Y (positiveMulEquiv M hM ε) := by
    obtain ⟨hl, hu⟩ := positive_conjugation_regularization_sandwich L X m M ε.val
      ε.property.le hmL hML
    let W := L * (X + algebraMap ℝ A ε.val) * L
    have hU : IsSelfAdjoint (X + algebraMap ℝ A ε.val) :=
      hX.isSelfAdjoint.add (IsSelfAdjoint.algebraMap A (.all ε.val))
    have hsa : IsSelfAdjoint W := hU.conjugate_self hL
    have hWs : ∀ x ∈ spectrum ℝ W, 0 < x := by
      intro x hx
      refine (mul_pos ε.property hm).trans_le ((algebraMap_le_iff_le_spectrum hsa).mp ?_ x hx)
      exact (le_add_of_nonneg_left hY).trans hl
    have hs := hconj (X + algebraMap ℝ A ε.val) hU (positive_shift_spectrum X hX ε.val ε.property)
    have hYsa (s : ℝ) : IsSelfAdjoint (Y + algebraMap ℝ A s) :=
      hY.isSelfAdjoint.add (IsSelfAdjoint.algebraMap A (.all s))
    have hl' := hmono _ W (hYsa _) hsa (positive_shift_spectrum Y hY _ (mul_pos ε.property hm)) hWs hl
    have hu' := hmono W _ hsa (hYsa _) hWs (positive_shift_spectrum Y hY _ (mul_pos ε.property hM)) hu
    change (τ (CFC.log W)).re = _ at hs
    constructor
    · dsimp only [F, positiveMulEquiv, Equiv.coe_fn_mk, c]
      rw [← EReal.coe_add, EReal.coe_le_coe_iff]
      linarith only [hl', hs]
    · dsimp only [F, positiveMulEquiv, Equiv.coe_fn_mk, c]
      rw [← EReal.coe_add, EReal.coe_le_coe_iff]
      linarith only [hu', hs]
  have hinf := (addRealOrderIso c).map_iInf (F X)
  change (⨅ ε, F X ε) + (c : EReal) = ⨅ ε, F X ε + (c : EReal) at hinf
  change (⨅ ε, F Y ε) = (⨅ ε, F X ε) + (c : EReal)
  rw [hinf]
  apply le_antisymm
  · rw [← (positiveMulEquiv m hm).iInf_comp (g := F Y)]
    exact iInf_mono fun ε => (hb ε).1
  · rw [← (positiveMulEquiv M hM).iInf_comp (g := F Y)]
    exact iInf_mono fun ε => (hb ε).2

/-- The invertible trace-log laws give both analytic one-sided scaling
laws for a self-adjoint positive conjugating factor, with no invertibility
requirement on the operator being scaled. -/
theorem fugledeKadisonLog_mul_of_invertible_trace_log
    (τ : A →L[ℂ] ℂ) (hτ : IsNormalizedTracialState τ) (L T : A) (hL : IsSelfAdjoint L)
    (m M : ℝ) (hm : 0 < m) (hM : 0 < M)
    (hmL : algebraMap ℝ A m ≤ L * L) (hML : L * L ≤ algebraMap ℝ A M)
    (hmono : ∀ U V : A, IsSelfAdjoint U → IsSelfAdjoint V → (∀ x ∈ spectrum ℝ U, 0 < x) →
      (∀ x ∈ spectrum ℝ V, 0 < x) → U ≤ V → (τ (CFC.log U)).re ≤ (τ (CFC.log V)).re)
    (hconj : ∀ U : A, IsSelfAdjoint U → (∀ x ∈ spectrum ℝ U, 0 < x) →
      (τ (CFC.log (L * U * L))).re =
        2 * (τ (CFC.log L)).re + (τ (CFC.log U)).re) :
    fugledeKadisonLog τ (T * L) = fugledeKadisonLog τ T + ((τ (CFC.log L)).re : EReal) ∧
      fugledeKadisonLog τ (L * T) = fugledeKadisonLog τ T + ((τ (CFC.log L)).re : EReal) := by
  have hright (V : A) :
      fugledeKadisonLog τ (V * L) = fugledeKadisonLog τ V + ((τ (CFC.log L)).re : EReal) := by
    have hGram : star (V * L) * (V * L) = L * (star V * V) * L := by
      simp only [star_mul, hL.star_eq, mul_assoc]
    rw [fugledeKadisonLog_eq_tracialGramLog, fugledeKadisonLog_eq_tracialGramLog, hGram]
    exact tracialGramLog_conjugation_of_invertible_trace_log τ L _
      hL (star_mul_self_nonneg V) m M hm hM hmL hML hmono hconj
  refine ⟨hright T, ?_⟩
  calc
    fugledeKadisonLog τ (L * T) = fugledeKadisonLog τ (star (L * T)) :=
      (fugledeKadisonLog_adjoint τ hτ (L * T)).symm
    _ = fugledeKadisonLog τ (star T * L) := by rw [star_mul, hL.star_eq]
    _ = fugledeKadisonLog τ (star T) + ((τ (CFC.log L)).re : EReal) := hright (star T)
    _ = _ := by rw [fugledeKadisonLog_adjoint τ hτ]

/-- In the tracial logarithmic derivative of a positive conjugation
path, the inverse factors cancel by cyclicity. -/
theorem tracial_inverse_conjugation_derivative (τ : A →L[ℂ] ℂ)
    (hτ : IsNormalizedTracialState τ) (W : Aˣ) (H : A) :
    τ ((↑W⁻¹ : A) * (H * (W : A) + (W : A) * H)) = τ H + τ H := by
  rw [mul_add, map_add, ← mul_assoc (↑W⁻¹ : A) (W : A) H, Units.inv_mul, one_mul,
    ← mul_assoc (↑W⁻¹ : A) H (W : A), hτ.cyclic ((↑W⁻¹ : A) * H) (W : A),
    ← mul_assoc (W : A) (↑W⁻¹ : A) H, Units.mul_inv, one_mul]

end

end MOC
