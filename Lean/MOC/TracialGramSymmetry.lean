import MOC.FugledeKadisonTraceLog
import Mathlib.Topology.ContinuousMap.StoneWeierstrass

/-! The two Gram operators have the same scalar law under a trace. -/

namespace MOC

noncomputable section

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

private theorem trace_cyclic_power (τ : A →L[ℂ] ℂ) (hτ : IsNormalizedTracialState τ)
    (x y : A) (n : ℕ) : τ ((x * y) ^ n) = τ ((y * x) ^ n) := by
  cases n with
  | zero => simp only [pow_zero]
  | succ n =>
    rw [pow_succ (x * y), ← mul_assoc, mul_pow_mul, mul_assoc x ((y * x) ^ n) y,
      hτ.cyclic x, mul_assoc ((y * x) ^ n) y x, ← pow_succ]

private theorem trace_cyclic_polynomial (τ : A →L[ℂ] ℂ)
    (hτ : IsNormalizedTracialState τ) (x y : A) (p : Polynomial ℝ) :
    τ (Polynomial.aeval (x * y) p) = τ (Polynomial.aeval (y * x) p) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, hp, hq]
  | monomial n c =>
    rw [Polynomial.aeval_monomial, Polynomial.aeval_monomial,
      ← Algebra.smul_def, ← Algebra.smul_def,
      RCLike.real_smul_eq_coe_smul (K := ℂ), RCLike.real_smul_eq_coe_smul (K := ℂ),
      map_smul, map_smul, trace_cyclic_power τ hτ]

/-- Applying a continuous function to either Gram operator gives the
same trace, provided the function is continuous on a common compact set
containing both spectra. -/
theorem tracial_cfc_gram_symmetry (τ : A →L[ℂ] ℂ)
    (hτ : IsNormalizedTracialState τ) (T : A) (S : Set ℝ) [CompactSpace S]
    (hX : spectrum ℝ (star T * T) ⊆ S) (hY : spectrum ℝ (T * star T) ⊆ S)
    (f : ℝ → ℝ) (hf : ContinuousOn f S) :
    τ (cfc f (star T * T)) = τ (cfc f (T * star T)) := by
  let hx : IsSelfAdjoint (star T * T) := IsSelfAdjoint.star_mul_self T
  let hy : IsSelfAdjoint (T * star T) := by
    simpa only [star_star] using IsSelfAdjoint.star_mul_self (star T)
  let X := cfcHomSuperset hx hX
  let Y := cfcHomSuperset hy hY
  have hpoly (a : A) (G : C(S, ℝ) →⋆ₐ[ℝ] A)
      (hG : G ((ContinuousMap.id ℝ).restrict S) = a) (p : Polynomial ℝ) :
      G (p.toContinuousMapOn S) = Polynomial.aeval a p := by
    have he : G.toAlgHom.comp (Polynomial.toContinuousMapOnAlgHom S) =
        Polynomial.aeval a := by
      apply Polynomial.algHom_ext
      simpa only [AlgHom.comp_apply, Polynomial.toContinuousMapOnAlgHom_apply,
        Polynomial.toContinuousMapOn_X_eq_restrict_id, Polynomial.aeval_X] using hG
    exact DFunLike.congr_fun he p
  have hd : Dense (polynomialFunctions S : Set C(S, ℝ)) := by
    rw [dense_iff_closure_eq]
    exact congrArg (fun L : Subalgebra ℝ C(S, ℝ) => (L : Set C(S, ℝ)))
      (polynomialFunctions.topologicalClosure S)
  have hEq : (fun g => τ (X g)) = fun g => τ (Y g) := by
    apply Continuous.ext_on hd
      (τ.continuous.comp (cfcHomSuperset_continuous hx hX))
      (τ.continuous.comp (cfcHomSuperset_continuous hy hY))
    intro g hg
    rw [polynomialFunctions_coe] at hg
    obtain ⟨p, rfl⟩ := hg
    change τ (X (p.toContinuousMapOn S)) = τ (Y (p.toContinuousMapOn S))
    rw [hpoly _ X (cfcHomSuperset_id hx hX), hpoly _ Y (cfcHomSuperset_id hy hY),
      trace_cyclic_polynomial τ hτ]
  rw [cfc_apply f (star T * T) hx (hf.mono hX), cfc_apply f (T * star T) hy (hf.mono hY)]
  exact congrFun hEq (⟨_, hf.restrict⟩ : C(S, ℝ))

/-- The analytic Fuglede–Kadison determinant has the same logarithm for
an operator and its adjoint, including the extended value at zero. -/
theorem fugledeKadisonLog_adjoint (τ : A →L[ℂ] ℂ)
    (hτ : IsNormalizedTracialState τ) (T : A) :
    fugledeKadisonLog τ (star T) = fugledeKadisonLog τ T := by
  let M := max ‖star T * T‖ ‖T * star T‖
  let S := Set.Icc (0 : ℝ) M
  have hX : spectrum ℝ (star T * T) ⊆ S := by
    intro x hx
    exact ⟨spectrum_star_mul_self_nonneg x hx,
      (Real.le_norm_self x).trans ((spectrum.norm_le_norm_of_mem hx).trans (le_max_left _ _))⟩
  have hY : spectrum ℝ (T * star T) ⊆ S := by
    intro x hx
    have hpos : 0 ≤ x := spectrum_star_mul_self_nonneg (b := star T) x
      (by simpa only [star_star] using hx)
    exact ⟨hpos,
      (Real.le_norm_self x).trans ((spectrum.norm_le_norm_of_mem hx).trans (le_max_right _ _))⟩
  have he (ε : Set.Ioi (0 : ℝ)) : τ (cfc (fun t : ℝ => Real.log (t + ε.val))
        (star T * T)) = τ (cfc (fun t : ℝ => Real.log (t + ε.val)) (T * star T)) := by
    apply tracial_cfc_gram_symmetry τ hτ T S hX hY
    apply Real.continuousOn_log.comp (continuous_id.add continuous_const).continuousOn
    intro x hx
    exact (add_pos_of_nonneg_of_pos hx.1 ε.property).ne'
  simp only [fugledeKadisonLog, star_star, he]

end

end MOC
