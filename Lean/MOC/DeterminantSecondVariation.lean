import MOC.Jacobi
import Mathlib.Analysis.Calculus.FirstDerivativeTest
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Normed.Algebra.MatrixExponential

/-! The second derivative of the determinant along a matrix path. -/

open Filter Matrix Set
open scoped Topology

namespace MOC

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

/-- Jacobi's formula along a differentiable path at an invertible matrix. -/
theorem hasDerivAt_det_of_ne_zero {M : ℝ → Matrix ι ι ℂ} {D : Matrix ι ι ℂ} {t : ℝ}
    (hM : HasDerivAt M D t) (hnz : (M t).det ≠ 0) :
    HasDerivAt (fun s => (M s).det) ((M t).det * ((M t)⁻¹ * D).trace) t := by
  let C := M t
  have hC : IsUnit C.det := isUnit_iff_ne_zero.mpr hnz
  have hAtOne : C⁻¹ * M t = diagonal (fun _ => 1) :=
    (C.nonsing_inv_mul hC).trans Matrix.diagonal_one.symm
  have hPath := hM.const_mul C⁻¹
  have hentry (i j : ι) : HasDerivAt (fun s => (C⁻¹ * M s) i j) ((C⁻¹ * D) i j) t := by
    let E : Matrix ι ι ℂ →L[ℝ] ℂ :=
      ⟨Matrix.entryLinearMap ℝ ℂ i j, continuous_apply_apply i j⟩
    exact E.hasFDerivAt.comp_hasDerivAt t hPath
  have hdet := hasDerivAt_det_diagonal (fun s => C⁻¹ * M s) (C⁻¹ * D) t (fun _ => 1)
    hAtOne hentry
  have he (s : ℝ) : C.det * (C⁻¹ * M s).det = (M s).det := by
    rw [← Matrix.det_mul, ← Matrix.mul_assoc, C.mul_nonsing_inv hC, Matrix.one_mul]
  simpa only [he, Finset.prod_const_one, one_mul, Matrix.trace, Matrix.diag_apply] using
    hdet.const_mul C.det

/-- The second derivative of `det M` at the identity consists of the trace
of the acceleration and the two quadratic trace terms of the velocity. -/
theorem hasDerivAt_deriv_det_of_eq_one {M V : ℝ → Matrix ι ι ℂ} {A : Matrix ι ι ℂ}
    (hM : ∀ᶠ t in 𝓝 (0 : ℝ), HasDerivAt M (V t) t)
    (h₀ : M 0 = 1) (hV : HasDerivAt V A 0) :
    HasDerivAt (deriv (fun t => (M t).det))
      (A.trace + (V 0).trace ^ 2 - (V 0 * V 0).trace) 0 := by
  have hM₀ := hM.self_of_nhds
  have hn : (M 0).det ≠ 0 := by simp [h₀]
  have hd := hasDerivAt_det_of_ne_zero hM₀ hn
  have hdn := hd.continuousAt.eventually_ne hn
  have hd' : HasDerivAt (fun t => (M t).det) (V 0).trace 0 := by
    simpa only [h₀, Matrix.det_one, inv_one, Matrix.one_mul, one_mul] using hd
  have hInv' : HasFDerivAt (Ring.inverse : Matrix ι ι ℂ → Matrix ι ι ℂ)
      (-ContinuousLinearMap.mulLeftRight ℝ (Matrix ι ι ℂ) 1 1) (M 0) := by
    simpa only [h₀, Units.val_one, inv_one] using
      hasFDerivAt_ringInverse (𝕜 := ℝ) (1 : (Matrix ι ι ℂ)ˣ)
  have hInv : HasDerivAt (fun t => (M t)⁻¹) (-(V 0)) 0 := by
    have hi := hInv'.comp_hasDerivAt 0 hM₀
    simpa only [Function.comp_def, ContinuousLinearMap.neg_apply, ContinuousLinearMap.mulLeftRight_apply,
      Matrix.one_mul, Matrix.mul_one, ← Matrix.nonsing_inv_eq_ringInverse] using hi
  let L : Matrix ι ι ℂ →L[ℝ] ℂ :=
    ⟨Matrix.traceLinearMap ι ℝ ℂ, by
      change Continuous (fun X : Matrix ι ι ℂ => X.trace)
      unfold Matrix.trace
      exact continuous_finset_sum _ (fun i _ => continuous_apply_apply i i)⟩
  have ht : HasDerivAt (fun t => ((M t)⁻¹ * V t).trace)
      (A.trace - (V 0 * V 0).trace) 0 := by
    have hp := L.hasFDerivAt.comp_hasDerivAt 0 (hInv.mul hV)
    simpa only [L, ContinuousLinearMap.coe_mk', Matrix.traceLinearMap_apply, Function.comp_apply,
      h₀, inv_one, Matrix.one_mul, Matrix.neg_mul, Matrix.trace_add, Matrix.trace_neg,
      sub_eq_add_neg, add_comm] using hp
  have hd₂ := hd'.mul ht
  have hformula : deriv (fun t => (M t).det) =ᶠ[𝓝 (0 : ℝ)]
      (fun t => (M t).det * ((M t)⁻¹ * V t).trace) := by
    filter_upwards [hM, hdn] with t ht hn
    exact (hasDerivAt_det_of_ne_zero ht hn).deriv
  convert hd₂.congr_of_eventuallyEq hformula using 1
  simp only [h₀, Matrix.det_one, inv_one, Matrix.one_mul, one_mul, pow_two]
  ring

/-- A twice differentiable real function has nonpositive second derivative at
a local maximum. The path only needs to be differentiable near that point. -/
theorem second_derivative_nonpos_of_local_max {f : ℝ → ℝ} {q : ℝ}
    (hmax : IsLocalMax f 0) (hf : ∀ᶠ t in 𝓝 (0 : ℝ), DifferentiableAt ℝ f t)
    (h₂ : HasDerivAt (deriv f) q 0) : q ≤ 0 := by
  by_contra! hq
  have hf₀ := hf.self_of_nhds
  have hz : deriv f 0 = 0 := hmax.hasDerivAt_eq_zero hf₀.hasDerivAt
  have hleft : ∀ᶠ t in 𝓝[<] (0 : ℝ), deriv f t ≤ 0 := by
    filter_upwards [h₂.tendsto_slope_zero_left (Ioi_mem_nhds hq), self_mem_nhdsWithin] with t ht htneg
    change t < 0 at htneg
    simp only [mem_Ioi, zero_add, hz, sub_zero, smul_eq_mul] at ht
    exact (neg_of_mul_pos_right ht (inv_nonpos.mpr htneg.le)).le
  have hright : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < deriv f t := by
    filter_upwards [h₂.tendsto_slope_zero_right (Ioi_mem_nhds hq), self_mem_nhdsWithin] with t ht htpos
    change 0 < t at htpos
    simp only [mem_Ioi, zero_add, hz, sub_zero, smul_eq_mul] at ht
    exact pos_of_mul_pos_right ht (inv_pos.mpr htpos).le
  have hmin := isLocalMin_of_deriv' hf₀.continuousAt
    (hf.filter_mono nhdsWithin_le_nhds) (hf.filter_mono nhdsWithin_le_nhds)
    hleft (hright.mono fun _ ht => ht.le)
  have heq : f =ᶠ[𝓝 (0 : ℝ)] fun _ => f 0 := by
    filter_upwards [hmax, hmin] with t h₁ h₂
    exact le_antisymm h₁ h₂
  have hzero : deriv f =ᶠ[𝓝 (0 : ℝ)] fun _ => 0 := by
    filter_upwards [heq.eventuallyEq_nhds] with t ht
    exact ht.deriv_eq.trans (deriv_const t (f 0))
  obtain ⟨t, ht, ht₀⟩ := (hright.and (hzero.filter_mono nhdsWithin_le_nhds)).exists
  exact (ne_of_gt ht) ht₀

end MOC
