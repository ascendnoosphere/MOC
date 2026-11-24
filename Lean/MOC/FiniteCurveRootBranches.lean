import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv

/-! Holomorphic local graphs at simple roots of plane polynomial curves. -/

open Filter Set
open scoped Topology BigOperators

namespace MOC

private noncomputable def triangularEquiv
    (L : ℂ × ℂ →L[ℂ] ℂ) (hL : L (0, 1) ≠ 0) : (ℂ × ℂ) ≃L[ℂ] (ℂ × ℂ) := by
  have hadd (p : ℂ × ℂ) : L p = p.1 * L (1, 0) + p.2 * L (0, 1) := by
    have hp : p = p.1 • ((1, 0) : ℂ × ℂ) + p.2 • ((0, 1) : ℂ × ℂ) := by
      ext <;> simp
    conv_lhs => rw [hp]
    simp only [map_add, map_smul, smul_eq_mul]
  let A := (ContinuousLinearMap.fst ℂ ℂ ℂ).prod L
  refine ContinuousLinearEquiv.ofBijective A (LinearMap.ker_eq_bot.mpr ?_)
    (LinearMap.range_eq_top.mpr ?_)
  · intro p q hpq
    change (p.1, L p) = (q.1, L q) at hpq
    have h₁ : p.1 = q.1 := by injection hpq
    have h₂ : L p = L q := congrArg Prod.snd hpq
    apply Prod.ext h₁
    rw [hadd p, hadd q, h₁, add_right_inj] at h₂
    exact mul_right_cancel₀ hL h₂
  · intro q
    refine ⟨(q.1, (q.2 - q.1 * L (1, 0)) / L (0, 1)), Prod.ext rfl ?_⟩
    change L (q.1, (q.2 - q.1 * L (1, 0)) / L (0, 1)) = q.2
    rw [hadd, Prod.fst, Prod.snd, div_mul_cancel₀ _ hL]
    ring

private theorem triangularEquiv_coe
    (L : ℂ × ℂ →L[ℂ] ℂ) (hL : L (0, 1) ≠ 0) :
    (triangularEquiv L hL : (ℂ × ℂ) →L[ℂ] (ℂ × ℂ)) =
      (ContinuousLinearMap.fst ℂ ℂ ℂ).prod L := by
  rfl

/-- A simple vertical zero has a local holomorphic graph, and this graph
contains every nearby zero. This is the local input for the root cover of
a finite complex plane curve. -/
theorem exists_local_holomorphic_zero_graph
    (F : ℂ × ℂ → ℂ) (hF : ContDiff ℂ 1 F) (z₀ w₀ : ℂ)
    (hzero : F (z₀, w₀) = 0) (hsimple : fderiv ℂ F (z₀, w₀) (0, 1) ≠ 0) :
    ∃ g : ℂ → ℂ, g z₀ = w₀ ∧
      (∀ᶠ z in 𝓝 z₀, F (z, g z) = 0 ∧ DifferentiableAt ℂ g z) ∧
      ∀ᶠ p in 𝓝 (z₀, w₀), F p = 0 → p.2 = g p.1 := by
  let H (p : ℂ × ℂ) := (p.1, F p)
  let p₀ := (z₀, w₀)
  let E := triangularEquiv (fderiv ℂ F p₀) hsimple
  have hder (p : ℂ × ℂ) :
      HasStrictFDerivAt H ((ContinuousLinearMap.fst ℂ ℂ ℂ).prod (fderiv ℂ F p)) p :=
    (ContinuousLinearMap.fst ℂ ℂ ℂ).hasStrictFDerivAt.prodMk (hF.hasStrictFDerivAt le_rfl)
  have hD : HasStrictFDerivAt H (E : (ℂ × ℂ) →L[ℂ] (ℂ × ℂ)) p₀ := by
    rw [triangularEquiv_coe]
    exact hder p₀
  let e := hD.toPartialHomeomorph H
  have he (p : ℂ × ℂ) : e p = H p := rfl
  have hep : p₀ ∈ e.source := hD.mem_toPartialHomeomorph_source
  have heq : (z₀, (0 : ℂ)) ∈ e.target := by
    have h := e.map_source hep
    simpa only [he, H, p₀, hzero] using h
  let j (z : ℂ) := (z, (0 : ℂ))
  let g (z : ℂ) := (e.symm (j z)).2
  have hij : e.symm (j z₀) = p₀ := by
    have h : j z₀ = e p₀ := by simp only [he, H, hzero, j, p₀]
    rw [h, e.left_inv hep]
  have hj : Continuous j := continuous_id.prodMk continuous_const
  have ht : ∀ᶠ z in 𝓝 z₀, j z ∈ e.target :=
    hj.continuousAt (e.open_target.mem_nhds heq)
  have hs : ∀ᶠ p in 𝓝 p₀, fderiv ℂ F p (0, 1) ≠ 0 := by
    exact (isOpen_ne_fun ((hF.continuous_fderiv_apply le_rfl).comp (continuous_id.prodMk (continuous_const (y := ((0, 1) : ℂ × ℂ))))) continuous_const).mem_nhds hsimple
  have hnear : ∀ᶠ z in 𝓝 z₀, fderiv ℂ F (e.symm (j z)) (0, 1) ≠ 0 := by
    have hj₀ : ContinuousAt j z₀ := hj.continuousAt
    have he₀ : ContinuousAt e.symm (j z₀) := e.continuousAt_symm heq
    have hc : Tendsto (fun z => e.symm (j z)) (𝓝 z₀) (𝓝 p₀) := by
      simpa only [ContinuousAt, Function.comp_apply, hij] using he₀.comp hj₀
    exact hc hs
  refine ⟨g, congrArg Prod.snd hij, ?_, ?_⟩
  · filter_upwards [ht, hnear] with z hz hs
    have hright := e.right_inv hz
    have heval : H (e.symm (j z)) = j z := by simpa only [he] using hright
    have hfst : (e.symm (j z)).1 = z := congrArg Prod.fst heval
    have hsnd : F (e.symm (j z)) = 0 := congrArg Prod.snd heval
    have hzg : (z, g z) = e.symm (j z) := Prod.ext hfst.symm rfl
    refine ⟨hzg ▸ ?_, ?_⟩
    · simpa only [hzg] using hsnd
    · let E' := triangularEquiv (fderiv ℂ F (e.symm (j z))) hs
      have h' : HasStrictFDerivAt e (E' : (ℂ × ℂ) →L[ℂ] (ℂ × ℂ)) (e.symm (j z)) := by
        rw [triangularEquiv_coe, show (e : ℂ × ℂ → ℂ × ℂ) = H from rfl]
        exact hder _
      have hd := (e.hasStrictFDerivAt_symm hz h').differentiableAt
      have hdj : DifferentiableAt ℂ j z := differentiableAt_id.prodMk (differentiableAt_const (0 : ℂ))
      exact (hd.comp z hdj).snd
  · filter_upwards [e.open_source.mem_nhds hep] with p hp h0
    have he' : e p = j p.1 := by simp only [he, H, h0, j]
    change p.2 = (e.symm (j p.1)).2
    rw [← he', e.left_inv hp]

/-- Applied to a polynomial finite projection, a simple specialized root has
a unique local holomorphic continuation among the nearby roots. -/
theorem exists_local_holomorphic_simple_root
    (P : Polynomial (Polynomial ℂ)) (z₀ w₀ : ℂ)
    (hzero : (P.map (Polynomial.evalRingHom z₀)).IsRoot w₀)
    (hsimple : (P.map (Polynomial.evalRingHom z₀)).derivative.eval w₀ ≠ 0) :
    ∃ g : ℂ → ℂ, g z₀ = w₀ ∧
      (∀ᶠ z in 𝓝 z₀, (P.map (Polynomial.evalRingHom z)).IsRoot (g z) ∧
        DifferentiableAt ℂ g z) ∧
      ∀ᶠ p : ℂ × ℂ in 𝓝 (z₀, w₀),
        (P.map (Polynomial.evalRingHom p.1)).IsRoot p.2 → p.2 = g p.1 := by
  open Polynomial in
  let F (p : ℂ × ℂ) := (P.map (evalRingHom p.1)).eval p.2
  have hev (q : Polynomial ℂ) : ContDiff ℂ 1 (fun z => q.eval z) := by
    simp_rw [Polynomial.eval_eq_sum_range]
    exact ContDiff.sum (fun k _ =>
      contDiff_const.mul (contDiff_id.pow k))
  have hformula (p : ℂ × ℂ) :
      F p = ∑ k ∈ Finset.range (P.natDegree + 1), (P.coeff k).eval p.1 * p.2 ^ k := by
    dsimp only [F]
    rw [Polynomial.eval_map, Polynomial.eval₂_eq_sum_range]
    rfl
  have hF : ContDiff ℂ 1 F := by
    rw [funext hformula]
    exact ContDiff.sum (fun k _ =>
      ((hev (P.coeff k)).comp contDiff_fst).mul (contDiff_snd.pow k))
  let j (w : ℂ) := (z₀, w)
  let J : ℂ →L[ℂ] ℂ × ℂ := (0 : ℂ →L[ℂ] ℂ).prod (1 : ℂ →L[ℂ] ℂ)
  have hj : HasFDerivAt j J w₀ :=
    (hasFDerivAt_const z₀ w₀).prodMk (hasFDerivAt_id w₀)
  have hd := ((hF.differentiable (by decide) (z₀, w₀)).hasFDerivAt.comp w₀ hj).fderiv
  have hsimple' : fderiv ℂ F (z₀, w₀) (0, 1) ≠ 0 := by
    have hh := congrArg (fun L : ℂ →L[ℂ] ℂ => L 1) hd
    change fderiv ℂ (fun w => (P.map (Polynomial.evalRingHom z₀)).eval w) w₀ 1 =
      fderiv ℂ F (z₀, w₀) (0, 1) at hh
    rw [← hh, (P.map (Polynomial.evalRingHom z₀)).fderiv]
    simpa using hsimple
  exact exists_local_holomorphic_zero_graph F hF z₀ w₀ hzero hsimple'

end MOC
