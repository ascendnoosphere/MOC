import Mathlib.Analysis.Complex.OpenMapping
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Algebra.Polynomial.Roots

/-! A quotient of complex polynomials that is real on an open set is constant. -/

open Filter Set
open scoped Topology ComplexConjugate

namespace MOC

/-- If the product of one polynomial value and the conjugate of another
is real on a nonempty open set, the polynomials are real scalar multiples
when the second polynomial is nonzero. -/
theorem polynomial_eq_real_mul_of_im_mul_conj_eq_zero {P Q : Polynomial ℂ}
    {S : Set ℂ} (hS : IsOpen S) (hne : S.Nonempty) (hQ : Q ≠ 0)
    (hreal : ∀ z ∈ S, (P.eval z * conj (Q.eval z)).im = 0) :
    ∃ c : ℝ, P = Polynomial.C (c : ℂ) * Q := by
  have hp := AnalyticOnNhd.eval_polynomial (𝕜 := ℂ) P
  have hq := AnalyticOnNhd.eval_polynomial (𝕜 := ℂ) Q
  obtain ⟨x, hx, hqx⟩ : ∃ x ∈ S, Q.eval x ≠ 0 := by
    by_contra! hz
    obtain ⟨y, hy⟩ := hne
    have hy' : ∀ᶠ z in 𝓝 y, z ∈ S := hS.mem_nhds hy
    have he : (fun z => Q.eval z) =ᶠ[𝓝 y] (fun _ => (0 : ℂ)) :=
      hy'.mono (fun z hz' => hz z hz')
    have hzero := hq.eq_of_eventuallyEq analyticOnNhd_const he
    exact hQ (Polynomial.funext fun z => by simpa only [Polynomial.eval_zero] using congrFun hzero z)
  let f (z : ℂ) := P.eval z / Q.eval z
  have hf : AnalyticAt ℂ f x :=
    (hp x (mem_univ x)).fun_div (hq x (mem_univ x)) hqx
  have hfReal (z : ℂ) (hz : z ∈ S) : (f z).im = 0 := by
    have h := hreal z hz
    rw [Complex.mul_im, Complex.conj_re, Complex.conj_im, mul_neg, add_comm,
      ← sub_eq_add_neg] at h
    change (P.eval z / Q.eval z).im = 0
    rw [Complex.div_im, ← sub_div, h, zero_div]
  have hconst : ∀ᶠ z in 𝓝 x, f z = f x := by
    refine hf.eventually_constant_or_nhds_le_map_nhds.resolve_right ?_
    intro hopen
    have hx' : ∀ᶠ z in 𝓝 x, z ∈ S := hS.mem_nhds hx
    have hmem : (Complex.im ⁻¹' ({0} : Set ℝ)) ∈ 𝓝 (f x) :=
      hopen (hx'.mono fun z hz => hfReal z hz)
    have hfx := mem_interior_iff_mem_nhds.mpr hmem
    rw [Complex.interior_preimage_im, interior_singleton] at hfx
    exact hfx
  have hc : (↑(f x).re : ℂ) = f x :=
    Complex.ext rfl (by rw [Complex.ofReal_im, hfReal x hx])
  have hnn : ∀ᶠ z in 𝓝 x, Q.eval z ≠ 0 :=
    (hq x (mem_univ x)).continuousAt.eventually_ne hqx
  let R := Polynomial.C (↑(f x).re : ℂ) * Q
  refine ⟨(f x).re, Polynomial.funext fun z => ?_⟩
  have he : (fun z => P.eval z) =ᶠ[𝓝 x] (fun z => R.eval z) := by
    filter_upwards [hconst, hnn] with z hz hqz
    rw [show R.eval z = (↑(f x).re : ℂ) * Q.eval z by simp [R], hc]
    exact (div_eq_iff hqz).mp hz
  exact congrFun (hp.eq_of_eventuallyEq (AnalyticOnNhd.eval_polynomial (𝕜 := ℂ) R) he) z

end MOC
