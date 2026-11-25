import MOC.PolynomialRootPersistence
import Mathlib.Algebra.Polynomial.Reverse

/-! A finite root persists even when the leading coefficient of the plane equation vanishes. -/

open Filter Polynomial Set
open scoped Topology

namespace MOC

private theorem continuous_specialized_eval
    (P : Polynomial (Polynomial ℂ)) (b : ℂ) :
    Continuous fun a : ℂ => (P.map (Polynomial.evalRingHom a)).eval b := by
  simp only [Polynomial.eval_map, Polynomial.eval₂_eq_sum, Polynomial.sum_def,
    Polynomial.coe_evalRingHom]
  exact continuous_finset_sum _ fun j _ => (P.coeff j).continuous.mul continuous_const

private theorem eval_reflect_eq_zero_iff
    {p : Polynomial ℂ} {D : ℕ} (hp : p.natDegree ≤ D) {w : ℂ} (hw : w ≠ 0) :
    (p.reflect D).eval w = 0 ↔ p.eval w⁻¹ = 0 := by
  letI := invertibleOfNonzero (inv_ne_zero hw)
  simpa only [Polynomial.eval₂_eq_eval_map, Polynomial.map_id, invOf_eq_inv, inv_inv] using
    Polynomial.eval₂_reflect_eq_zero_iff (RingHom.id ℂ) w⁻¹ D p hp

/-- If the distinguished specialization is a nonzero polynomial, each
neighborhood of one of its roots contains a root for all nearby parameters.
The degree of specialization may jump. -/
theorem eventually_exists_specialized_root_mem_nhds_of_ne_zero
    (P : Polynomial (Polynomial ℂ)) {a₀ b₀ : ℂ}
    (hP : P.map (Polynomial.evalRingHom a₀) ≠ 0)
    (hroot : (P.map (Polynomial.evalRingHom a₀)).eval b₀ = 0)
    {V : Set ℂ} (hV : V ∈ 𝓝 b₀) :
    ∀ᶠ a in 𝓝 a₀, ∃ b ∈ V, (P.map (Polynomial.evalRingHom a)).eval b = 0 := by
  classical
  obtain ⟨c, hc⟩ := (Polynomial.finite_setOf_isRoot hP).exists_not_mem
  have hc' : (P.map (Polynomial.evalRingHom a₀)).eval c ≠ 0 := hc
  have hbc : b₀ ≠ c := fun h => hc' (h ▸ hroot)
  let Q := P.comp (Polynomial.X + Polynomial.C (Polynomial.C c))
  let q (a : ℂ) := Q.map (Polynomial.evalRingHom a)
  let d := Q.natDegree
  let w₀ := (b₀ - c)⁻¹
  have hshift (a w : ℂ) : (q a).eval w = (P.map (Polynomial.evalRingHom a)).eval (w + c) := by
    simp [q, Q, Polynomial.map_comp, Polynomial.eval_comp]
  have hw₀ : w₀ ≠ 0 := inv_ne_zero (sub_ne_zero.mpr hbc)
  have hw : w₀⁻¹ + c = b₀ := by simp [w₀]
  have hq₀ : (q a₀).eval 0 ≠ 0 := by simpa only [hshift, zero_add] using hc'
  have hcont₀ : ContinuousAt (fun a => (q a).eval 0) a₀ :=
    (continuous_specialized_eval Q 0).continuousAt
  have hnear := hcont₀.eventually_ne hq₀
  let r (a : ℂ) := (q a).reflect d
  let R (a : ℂ) := if (q a).eval 0 ≠ 0 then Polynomial.C ((q a).eval 0)⁻¹ * r a
    else Polynomial.X ^ d
  have hbd (a : ℂ) : (q a).natDegree ≤ d := Polynomial.natDegree_map_le
  have hrbd (a : ℂ) : (r a).natDegree ≤ d := by
    refine Polynomial.natDegree_le_iff_coeff_eq_zero.mpr fun j hj => ?_
    simp only [r, Polynomial.coeff_reflect, Polynomial.revAt_eq_self_of_lt hj]
    exact Polynomial.coeff_eq_zero_of_natDegree_lt ((hbd a).trans_lt hj)
  have hRd (a : ℂ) : (R a).Monic ∧ (R a).natDegree = d := by
    by_cases h : (q a).eval 0 ≠ 0
    · rw [show R a = Polynomial.C ((q a).eval 0)⁻¹ * r a from if_pos h]
      have hle : (Polynomial.C ((q a).eval 0)⁻¹ * r a).natDegree ≤ d := by
        exact Polynomial.natDegree_mul_le.trans (by simpa using hrbd a)
      have hcoeff : (Polynomial.C ((q a).eval 0)⁻¹ * r a).coeff d = 1 := by
        rw [Polynomial.coeff_C_mul, show (r a).coeff d = (q a).eval 0 by
          simp [r, Polynomial.revAt_le, Polynomial.eval_zero]]
        exact inv_mul_cancel₀ h
      exact ⟨Polynomial.monic_of_natDegree_le_of_coeff_eq_one d hle hcoeff,
        le_antisymm hle (Polynomial.le_natDegree_of_ne_zero (hcoeff.trans_ne one_ne_zero))⟩
    · rw [show R a = Polynomial.X ^ d from if_neg h]
      exact ⟨Polynomial.monic_X_pow _, Polynomial.natDegree_X_pow _⟩
  have hcont : ContinuousAt (fun a => (R a).eval w₀) a₀ := by
    have hrcont : ContinuousAt (fun a => (r a).eval w₀) a₀ := by
      have h : ContinuousAt (fun a => ((Q.reflect d).map (Polynomial.evalRingHom a)).eval w₀) a₀ :=
        (continuous_specialized_eval (Q.reflect d) w₀).continuousAt
      simpa only [r, q, Polynomial.reflect_map] using h
    refine ((hcont₀.inv₀ hq₀).mul hrcont).congr_of_eventuallyEq ?_
    filter_upwards [hnear] with a ha
    simp [R, ha, Polynomial.eval_mul, Polynomial.eval_C]
  have hR₀ : (R a₀).eval w₀ = 0 := by
    have hz : (r a₀).eval w₀ = 0 := (eval_reflect_eq_zero_iff (hbd a₀) hw₀).mpr (by
      rw [hshift, hw, hroot])
    simp [R, hq₀, hz, Polynomial.eval_mul]
  let W := (fun w : ℂ => w⁻¹ + c) ⁻¹' V ∩ {w : ℂ | w ≠ 0}
  have hW : W ∈ 𝓝 w₀ := by
    have hcw : ContinuousAt (fun w : ℂ => w⁻¹ + c) w₀ :=
      (continuousAt_inv₀ hw₀).add continuousAt_const
    exact Filter.inter_mem (hcw (hw.symm ▸ hV)) (isOpen_ne.mem_nhds hw₀)
  have he := eventually_exists_root_mem_nhds R (fun a => (hRd a).1) (fun a => (hRd a).2)
    hcont hR₀ hW
  filter_upwards [he, hnear] with a ha ha₀
  obtain ⟨w, hwW, hR⟩ := ha
  have hr : (r a).eval w = 0 := by
    have hmul : ((q a).eval 0)⁻¹ * (r a).eval w = 0 := by
      simpa [R, ha₀, Polynomial.eval_mul, Polynomial.eval_C] using hR
    exact (mul_eq_zero.mp hmul).resolve_left (inv_ne_zero ha₀)
  have hq := (eval_reflect_eq_zero_iff (hbd a) hwW.2).mp hr
  exact ⟨w⁻¹ + c, hwW.1, (hshift a w⁻¹).symm.trans hq⟩

end MOC
