import MOC.SchurPivot
import MOC.StrongSupport

/-! The full Schur phase circle under a quadratic determinant support penalty. -/

open BigOperators Filter Matrix
open scoped Topology

namespace MOC

noncomputable section

private theorem phase_quadratic_form (ξ P R : ℂ) (hP : (ξ * P).im = 0)
    (hpenalty : ∀ z : ℂ, Complex.normSq z = 1 →
      let δ := (((1 - z.re : ℝ) : ℂ) * R + (z.im : ℂ) * (Complex.I * P))
      (ξ * δ).re ≤ -Complex.normSq δ / 2) :
    ∀ u v : ℝ,
      Complex.normSq ((u : ℂ) * (Complex.I * P) + (v : ℂ) * R) ≤
        -(ξ * R).re * (u ^ 2 + v ^ 2) := by
  have hI : (ξ * (Complex.I * P)).re = 0 := by
    rw [show ξ * (Complex.I * P) = Complex.I * (ξ * P) by ring, Complex.I_mul_re, hP, neg_zero]
  have hre (r : ℝ) (w : ℂ) : ((r : ℂ) * w).re = r * w.re := by simp
  have hstep (u v : ℝ) (hv : v ≠ 0) :
      Complex.normSq ((u : ℂ) * (Complex.I * P) + (v : ℂ) * R) ≤
        -(ξ * R).re * (u ^ 2 + v ^ 2) := by
    let d := u ^ 2 + v ^ 2
    have hd : 0 < d := add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_ne_zero hv)
    let z : ℂ := ⟨(u ^ 2 - v ^ 2) / d, 2 * u * v / d⟩
    have hz : Complex.normSq z = 1 := by
      simp only [z, Complex.normSq_mk]
      field_simp [hd.ne'] <;> dsimp only [d] <;> ring
    have hzr : 1 - z.re = 2 * v ^ 2 / d := by
      change 1 - (u ^ 2 - v ^ 2) / d = _
      field_simp [hd.ne'] <;> dsimp only [d] <;> ring
    let δ : ℂ := ((1 - z.re : ℝ) : ℂ) * R + (z.im : ℂ) * (Complex.I * P)
    let q : ℝ := 2 * v ^ 2 / d
    let k : ℝ := 2 * v / d
    let W : ℂ := (u : ℂ) * (Complex.I * P) + (v : ℂ) * R
    have hq : 0 < q := div_pos (mul_pos (by norm_num) (sq_pos_of_ne_zero hv)) hd
    have hreal : (ξ * δ).re = q * (ξ * R).re := by
      have he : ξ * δ = ((1 - z.re : ℝ) : ℂ) * (ξ * R) +
          (z.im : ℂ) * (ξ * (Complex.I * P)) := by
        dsimp only [δ]
        ring
      rw [he, Complex.add_re, hre, hre, hI, mul_zero, add_zero, hzr]
    have hkV : q = k * v := by dsimp only [q, k]; field_simp [hd.ne'] <;> ring
    have hkU : z.im = k * u := by dsimp only [z, k]; field_simp [hd.ne'] <;> ring
    have hδ : δ = (k : ℂ) * W := by
      dsimp only [δ, W]
      rw [hzr, ← show q = 2 * v ^ 2 / d by rfl, hkV, hkU, Complex.ofReal_mul, Complex.ofReal_mul]
      ring
    have hk2 : k ^ 2 = q * (2 / d) := by
      dsimp only [k, q]
      field_simp [hd.ne'] <;> ring
    have hh : (ξ * δ).re ≤ -Complex.normSq δ / 2 := hpenalty z hz
    rw [hreal, hδ, Complex.normSq_mul, Complex.normSq_ofReal, ← sq, hk2] at hh
    have he : -(q * (2 / d) * Complex.normSq W) / 2 = q * (-Complex.normSq W / d) := by ring
    rw [he] at hh
    have hle := (le_div_iff₀ hd).mp (le_of_mul_le_mul_left hh hq)
    change Complex.normSq W ≤ -(ξ * R).re * d
    linarith only [hle]
  intro u v
  by_cases hv : v = 0
  · subst v
    have hleft : Continuous (fun t : ℝ =>
        Complex.normSq ((u : ℂ) * (Complex.I * P) + (t : ℂ) * R)) :=
      Complex.continuous_normSq.comp (by fun_prop)
    have hright : Continuous (fun t : ℝ => -(ξ * R).re * (u ^ 2 + t ^ 2)) := by fun_prop
    refine le_of_tendsto_of_tendsto
      (hleft.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
      (hright.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact hstep u t ht
  · exact hstep u v hv

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The quadratic support penalty along a Schur phase bounds a real quadratic
form combining the first-order imaginary motion and the reflection chord. -/
theorem schurPhase_quadratic_support_bound (x : ℂ) (p v : Matrix Unit ι ℂ)
    (w : Matrix ι Unit ℂ) (T : Matrix ι ι ℂ) (hT : T.det ≠ 0) (ξ : ℂ)
    (hpenalty : ∀ z : ℂ, Complex.normSq z = 1 →
      let δ := (schurPhaseSum x p v w T z).det - (schurPhaseSum x p v w T 1).det
      (ξ * δ).re ≤ -Complex.normSq δ / 2) :
    let P := T.det * (p * T⁻¹ * w) () ()
    let R := P - 2 * (T.det * (v * T⁻¹ * w) () ())
    (ξ * P).im = 0 ∧
      ∀ u t : ℝ,
        Complex.normSq ((u : ℂ) * (Complex.I * P) + (t : ℂ) * R) ≤
          -(ξ * R).re * (u ^ 2 + t ^ 2) := by
  intro P R
  let S := schurPhaseSum x p v w T
  have hmax (z : ℂ) (hz : Complex.normSq z = 1) :
      (ξ * (S z).det).re ≤ (ξ * (S 1).det).re := by
    have h := hpenalty z hz
    change (ξ * ((S z).det - (S 1).det)).re ≤ -Complex.normSq ((S z).det - (S 1).det) / 2 at h
    rw [mul_sub, Complex.sub_re] at h
    linarith only [h, Complex.normSq_nonneg ((S z).det - (S 1).det)]
  have hP : (ξ * P).im = 0 := by
    simpa only [P, mul_assoc] using
      (schurPhase_support_coefficients x p v w T hT ξ hmax).2
  refine ⟨hP, phase_quadratic_form ξ P R hP ?_⟩
  intro z hz
  have hzz : z * star z = 1 := by
    rw [Complex.star_def, Complex.mul_conj, hz, Complex.ofReal_one]
  have hz1 : (z - 1) * (star z - 1) = (2 : ℂ) * ((1 - z.re : ℝ) : ℂ) := by
    calc
      _ = 2 - (z + star z) := by linear_combination hzz
      _ = _ := by rw [Complex.star_def, Complex.add_conj, Complex.ofReal_sub]; ring
  have hz2 : 1 - star z = ((1 - z.re : ℝ) : ℂ) + (z.im : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [Complex.star_def]
  have hδ :
      (S z).det - (S 1).det =
        ((1 - z.re : ℝ) : ℂ) * R + (z.im : ℂ) * (Complex.I * P) := by
    change (schurPhaseSum x p v w T z).det - (schurPhaseSum x p v w T 1).det = _
    rw [det_schurPhaseSum x p v w T hT z, det_schurPhaseSum x p v w T hT 1, hz1, hz2]
    simp only [star_one, sub_self, zero_mul, mul_zero, add_zero, sub_zero]
    dsimp only [R, P]
    ring
  simpa only [← hδ] using hpenalty z hz

/-- A zero reflection support loss forces the whole Schur phase determinant
curve to be constant under the quadratic penalty. -/
theorem schurPhase_flat_of_zero_reflection_support_loss (x : ℂ) (p v : Matrix Unit ι ℂ)
    (w : Matrix ι Unit ℂ) (T : Matrix ι ι ℂ) (hT : T.det ≠ 0) (ξ : ℂ)
    (hpenalty : ∀ z : ℂ, Complex.normSq z = 1 →
      let δ := (schurPhaseSum x p v w T z).det - (schurPhaseSum x p v w T 1).det
      (ξ * δ).re ≤ -Complex.normSq δ / 2)
    (hflat : (ξ * (T.det * (p * T⁻¹ * w) () () -
      2 * (T.det * (v * T⁻¹ * w) () ()))).re = 0) :
    (p * T⁻¹ * w) () () = 0 ∧ (v * T⁻¹ * w) () () = 0 := by
  let P := T.det * (p * T⁻¹ * w) () ()
  let Q := T.det * (v * T⁻¹ * w) () ()
  let R := P - 2 * Q
  have hb := (schurPhase_quadratic_support_bound x p v w T hT ξ hpenalty).2
  change (ξ * R).re = 0 at hflat
  have hp := hb 1 0
  have hr := hb 0 1
  change Complex.normSq (((1 : ℝ) : ℂ) * (Complex.I * P) + ((0 : ℝ) : ℂ) * R) ≤
    -(ξ * R).re * (1 ^ 2 + 0 ^ 2) at hp
  change Complex.normSq (((0 : ℝ) : ℂ) * (Complex.I * P) + ((1 : ℝ) : ℂ) * R) ≤
    -(ξ * R).re * (0 ^ 2 + 1 ^ 2) at hr
  simp only [Complex.ofReal_one, Complex.ofReal_zero, one_mul, zero_mul, add_zero, zero_add,
    Complex.normSq_mul, Complex.normSq_I, hflat, neg_zero] at hp hr
  have hP : P = 0 :=
    Complex.normSq_eq_zero.mp (le_antisymm hp (Complex.normSq_nonneg P))
  have hR : R = 0 :=
    Complex.normSq_eq_zero.mp (le_antisymm hr (Complex.normSq_nonneg R))
  have hQ : Q = 0 := by
    have hq : 2 * Q = 0 := by simpa only [R, hP, zero_sub, neg_eq_zero] using hR
    exact (mul_eq_zero.mp hq).resolve_left two_ne_zero
  exact ⟨(mul_eq_zero.mp hP).resolve_left hT, (mul_eq_zero.mp hQ).resolve_left hT⟩

end

end MOC
