import MOC.StrongSupport
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

/-! A sextic test for the quadratic support penalty on a degree-two phase
orbit. The half-angle parameters retain the complex determinant motion. -/

open Filter
open scoped Topology

namespace MOC

noncomputable section

/-- The complex increment on a phase circle written in the two coordinates
`y = Im z` and `h = 1 - Re z`. -/
def rankTwoPhaseChange (P R T S z : ℂ) : ℂ :=
  let h := 1 - z.re
  let y := z.im
  (y : ℂ) * P + (h : ℂ) * R + ((h * y : ℝ) : ℂ) * T + ((h ^ 2 : ℝ) : ℂ) * S

/-- Every degree-two Laurent phase increment has the required four-coefficient form. -/
theorem rankTwoPhaseChange_eq_laurent (A B C D z : ℂ) (hz : Complex.normSq z = 1) :
    rankTwoPhaseChange (Complex.I * (A - B + 2 * (C - D)))
      (-(A + B + 4 * (C + D))) (-2 * Complex.I * (C - D)) (2 * (C + D)) z =
        (z - 1) * A + (star z - 1) * B + (z ^ 2 - 1) * C + ((star z) ^ 2 - 1) * D := by
  let h := 1 - z.re
  let y := z.im
  have hhy : h ^ 2 + y ^ 2 = 2 * h := by
    rw [Complex.normSq_apply] at hz
    dsimp only [h, y]
    nlinarith only [hz]
  have hhC := congrArg (fun x : ℝ => (x : ℂ)) hhy
  push_cast at hhC
  have hz₁ : z = ((1 - h : ℝ) : ℂ) + (y : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [h, y]
  have hz₂ : star z = ((1 - h : ℝ) : ℂ) - (y : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [h, y, Complex.star_def]
  change (y : ℂ) * (Complex.I * (A - B + 2 * (C - D))) +
    (h : ℂ) * (-(A + B + 4 * (C + D))) + ((h * y : ℝ) : ℂ) * (-2 * Complex.I * (C - D)) +
    ((h ^ 2 : ℝ) : ℂ) * (2 * (C + D)) = _
  rw [hz₂, hz₁]
  push_cast
  linear_combination (C + D) * hhC - (y : ℂ) ^ 2 * (C + D) * Complex.I_sq

/-- The homogeneous half-angle polynomial of a disk support inequality. -/
def rankTwoPhaseDiskSextic (ξ P R T S : ℂ) (u v : ℝ) : ℝ :=
  let d := u ^ 2 + v ^ 2
  -((ξ * R).re * d + 2 * u * v * (ξ * T).re + 2 * v ^ 2 * (ξ * S).re) * d ^ 2 -
    Complex.normSq
      (((u : ℂ) * P + (v : ℂ) * R) * (d : ℂ) +
        ((2 * v ^ 2 : ℝ) : ℂ) * ((u : ℂ) * T + (v : ℂ) * S))

private theorem phaseDisk_re_real_mul (ξ Ω : ℂ) (r : ℝ) :
    (ξ * ((r : ℂ) * Ω)).re = r * (ξ * Ω).re := by
  rw [mul_left_comm ξ]
  simp

/-- Disk support of a rank-two phase fiber with stationary first-order support
forces its binary sextic to be nonnegative. -/
theorem rankTwoPhase_disk_sextic_nonneg (ξ P R T S : ℂ) (hP : (ξ * P).re = 0)
    (hpenalty : ∀ z : ℂ, Complex.normSq z = 1 →
      (ξ * rankTwoPhaseChange P R T S z).re ≤ -Complex.normSq (rankTwoPhaseChange P R T S z) / 2) :
    ∀ u v : ℝ, 0 ≤ rankTwoPhaseDiskSextic ξ P R T S u v := by
  have hne (u v : ℝ) (hv : v ≠ 0) : 0 ≤ rankTwoPhaseDiskSextic ξ P R T S u v := by
    let d := u ^ 2 + v ^ 2
    have hd : 0 < d := add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_ne_zero hv)
    let z : ℂ := ⟨1 - 2 * v ^ 2 / d, 2 * u * v / d⟩
    have hz : Complex.normSq z = 1 := by
      simp only [z, Complex.normSq_mk]
      field_simp [hd.ne'] <;> dsimp only [d] <;> ring
    have hzr : 1 - z.re = 2 * v ^ 2 / d := by
      change 1 - (1 - 2 * v ^ 2 / d) = _
      ring
    let W := ((u : ℂ) * P + (v : ℂ) * R) * (d : ℂ) +
      ((2 * v ^ 2 : ℝ) : ℂ) * ((u : ℂ) * T + (v : ℂ) * S)
    let F := (ξ * R).re * d + 2 * u * v * (ξ * T).re + 2 * v ^ 2 * (ξ * S).re
    let k := 2 * v / d ^ 2
    let q := 2 * v ^ 2 / d ^ 2
    have hq : 0 < q := div_pos (mul_pos (by norm_num) (sq_pos_of_ne_zero hv)) (pow_pos hd 2)
    have hratio : k * v = q := by dsimp only [k, q]; field_simp [hd.ne'] <;> ring
    have hsq : k * k / 2 = q / d ^ 2 := by dsimp only [k, q]; field_simp [hd.ne'] <;> ring
    have hW : (ξ * W).re = v * F := by
      dsimp only [W, F]
      rw [mul_comm _ (d : ℂ)]
      simp only [mul_add, Complex.add_re, phaseDisk_re_real_mul, hP, mul_zero, zero_add]
      ring
    have hδ : rankTwoPhaseChange P R T S z = (k : ℂ) * W := by
      have hdC : (d : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hd.ne'
      simp only [rankTwoPhaseChange, hzr, show z.im = 2 * u * v / d from rfl, W, k]
      push_cast
      field_simp [hdC] <;> ring
    have hRe : (ξ * rankTwoPhaseChange P R T S z).re = q * F := by
      rw [hδ, phaseDisk_re_real_mul, hW, ← mul_assoc, hratio]
    have hnorm : -Complex.normSq (rankTwoPhaseChange P R T S z) / 2 =
        q * (-Complex.normSq W / d ^ 2) := by
      rw [hδ, Complex.normSq_mul, Complex.normSq_ofReal]
      calc
        _ = -(k * k / 2) * Complex.normSq W := by ring
        _ = _ := by rw [hsq]; ring
    have hp := hpenalty z hz
    rw [hRe, hnorm] at hp
    have hF := (le_div_iff₀ (pow_pos hd 2)).mp (le_of_mul_le_mul_left hp hq)
    change 0 ≤ -F * d ^ 2 - Complex.normSq W
    linarith only [hF]
  intro u v
  by_cases hv : v = 0
  · subst v
    have hc : Continuous (rankTwoPhaseDiskSextic ξ P R T S u) := by
      unfold rankTwoPhaseDiskSextic
      simp only [Complex.normSq_eq_norm_sq]
      fun_prop
    refine le_of_tendsto_of_tendsto (b := 𝓝[≠] (0 : ℝ))
      tendsto_const_nhds (hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact hne u t ht
  · exact hne u v hv

/-- In a Hessian-null phase direction the fourth-order support loss controls
the first remaining complex motion. -/
theorem rankTwoPhase_quartic_bound_of_null_disk (ξ P R T S : ℂ) (hP : (ξ * P).re = 0)
    (hR : (ξ * R).re = 0)
    (hpenalty : ∀ z : ℂ, Complex.normSq z = 1 →
      (ξ * rankTwoPhaseChange P R T S z).re ≤ -Complex.normSq (rankTwoPhaseChange P R T S z) / 2) :
    P = 0 ∧ Complex.normSq R ≤ -2 * (ξ * S).re := by
  have h6 := rankTwoPhase_disk_sextic_nonneg ξ P R T S hP hpenalty
  have ht := h6 1 0
  have hp : P = 0 := by
    norm_num [rankTwoPhaseDiskSextic, hR] at ht
    exact Complex.normSq_eq_zero.mp (le_antisymm (by linarith only [ht]) (Complex.normSq_nonneg _))
  let G (t : ℝ) :=
    -2 * (ξ * S).re * (1 + t ^ 2) ^ 2 -
      Complex.normSq (((1 + t ^ 2 : ℝ) : ℂ) * R + ((2 * t ^ 2 : ℝ) : ℂ) * S) -
      4 * t ^ 2 * Complex.normSq T
  have hfactor (t : ℝ) :
      rankTwoPhaseDiskSextic ξ P R T S 1 t + rankTwoPhaseDiskSextic ξ P R T S 1 (-t) =
        2 * t ^ 2 * G t := by
    simp [rankTwoPhaseDiskSextic, G, hp, hR, Complex.normSq_apply,
      Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im] <;> ring
  have hn (t : ℝ) (ht : t ≠ 0) : 0 ≤ G t := by
    have hs := add_nonneg (h6 1 t) (h6 1 (-t))
    rw [hfactor] at hs
    exact nonneg_of_mul_nonneg_right hs (mul_pos (by norm_num) (sq_pos_of_ne_zero ht))
  have hc : Continuous G := by
    unfold G
    simp only [Complex.normSq_eq_norm_sq]
    fun_prop
  have ht₀ : 0 ≤ G 0 := by
    refine le_of_tendsto_of_tendsto (b := 𝓝[≠] (0 : ℝ))
      tendsto_const_nhds (hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact hn t ht
  refine ⟨hp, ?_⟩
  simp only [G, zero_pow (by decide : (2 : ℕ) ≠ 0), add_zero, one_pow, Complex.ofReal_one,
    mul_zero, Complex.ofReal_zero, zero_mul, one_mul, sub_zero] at ht₀
  linarith only [ht₀]

/-- A disk-supported phase fiber with vanishing first, second, and fourth
projected coefficients has constant complex determinant. -/
theorem rankTwoPhase_eq_zero_of_flat_disk (ξ P R T S : ℂ) (hP : (ξ * P).re = 0)
    (hR : (ξ * R).re = 0) (hS : (ξ * S).re = 0)
    (hpenalty : ∀ z : ℂ, Complex.normSq z = 1 →
      (ξ * rankTwoPhaseChange P R T S z).re ≤ -Complex.normSq (rankTwoPhaseChange P R T S z) / 2)
    {z : ℂ} (hz : Complex.normSq z = 1) : rankTwoPhaseChange P R T S z = 0 := by
  have hRe (w : ℂ) : (ξ * rankTwoPhaseChange P R T S w).re =
      (1 - w.re) * w.im * (ξ * T).re := by
    simp only [rankTwoPhaseChange, mul_add, Complex.add_re, phaseDisk_re_real_mul,
      hP, hR, hS, mul_zero, zero_add, add_zero]
  have hnonpos (w : ℂ) (hw : Complex.normSq w = 1) : (ξ * rankTwoPhaseChange P R T S w).re ≤ 0 :=
    (hpenalty w hw).trans (by linarith only [Complex.normSq_nonneg (rankTwoPhaseChange P R T S w)])
  have hi := hnonpos Complex.I Complex.normSq_I
  have hj := hnonpos (-Complex.I) (by rw [Complex.normSq_neg, Complex.normSq_I])
  have hT : (ξ * T).re = 0 := by
    rw [hRe] at hi hj
    norm_num at hi hj
    linarith only [hi, hj]
  have hp := hpenalty z hz
  rw [hRe, hT, mul_zero] at hp
  exact Complex.normSq_eq_zero.mp
    (le_antisymm (by linarith only [hp]) (Complex.normSq_nonneg _))

end

end MOC
