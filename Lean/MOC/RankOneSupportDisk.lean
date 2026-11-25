import MOC.PhaseDiskSextic
import MOC.RankOneOrbitDeterminant

/-! The full quadratic support condition for a stationary rank-one phase
curve is the positive-semidefiniteness of a real two-by-two form. -/

open BigOperators Matrix

namespace MOC

noncomputable section

private theorem phase_quadratic_psd (a b c : ℝ) :
    (∀ u v : ℝ, 0 ≤ a * u ^ 2 + b * v ^ 2 - 2 * c * u * v) ↔
      0 ≤ a ∧ 0 ≤ b ∧ c ^ 2 ≤ a * b := by
  constructor
  · intro H
    have ha : 0 ≤ a := by simpa using H 1 0
    have hb : 0 ≤ b := by simpa using H 0 1
    refine ⟨ha, hb, ?_⟩
    rcases ha.eq_or_lt with hzero | hpos
    · have hc : c = 0 := by
        by_contra hc
        have ht := H (b + 1) c
        have hw := mul_pos (show 0 < b + 2 by linarith only [hb]) (sq_pos_of_ne_zero hc)
        rw [← hzero, zero_mul] at ht
        nlinarith only [ht, hw]
      simp [← hzero, hc]
    · have ht := H c a
      rw [show a * c ^ 2 + b * a ^ 2 - 2 * c * c * a =
        a * (a * b - c ^ 2) by ring] at ht
      exact sub_nonneg.mp (nonneg_of_mul_nonneg_right ht hpos)
  · rintro ⟨ha, hb, hc⟩ u v
    rcases ha.eq_or_lt with hzero | hpos
    · have hs : c ^ 2 ≤ 0 := by simpa only [← hzero, zero_mul] using hc
      have hcz : c = 0 := by
        by_contra hn
        exact (not_lt_of_ge hs) (sq_pos_of_ne_zero hn)
      simpa [← hzero, hcz] using mul_nonneg hb (sq_nonneg v)
    · have ht : 0 ≤ (a * u - c * v) ^ 2 + (a * b - c ^ 2) * v ^ 2 :=
        add_nonneg (sq_nonneg _) (mul_nonneg (sub_nonneg.mpr hc) (sq_nonneg _))
      rw [show (a * u - c * v) ^ 2 + (a * b - c ^ 2) * v ^ 2 =
        a * (a * u ^ 2 + b * v ^ 2 - 2 * c * u * v) by ring] at ht
      exact nonneg_of_mul_nonneg_right ht hpos

/-- For `Δ = yP + (1-x)R` with zero projected tangent, these three inequalities
are equivalent to quadratic support with penalty coefficient one. -/
theorem rankOnePhase_disk_iff (ξ P R : ℂ) (hP : (ξ * P).re = 0) :
    let L := -(ξ * R).re
    let a := L - 2 * Complex.normSq P
    let b := L - 2 * Complex.normSq R
    (∀ z : ℂ, Complex.normSq z = 1 →
      (ξ * rankTwoPhaseChange P R 0 0 z).re ≤ -Complex.normSq (rankTwoPhaseChange P R 0 0 z)) ↔
      0 ≤ a ∧ 0 ≤ b ∧ (2 * (P * star R).re) ^ 2 ≤ a * b := by
  intro L a b
  let c := 2 * (P * star R).re
  have hGram (u v : ℝ) :
      L * (u ^ 2 + v ^ 2) - 2 * Complex.normSq ((u : ℂ) * P + (v : ℂ) * R) =
        a * u ^ 2 + b * v ^ 2 - 2 * c * u * v := by
    simp [a, b, c, Complex.star_def, Complex.normSq_apply, Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.mul_im] <;> ring
  rw [← phase_quadratic_psd a b c]
  constructor
  · intro H u v
    let ν := ξ / 2
    have hscale (w : ℂ) : (ν * w).re = (ξ * w).re / 2 := by
      rw [show ν * w = ((1 / 2 : ℝ) : ℂ) * (ξ * w) by
        dsimp only [ν]
        push_cast
        ring]
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
      ring
    have hs := rankTwoPhase_disk_sextic_nonneg ν P R 0 0 (by rw [hscale, hP, zero_div])
      (fun z hz => by
        rw [hscale]
        linarith only [H z hz]) u v
    let d := u ^ 2 + v ^ 2
    have hfact : rankTwoPhaseDiskSextic ν P R 0 0 u v =
        (L * d - 2 * Complex.normSq ((u : ℂ) * P + (v : ℂ) * R)) * (d ^ 2 / 2) := by
      simp only [rankTwoPhaseDiskSextic, mul_zero, Complex.zero_re, add_zero]
      change -((ν * R).re * d) * d ^ 2 -
        Complex.normSq (((u : ℂ) * P + (v : ℂ) * R) * (d : ℂ)) = _
      rw [hscale, Complex.normSq_mul, Complex.normSq_ofReal]
      dsimp only [L]
      ring
    by_cases hd : d = 0
    · have hu : u = 0 := by
        by_contra hu
        exact (add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero hu) (sq_nonneg v)).ne' hd
      have hv : v = 0 := by
        by_contra hv
        exact (add_pos_of_nonneg_of_pos (sq_nonneg u) (sq_pos_of_ne_zero hv)).ne' hd
      simp [hu, hv]
    · have hpos : 0 < d := lt_of_le_of_ne (add_nonneg (sq_nonneg u) (sq_nonneg v)) (Ne.symm hd)
      rw [hfact, hGram u v] at hs
      exact nonneg_of_mul_nonneg_left hs (div_pos (pow_pos hpos 2) (by norm_num))
  · intro H z hz
    have hs := H z.im (1 - z.re)
    rw [← hGram] at hs
    have hnorm : z.im ^ 2 + (1 - z.re) ^ 2 = 2 * (1 - z.re) := by
      rw [Complex.normSq_apply] at hz
      nlinarith only [hz]
    rw [hnorm] at hs
    simp only [rankTwoPhaseChange, mul_zero, add_zero]
    have hproj : (ξ * ((z.im : ℂ) * P + ((1 - z.re : ℝ) : ℂ) * R)).re =
        -L * (1 - z.re) := by
      rw [mul_add, Complex.add_re, mul_left_comm ξ (z.im : ℂ),
        mul_left_comm ξ ((1 - z.re : ℝ) : ℂ)]
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at hP ⊢
      rw [show ξ.re * P.re - ξ.im * P.im = 0 from hP, mul_zero, zero_add]
      dsimp only [L]
      simp only [Complex.mul_re]
      ring
    rw [hproj]
    linarith only [hs]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Recover the first sine and cosine changes of a rank-one phase orbit
from four phase evaluations at a nonsingular base point. -/
theorem rankOnePhaseLeft_harmonics (A B : Matrix ι ι ℂ) (u : ι → ℂ)
    (hu : ∑ i, star (u i) * u i = 1) (hT : IsUnit (A - B).det) :
    let f (z : ℂ) := (rankOnePhase u z * A * (rankOnePhase u z)ᴴ - B).det
    let P := (f Complex.I - f (-Complex.I)) / 2
    let R := (f (-1) - f 1) / 2
    ∀ z : ℂ, Complex.normSq z = 1 →
      f z = f 1 + (z.im : ℂ) * P + ((1 - z.re : ℝ) : ℂ) * R := by
  intro f P R
  let T := A - B
  let C : Matrix ι Unit ℂ := fun i _ => u i
  let E := (Cᴴ * A * T⁻¹ * C) () () + (Cᴴ * T⁻¹ * (-(B * C))) () () - 1
  let F := (Cᴴ * A * T⁻¹ * C) () () * (Cᴴ * T⁻¹ * (-(B * C))) () () -
    (Cᴴ * A * T⁻¹ * (-(B * C))) () () * (Cᴴ * T⁻¹ * C) () ()
  let P' := T.det * (Complex.I * E)
  let R' := T.det * (E - 2 * F)
  have hf (z : ℂ) (hz : Complex.normSq z = 1) :
      f z = T.det + (z.im : ℂ) * P' + ((1 - z.re : ℝ) : ℂ) * R' := by
    have hu' : z * star z = 1 := by
      rw [Complex.star_def, Complex.mul_conj, hz, Complex.ofReal_one]
    have hdet : f z = T.det * (1 + (1 - star z) * E + (z + star z - 2) * F) :=
      det_rankOnePhase_left_conjugation A B u hu z hu' hT
    have h₁ : 1 - star z = ((1 - z.re : ℝ) : ℂ) + (z.im : ℂ) * Complex.I := by
      apply Complex.ext <;> simp [Complex.star_def]
    have h₂ : z + star z - 2 = -2 * ((1 - z.re : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [Complex.star_def] <;> ring
    rw [hdet, h₁, h₂]
    dsimp only [P', R']
    ring
  have hf₁ : f 1 = T.det := by simpa using hf 1 (by simp)
  have hPf : P = P' := by
    dsimp only [P]
    rw [hf Complex.I Complex.normSq_I, hf (-Complex.I) (by simp)]
    simp <;> ring
  have hRf : R = R' := by
    dsimp only [R]
    rw [hf (-1) (by simp), hf₁]
    simp <;> ring
  intro z hz
  rw [hf z hz, hf₁, hPf, hRf]

/-- The exact disk criterion for a rank-one conjugation orbit. -/
theorem rankOnePhaseLeft_disk_iff (A B : Matrix ι ι ℂ) (u : ι → ℂ)
    (hu : ∑ i, star (u i) * u i = 1) (hT : IsUnit (A - B).det) (ξ : ℂ) :
    let f (z : ℂ) := (rankOnePhase u z * A * (rankOnePhase u z)ᴴ - B).det
    let P := (f Complex.I - f (-Complex.I)) / 2
    let R := (f (-1) - f 1) / 2
    let L := -(ξ * R).re
    let a := L - 2 * Complex.normSq P
    let b := L - 2 * Complex.normSq R
    (ξ * P).re = 0 →
      ((∀ z : ℂ, Complex.normSq z = 1 → (ξ * (f z - f 1)).re ≤ -Complex.normSq (f z - f 1)) ↔
        0 ≤ a ∧ 0 ≤ b ∧ (2 * (P * star R).re) ^ 2 ≤ a * b) := by
  intro f P R L a b hP
  have hδ (z : ℂ) (hz : Complex.normSq z = 1) :
      f z - f 1 = rankTwoPhaseChange P R 0 0 z := by
    have hf : f z = f 1 + (z.im : ℂ) * P + ((1 - z.re : ℝ) : ℂ) * R :=
      rankOnePhaseLeft_harmonics A B u hu hT z hz
    rw [hf]
    simp only [rankTwoPhaseChange, mul_zero, add_zero]
    ring
  have hc :
      (∀ z : ℂ, Complex.normSq z = 1 → (ξ * (f z - f 1)).re ≤ -Complex.normSq (f z - f 1)) ↔
      (∀ z : ℂ, Complex.normSq z = 1 →
        (ξ * rankTwoPhaseChange P R 0 0 z).re ≤ -Complex.normSq (rankTwoPhaseChange P R 0 0 z)) := by
    constructor
    · intro hh z hz
      rw [← hδ z hz]
      exact hh z hz
    · intro hh z hz
      rw [hδ z hz]
      exact hh z hz
  exact hc.trans (rankOnePhase_disk_iff ξ P R hP)

end

end MOC
