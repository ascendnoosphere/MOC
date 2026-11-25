import MOC.RankOneOrbitDeterminant
import MOC.Variational
import Mathlib.Tactic.Positivity

/-! Secondary optimization along a support line is compatible with a fixed
support direction and therefore retains its matching contacts. -/

open BigOperators Matrix

namespace MOC

private theorem unit_circle_linear_tangent_eq_zero (a b : ℝ)
    (h : ∀ z : ℂ, Complex.normSq z = 1 → a * z.im + b * (1 - z.re) ≤ 0) :
    a = 0 := by
  by_contra ha
  let d := b ^ 2 + 1
  let D := d ^ 2 + a ^ 2
  have hD : 0 < D := add_pos_of_nonneg_of_pos (sq_nonneg d) (sq_pos_of_ne_zero ha)
  let z : ℂ := ⟨(d ^ 2 - a ^ 2) / D, (2 * d * a) / D⟩
  have hz : Complex.normSq z = 1 := by
    rw [Complex.normSq_apply]
    change ((d ^ 2 - a ^ 2) / D) * ((d ^ 2 - a ^ 2) / D) +
      ((2 * d * a) / D) * ((2 * d * a) / D) = 1
    field_simp [hD.ne'] <;> dsimp only [D] <;> ring
  have he : a * z.im + b * (1 - z.re) = 2 * a ^ 2 * (d + b) / D := by
    change a * ((2 * d * a) / D) + b * (1 - (d ^ 2 - a ^ 2) / D) = _
    field_simp [hD.ne'] <;> dsimp only [D] <;> ring
  have hb : 0 < d + b := by
    dsimp only [d]
    nlinarith only [sq_nonneg (b + 1 / 2)]
  have hp : 0 < 2 * a ^ 2 * (d + b) / D :=
    div_pos (mul_pos (mul_pos (by norm_num) (sq_pos_of_ne_zero ha)) hb) hD
  exact hp.not_le (he ▸ h z hz)

/-- A flat rank-one support direction has zero complex tangent after
maximizing the tangential projection among points tied in real support. -/
theorem first_harmonic_tangent_eq_zero_of_lexicographic_maximum
    (η P R : ℂ) (hη : η ≠ 0) (hflat : (η * R).re = 0) :
    let w (z : ℂ) := (z.im : ℂ) * P + ((1 - z.re : ℝ) : ℂ) * R
    (∀ z, Complex.normSq z = 1 → (η * w z).re ≤ 0) →
    (∀ z, Complex.normSq z = 1 → (η * w z).re = 0 → (η * w z).im ≤ 0) → P = 0 := by
  intro w hmax htie
  have hr (z : ℂ) : (η * w z).re = z.im * (η * P).re + (1 - z.re) * (η * R).re := by
    dsimp only [w]
    rw [mul_add, Complex.add_re, mul_left_comm η (z.im : ℂ) P,
      mul_left_comm η ((1 - z.re : ℝ) : ℂ) R, Complex.re_ofReal_mul, Complex.re_ofReal_mul]
  have hi (z : ℂ) : (η * w z).im = z.im * (η * P).im + (1 - z.re) * (η * R).im := by
    dsimp only [w]
    rw [mul_add, Complex.add_im, mul_left_comm η (z.im : ℂ) P,
      mul_left_comm η ((1 - z.re : ℝ) : ℂ) R, Complex.im_ofReal_mul, Complex.im_ofReal_mul]
  have hpos := hmax Complex.I Complex.normSq_I
  have hneg := hmax (-Complex.I) (by simp)
  rw [hr, hflat] at hpos hneg
  have hpr : (η * P).re = 0 := by
    simp only [Complex.neg_im, Complex.I_im, one_mul, neg_mul, mul_zero, add_zero] at hpos hneg
    linarith only [hpos, hneg]
  have hpi : (η * P).im = 0 := by
    apply unit_circle_linear_tangent_eq_zero (η * P).im (η * R).im
    intro z hz
    have hz' : (η * w z).re = 0 := by simp only [hr, hpr, hflat, mul_zero, add_zero]
    have ht := htie z hz hz'
    rw [hi] at ht
    simpa only [mul_comm ((η * P).im) z.im, mul_comm ((η * R).im) (1 - z.re)] using ht
  have hzero : η * P = 0 := Complex.ext hpr hpi
  exact (mul_eq_zero.mp hzero).resolve_left hη

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The original support direction can be kept while maximizing its
tangential determinant projection on the exposed part of the orbit. -/
theorem exists_support_tangent_maximizer (a b : ι → ℂ) (η : ℂ) :
    ∃ U : Matrix ι ι ℂ, IsUnitary U ∧
      (∀ V : Matrix ι ι ℂ, IsUnitary V →
        (η * determinantValue a b V).re ≤ (η * determinantValue a b U).re) ∧
      ∀ V : Matrix ι ι ℂ, IsUnitary V →
        (η * determinantValue a b V).re = (η * determinantValue a b U).re →
        (η * determinantValue a b V).im ≤ (η * determinantValue a b U).im := by
  obtain ⟨W, hW, hmax⟩ := exists_support_maximizer a b η
  let f (V : Matrix ι ι ℂ) := (η * determinantValue a b V).re
  let g (V : Matrix ι ι ℂ) := (η * determinantValue a b V).im
  let K : Set (Matrix ι ι ℂ) := {V | IsUnitary V} ∩ {V | f V = f W}
  have hf : Continuous f := by unfold f determinantValue; fun_prop
  have hg : Continuous g := by unfold g determinantValue; fun_prop
  have hK : IsCompact K := isCompact_setOf_isUnitary.inter_right (isClosed_eq hf continuous_const)
  obtain ⟨U, hU, hG⟩ := hK.exists_isMaxOn ⟨W, hW, rfl⟩ hg.continuousOn
  refine ⟨U, hU.1, ?_, fun V hV he => hG ⟨hV, he.trans hU.2⟩⟩
  intro V hV
  change f V ≤ f U
  rw [hU.2]
  exact hmax V hV

/-- On a rank-one conjugation fiber a tied reflection at a lexicographic
support maximum forces the two quarter-turn determinants to agree. -/
theorem rankOnePhase_quarter_turn_eq_of_lexicographic_maximum
    (A B : Matrix ι ι ℂ) (u : ι → ℂ) (hu : ∑ i, star (u i) * u i = 1)
    (hT : IsUnit (A - B).det) (η : ℂ) (hη : η ≠ 0) :
    let f (z : ℂ) := (rankOnePhase u z * A * (rankOnePhase u z)ᴴ - B).det
    (∀ z, Complex.normSq z = 1 → (η * (f z - f 1)).re ≤ 0) →
    (η * (f (-1) - f 1)).re = 0 →
    (∀ z, Complex.normSq z = 1 → (η * (f z - f 1)).re = 0 →
      (η * (f z - f 1)).im ≤ 0) →
    f Complex.I = f (-Complex.I) := by
  intro f hmax hreflection htie
  let T := A - B
  let C : Matrix ι Unit ℂ := fun i _ => u i
  let α := (Cᴴ * A * T⁻¹ * C) () ()
  let β := (Cᴴ * T⁻¹ * (-(B * C))) () ()
  let E := α + β - 1
  let F := α * β - (Cᴴ * A * T⁻¹ * (-(B * C))) () () * (Cᴴ * T⁻¹ * C) () ()
  let P := T.det * (Complex.I * E)
  let R := T.det * (E - 2 * F)
  have hf (z : ℂ) (hz : Complex.normSq z = 1) :
      f z = T.det + (z.im : ℂ) * P + ((1 - z.re : ℝ) : ℂ) * R := by
    have hu' : z * star z = 1 := by rw [Complex.star_def, Complex.mul_conj, hz, Complex.ofReal_one]
    have hdet : f z = T.det * (1 + (1 - star z) * E + (z + star z - 2) * F) :=
      det_rankOnePhase_left_conjugation A B u hu z hu' hT
    have h₁ : 1 - star z = ((1 - z.re : ℝ) : ℂ) + (z.im : ℂ) * Complex.I := by
      apply Complex.ext <;> simp [Complex.star_def]
    have h₂ : z + star z - 2 = -2 * ((1 - z.re : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [Complex.star_def] <;> ring
    rw [hdet, h₁, h₂]
    dsimp only [P, R]
    ring
  have hf₁ : f 1 = T.det := by simpa using hf 1 (by simp)
  have hd (z : ℂ) (hz : Complex.normSq z = 1) : f z - f 1 =
      (z.im : ℂ) * P + ((1 - z.re : ℝ) : ℂ) * R := by rw [hf z hz, hf₁]; ring
  have h2R : f (-1) - f 1 = (2 : ℂ) * R := by
    rw [hd (-1) (by simp)]
    norm_num [Complex.ofReal_add]
  rw [h2R, show η * ((2 : ℂ) * R) = ((2 : ℝ) : ℂ) * (η * R) by push_cast; ring,
    Complex.re_ofReal_mul] at hreflection
  have hflat : (η * R).re = 0 := by linarith only [hreflection]
  have hP : P = 0 := first_harmonic_tangent_eq_zero_of_lexicographic_maximum η P R hη hflat
    (fun z hz => by
      change (η * ((z.im : ℂ) * P + ((1 - z.re : ℝ) : ℂ) * R)).re ≤ 0
      rw [← hd z hz]
      exact hmax z hz)
    (fun z hz => by
      change (η * ((z.im : ℂ) * P + ((1 - z.re : ℝ) : ℂ) * R)).re = 0 →
        (η * ((z.im : ℂ) * P + ((1 - z.re : ℝ) : ℂ) * R)).im ≤ 0
      rw [← hd z hz]
      exact htie z hz)
  rw [hf Complex.I Complex.normSq_I, hf (-Complex.I) (by simp), hP]
  simp

/-- The quarter-turn criterion on the ordinary determinant orbit. The
matching support direction is the same `η` in both maximizations. -/
theorem determinantValue_rankOne_quarter_turn_eq_of_support_tangent_maximum
    (a b : ι → ℂ) (U : Matrix ι ι ℂ) (hU : IsUnitary U)
    (hdet : IsUnit (determinantValue a b U)) (η : ℂ) (hη : η ≠ 0)
    (hmax : ∀ V : Matrix ι ι ℂ, IsUnitary V →
      (η * determinantValue a b V).re ≤ (η * determinantValue a b U).re)
    (htie : ∀ V : Matrix ι ι ℂ, IsUnitary V →
      (η * determinantValue a b V).re = (η * determinantValue a b U).re →
      (η * determinantValue a b V).im ≤ (η * determinantValue a b U).im)
    (u : ι → ℂ) (hu : ∑ i, star (u i) * u i = 1)
    (hflat : (η * determinantValue a b (rankOnePhase u (-1) * U)).re =
      (η * determinantValue a b U).re) :
    determinantValue a b (rankOnePhase u Complex.I * U) =
      determinantValue a b (rankOnePhase u (-Complex.I) * U) := by
  let A := U * diagonal b * Uᴴ
  let B := -(diagonal a)
  let V (z : ℂ) := rankOnePhase u z
  let f (z : ℂ) := (V z * A * (V z)ᴴ - B).det
  have hf (z : ℂ) : f z = determinantValue a b (V z * U) := by
    dsimp only [f, A, B, determinantValue]
    rw [Matrix.conjTranspose_mul, sub_neg_eq_add]
    simp only [Matrix.mul_assoc]
    rw [add_comm]
  have hf₁ : f 1 = determinantValue a b U := by
    rw [hf]
    simp [V, rankOnePhase]
  have hT : IsUnit (A - B).det := by
    change IsUnit ((A - B).det)
    dsimp only [A, B]
    rw [sub_neg_eq_add, add_comm]
    exact hdet
  have hunit (z : ℂ) (hz : Complex.normSq z = 1) : IsUnitary (V z * U) := by
    have hz' : z * star z = 1 := by rw [Complex.star_def, Complex.mul_conj, hz, Complex.ofReal_one]
    obtain ⟨hL, hR⟩ := rankOnePhase_unitary u z hu hz'
    change V z * (V z)ᴴ = 1 at hL
    change (V z)ᴴ * V z = 1 at hR
    constructor
    · rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc U Uᴴ,
        hU.1, Matrix.one_mul, hL]
    · rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (V z)ᴴ (V z),
        hR, Matrix.one_mul, hU.2]
  change determinantValue a b (V Complex.I * U) = determinantValue a b (V (-Complex.I) * U)
  rw [← hf Complex.I, ← hf (-Complex.I)]
  apply rankOnePhase_quarter_turn_eq_of_lexicographic_maximum A B u hu hT η hη
  · intro z hz
    change (η * (f z - f 1)).re ≤ 0
    rw [hf₁, hf, mul_sub, Complex.sub_re]
    exact sub_nonpos.mpr (hmax _ (hunit z hz))
  · change (η * (f (-1) - f 1)).re = 0
    rw [hf₁, hf, mul_sub, Complex.sub_re, sub_eq_zero]
    exact hflat
  · intro z hz hz'
    change (η * (f z - f 1)).im ≤ 0
    change (η * (f z - f 1)).re = 0 at hz'
    rw [hf₁, hf, mul_sub, Complex.sub_re, sub_eq_zero] at hz'
    rw [hf₁, hf, mul_sub, Complex.sub_im]
    exact sub_nonpos.mpr (htie _ (hunit z hz) hz')

end MOC
