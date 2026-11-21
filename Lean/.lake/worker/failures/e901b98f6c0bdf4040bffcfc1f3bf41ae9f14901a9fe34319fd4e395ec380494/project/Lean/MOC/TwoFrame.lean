import MOC.Core
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Complex.BigOperators
import Mathlib.Data.Matrix.Notation
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! Bloch coordinates and the real-axis projection in the two-frame matching theorem. -/

open BigOperators Matrix Finset

namespace MOC

noncomputable section

/-- The masses and directions of the rows of a two-column isometry. -/
structure BlochFrame (ρ : Type*) [Fintype ρ] where
  mass : ρ → ℝ
  direction : ρ → Fin 3 → ℝ
  mass_nonneg : ∀ i, 0 ≤ mass i
  sum_mass : ∑ i, mass i = 2
  direction_unit : ∀ i, ∑ k, direction i k ^ 2 = 1
  mean_zero : ∀ k, ∑ i, mass i * direction i k = 0

variable {ρ : Type*} [Fintype ρ]

/-- The squared wedge of two rows, expressed in their Bloch coordinates. -/
def blochWedge (p q : ℝ) (u v : Fin 3 → ℝ) : ℝ :=
  p * q * (1 - ∑ k, u k * v k) / 2

/-- Summing the within-frame wedge masses recovers the mass of the given row. -/
theorem BlochFrame.sum_blochWedge (E : BlochFrame ρ) (p : ℝ) (u : Fin 3 → ℝ) :
    ∑ i, blochWedge p (E.mass i) u (E.direction i) = p := by
  have hzero : (∑ i, E.mass i * ∑ k, u k * E.direction i k) = 0 := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    simp_rw [mul_left_comm (E.mass _), ← Finset.mul_sum, E.mean_zero, mul_zero, Finset.sum_const_zero]
  calc
    _ = p / 2 * ((∑ i, E.mass i) - ∑ i, E.mass i * ∑ k, u k * E.direction i k) := by
      rw [Finset.sum_sub_distrib.symm, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      unfold blochWedge
      ring
    _ = _ := by rw [E.sum_mass, hzero]; ring

theorem blochWedge_eq_distance (p q : ℝ) (u v : Fin 3 → ℝ)
    (hu : ∑ k, u k ^ 2 = 1) (hv : ∑ k, v k ^ 2 = 1) :
    blochWedge p q u v = p * q * (∑ k, (u k - v k) ^ 2) / 4 := by
  have h : (∑ k, (u k - v k) ^ 2) =
      (∑ k, u k ^ 2) + (∑ k, v k ^ 2) - 2 * ∑ k, u k * v k := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [blochWedge, h, hu, hv]
  ring

def rowMass (v : Fin 2 → ℂ) : ℝ := Complex.normSq (v 0) + Complex.normSq (v 1)

def rowBloch (v : Fin 2 → ℂ) : Fin 3 → ℝ :=
  ![2 * (v 0 * star (v 1)).re, 2 * (v 0 * star (v 1)).im,
    Complex.normSq (v 0) - Complex.normSq (v 1)]

def rowDirection (v : Fin 2 → ℂ) : Fin 3 → ℝ :=
  if rowMass v = 0 then ![1, 0, 0] else fun k => rowBloch v k / rowMass v

theorem rowBloch_norm_sq (v : Fin 2 → ℂ) :
    ∑ k, rowBloch v k ^ 2 = rowMass v ^ 2 := by
  simp [rowBloch, rowMass, Fin.sum_univ_three, Complex.normSq_apply, Complex.mul_re, Complex.mul_im,
    Complex.star_def]
  ring

theorem rowMass_nonneg (v : Fin 2 → ℂ) : 0 ≤ rowMass v :=
  add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)

theorem rowMass_eq_zero_iff (v : Fin 2 → ℂ) : rowMass v = 0 ↔ v = 0 := by
  constructor
  · intro h
    unfold rowMass at h
    have h0 : Complex.normSq (v 0) = 0 := by
      linarith [Complex.normSq_nonneg (v 0), Complex.normSq_nonneg (v 1)]
    have h1 : Complex.normSq (v 1) = 0 := by
      linarith [Complex.normSq_nonneg (v 0), Complex.normSq_nonneg (v 1)]
    ext i
    fin_cases i
    · exact Complex.normSq_eq_zero.mp h0
    · exact Complex.normSq_eq_zero.mp h1
  · rintro rfl
    simp [rowMass]

theorem rowDirection_norm_sq (v : Fin 2 → ℂ) :
    ∑ k, rowDirection v k ^ 2 = 1 := by
  by_cases h : rowMass v = 0
  · norm_num [rowDirection, h, Fin.sum_univ_three]
    rfl
  · simp only [rowDirection, if_neg h, div_pow, ← Finset.sum_div,
      rowBloch_norm_sq, div_self (pow_ne_zero _ h)]

theorem rowMass_mul_direction (v : Fin 2 → ℂ) (k : Fin 3) :
    rowMass v * rowDirection v k = rowBloch v k := by
  by_cases h : rowMass v = 0
  · rw [(rowMass_eq_zero_iff v).mp h]
    fin_cases k <;> simp [rowMass, rowBloch]
  · rw [rowDirection, if_neg h]
    field_simp

theorem normSq_wedge_eq_bloch (v w : Fin 2 → ℂ) :
    2 * Complex.normSq (v 0 * w 1 - v 1 * w 0) =
      rowMass v * rowMass w - ∑ k, rowBloch v k * rowBloch w k := by
  simp [rowBloch, rowMass, Fin.sum_univ_three, Complex.normSq_apply, Complex.mul_re, Complex.mul_im,
    Complex.star_def]
  ring

theorem normSq_wedge_eq_blochWedge (v w : Fin 2 → ℂ) :
    Complex.normSq (v 0 * w 1 - v 1 * w 0) =
      blochWedge (rowMass v) (rowMass w) (rowDirection v) (rowDirection w) := by
  have h :
      (∑ k, rowBloch v k * rowBloch w k) =
        rowMass v * rowMass w * ∑ k, rowDirection v k * rowDirection w k := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [← rowMass_mul_direction, ← rowMass_mul_direction]
    ring
  rw [blochWedge]
  linarith [normSq_wedge_eq_bloch v w, h]

private theorem sum_normSq_column_eq_one (E : Matrix ρ (Fin 2) ℂ) (hE : Eᴴ * E = 1)
    (j : Fin 2) : ∑ i, Complex.normSq (E i j) = 1 := by
  apply Complex.ofReal_injective
  have hj := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M j j) hE
  simpa only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply_eq, Complex.ofReal_sum,
    Complex.ofReal_one, Complex.normSq_eq_conj_mul_self] using hj

/-- Produce a Bloch frame directly from the columns of an isometry. -/
def BlochFrame.ofMatrix (E : Matrix ρ (Fin 2) ℂ) (hE : Eᴴ * E = 1) : BlochFrame ρ where
  mass i := rowMass (E i)
  direction i := rowDirection (E i)
  mass_nonneg i := rowMass_nonneg (E i)
  direction_unit i := rowDirection_norm_sq (E i)
  sum_mass := by
    norm_num [rowMass, Finset.sum_add_distrib, sum_normSq_column_eq_one E hE]
  mean_zero k := by
    have ho : ∑ i, E i 0 * star (E i 1) = 0 := by
      have hn : (1 : Fin 2) ≠ 0 := by decide
      have hj := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 1 0) hE
      simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply, hn, mul_comm]
        using hj
    have hr := congrArg Complex.re ho
    have hi := congrArg Complex.im ho
    rw [Complex.re_sum, Complex.zero_re] at hr
    rw [Complex.im_sum, Complex.zero_im] at hi
    simp_rw [rowMass_mul_direction]
    fin_cases k
    · change (∑ i, 2 * (E i 0 * star (E i 1)).re) = 0
      rw [← Finset.mul_sum, hr, mul_zero]
    · change (∑ i, 2 * (E i 0 * star (E i 1)).im) = 0
      rw [← Finset.mul_sum, hi, mul_zero]
    · simp [rowBloch, Finset.sum_sub_distrib, sum_normSq_column_eq_one E hE]

private def realDirection (x : ℝ) : Fin 3 → ℝ :=
  ![2 * x / (1 + x ^ 2), 0, (1 - x ^ 2) / (1 + x ^ 2)]

/-- Project one frame onto an axis, with the coordinates rescaled to have
weighted mean zero and weighted second moment two. -/
def BlochFrame.project (E : BlochFrame ρ) (x : ρ → ℝ)
    (hmean : ∑ i, E.mass i * x i = 0)
    (hvariance : ∑ i, E.mass i * x i ^ 2 = 2) : BlochFrame ρ where
  mass i := E.mass i * (1 + x i ^ 2) / 2
  direction i := realDirection (x i)
  mass_nonneg i := by
    have hi := E.mass_nonneg i
    positivity
  sum_mass := by
    rw [← Finset.sum_div]
    norm_num [mul_add, Finset.sum_add_distrib, E.sum_mass, hvariance]
  direction_unit i := by
    have hden : 0 < 1 + x i ^ 2 := by positivity
    simp [realDirection, Fin.sum_univ_three]
    field_simp
    ring
  mean_zero k := by
    have hden (i : ρ) : 0 < 1 + x i ^ 2 := by positivity
    have h0 (i : ρ) :
        E.mass i * (1 + x i ^ 2) / 2 * (2 * x i / (1 + x i ^ 2)) = E.mass i * x i := by
      field_simp [ne_of_gt (hden i)]
      ring
    have h2 (i : ρ) :
        E.mass i * (1 + x i ^ 2) / 2 * ((1 - x i ^ 2) / (1 + x i ^ 2)) =
          (E.mass i - E.mass i * x i ^ 2) / 2 := by
      field_simp [ne_of_gt (hden i)]
      ring
    fin_cases k
    · simp [realDirection, h0, hmean]
    · simp [realDirection]
    · simp [realDirection, h2, ← Finset.sum_div, Finset.sum_sub_distrib, E.sum_mass, hvariance]

/-- All squared wedges of two projected frames use the same squared-distance formula. -/
theorem BlochFrame.project_wedge {σ : Type*} [Fintype σ]
    (E : BlochFrame ρ) (F : BlochFrame σ) (x : ρ → ℝ) (y : σ → ℝ)
    (hx₀ : ∑ i, E.mass i * x i = 0) (hx₂ : ∑ i, E.mass i * x i ^ 2 = 2)
    (hy₀ : ∑ j, F.mass j * y j = 0) (hy₂ : ∑ j, F.mass j * y j ^ 2 = 2)
    (i : ρ) (j : σ) :
    blochWedge ((E.project x hx₀ hx₂).mass i) ((F.project y hy₀ hy₂).mass j)
      ((E.project x hx₀ hx₂).direction i) ((F.project y hy₀ hy₂).direction j) =
        E.mass i * F.mass j * (x i - y j) ^ 2 / 4 := by
  have hx : 0 < 1 + x i ^ 2 := by positivity
  have hy : 0 < 1 + y j ^ 2 := by positivity
  simp [BlochFrame.project, blochWedge, realDirection, Fin.sum_univ_three]
  field_simp
  ring

/-- At a mass-preserving projection, every row of positive mass lies on one
of the two opposite directions used in the matching construction. -/
theorem BlochFrame.project_eq_opposite_of_mass_eq (E : BlochFrame ρ) (x : ρ → ℝ)
    (hx₀ : ∑ i, E.mass i * x i = 0) (hx₂ : ∑ i, E.mass i * x i ^ 2 = 2)
    (i : ρ) (hi : 0 < E.mass i) (hproj : (E.project x hx₀ hx₂).mass i = E.mass i) :
    (E.project x hx₀ hx₂).direction i = ![1, 0, 0] ∨
      (E.project x hx₀ hx₂).direction i = ![-1, 0, 0] := by
  change E.mass i * (1 + x i ^ 2) / 2 = E.mass i at hproj
  have hm : E.mass i * (x i ^ 2 - 1) = 0 := by linarith
  have hs : x i ^ 2 = 1 := sub_eq_zero.mp ((mul_eq_zero.mp hm).resolve_left hi.ne')
  have hdiff : (x i - 1) * (x i + 1) = 0 := by nlinarith
  rcases mul_eq_zero.mp hdiff with hpos | hneg
  · left
    change realDirection (x i) = _
    rw [sub_eq_zero.mp hpos]
    ext k
    fin_cases k <;> norm_num [realDirection]
  · right
    change realDirection (x i) = _
    rw [eq_neg_of_add_eq_zero_left hneg]
    ext k
    fin_cases k <;> norm_num [realDirection]

def BlochFrame.axisCoord (E : BlochFrame ρ) (B : Matrix (Fin 3) (Fin 3) ℝ)
    (k : Fin 3) (i : ρ) : ℝ := (B *ᵥ E.direction i) k

def BlochFrame.axisVariance (E : BlochFrame ρ) (B : Matrix (Fin 3) (Fin 3) ℝ)
    (k : Fin 3) : ℝ := ∑ i, E.mass i * E.axisCoord B k i ^ 2

theorem BlochFrame.axisCoord_mean (E : BlochFrame ρ) (B : Matrix (Fin 3) (Fin 3) ℝ)
    (k : Fin 3) : ∑ i, E.mass i * E.axisCoord B k i = 0 := by
  simp only [axisCoord, Matrix.mulVec, dotProduct, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [mul_left_comm (E.mass _), ← Finset.mul_sum, E.mean_zero, mul_zero, Finset.sum_const_zero]

theorem BlochFrame.axisVariance_nonneg (E : BlochFrame ρ) (B : Matrix (Fin 3) (Fin 3) ℝ)
    (k : Fin 3) : 0 ≤ E.axisVariance B k :=
  Finset.sum_nonneg (fun i _ => mul_nonneg (E.mass_nonneg i) (sq_nonneg _))

private theorem sum_squares_mulVec (B : Matrix (Fin 3) (Fin 3) ℝ) (hB : Bᵀ * B = 1)
    (v : Fin 3 → ℝ) : ∑ k, (B *ᵥ v) k ^ 2 = ∑ k, v k ^ 2 := by
  simp only [pow_two]
  change (B *ᵥ v) ⬝ᵥ (B *ᵥ v) = v ⬝ᵥ v
  rw [dotProduct_mulVec, ← Matrix.vecMul_transpose B v, Matrix.vecMul_vecMul, hB,
    Matrix.vecMul_one]

theorem BlochFrame.sum_axisVariance (E : BlochFrame ρ) (B : Matrix (Fin 3) (Fin 3) ℝ)
    (hB : Bᵀ * B = 1) : ∑ k, E.axisVariance B k = 2 := by
  unfold axisVariance
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, axisCoord, sum_squares_mulVec B hB, E.direction_unit, mul_one]
  exact E.sum_mass

private def BlochFrame.axisScale (E : BlochFrame ρ) (B : Matrix (Fin 3) (Fin 3) ℝ)
    (k : Fin 3) : ℝ := Real.sqrt (2 / E.axisVariance B k)

def BlochFrame.projectAxis (E : BlochFrame ρ) (B : Matrix (Fin 3) (Fin 3) ℝ)
    (k : Fin 3) (hV : 0 < E.axisVariance B k) : BlochFrame ρ :=
  E.project (fun i => E.axisScale B k * E.axisCoord B k i)
    (by simp_rw [mul_left_comm (E.mass _), ← Finset.mul_sum, E.axisCoord_mean, mul_zero])
    (by
      simp_rw [mul_pow, mul_left_comm (E.mass _), ← Finset.mul_sum]
      change (E.axisScale B k) ^ 2 * E.axisVariance B k = 2
      rw [axisScale, Real.sq_sqrt (div_nonneg (by norm_num) hV.le),
        div_mul_cancel₀ _ hV.ne'])

/-- On a zero-variance axis the projected frame has no weight in the decomposition. -/
def BlochFrame.alongAxis (E : BlochFrame ρ) (B : Matrix (Fin 3) (Fin 3) ℝ)
    (k : Fin 3) : BlochFrame ρ :=
  if hV : 0 < E.axisVariance B k then E.projectAxis B k hV else E

private theorem axisCoord_eq_zero_of_variance_eq_zero
    (E : BlochFrame ρ) (B : Matrix (Fin 3) (Fin 3) ℝ) (k : Fin 3)
    (hV : E.axisVariance B k = 0) (i : ρ) (hi : E.mass i ≠ 0) :
    E.axisCoord B k i = 0 := by
  have hterm (j : ρ) : 0 ≤ E.mass j * E.axisCoord B k j ^ 2 :=
    mul_nonneg (E.mass_nonneg j) (sq_nonneg _)
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hterm j)).mp hV i (mem_univ i)
  exact (pow_eq_zero ((mul_eq_zero.mp hzero).resolve_left hi))

/-- If the two frames have equal moments on each orthonormal axis, their whole
profile is a convex average of projected profiles with the common weights (V_k/2). -/
theorem blochWedge_eq_average_axes {σ : Type*} [Fintype σ]
    (E : BlochFrame ρ) (F : BlochFrame σ) (B : Matrix (Fin 3) (Fin 3) ℝ)
    (hB : Bᵀ * B = 1) (hV : ∀ k, E.axisVariance B k = F.axisVariance B k)
    (i : ρ) (j : σ) :
    blochWedge (E.mass i) (F.mass j) (E.direction i) (F.direction j) =
      ∑ k, E.axisVariance B k / 2 *
        blochWedge ((E.alongAxis B k).mass i) ((F.alongAxis B k).mass j)
          ((E.alongAxis B k).direction i) ((F.alongAxis B k).direction j) := by
  have hdist := sum_squares_mulVec B hB (E.direction i - F.direction j)
  simp only [Matrix.mulVec_sub, Pi.sub_apply] at hdist
  change (∑ k, (E.axisCoord B k i - F.axisCoord B k j) ^ 2) =
    ∑ k, (E.direction i k - F.direction j k) ^ 2 at hdist
  rw [blochWedge_eq_distance _ _ _ _ (E.direction_unit i) (F.direction_unit j), ← hdist]
  rw [Finset.mul_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hv : 0 < E.axisVariance B k
  · have hv' := (hV k) ▸ hv
    have hscale : F.axisScale B k = E.axisScale B k := by simp [BlochFrame.axisScale, hV k]
    simp only [BlochFrame.alongAxis, dif_pos hv, dif_pos hv', BlochFrame.projectAxis,
      BlochFrame.project_wedge, hscale, ← mul_sub, mul_pow]
    rw [BlochFrame.axisScale, Real.sq_sqrt (div_nonneg (by norm_num) hv.le)]
    field_simp [hv.ne']
  · have hz : E.axisVariance B k = 0 :=
      le_antisymm (le_of_not_gt hv) (E.axisVariance_nonneg B k)
    rw [hz, zero_div, zero_mul]
    by_cases hi : E.mass i = 0
    · simp [hi]
    by_cases hj : F.mass j = 0
    · simp [hj]
    have hE := axisCoord_eq_zero_of_variance_eq_zero E B k hz i hi
    have hF := axisCoord_eq_zero_of_variance_eq_zero F B k ((hV k).symm ▸ hz) j hj
    simp [hE, hF]

end

end MOC
