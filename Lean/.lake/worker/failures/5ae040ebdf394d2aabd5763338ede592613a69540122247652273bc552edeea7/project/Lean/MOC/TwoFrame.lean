import MOC.Core
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.NormedSpace.HahnBanach.Separation
import Mathlib.Data.Complex.BigOperators
import Mathlib.Data.Matrix.Notation
import Mathlib.Data.Real.Sqrt
import Mathlib.LinearAlgebra.Matrix.Spectrum
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Order.Compact

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
    ring
  · have hz : E.axisVariance B k = 0 :=
      le_antisymm (le_of_not_gt hv) (E.axisVariance_nonneg B k)
    rw [hz, zero_div, zero_mul]
    by_cases hi : E.mass i = 0
    · simp [hi]
    by_cases hj : F.mass j = 0
    · simp [hj]
    have hE := axisCoord_eq_zero_of_variance_eq_zero E B k hz i hi
    have hF := axisCoord_eq_zero_of_variance_eq_zero F B k ((hV k).symm.trans hz) j hj
    simp [hE, hF]

private theorem exists_perm_two {p q : Fin 3} (hpq : p ≠ q) :
    ∃ σ : Equiv.Perm (Fin 3), σ 0 = p ∧ σ 1 = q := by
  let f := Equiv.swap (0 : Fin 3) p
  let g := Equiv.swap (f 1) q
  have hf : f 0 = p := Equiv.swap_apply_left _ _
  have hpf : p ≠ f 1 := by
    intro h
    have he := f.injective (hf.trans h)
    exact (by decide : (0 : Fin 3) ≠ 1) he
  refine ⟨f.trans g, ?_, ?_⟩
  · change g (f 0) = p
    rw [hf]
    exact Equiv.swap_apply_of_ne_of_ne hpf hpq
  · exact Equiv.swap_apply_left _ _

private theorem flat_diagonal_of_opposite (eig : Fin 3 → ℝ)
    (hpos : 0 < eig 0) (hneg : eig 1 < 0) (htrace : ∑ i, eig i = 0) :
    ∃ R : Matrix (Fin 3) (Fin 3) ℝ,
      Rᵀ * R = 1 ∧ ∀ i, (R * diagonal eig * Rᵀ) i i = 0 := by
  let d := eig 0 - eig 1
  have hd : 0 < d := sub_pos.mpr (lt_trans hneg hpos)
  let a := Real.sqrt (-eig 1 / d)
  let b := Real.sqrt (eig 0 / d)
  let c := Real.sqrt (1 / 2)
  have ha : a ^ 2 = -eig 1 / d := Real.sq_sqrt (div_nonneg (neg_nonneg.mpr hneg.le) hd.le)
  have hb : b ^ 2 = eig 0 / d := Real.sq_sqrt (div_nonneg hpos.le hd.le)
  have hc : c ^ 2 = (1 : ℝ) / 2 := Real.sq_sqrt (by norm_num)
  have hab : a ^ 2 + b ^ 2 = 1 := by
    rw [ha, hb, ← add_div, ← div_self hd.ne']
    congr 1
    dsimp only [d]
    ring
  have ht : a ^ 2 * eig 0 + b ^ 2 * eig 1 = 0 := by
    rw [ha, hb]
    field_simp [hd.ne']
    ring
  have hs : b ^ 2 * eig 0 + a ^ 2 * eig 1 + eig 2 = 0 := by
    calc
      _ = (a ^ 2 + b ^ 2) * (eig 0 + eig 1) + eig 2 - (a ^ 2 * eig 0 + b ^ 2 * eig 1) := by ring
      _ = _ := by simpa [hab, ht, Fin.sum_univ_three] using htrace
  let R : Matrix (Fin 3) (Fin 3) ℝ := !![a, b, 0; -c * b, c * a, c; c * b, -c * a, c]
  have hRR : R * Rᵀ = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [R, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, Fin.sum_univ_three,
        Matrix.cons_val']
    all_goals first
      | ring1
      | linear_combination hab
      | linear_combination c ^ 2 * hab + 2 * hc
      | linear_combination -(c ^ 2) * hab
  refine ⟨R, Matrix.mul_eq_one_comm.mp hRR, ?_⟩
  intro i
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply]
  fin_cases i <;> simp [R, Fin.sum_univ_three, Matrix.cons_val']
  all_goals first | linear_combination ht | linear_combination c ^ 2 * hs

/-- Every real symmetric traceless three-by-three matrix has zero diagonal
in some orthonormal coordinates. -/
theorem exists_flat_diagonal (H : Matrix (Fin 3) (Fin 3) ℝ)
    (hH : H.IsHermitian) (htrace : H.trace = 0) :
    ∃ B : Matrix (Fin 3) (Fin 3) ℝ,
      Bᵀ * B = 1 ∧ ∀ i, (B * H * Bᵀ) i i = 0 := by
  classical
  let eig := hH.eigenvalues
  let U : Matrix (Fin 3) (Fin 3) ℝ := hH.eigenvectorUnitary
  have hU : Uᵀ * U = 1 := by
    simpa only [U, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
      using unitary.coe_star_mul_self hH.eigenvectorUnitary
  have hHdiag : H = U * diagonal eig * Uᵀ := by
    simpa only [U, eig, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial,
      RCLike.ofReal_real_eq_id, Function.id_comp] using hH.spectral_theorem
  have heig : ∑ i, eig i = 0 := by
    rw [hHdiag, Matrix.trace_mul_cycle, hU, Matrix.one_mul, Matrix.trace_diagonal] at htrace
    exact htrace
  by_cases hz : ∀ i, eig i = 0
  · refine ⟨1, by simp, ?_⟩
    intro i
    have hzero : eig = 0 := funext hz
    have hdz : diagonal (0 : Fin 3 → ℝ) = 0 := Matrix.diagonal_zero
    simp [hHdiag, hzero, hdz]
  have hplus : ∃ i, 0 < eig i := by
    by_contra! hh
    have hsum : ∑ i, -eig i = 0 := by rw [Finset.sum_neg_distrib, heig, neg_zero]
    have hzero := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => neg_nonneg.mpr (hh i))).mp hsum
    exact hz (fun i => neg_eq_zero.mp (hzero i (mem_univ i)))
  have hminus : ∃ i, eig i < 0 := by
    by_contra! hh
    have hzero := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hh i)).mp heig
    exact hz (fun i => hzero i (mem_univ i))
  obtain ⟨p, hp⟩ := hplus
  obtain ⟨q, hq⟩ := hminus
  have hpq : p ≠ q := by intro he; rw [he] at hp; exact (lt_asymm hp hq)
  obtain ⟨σ, hσ₀, hσ₁⟩ := exists_perm_two hpq
  let μ := eig ∘ σ
  have hμ : ∑ i, μ i = 0 := by dsimp only [μ, Function.comp_apply]; rw [Equiv.sum_comp, heig]
  obtain ⟨R, hR, hRzero⟩ := flat_diagonal_of_opposite μ
    (by change 0 < eig (σ 0); rwa [hσ₀]) (by change eig (σ 1) < 0; rwa [hσ₁]) hμ
  let V := U.submatrix id σ
  have hVV : Vᵀ * V = 1 := by
    dsimp only [V]
    rw [Matrix.transpose_submatrix, ← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id,
      hU, Matrix.submatrix_one σ σ.injective]
  have hVdiag : V * diagonal μ * Vᵀ = H := by
    rw [hHdiag]
    dsimp only [V, μ]
    rw [Matrix.transpose_submatrix, ← Matrix.submatrix_diagonal _ σ σ.injective,
      ← Matrix.submatrix_mul _ _ _ _ _ σ.bijective,
      ← Matrix.submatrix_mul _ _ _ _ _ σ.bijective, Matrix.submatrix_id_id]
  let B := R * Vᵀ
  have hBt : Bᵀ = V * Rᵀ := by simp [B, Matrix.transpose_mul]
  refine ⟨B, ?_, ?_⟩
  · rw [hBt]
    change (V * Rᵀ) * (R * Vᵀ) = 1
    have hprod : (V * Rᵀ) * (R * Vᵀ) = V * (Rᵀ * R) * Vᵀ := by
      simp only [Matrix.mul_assoc]
    rw [hprod, hR, Matrix.mul_one, Matrix.mul_eq_one_comm.mp hVV]
  · intro i
    rw [hBt, ← hVdiag]
    change ((R * Vᵀ) * (V * diagonal μ * Vᵀ) * (V * Rᵀ)) i i = 0
    have hprod : (R * Vᵀ) * (V * diagonal μ * Vᵀ) * (V * Rᵀ) =
        R * (Vᵀ * V) * diagonal μ * (Vᵀ * V) * Rᵀ := by simp only [Matrix.mul_assoc]
    rw [hprod, hVV, Matrix.mul_one, Matrix.mul_one]
    exact hRzero i

private def BlochFrame.covariance (E : BlochFrame ρ) : Matrix (Fin 3) (Fin 3) ℝ :=
  ∑ i, E.mass i • Matrix.vecMulVec (E.direction i) (E.direction i)

private theorem BlochFrame.covariance_hermitian (E : BlochFrame ρ) : E.covariance.IsHermitian := by
  change E.covarianceᴴ = E.covariance
  rw [Matrix.conjTranspose_eq_transpose_of_trivial]
  ext k l
  simp only [Matrix.transpose_apply, covariance, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.vecMulVec_apply]
  apply Finset.sum_congr rfl
  intro i _
  ring

private theorem BlochFrame.trace_covariance (E : BlochFrame ρ) : E.covariance.trace = 2 := by
  have hdiag (i : ρ) : (Matrix.vecMulVec (E.direction i) (E.direction i)).trace = 1 := by
    simpa [Matrix.trace, Matrix.vecMulVec_apply, pow_two] using E.direction_unit i
  simp [covariance, Matrix.trace_sum, Matrix.trace_smul, hdiag, E.sum_mass]

private theorem outer_conj_diagonal (B : Matrix (Fin 3) (Fin 3) ℝ) (v : Fin 3 → ℝ) (k : Fin 3) :
    (B * Matrix.vecMulVec v v * Bᵀ) k k = (B *ᵥ v) k ^ 2 := by
  have hv (j : Fin 3) : (B * Matrix.vecMulVec v v) k j = (B *ᵥ v) k * v j := by
    simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.mulVec, dotProduct,
      Finset.sum_mul, mul_assoc]
  rw [Matrix.mul_apply]
  simp only [hv, Matrix.transpose_apply, pow_two, mul_assoc, ← Finset.mul_sum]
  congr 1
  simp only [Matrix.mulVec, dotProduct]
  apply Finset.sum_congr rfl
  intro j _
  exact mul_comm _ _

private theorem BlochFrame.axisVariance_eq_covariance (E : BlochFrame ρ)
    (B : Matrix (Fin 3) (Fin 3) ℝ) (k : Fin 3) :
    (B * E.covariance * Bᵀ) k k = E.axisVariance B k := by
  simp only [covariance, Matrix.mul_sum, Matrix.sum_mul, Matrix.sum_apply, Matrix.mul_smul,
    Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul, outer_conj_diagonal, axisVariance, axisCoord]

/-- Two Bloch frames admit common orthonormal axes with equal weighted second moments. -/
theorem equal_axisVariance_exists {σ : Type*} [Fintype σ]
    (E : BlochFrame ρ) (F : BlochFrame σ) :
    ∃ B : Matrix (Fin 3) (Fin 3) ℝ,
      Bᵀ * B = 1 ∧ ∀ k, E.axisVariance B k = F.axisVariance B k := by
  let H := E.covariance - F.covariance
  have hh : H.IsHermitian := E.covariance_hermitian.sub F.covariance_hermitian
  have ht : H.trace = 0 := by
    simp [H, Matrix.trace_sub, E.trace_covariance, F.trace_covariance]
  obtain ⟨B, hB, hdiag⟩ := exists_flat_diagonal H hh ht
  refine ⟨B, hB, ?_⟩
  intro k
  have hz := hdiag k
  simp only [H, Matrix.mul_sub, Matrix.sub_mul, Matrix.sub_apply,
    E.axisVariance_eq_covariance, F.axisVariance_eq_covariance] at hz
  exact sub_eq_zero.mp hz

private abbrev RawBlochFrame (ρ : Type*) := (ρ → ℝ) × (ρ → Fin 3 → ℝ)

private def RawBlochFrame.Valid (x : RawBlochFrame ρ) : Prop :=
  (∀ i, 0 ≤ x.1 i) ∧ (∑ i, x.1 i = 2) ∧
  (∀ i, ∑ k, x.2 i k ^ 2 = 1) ∧ (∀ k, ∑ i, x.1 i * x.2 i k = 0)

private def BlochFrame.raw (E : BlochFrame ρ) : RawBlochFrame ρ := (E.mass, E.direction)

private theorem BlochFrame.raw_valid (E : BlochFrame ρ) : RawBlochFrame.Valid E.raw :=
  ⟨E.mass_nonneg, E.sum_mass, E.direction_unit, E.mean_zero⟩

private def RawBlochFrame.toFrame (x : RawBlochFrame ρ) (hx : x.Valid) : BlochFrame ρ :=
  ⟨x.1, x.2, hx.1, hx.2.1, hx.2.2.1, hx.2.2.2⟩

private theorem isCompact_blochData : IsCompact {x : RawBlochFrame ρ | x.Valid} := by
  let P : Set (ρ → ℝ) := Set.pi Set.univ fun _ => Set.Icc 0 2
  let Q : Set (ρ → Fin 3 → ℝ) := Set.pi Set.univ fun _ =>
    Set.pi Set.univ fun _ => Set.Icc (-1) 1
  have hP : IsCompact P := isCompact_univ_pi (fun _ => isCompact_Icc)
  have hQ : IsCompact Q := isCompact_univ_pi (fun _ => isCompact_univ_pi (fun _ => isCompact_Icc))
  refine (hP.prod hQ).of_isClosed_subset ?_ ?_
  · have hnn : IsClosed {x : RawBlochFrame ρ | ∀ i, 0 ≤ x.1 i} := by
      rw [Set.setOf_forall]
      exact isClosed_iInter fun i => isClosed_le continuous_const (by fun_prop)
    have hm : IsClosed {x : RawBlochFrame ρ | ∑ i, x.1 i = 2} :=
      isClosed_eq (by fun_prop) continuous_const
    have hunit : IsClosed {x : RawBlochFrame ρ | ∀ i, ∑ k, x.2 i k ^ 2 = 1} := by
      rw [Set.setOf_forall]
      exact isClosed_iInter fun i => isClosed_eq (by fun_prop) continuous_const
    have hmean : IsClosed {x : RawBlochFrame ρ | ∀ k, ∑ i, x.1 i * x.2 i k = 0} := by
      rw [Set.setOf_forall]
      exact isClosed_iInter fun k => isClosed_eq (by fun_prop) continuous_const
    exact hnn.inter (hm.inter (hunit.inter hmean))
  · rintro x ⟨hnn, hm, hunit, _⟩
    refine ⟨fun i _ => ⟨hnn i, ?_⟩, fun i _ k _ => ?_⟩
    · have hi := Finset.single_le_sum (f := x.1) (fun j _ => hnn j) (mem_univ i)
      exact hi.trans_eq hm
    · have hk := Finset.single_le_sum (f := fun k => x.2 i k ^ 2)
          (fun k _ => sq_nonneg (x.2 i k)) (mem_univ k)
      have hs : x.2 i k ^ 2 ≤ 1 := hk.trans_eq (hunit i)
      exact abs_le_of_sq_le_sq' (by simpa only [one_pow] using hs) zero_le_one

/-! The profile includes all within-frame and cross-frame squared wedges. -/

abbrev TwoFrameProfile (ρ σ : Type*) := ((ρ ⊕ σ) × (ρ ⊕ σ)) → ℝ

variable {σ : Type*} [Fintype σ]

private def rawPairProfile (x : RawBlochFrame ρ × RawBlochFrame σ) : TwoFrameProfile ρ σ :=
  fun ij => blochWedge (Sum.elim x.1.1 x.2.1 ij.1) (Sum.elim x.1.1 x.2.1 ij.2)
    (Sum.elim x.1.2 x.2.2 ij.1) (Sum.elim x.1.2 x.2.2 ij.2)

def twoFrameProfile (E : BlochFrame ρ) (F : BlochFrame σ) : TwoFrameProfile ρ σ :=
  rawPairProfile (E.raw, F.raw)

omit [Fintype ρ] [Fintype σ] in
private theorem rawPairProfile_continuous :
    Continuous (rawPairProfile : RawBlochFrame ρ × RawBlochFrame σ → TwoFrameProfile ρ σ) := by
  apply continuous_pi
  rintro ⟨i, j⟩
  cases i <;> cases j <;> simp only [rawPairProfile, blochWedge, Sum.elim_inl, Sum.elim_inr] <;> fun_prop

private def twoFrameProfiles (ρ σ : Type*) [Fintype ρ] [Fintype σ] : Set (TwoFrameProfile ρ σ) :=
  Set.range (fun EF : BlochFrame ρ × BlochFrame σ => twoFrameProfile EF.1 EF.2)

private theorem isCompact_twoFrameProfiles : IsCompact (twoFrameProfiles ρ σ) := by
  have hd := (isCompact_blochData (ρ := ρ)).prod (isCompact_blochData (ρ := σ))
  have he : twoFrameProfiles ρ σ = rawPairProfile ''
        ({x : RawBlochFrame ρ | x.Valid} ×ˢ {y : RawBlochFrame σ | y.Valid}) := by
    ext p
    constructor
    · rintro ⟨⟨E, F⟩, rfl⟩
      exact ⟨(E.raw, F.raw), ⟨E.raw_valid, F.raw_valid⟩, rfl⟩
    · rintro ⟨⟨x, y⟩, ⟨hx, hy⟩, rfl⟩
      exact ⟨(x.toFrame hx, y.toFrame hy), rfl⟩
  rw [he]
  exact hd.image rawPairProfile_continuous

private theorem twoFrameProfile_eq_sum_axes (E : BlochFrame ρ) (F : BlochFrame σ)
    (B : Matrix (Fin 3) (Fin 3) ℝ) (hB : Bᵀ * B = 1)
    (hV : ∀ k, E.axisVariance B k = F.axisVariance B k) :
    twoFrameProfile E F =
      ∑ k, (E.axisVariance B k / 2) • twoFrameProfile (E.alongAxis B k) (F.alongAxis B k) := by
  ext ⟨i, j⟩
  cases i <;> cases j <;>
    simp only [twoFrameProfile, rawPairProfile, BlochFrame.raw, Sum.elim_inl, Sum.elim_inr,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  · exact blochWedge_eq_average_axes E E B hB (fun _ => rfl) _ _
  · exact blochWedge_eq_average_axes E F B hB hV _ _
  · simpa only [hV] using blochWedge_eq_average_axes F E B hB (fun k => (hV k).symm) _ _
  · simpa only [hV] using blochWedge_eq_average_axes F F B hB (fun _ => rfl) _ _

private theorem maximal_linear_eq_of_average {τ : Type*} (L : (τ → ℝ) →ₗ[ℝ] ℝ)
    (w : Fin 3 → ℝ) (P : Fin 3 → τ → ℝ) (z : τ → ℝ) (hw : ∀ k, 0 ≤ w k)
    (hw₁ : ∑ k, w k = 1) (hz : z = ∑ k, w k • P k)
    (hmax : ∀ k, L (P k) ≤ L z) (k : Fin 3) (hk : 0 < w k) : L (P k) = L z := by
  have hL := congrArg L hz
  simp only [map_sum, map_smul, smul_eq_mul] at hL
  have hzero : ∑ l, w l * (L z - L (P l)) = 0 := by
    simp_rw [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hw₁, one_mul, ← hL, sub_self]
  have ht := (Finset.sum_eq_zero_iff_of_nonneg
    (fun l _ => mul_nonneg (hw l) (sub_nonneg.mpr (hmax l)))).mp hzero k (mem_univ k)
  exact (sub_eq_zero.mp ((mul_eq_zero.mp ht).resolve_left hk.ne')).symm

private def profileEnergy {τ : Type*} [Fintype τ] (z : τ → ℝ) : ℝ := ∑ i, z i ^ 2

private theorem maximal_energy_eq_of_average {τ : Type*} [Fintype τ]
    (w : Fin 3 → ℝ) (P : Fin 3 → τ → ℝ) (z : τ → ℝ) (hw : ∀ k, 0 ≤ w k)
    (hw₁ : ∑ k, w k = 1) (hz : z = ∑ k, w k • P k)
    (hmax : ∀ k, 0 < w k → profileEnergy (P k) ≤ profileEnergy z)
    (k : Fin 3) (hk : 0 < w k) : P k = z := by
  have hpoint (i : τ) : z i = ∑ l, w l * P l i := by
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using congrArg (fun f => f i) hz
  have hsq (i : τ) :
      (∑ l, w l * (P l i - z i) ^ 2) = (∑ l, w l * P l i ^ 2) - z i ^ 2 := by
    calc
      _ = (∑ l, w l * P l i ^ 2) - 2 * z i * (∑ l, w l * P l i) +
          z i ^ 2 * (∑ l, w l) := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro l _
        ring
      _ = _ := by rw [← hpoint i, hw₁]; ring
  let V (l : Fin 3) : ℝ := ∑ i, (P l i - z i) ^ 2
  have hid : (∑ l, w l * V l) =
      (∑ l, w l * profileEnergy (P l)) - profileEnergy z := by
    calc
      _ = ∑ i, ∑ l, w l * (P l i - z i) ^ 2 := by
        simp_rw [V, Finset.mul_sum]
        exact Finset.sum_comm
      _ = ∑ i, ((∑ l, w l * P l i ^ 2) - z i ^ 2) := Finset.sum_congr rfl (fun i _ => hsq i)
      _ = _ := by
        rw [Finset.sum_sub_distrib, Finset.sum_comm]
        simp only [profileEnergy, Finset.mul_sum]
  have hV (l : Fin 3) : 0 ≤ V l := Finset.sum_nonneg fun i _ => sq_nonneg (P l i - z i)
  have htotal : ∑ l, w l * V l = 0 := by
    apply le_antisymm _ (Finset.sum_nonneg fun l _ => mul_nonneg (hw l) (hV l))
    rw [hid, sub_nonpos]
    calc
      _ ≤ ∑ l, w l * profileEnergy z := by
        apply Finset.sum_le_sum
        intro l _
        rcases eq_or_lt_of_le (hw l) with hl | hl
        · simp [← hl]
        · exact mul_le_mul_of_nonneg_left (hmax l hl) (hw l)
      _ = _ := by rw [← Finset.sum_mul, hw₁, one_mul]
  have hVzero : V k = 0 := by
    have ht := (Finset.sum_eq_zero_iff_of_nonneg
      (fun l _ => mul_nonneg (hw l) (hV l))).mp htotal k (mem_univ k)
    exact (mul_eq_zero.mp ht).resolve_left hk.ne'
  funext i
  have ht := (Finset.sum_eq_zero_iff_of_nonneg (fun l _ => sq_nonneg (P k l - z l))).mp
    hVzero i (mem_univ i)
  exact sub_eq_zero.mp (pow_eq_zero ht)

private theorem profile_mass_eq (E E' : BlochFrame ρ) (F F' : BlochFrame σ)
    (h : twoFrameProfile E' F' = twoFrameProfile E F) :
    (∀ i, E'.mass i = E.mass i) ∧ (∀ j, F'.mass j = F.mass j) := by
  constructor
  · intro i
    calc
      _ = ∑ k : ρ, twoFrameProfile E' F' (Sum.inl i, Sum.inl k) :=
        (E'.sum_blochWedge (E'.mass i) (E'.direction i)).symm
      _ = ∑ k : ρ, twoFrameProfile E F (Sum.inl i, Sum.inl k) := by rw [h]
      _ = _ := E.sum_blochWedge (E.mass i) (E.direction i)
  · intro j
    calc
      _ = ∑ k : σ, twoFrameProfile E' F' (Sum.inr j, Sum.inr k) :=
        (F'.sum_blochWedge (F'.mass j) (F'.direction j)).symm
      _ = ∑ k : σ, twoFrameProfile E F (Sum.inr j, Sum.inr k) := by rw [h]
      _ = _ := F.sum_blochWedge (F.mass j) (F.direction j)

/-- A linear cost on the full profile has a maximizing frame pair whose positive
rows lie on the two opposite directions of a common axis. -/
theorem exists_antipodal_maximizer (E : BlochFrame ρ) (F : BlochFrame σ)
    (L : TwoFrameProfile ρ σ →L[ℝ] ℝ) :
    ∃ E' : BlochFrame ρ, ∃ F' : BlochFrame σ,
      (∀ i, 0 < E'.mass i → E'.direction i = ![1, 0, 0] ∨ E'.direction i = ![-1, 0, 0]) ∧
      (∀ j, 0 < F'.mass j → F'.direction j = ![1, 0, 0] ∨ F'.direction j = ![-1, 0, 0]) ∧
      ∀ (E'' : BlochFrame ρ) (F'' : BlochFrame σ),
        L (twoFrameProfile E'' F'') ≤ L (twoFrameProfile E' F') := by
  classical
  have hne : (twoFrameProfiles ρ σ).Nonempty := ⟨_, ⟨(E, F), rfl⟩⟩
  obtain ⟨u, hu, huMax⟩ := isCompact_twoFrameProfiles.exists_isMaxOn hne L.continuous.continuousOn
  let S := twoFrameProfiles ρ σ ∩ {q | L q = L u}
  have hS : IsCompact S :=
    isCompact_twoFrameProfiles.inter_right (isClosed_eq L.continuous continuous_const)
  have henergy : Continuous (profileEnergy : TwoFrameProfile ρ σ → ℝ) := by
    unfold profileEnergy
    fun_prop
  obtain ⟨z, hz, hzMax⟩ := hS.exists_isMaxOn ⟨u, hu, rfl⟩ henergy.continuousOn
  obtain ⟨⟨E₀, F₀⟩, hpair⟩ := hz.1
  subst z
  obtain ⟨B, hB, hV⟩ := equal_axisVariance_exists E₀ F₀
  let w (k : Fin 3) := E₀.axisVariance B k / 2
  let P (k : Fin 3) := twoFrameProfile (E₀.alongAxis B k) (F₀.alongAxis B k)
  have hw (k : Fin 3) : 0 ≤ w k := div_nonneg (E₀.axisVariance_nonneg B k) (by norm_num)
  have hw₁ : ∑ k, w k = 1 := by
    norm_num [w, ← Finset.sum_div, E₀.sum_axisVariance B hB]
  have hcenter : twoFrameProfile E₀ F₀ = ∑ k, w k • P k :=
    twoFrameProfile_eq_sum_axes E₀ F₀ B hB hV
  have hmem (k : Fin 3) : P k ∈ twoFrameProfiles ρ σ :=
    ⟨(E₀.alongAxis B k, F₀.alongAxis B k), rfl⟩
  have hu_eq : L (twoFrameProfile E₀ F₀) = L u := hz.2
  have hL (k : Fin 3) (hk : 0 < w k) : L (P k) = L (twoFrameProfile E₀ F₀) :=
    maximal_linear_eq_of_average L.toLinearMap w P _ hw hw₁ hcenter
      (fun l => hu_eq ▸ huMax (hmem l)) k hk
  have hmax (k : Fin 3) (hk : 0 < w k) : profileEnergy (P k) ≤ profileEnergy (twoFrameProfile E₀ F₀) :=
    hzMax (show P k ∈ S from ⟨hmem k, (hL k hk).trans hu_eq⟩)
  have hex : ∃ k, 0 < w k := by
    by_contra! hnone
    have heq (k : Fin 3) : w k = 0 := (hnone k).antisymm (hw k)
    simp [heq] at hw₁
  obtain ⟨k, hk⟩ := hex
  have hp : P k = twoFrameProfile E₀ F₀ :=
    maximal_energy_eq_of_average w P _ hw hw₁ hcenter hmax k hk
  have hVp : 0 < E₀.axisVariance B k := by
    dsimp only [w] at hk
    linarith
  have hVq : 0 < F₀.axisVariance B k := by rwa [← hV k]
  obtain ⟨heq, hfeq⟩ := profile_mass_eq E₀ (E₀.alongAxis B k) F₀ (F₀.alongAxis B k) hp
  refine ⟨E₀.alongAxis B k, F₀.alongAxis B k, ?_, ?_, ?_⟩
  · intro i hi
    simp only [BlochFrame.alongAxis, dif_pos hVp] at heq hi ⊢
    have hpos : 0 < E₀.mass i := (heq i) ▸ hi
    exact E₀.project_eq_opposite_of_mass_eq _ _ _ i hpos (heq i)
  · intro j hj
    simp only [BlochFrame.alongAxis, dif_pos hVq] at hfeq hj ⊢
    have hpos : 0 < F₀.mass j := (hfeq j) ▸ hj
    exact F₀.project_eq_opposite_of_mass_eq _ _ _ j hpos (hfeq j)
  · intro E'' F''
    change L (twoFrameProfile E'' F'') ≤ L (P k)
    rw [hL k hk, hu_eq]
    exact huMax (show twoFrameProfile E'' F'' ∈ twoFrameProfiles ρ σ from ⟨(E'', F''), rfl⟩)

private def plusMass (E : BlochFrame ρ) (i : ρ) : ℝ :=
  if E.direction i = ![1, 0, 0] then E.mass i else 0

private def minusMass (E : BlochFrame ρ) (i : ρ) : ℝ :=
  if E.direction i = ![1, 0, 0] then 0 else E.mass i

private theorem antipodes_ne : (![(-1 : ℝ), 0, 0] : Fin 3 → ℝ) ≠ ![1, 0, 0] := by
  intro he
  have h := congrArg (fun f : Fin 3 → ℝ => f 0) he
  norm_num at h

private theorem antipodal_masses_sum (E : BlochFrame ρ)
    (hE : ∀ i, 0 < E.mass i → E.direction i = ![1, 0, 0] ∨ E.direction i = ![-1, 0, 0]) :
    (∑ i, plusMass E i = 1) ∧ (∑ i, minusMass E i = 1) := by
  have hp (i : ρ) : plusMass E i + minusMass E i = E.mass i := by
    by_cases h : E.direction i = ![1, 0, 0] <;> simp [plusMass, minusMass, h]
  have hm (i : ρ) : plusMass E i - minusMass E i = E.mass i * E.direction i 0 := by
    rcases eq_or_lt_of_le (E.mass_nonneg i) with hz | hz
    · simp [plusMass, minusMass, ← hz]
    rcases hE i hz with h | h
    · simp [plusMass, minusMass, h]
    · simp [plusMass, minusMass, h, antipodes_ne]
  have heq₁ := Finset.sum_congr rfl (fun i (_ : i ∈ univ) => hp i)
  have heq₂ := Finset.sum_congr rfl (fun i (_ : i ∈ univ) => hm i)
  rw [Finset.sum_add_distrib, E.sum_mass] at heq₁
  rw [Finset.sum_sub_distrib, E.mean_zero] at heq₂
  constructor <;> linarith

private theorem blochWedge_eq_antipodal {τ : Type*} [Fintype τ]
    (E : BlochFrame ρ) (F : BlochFrame τ)
    (i : ρ) (j : τ)
    (hE : 0 < E.mass i → E.direction i = ![1, 0, 0] ∨ E.direction i = ![-1, 0, 0])
    (hF : 0 < F.mass j → F.direction j = ![1, 0, 0] ∨ F.direction j = ![-1, 0, 0]) :
    blochWedge (E.mass i) (F.mass j) (E.direction i) (F.direction j) =
      plusMass E i * minusMass F j + minusMass E i * plusMass F j := by
  rcases eq_or_lt_of_le (E.mass_nonneg i) with hz | hp
  · simp [blochWedge, plusMass, minusMass, ← hz]
  rcases eq_or_lt_of_le (F.mass_nonneg j) with hz | hq
  · simp [blochWedge, plusMass, minusMass, ← hz]
  have hp₂ : (![1, 0, 0] : Fin 3 → ℝ) 2 = 0 := rfl
  have hm₂ : (![-1, 0, 0] : Fin 3 → ℝ) 2 = 0 := rfl
  rcases hE hp with hE | hE <;> rcases hF hq with hF | hF <;>
    norm_num [blochWedge, plusMass, minusMass, hE, hF, antipodes_ne, Fin.sum_univ_three,
      Matrix.cons_val', hp₂, hm₂]

/-- Four endpoints, labelled by their two directions. The actual edges cross
directions between the two frames. -/
abbrev TwoEdgeMatching (ρ σ : Type*) :=
  {m : (ρ × σ) × (ρ × σ) // m.1.1 ≠ m.2.1 ∧ m.1.2 ≠ m.2.2}

private def choiceIndicator [DecidableEq ρ] [DecidableEq σ] (m : ρ × σ) : ρ ⊕ σ → ℝ :=
  Sum.elim (fun i => if m.1 = i then 1 else 0) (fun j => if m.2 = j then 1 else 0)

private def choiceProfile [DecidableEq ρ] [DecidableEq σ] (m : (ρ × σ) × (ρ × σ)) :
    TwoFrameProfile ρ σ :=
  fun ij => choiceIndicator m.1 ij.1 * choiceIndicator m.2 ij.2 +
    choiceIndicator m.2 ij.1 * choiceIndicator m.1 ij.2

/-- The indicator profile of one two-edge matching. On a cross-frame pair it
tests edge membership, and within a frame it tests the unordered selected pair. -/
def twoEdgeProfile [DecidableEq ρ] [DecidableEq σ] (m : TwoEdgeMatching ρ σ) :
    TwoFrameProfile ρ σ :=
  choiceProfile m.val

private theorem sum_choiceIndicator [DecidableEq ρ] [DecidableEq σ]
    (p : ρ → ℝ) (q : σ → ℝ) (hp : ∑ i, p i = 1) (hq : ∑ j, q j = 1) (x : ρ ⊕ σ) :
    (∑ m : ρ × σ, (p m.1 * q m.2) * choiceIndicator m x) = Sum.elim p q x := by
  cases x with
  | inl i =>
      rw [Fintype.sum_prod_type]
      simp only [choiceIndicator, Sum.elim_inl]
      trans ∑ i', if i' = i then p i' else 0
      · apply Finset.sum_congr rfl
        intro i' _
        by_cases hi : i' = i <;> simp [hi, ← Finset.mul_sum, hq]
      · simp
  | inr j =>
      rw [Fintype.sum_prod_type]
      simp only [choiceIndicator, Sum.elim_inr]
      simp_rw [mul_assoc, ← Finset.mul_sum, mul_ite, mul_one, mul_zero]
      simp [← Finset.sum_mul, hp]

private theorem antipodal_profile_mem_hull [DecidableEq ρ] [DecidableEq σ]
    (E : BlochFrame ρ) (F : BlochFrame σ)
    (hE : ∀ i, 0 < E.mass i → E.direction i = ![1, 0, 0] ∨ E.direction i = ![-1, 0, 0])
    (hF : ∀ j, 0 < F.mass j → F.direction j = ![1, 0, 0] ∨ F.direction j = ![-1, 0, 0]) :
    twoFrameProfile E F ∈ convexHull ℝ (Set.range (twoEdgeProfile (ρ := ρ) (σ := σ))) := by
  obtain ⟨hp₀, hm₀⟩ := antipodal_masses_sum E hE
  obtain ⟨hp₁, hm₁⟩ := antipodal_masses_sum F hF
  let wp (v : ρ × σ) := plusMass E v.1 * plusMass F v.2
  let wm (v : ρ × σ) := minusMass E v.1 * minusMass F v.2
  let w (m : (ρ × σ) × (ρ × σ)) := wp m.1 * wm m.2
  let valid (m : (ρ × σ) × (ρ × σ)) := m.1.1 ≠ m.2.1 ∧ m.1.2 ≠ m.2.2
  let s : Finset ((ρ × σ) × (ρ × σ)) := univ.filter valid
  have hwp : ∑ v, wp v = 1 := by simp [wp, Fintype.sum_prod_type, ← Finset.mul_sum, hp₀, hp₁]
  have hwm : ∑ v, wm v = 1 := by simp [wm, Fintype.sum_prod_type, ← Finset.mul_sum, hm₀, hm₁]
  have hw : ∑ m, w m = 1 := by simp [w, Fintype.sum_prod_type, ← Finset.mul_sum, hwp, hwm]
  have hnonneg (m : (ρ × σ) × (ρ × σ)) : 0 ≤ w m := by
    unfold w wp wm plusMass minusMass
    split_ifs <;> simp [E.mass_nonneg, F.mass_nonneg, mul_nonneg]
  have hzero (m : (ρ × σ) × (ρ × σ)) (hm : ¬ valid m) : w m = 0 := by
    have hbad : m.1.1 = m.2.1 ∨ m.1.2 = m.2.2 := by
      simpa only [valid, not_and_or, not_ne_iff] using hm
    rcases hbad with h | h
    · by_cases he : E.direction m.2.1 = ![1, 0, 0] <;>
        simp [w, wp, wm, plusMass, minusMass, h, he]
    · by_cases hf : F.direction m.2.2 = ![1, 0, 0] <;>
        simp [w, wp, wm, plusMass, minusMass, h, hf]
  have hfilter (f : ((ρ × σ) × (ρ × σ)) → ℝ) :
      (∑ m ∈ s, w m * f m) = ∑ m, w m * f m := by
    dsimp only [s]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro m _
    by_cases h : valid m
    · exact if_pos h
    · rw [if_neg h, hzero m h, zero_mul]
  have hsum : ∑ m ∈ s, w m = 1 := by simpa using (hfilter (fun _ => 1)).trans (by simpa using hw)
  have hform (x y : ρ ⊕ σ) :
      (∑ m, w m * (choiceIndicator m.1 x * choiceIndicator m.2 y)) =
        Sum.elim (plusMass E) (plusMass F) x * Sum.elim (minusMass E) (minusMass F) y := by
    rw [← sum_choiceIndicator _ _ hp₀ hp₁, ← sum_choiceIndicator _ _ hm₀ hm₁,
      Fintype.sum_prod_type, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro u _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v _
    dsimp [w, wp, wm]
    ring
  have hcenter : s.centerMass w choiceProfile = twoFrameProfile E F := by
    rw [s.centerMass_eq_of_sum_1 choiceProfile hsum]
    funext ij
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hfilter, choiceProfile,
      mul_add, Finset.sum_add_distrib, hform]
    have hs : (∑ m, w m * (choiceIndicator m.2 ij.1 * choiceIndicator m.1 ij.2)) =
        Sum.elim (minusMass E) (minusMass F) ij.1 * Sum.elim (plusMass E) (plusMass F) ij.2 := by
      calc
        _ = ∑ m, w m * (choiceIndicator m.1 ij.2 * choiceIndicator m.2 ij.1) :=
          Finset.sum_congr rfl (fun m _ => by rw [mul_comm (choiceIndicator m.2 ij.1)])
        _ = _ := (hform ij.2 ij.1).trans (mul_comm _ _)
    rw [hs]
    rcases ij with ⟨i, j⟩
    cases i <;> cases j <;>
      simp only [twoFrameProfile, rawPairProfile, BlochFrame.raw, Sum.elim_inl, Sum.elim_inr]
    · exact (blochWedge_eq_antipodal E E _ _ (hE _) (hE _)).symm
    · exact (blochWedge_eq_antipodal E F _ _ (hE _) (hF _)).symm
    · exact (blochWedge_eq_antipodal F E _ _ (hF _) (hE _)).symm
    · exact (blochWedge_eq_antipodal F F _ _ (hF _) (hF _)).symm
  rw [← hcenter]
  refine s.centerMass_mem_convexHull (fun m _ => hnonneg m) (by simp [hsum]) ?_
  intro m hm
  exact ⟨⟨m, (Finset.mem_filter.mp hm).2⟩, rfl⟩

/-- The two-frame matching theorem. The complete stacked squared-wedge profile
is a convex combination of two-edge matching profiles. -/
theorem twoFrameProfile_mem_hull_two_edge [DecidableEq ρ] [DecidableEq σ]
    (E : BlochFrame ρ) (F : BlochFrame σ) :
    twoFrameProfile E F ∈ convexHull ℝ (Set.range (twoEdgeProfile (ρ := ρ) (σ := σ))) := by
  classical
  let K := convexHull ℝ (Set.range (twoEdgeProfile (ρ := ρ) (σ := σ)))
  have hK : IsClosed K := (Set.finite_range _).isCompact_convexHull.isClosed
  by_contra hn
  obtain ⟨L, u, hL, hgt⟩ :=
    geometric_hahn_banach_closed_point (convex_convexHull ℝ _) hK hn
  obtain ⟨E', F', hE', hF', hmax⟩ := exists_antipodal_maximizer E F L
  have hj := hL _ (antipodal_profile_mem_hull E' F' hE' hF')
  exact (not_lt_of_ge (hmax E F)) (lt_trans hj hgt)

/-- The two-frame profile expressed directly by squared wedges of the input rows. -/
theorem squaredWedge_mem_hull_two_edge [DecidableEq ρ] [DecidableEq σ]
    (E : Matrix ρ (Fin 2) ℂ) (F : Matrix σ (Fin 2) ℂ)
    (hE : Eᴴ * E = 1) (hF : Fᴴ * F = 1) :
    let W := Sum.elim E F
    (fun ij : (ρ ⊕ σ) × (ρ ⊕ σ) =>
      Complex.normSq (W ij.1 0 * W ij.2 1 - W ij.1 1 * W ij.2 0)) ∈
      convexHull ℝ (Set.range (twoEdgeProfile (ρ := ρ) (σ := σ))) := by
  have h := twoFrameProfile_mem_hull_two_edge (BlochFrame.ofMatrix E hE) (BlochFrame.ofMatrix F hF)
  convert h using 1
  funext ij
  rcases ij with ⟨i, j⟩
  cases i <;> cases j <;>
    exact normSq_wedge_eq_blochWedge _ _

private theorem weighted_gram_entry [DecidableEq ρ]
    (W : Matrix ρ (Fin 2) ℂ) (d : ρ → ℂ) (i j : Fin 2) :
    (Wᴴ * diagonal d * W) i j = ∑ k, star (W k i) * d k * W k j := by
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.conjTranspose_apply]

/-- Cauchy–Binet in two columns, written as a sum over ordered pairs so that
no order structure is imposed on the row labels. -/
theorem det_weighted_gram_two [DecidableEq ρ] (W : Matrix ρ (Fin 2) ℂ) (d : ρ → ℂ) :
    (Wᴴ * diagonal d * W).det =
      (∑ i, ∑ j, (d i * d j) *
        (Complex.normSq (W i 0 * W j 1 - W i 1 * W j 0) : ℂ)) / 2 := by
  let cost (i j : ρ) :=
    (star (W i 0) * d i * W i 0) * (star (W j 1) * d j * W j 1) -
    (star (W i 0) * d i * W i 1) * (star (W j 1) * d j * W j 0)
  have hd : (Wᴴ * diagonal d * W).det = ∑ i, ∑ j, cost i j := by
    rw [Matrix.det_fin_two]
    simp only [weighted_gram_entry, cost, Finset.sum_sub_distrib, Finset.sum_mul]
    simp only [Finset.mul_sum]
  have hsymm : (∑ i, ∑ j, cost j i) = ∑ i, ∑ j, cost i j := Finset.sum_comm
  have hwedge (i j : ρ) : cost i j + cost j i = (d i * d j) *
      (Complex.normSq (W i 0 * W j 1 - W i 1 * W j 0) : ℂ) := by
    rw [Complex.normSq_eq_conj_mul_self, starRingEnd_apply, star_sub,
      StarMul.star_mul, StarMul.star_mul]
    dsimp only [cost]
    ring
  rw [hd]
  symm
  apply (div_eq_iff (show (2 : ℂ) ≠ 0 by norm_num)).mpr
  simp_rw [← hwedge, Finset.sum_add_distrib, hsymm]
  ring

private def wedgeEvaluation {τ : Type*} [Fintype τ] (d : τ → ℂ) :
    ((τ × τ) → ℝ) →ₗ[ℝ] ℂ where
  toFun w := (∑ ij : τ × τ, (d ij.1 * d ij.2) * (w ij : ℂ)) / 2
  map_add' a b := by
    simp only [Pi.add_apply, Complex.ofReal_add, mul_add, Finset.sum_add_distrib, add_div]
  map_smul' q w := by
    change (∑ ij : τ × τ, (d ij.1 * d ij.2) * ((q * w ij : ℝ) : ℂ)) / 2 =
      q • ((∑ ij : τ × τ, (d ij.1 * d ij.2) * (w ij : ℂ)) / 2)
    rw [Complex.real_smul, ← mul_div_assoc, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro ij _
    rw [Complex.ofReal_mul]
    ring

private theorem sum_weighted_choiceIndicator [DecidableEq ρ] [DecidableEq σ]
    (d : ρ ⊕ σ → ℂ) (a : ρ × σ) :
    (∑ i, d i * (choiceIndicator a i : ℂ)) = d (Sum.inl a.1) + d (Sum.inr a.2) := by
  rw [Fintype.sum_sum_type]
  simp [choiceIndicator, apply_ite, mul_ite, eq_comm]

private theorem wedgeEvaluation_choice [DecidableEq ρ] [DecidableEq σ]
    (d : ρ ⊕ σ → ℂ) (m : TwoEdgeMatching ρ σ) :
    wedgeEvaluation d (twoEdgeProfile m) =
      (d (Sum.inl m.val.1.1) + d (Sum.inr m.val.1.2)) *
        (d (Sum.inl m.val.2.1) + d (Sum.inr m.val.2.2)) := by
  have hp (a b : ρ × σ) :
      (∑ ij : (ρ ⊕ σ) × (ρ ⊕ σ), (d ij.1 * d ij.2) *
        ((choiceIndicator a ij.1 * choiceIndicator b ij.2 : ℝ) : ℂ)) =
      (∑ i, d i * (choiceIndicator a i : ℂ)) * (∑ j, d j * (choiceIndicator b j : ℂ)) := by
    rw [Fintype.sum_prod_type, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [Complex.ofReal_mul]
    ring
  change (∑ ij : (ρ ⊕ σ) × (ρ ⊕ σ), (d ij.1 * d ij.2) *
      (choiceProfile m.val ij : ℂ)) / 2 = _
  simp only [choiceProfile, Complex.ofReal_add, mul_add, Finset.sum_add_distrib, hp,
    sum_weighted_choiceIndicator]
  ring

/-- A single law on two-edge matchings represents the compressed determinant
for every choice of the two spectra. -/
theorem exists_twoFrame_compression_weights [DecidableEq ρ] [DecidableEq σ]
    (E : Matrix ρ (Fin 2) ℂ) (F : Matrix σ (Fin 2) ℂ)
    (hE : Eᴴ * E = 1) (hF : Fᴴ * F = 1) :
    ∃ (s : Finset (TwoEdgeMatching ρ σ)) (w : TwoEdgeMatching ρ σ → ℝ),
      (∀ m ∈ s, 0 ≤ w m) ∧ (∑ m ∈ s, w m = 1) ∧ ∀ (x : ρ → ℂ) (y : σ → ℂ),
        (∑ m ∈ s, (w m : ℂ) *
          ((x m.val.1.1 + y m.val.1.2) * (x m.val.2.1 + y m.val.2.2))) =
          (Eᴴ * diagonal x * E + Fᴴ * diagonal y * F).det := by
  let W : Matrix (ρ ⊕ σ) (Fin 2) ℂ := Sum.elim E F
  let p : TwoFrameProfile ρ σ :=
    fun ij => Complex.normSq (W ij.1 0 * W ij.2 1 - W ij.1 1 * W ij.2 0)
  have hp : p ∈ convexHull ℝ (Set.range (twoEdgeProfile (ρ := ρ) (σ := σ))) :=
    squaredWedge_mem_hull_two_edge E F hE hF
  rw [convexHull_range_eq_exists_affineCombination] at hp
  obtain ⟨s, w, hw, hs, hcomb⟩ := hp
  change s.affineCombination ℝ twoEdgeProfile w = p at hcomb
  rw [Finset.affineCombination_eq_linear_combination _ _ _ hs] at hcomb
  refine ⟨s, w, hw, hs, ?_⟩
  intro x y
  let d := Sum.elim x y
  have hgram : Wᴴ * diagonal d * W = Eᴴ * diagonal x * E + Fᴴ * diagonal y * F := by
    ext i j : 1
    rw [Matrix.add_apply, weighted_gram_entry W d, weighted_gram_entry E x,
      weighted_gram_entry F y, Fintype.sum_sum_type]
    rfl
  have hdet : wedgeEvaluation d p = (Eᴴ * diagonal x * E + Fᴴ * diagonal y * F).det := by
    rw [← hgram, det_weighted_gram_two]
    change (∑ ij : (ρ ⊕ σ) × (ρ ⊕ σ), (d ij.1 * d ij.2) * (p ij : ℂ)) / 2 = _
    rw [Fintype.sum_prod_type]
  calc
    _ = wedgeEvaluation d (∑ m ∈ s, w m • twoEdgeProfile m) := by
      simp [map_sum, map_smul, wedgeEvaluation_choice, Complex.real_smul, d]
    _ = _ := by rw [hcomb, hdet]

/-- The rank-two compressed determinant lies in the hull of the two-edge products. -/
theorem det_twoFrame_compression_mem_hull [DecidableEq ρ] [DecidableEq σ]
    (E : Matrix ρ (Fin 2) ℂ) (F : Matrix σ (Fin 2) ℂ)
    (hE : Eᴴ * E = 1) (hF : Fᴴ * F = 1) (x : ρ → ℂ) (y : σ → ℂ) :
    (Eᴴ * diagonal x * E + Fᴴ * diagonal y * F).det ∈ convexHull ℝ
      (Set.range fun m : TwoEdgeMatching ρ σ =>
        (x m.val.1.1 + y m.val.1.2) * (x m.val.2.1 + y m.val.2.2)) := by
  obtain ⟨s, w, hw, hs, hval⟩ := exists_twoFrame_compression_weights E F hE hF
  rw [convexHull_range_eq_exists_affineCombination]
  refine ⟨s, w, hw, hs, ?_⟩
  rw [Finset.affineCombination_eq_linear_combination _ _ _ hs]
  simpa only [Complex.real_smul] using hval x y

end

end MOC
