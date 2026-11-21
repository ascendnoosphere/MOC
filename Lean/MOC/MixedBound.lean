import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Notation
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! A quantitative lower bound for the canonical order-four mixed facet in
quaternion coordinates. The inputs to the bound are two real unit quaternions. -/

namespace MOC

private theorem sqrt_one_sub_sq_mul_le {a c : ℝ}
    (ha : a ∈ Set.Icc 0 1) (hc : c ∈ Set.Icc 0 1) :
    √(1 - a ^ 2) * √(1 - c ^ 2) ≤ 1 - (a ^ 2 + c ^ 2) / 2 := by
  have ha' : 0 ≤ 1 - a ^ 2 := by nlinarith [mul_nonneg ha.1 (sub_nonneg.mpr ha.2)]
  have hc' : 0 ≤ 1 - c ^ 2 := by nlinarith [mul_nonneg hc.1 (sub_nonneg.mpr hc.2)]
  nlinarith [Real.sq_sqrt ha', Real.sq_sqrt hc', sq_nonneg (√(1 - a ^ 2) - √(1 - c ^ 2))]

private noncomputable def mixedQuadratic (x y a b : ℝ) : ℝ :=
  (x * y * a ^ 2 + (1 - x) * (1 - y) * b ^ 2) / 2 - x * (1 - x) * a * b

private theorem mixed_quadratic_nonneg {x y a b : ℝ}
    (hx : x ∈ Set.Icc 0 1) (hy : y ∈ Set.Icc 0 1)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (h : x * (1 - x) ≤ y * (1 - y)) :
    0 ≤ mixedQuadratic x y a b := by
  have hA := mul_nonneg hx.1 hy.1
  have hB := mul_nonneg (sub_nonneg.mpr hx.2) (sub_nonneg.mpr hy.2)
  have hC := mul_nonneg hx.1 (sub_nonneg.mpr hx.2)
  have hs : x * (1 - x) ≤ √(x * y) * √((1 - x) * (1 - y)) := by
    rw [← Real.sqrt_mul hA]
    apply Real.le_sqrt_of_sq_le
    nlinarith [mul_nonneg hC (sub_nonneg.mpr h)]
  have hcross := mul_le_mul_of_nonneg_right hs (mul_nonneg ha hb)
  have hsq : 0 ≤ x * y * a ^ 2 + (1 - x) * (1 - y) * b ^ 2 -
      2 * (√(x * y) * √((1 - x) * (1 - y))) * (a * b) := by
    calc
      0 ≤ (√(x * y) * a - √((1 - x) * (1 - y)) * b) ^ 2 := sq_nonneg _
      _ = _ := by rw [sub_sq, mul_pow, mul_pow, Real.sq_sqrt hA, Real.sq_sqrt hB]; ring
  unfold mixedQuadratic
  linarith only [hsq, hcross]

private theorem cube_bound {x : ℝ} (hx : x ≤ 1) : x * (1 - x)^2 ≤ (4 / 27 : ℝ) := by
  have h := mul_nonneg (sq_nonneg (x - 1 / 3)) (show (0 : ℝ) ≤ 4 / 3 - x by linarith)
  nlinarith

private theorem mixed_quadratic_lower {x y a b : ℝ}
    (hx : x ∈ Set.Icc 0 1) (hy : y ∈ Set.Icc 0 1)
    (ha : a ∈ Set.Icc 0 1) (hb : b ∈ Set.Icc 0 1) :
    -(2 / 27 : ℝ) ≤ mixedQuadratic x y a b := by
  have ha' : a ^ 2 ≤ 1 := by nlinarith [mul_nonneg ha.1 (sub_nonneg.mpr ha.2)]
  have hb' : b ^ 2 ≤ 1 := by nlinarith [mul_nonneg hb.1 (sub_nonneg.mpr hb.2)]
  have h0 : -(2 / 27 : ℝ) ≤ mixedQuadratic x 0 a b := by
    have hsq := mul_nonneg (sub_nonneg.mpr hx.2) (sq_nonneg (b - x * a))
    have hcoef := mul_nonneg (mul_nonneg (sub_nonneg.mpr hx.2) (sq_nonneg x))
      (sub_nonneg.mpr ha')
    have hc := cube_bound (show 1 - x ≤ 1 by linarith [hx.1])
    unfold mixedQuadratic
    nlinarith
  have h1 : -(2 / 27 : ℝ) ≤ mixedQuadratic x 1 a b := by
    have hsq := mul_nonneg hx.1 (sq_nonneg (a - (1 - x) * b))
    have hcoef := mul_nonneg (mul_nonneg hx.1 (sq_nonneg (1 - x))) (sub_nonneg.mpr hb')
    unfold mixedQuadratic
    nlinarith [cube_bound hx.2]
  have h := add_le_add (mul_le_mul_of_nonneg_left h0 (sub_nonneg.mpr hy.2))
    (mul_le_mul_of_nonneg_left h1 hy.1)
  calc
    -(2 / 27 : ℝ) = (1 - y) * -(2 / 27 : ℝ) + y * -(2 / 27 : ℝ) := by ring
    _ ≤ (1 - y) * mixedQuadratic x 0 a b + y * mixedQuadratic x 1 a b := h
    _ = mixedQuadratic x y a b := by unfold mixedQuadratic; ring

private theorem normalized_mixed_lower {x y a b c d : ℝ}
    (hx : x ∈ Set.Icc 0 1) (hy : y ∈ Set.Icc 0 1)
    (ha : a ∈ Set.Icc 0 1) (hb : b ∈ Set.Icc 0 1)
    (hc : c ∈ Set.Icc 0 1) (hd : d ∈ Set.Icc 0 1) :
    -(2 / 27 : ℝ) ≤
      x * y * (1 - √(1 - a ^ 2) * √(1 - c ^ 2)) +
      (1 - x) * (1 - y) * (1 - √(1 - b ^ 2) * √(1 - d ^ 2)) -
      x * (1 - x) * a * b - y * (1 - y) * c * d := by
  have hquad : -(2 / 27 : ℝ) ≤ mixedQuadratic x y a b + mixedQuadratic y x c d := by
    rcases le_total (x * (1 - x)) (y * (1 - y)) with h | h
    · linarith [mixed_quadratic_nonneg hx hy ha.1 hb.1 h, mixed_quadratic_lower hy hx hc hd]
    · linarith [mixed_quadratic_lower hx hy ha hb, mixed_quadratic_nonneg hy hx hc.1 hd.1 h]
  refine hquad.trans ?_
  have hAC := mul_le_mul_of_nonneg_left (sqrt_one_sub_sq_mul_le ha hc) (mul_nonneg hx.1 hy.1)
  have hBD := mul_le_mul_of_nonneg_left (sqrt_one_sub_sq_mul_le hb hd)
    (mul_nonneg (sub_nonneg.mpr hx.2) (sub_nonneg.mpr hy.2))
  unfold mixedQuadratic
  linarith

private theorem normalize_pair (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    ∃ a ∈ Set.Icc (0 : ℝ) 1, |u - v| = (u + v) * a ∧
      2 * √(u * v) = (u + v) * √(1 - a ^ 2) := by
  by_cases h : u + v = 0
  · have hu' : u = 0 := by linarith
    have hv' : v = 0 := by linarith
    exact ⟨0, ⟨le_rfl, zero_le_one⟩, by simp [hu', hv'], by simp [hu', hv']⟩
  have hsum := lt_of_le_of_ne (add_nonneg hu hv) (Ne.symm h)
  let a := |u - v| / (u + v)
  have ha0 : 0 ≤ a := div_nonneg (abs_nonneg _) hsum.le
  have ha1 : a ≤ 1 := (div_le_one hsum).2 (abs_le.2 ⟨by linarith, by linarith⟩)
  have ham : |u - v| = (u + v) * a := by dsimp [a]; field_simp
  have har : 0 ≤ 1 - a ^ 2 := by nlinarith [mul_nonneg ha0 (sub_nonneg.mpr ha1)]
  refine ⟨a, ⟨ha0, ha1⟩, ham, ?_⟩
  have hL : 0 ≤ 2 * √(u * v) := by positivity
  have hR := mul_nonneg hsum.le (Real.sqrt_nonneg (1 - a ^ 2))
  have hms : (u - v) ^ 2 = ((u + v) * a) ^ 2 := by rw [← ham, sq_abs]
  have hs : (2 * √(u * v)) ^ 2 = ((u + v) * √(1 - a ^ 2)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (mul_nonneg hu hv), mul_pow, Real.sq_sqrt har]
    nlinarith only [hms]
  exact le_antisymm ((sq_le_sq₀ hL hR).1 hs.le) ((sq_le_sq₀ hR hL).1 hs.ge)

private theorem mixed_probability_lower
    {p₀ p₁ p₂ p₃ r₀ r₁ r₂ r₃ : ℝ}
    (hp₀ : 0 ≤ p₀) (hp₁ : 0 ≤ p₁) (hp₂ : 0 ≤ p₂) (hp₃ : 0 ≤ p₃)
    (hr₀ : 0 ≤ r₀) (hr₁ : 0 ≤ r₁) (hr₂ : 0 ≤ r₂) (hr₃ : 0 ≤ r₃)
    (hp : p₀ + p₁ + p₂ + p₃ = 1) (hr : r₀ + r₁ + r₂ + r₃ = 1) :
    -(2 / 27 : ℝ) ≤
      (p₀ + p₃) * (r₀ + r₃) + (p₁ + p₂) * (r₁ + r₂) +
      (p₀ - p₃) * (p₁ - p₂) + (r₀ - r₃) * (r₁ - r₂) -
      4 * √(p₀ * p₃) * √(r₀ * r₃) - 4 * √(p₁ * p₂) * √(r₁ * r₂) := by
  let x := p₀ + p₃
  let y := r₀ + r₃
  have hx : x ∈ Set.Icc (0 : ℝ) 1 := ⟨by dsimp [x]; linarith, by dsimp [x]; linarith⟩
  have hy : y ∈ Set.Icc (0 : ℝ) 1 := ⟨by dsimp [y]; linarith, by dsimp [y]; linarith⟩
  have hpx : p₁ + p₂ = 1 - x := by dsimp [x]; linarith
  have hry : r₁ + r₂ = 1 - y := by dsimp [y]; linarith
  obtain ⟨a, ha, ham, har⟩ := normalize_pair p₀ p₃ hp₀ hp₃
  obtain ⟨b, hb, hbm, hbr⟩ := normalize_pair p₁ p₂ hp₁ hp₂
  obtain ⟨c, hc, hcm, hcr⟩ := normalize_pair r₀ r₃ hr₀ hr₃
  obtain ⟨d, hd, hdm, hdr⟩ := normalize_pair r₁ r₂ hr₁ hr₂
  change |p₀ - p₃| = x * a at ham
  change 2 * √(p₀ * p₃) = x * √(1 - a ^ 2) at har
  change |r₀ - r₃| = y * c at hcm
  change 2 * √(r₀ * r₃) = y * √(1 - c ^ 2) at hcr
  rw [hpx] at hbm hbr
  rw [hry] at hdm hdr
  have hpp : -x * (1 - x) * a * b ≤ (p₀ - p₃) * (p₁ - p₂) := by
    calc
      _ = -|(p₀ - p₃) * (p₁ - p₂)| := by rw [abs_mul, ham, hbm]; ring
      _ ≤ _ := neg_abs_le _
  have hrr : -y * (1 - y) * c * d ≤ (r₀ - r₃) * (r₁ - r₂) := by
    calc
      _ = -|(r₀ - r₃) * (r₁ - r₂)| := by rw [abs_mul, hcm, hdm]; ring
      _ ≤ _ := neg_abs_le _
  have h03 : 4 * √(p₀ * p₃) * √(r₀ * r₃) = x * y * √(1 - a ^ 2) * √(1 - c ^ 2) := by
    calc
      _ = (2 * √(p₀ * p₃)) * (2 * √(r₀ * r₃)) := by ring
      _ = _ := by rw [har, hcr]; ring
  have h12 : 4 * √(p₁ * p₂) * √(r₁ * r₂) =
      (1 - x) * (1 - y) * √(1 - b ^ 2) * √(1 - d ^ 2) := by
    calc
      _ = (2 * √(p₁ * p₂)) * (2 * √(r₁ * r₂)) := by ring
      _ = _ := by rw [hbr, hdr]; ring
  change -(2 / 27 : ℝ) ≤ x * y + (p₁ + p₂) * (r₁ + r₂) +
    (p₀ - p₃) * (p₁ - p₂) + (r₀ - r₃) * (r₁ - r₂) -
    4 * √(p₀ * p₃) * √(r₀ * r₃) - 4 * √(p₁ * p₂) * √(r₁ * r₂)
  rw [hpx, hry, h03, h12]
  refine (normalized_mixed_lower hx hy ha hb hc hd).trans ?_
  let residual := x * y + (1 - x) * (1 - y) - x * y * √(1 - a ^ 2) * √(1 - c ^ 2) -
    (1 - x) * (1 - y) * √(1 - b ^ 2) * √(1 - d ^ 2)
  calc
    _ = residual + (-x * (1 - x) * a * b + -y * (1 - y) * c * d) := by dsimp [residual]; ring
    _ ≤ residual + ((p₀ - p₃) * (p₁ - p₂) + (r₀ - r₃) * (r₁ - r₂)) :=
      add_le_add_left (add_le_add hpp hrr) residual
    _ = _ := by dsimp [residual]; ring

/-- The canonical mixed-facet polynomial on a pair of real unit quaternions
has value at least −2/27. -/
theorem mixed_quaternion_lower {q₀ q₁ q₂ q₃ r₀ r₁ r₂ r₃ : ℝ}
    (hq : q₀ ^ 2 + q₁ ^ 2 + q₂ ^ 2 + q₃ ^ 2 = 1)
    (hr : r₀ ^ 2 + r₁ ^ 2 + r₂ ^ 2 + r₃ ^ 2 = 1) :
    -(2 / 27 : ℝ) ≤
      2 * ((q₀ * r₃ - q₃ * r₀) ^ 2 + (q₁ * r₂ + q₂ * r₁) ^ 2) +
      (q₀ ^ 2 + q₁ ^ 2 + r₀ ^ 2 + r₁ ^ 2 - 1) ^ 2 -
      (r₀ ^ 2 + r₂ ^ 2 - q₀ ^ 2 - q₂ ^ 2) ^ 2 := by
  have h03 : q₀ * q₃ * (r₀ * r₃) ≤ √(q₀ ^ 2 * q₃ ^ 2) * √(r₀ ^ 2 * r₃ ^ 2) := by
    rw [← mul_pow, ← mul_pow, Real.sqrt_sq_eq_abs, Real.sqrt_sq_eq_abs, ← abs_mul]
    exact le_abs_self _
  have h12 : -(√(q₁ ^ 2 * q₂ ^ 2) * √(r₁ ^ 2 * r₂ ^ 2)) ≤ q₁ * q₂ * (r₁ * r₂) := by
    rw [← mul_pow, ← mul_pow, Real.sqrt_sq_eq_abs, Real.sqrt_sq_eq_abs, ← abs_mul]
    exact neg_abs_le _
  have hd : q₀ ^ 2 + q₁ ^ 2 + r₀ ^ 2 + r₁ ^ 2 - 1 =
      ((q₀ ^ 2 - q₃ ^ 2) + (q₁ ^ 2 - q₂ ^ 2) + (r₀ ^ 2 - r₃ ^ 2) +
        (r₁ ^ 2 - r₂ ^ 2)) / 2 := by linarith only [hq, hr]
  have hv : r₀ ^ 2 + r₂ ^ 2 - q₀ ^ 2 - q₂ ^ 2 =
      ((r₀ ^ 2 - r₃ ^ 2) - (r₁ ^ 2 - r₂ ^ 2) - (q₀ ^ 2 - q₃ ^ 2) +
        (q₁ ^ 2 - q₂ ^ 2)) / 2 := by linarith only [hq, hr]
  rw [hd, hv]
  linarith only [mixed_probability_lower (sq_nonneg q₀) (sq_nonneg q₁) (sq_nonneg q₂)
    (sq_nonneg q₃) (sq_nonneg r₀) (sq_nonneg r₁) (sq_nonneg r₂) (sq_nonneg r₃) hq hr, h03, h12]

/-- In the basis `1, i, j, k`, the matrix for left multiplication by `q`
and right multiplication by `r`. -/
noncomputable def quaternionRotation (q r : Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![q 0, -q 1, -q 2, -q 3; q 1, q 0, -q 3, q 2;
    q 2, q 3, q 0, -q 1; q 3, -q 2, q 1, q 0] *
  !![r 0, -r 1, -r 2, -r 3; r 1, r 0, r 3, -r 2;
    r 2, -r 3, r 0, r 1; r 3, r 2, -r 1, r 0]

private theorem vec4_zero {α : Type*} (a b c d : α) : ![a, b, c, d] 0 = a := rfl
private theorem vec4_one {α : Type*} (a b c d : α) : ![a, b, c, d] 1 = b := rfl
private theorem vec4_two {α : Type*} (a b c d : α) : ![a, b, c, d] 2 = c := rfl
private theorem vec4_three {α : Type*} (a b c d : α) : ![a, b, c, d] 3 = d := rfl

<<<<<<< HEAD
/-- The squared-entry contribution and three signed two-by-two minors used
in the order-four weighted-mixed inequality. -/
theorem quaternionRotation_mixed_coordinates (q r : Fin 4 → ℝ)
    (hq : q 0 ^ 2 + q 1 ^ 2 + q 2 ^ 2 + q 3 ^ 2 = 1)
    (hr : r 0 ^ 2 + r 1 ^ 2 + r 2 ^ 2 + r 3 ^ 2 = 1) :
    let U := quaternionRotation q r
    U 1 2 ^ 2 + U 2 1 ^ 2 =
      2 * ((q 0 * r 3 - q 3 * r 0) ^ 2 + (q 1 * r 2 + q 2 * r 1) ^ 2) ∧
    U 2 2 * U 3 3 - U 2 3 * U 3 2 = q 0 ^ 2 + q 1 ^ 2 + r 0 ^ 2 + r 1 ^ 2 - 1 ∧
    U 1 1 * U 2 2 - U 1 2 * U 2 1 = 1 - q 1 ^ 2 - q 2 ^ 2 - r 1 ^ 2 - r 2 ^ 2 ∧
    U 1 0 * U 3 2 - U 1 2 * U 3 0 = r 0 ^ 2 + r 2 ^ 2 - q 0 ^ 2 - q 2 ^ 2 := by
=======
/-- The mixed cost is the sum of two squared entries and the difference
of two squared minors in the canonical order-four facet. -/
theorem mixed_quaternion_rotation_lower (q r : Fin 4 → ℝ)
    (hq : q 0 ^ 2 + q 1 ^ 2 + q 2 ^ 2 + q 3 ^ 2 = 1)
    (hr : r 0 ^ 2 + r 1 ^ 2 + r 2 ^ 2 + r 3 ^ 2 = 1) :
    let U := quaternionRotation q r;
    -(2 / 27 : ℝ) ≤ U 1 2 ^ 2 + U 2 1 ^ 2 +
      (U 2 2 * U 3 3 - U 2 3 * U 3 2) ^ 2 -
      (U 1 0 * U 3 2 - U 1 2 * U 3 0) ^ 2 := by
>>>>>>> origin/main
  let U := quaternionRotation q r
  have hentries : U 1 2 ^ 2 + U 2 1 ^ 2 =
      2 * ((q 0 * r 3 - q 3 * r 0) ^ 2 + (q 1 * r 2 + q 2 * r 1) ^ 2) := by
    dsimp [U]
    simp only [quaternionRotation, Matrix.mul_apply, Fin.sum_univ_four, Matrix.of_apply,
      vec4_zero, vec4_one, vec4_two, vec4_three]
    ring
  have hprincipal : U 2 2 * U 3 3 - U 2 3 * U 3 2 =
      q 0 ^ 2 + q 1 ^ 2 + r 0 ^ 2 + r 1 ^ 2 - 1 := by
    calc
      _ = (r 0 ^ 2 + r 1 ^ 2 + r 2 ^ 2 + r 3 ^ 2) * (q 0 ^ 2 + q 1 ^ 2) +
          (q 0 ^ 2 + q 1 ^ 2 + q 2 ^ 2 + q 3 ^ 2) * (r 0 ^ 2 + r 1 ^ 2) -
          (q 0 ^ 2 + q 1 ^ 2 + q 2 ^ 2 + q 3 ^ 2) * (r 0 ^ 2 + r 1 ^ 2 + r 2 ^ 2 + r 3 ^ 2) := by
        dsimp [U]
        simp only [quaternionRotation, Matrix.mul_apply, Fin.sum_univ_four, Matrix.of_apply,
          vec4_zero, vec4_one, vec4_two, vec4_three]
        ring
      _ = _ := by rw [hq, hr]; ring
<<<<<<< HEAD
  have hmiddle : U 1 1 * U 2 2 - U 1 2 * U 2 1 = 1 - q 1 ^ 2 - q 2 ^ 2 - r 1 ^ 2 - r 2 ^ 2 := by
    calc
      _ = (q 0 ^ 2 + q 1 ^ 2 + q 2 ^ 2 + q 3 ^ 2) * (r 0 ^ 2 + r 1 ^ 2 + r 2 ^ 2 + r 3 ^ 2) -
          (r 0 ^ 2 + r 1 ^ 2 + r 2 ^ 2 + r 3 ^ 2) * (q 1 ^ 2 + q 2 ^ 2) -
          (q 0 ^ 2 + q 1 ^ 2 + q 2 ^ 2 + q 3 ^ 2) * (r 1 ^ 2 + r 2 ^ 2) := by
        dsimp [U]
        simp only [quaternionRotation, Matrix.mul_apply, Fin.sum_univ_four, Matrix.of_apply,
          vec4_zero, vec4_one, vec4_two, vec4_three]
        ring
      _ = _ := by rw [hq, hr]; ring
=======
>>>>>>> origin/main
  have hoff : U 1 0 * U 3 2 - U 1 2 * U 3 0 =
      r 0 ^ 2 + r 2 ^ 2 - q 0 ^ 2 - q 2 ^ 2 := by
    calc
      _ = (q 0 ^ 2 + q 1 ^ 2 + q 2 ^ 2 + q 3 ^ 2) * (r 0 ^ 2 + r 2 ^ 2) -
          (r 0 ^ 2 + r 1 ^ 2 + r 2 ^ 2 + r 3 ^ 2) * (q 0 ^ 2 + q 2 ^ 2) := by
        dsimp [U]
        simp only [quaternionRotation, Matrix.mul_apply, Fin.sum_univ_four, Matrix.of_apply,
          vec4_zero, vec4_one, vec4_two, vec4_three]
        ring
      _ = _ := by rw [hq, hr]; ring
<<<<<<< HEAD
  exact ⟨hentries, hprincipal, hmiddle, hoff⟩

/-- The mixed cost is the sum of two squared entries and the difference
of two squared minors in the canonical order-four facet. -/
theorem mixed_quaternion_rotation_lower (q r : Fin 4 → ℝ)
    (hq : q 0 ^ 2 + q 1 ^ 2 + q 2 ^ 2 + q 3 ^ 2 = 1)
    (hr : r 0 ^ 2 + r 1 ^ 2 + r 2 ^ 2 + r 3 ^ 2 = 1) :
    let U := quaternionRotation q r;
    -(2 / 27 : ℝ) ≤ U 1 2 ^ 2 + U 2 1 ^ 2 +
      (U 2 2 * U 3 3 - U 2 3 * U 3 2) ^ 2 -
      (U 1 0 * U 3 2 - U 1 2 * U 3 0) ^ 2 := by
  obtain ⟨hentries, hprincipal, _, hoff⟩ := quaternionRotation_mixed_coordinates q r hq hr
  dsimp only
=======
  change -(2 / 27 : ℝ) ≤ U 1 2 ^ 2 + U 2 1 ^ 2 + _ - _
>>>>>>> origin/main
  rw [hentries, hprincipal, hoff]
  exact mixed_quaternion_lower hq hr

/-- The face average has height at most `H`. The relaxed apex has height
at most `H + (H - L)/6` and occurs with coefficient `-3 * f`. -/
theorem mixed_cap_support_error {H L face apex f : ℝ}
    (hHL : L ≤ H) (hface : face ≤ H) (hapex : apex ≤ H + (H - L) / 6)
    (hfmin : -(2 / 27 : ℝ) ≤ f) (hfmax : f ≤ 0) :
    (1 + 3 * f) * face - 3 * f * apex ≤ H + (H - L) / 27 := by
  have hF : 0 ≤ 1 + 3 * f := by linarith
  have hZ : 0 ≤ -3 * f := by linarith
  have hZmax : -3 * f ≤ 2 / 9 := by linarith
  have h := add_le_add (mul_le_mul_of_nonneg_left hface hF)
    (mul_le_mul_of_nonneg_left hapex hZ)
  have hwidth := mul_le_mul_of_nonneg_right hZmax (sub_nonneg.mpr hHL)
  linarith only [h, hwidth]

end MOC
