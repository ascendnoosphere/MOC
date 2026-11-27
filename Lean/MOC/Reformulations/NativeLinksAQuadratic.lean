import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Data.Real.Sqrt
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace MOC.Reformulations

noncomputable section

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- Half the trace of a normalized hyperbolic quadratic in direction `e`. -/
def quadraticSpectralMean (q : QuadraticForm ℝ E) (e x : E) : ℝ :=
  QuadraticMap.polar q e x / 2

/-- The discriminant divided by four; hyperbolicity makes this nonnegative. -/
def quadraticSpectralVariance (q : QuadraticForm ℝ E) (e x : E) : ℝ :=
  (quadraticSpectralMean q e x) ^ 2 - q x

theorem quadraticPencil_factor (q : QuadraticForm ℝ E) (e : E) (he : q e = 1)
    (x : E) (hx : 0 ≤ quadraticSpectralVariance q e x) (t : ℝ) :
    q (t • e - x) =
      (t - (quadraticSpectralMean q e x + Real.sqrt (quadraticSpectralVariance q e x))) *
      (t - (quadraticSpectralMean q e x - Real.sqrt (quadraticSpectralVariance q e x))) := by
  have h := Real.sq_sqrt hx
  have hq : ∀ a b : E, q (a + b) = q a + q b + QuadraticMap.polar q a b := by
    intro a b
    unfold QuadraticMap.polar
    ring
  rw [sub_eq_add_neg, hq, q.map_smul, he, QuadraticMap.polar_smul_left,
    QuadraticMap.polar_neg_right]
  rw [← neg_one_smul ℝ x, q.map_smul]
  simp only [smul_eq_mul]
  unfold quadraticSpectralVariance quadraticSpectralMean at *
  linear_combination h

/-- The degree-two hyperbolic polynomial bound. With roots (mean ± square root of
the variance), the two matching products bound the actual quadratic
determinant of the sum. This uses no matrix conjecture or lifted labels. -/
theorem hyperbolicQuadratic_matching_bounds (q : QuadraticForm ℝ E) (e x y : E)
    (hHyperbolic : ∀ z : E, 0 ≤ quadraticSpectralVariance q e z) :
    let a := quadraticSpectralMean q e x
    let b := quadraticSpectralMean q e y
    let r := Real.sqrt (quadraticSpectralVariance q e x)
    let s := Real.sqrt (quadraticSpectralVariance q e y)
    ((a + r) + (b + s)) * ((a - r) + (b - s)) ≤ q (x + y) ∧
    q (x + y) ≤ ((a + r) + (b - s)) * ((a - r) + (b + s)) := by
  dsimp
  let a := quadraticSpectralMean q e x
  let b := quadraticSpectralMean q e y
  let V := quadraticSpectralVariance q e x
  let W := quadraticSpectralVariance q e y
  let z := a * b - QuadraticMap.polar q x y / 2
  have hV : 0 ≤ V := hHyperbolic x
  have hW : 0 ≤ W := hHyperbolic y
  have hdiscrim : (2 * z) ^ 2 - 4 * V * W ≤ 0 := by
    apply discrim_le_zero (a := V) (b := 2 * z) (c := W)
    intro t
    have he : quadraticSpectralVariance q e (t • x + y) = V * (t * t) + 2 * z * t + W := by
      dsimp [quadraticSpectralVariance, z, V, W, a, b, quadraticSpectralMean]
      have hq : q (t • x + y) = q (t • x) + q y + QuadraticMap.polar q (t • x) y := by
        unfold QuadraticMap.polar
        ring
      rw [hq, q.map_smul, QuadraticMap.polar_add_right, QuadraticMap.polar_smul_right,
        QuadraticMap.polar_smul_left]
      simp only [smul_eq_mul]
      ring
    exact he ▸ hHyperbolic (t • x + y)
  have hz : |z| ≤ Real.sqrt V * Real.sqrt W := by
    rw [← Real.sqrt_mul hV, ← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (by nlinarith only [hdiscrim])
  obtain ⟨hzlo, hzhi⟩ := abs_le.mp hz
  have hsx := Real.sq_sqrt hV
  have hsy := Real.sq_sqrt hW
  have hq : q (x + y) = (a + b) ^ 2 - (V + W + 2 * z) := by
    dsimp [V, W, z, quadraticSpectralVariance]
    unfold QuadraticMap.polar
    ring
  change ((a + Real.sqrt V) + (b + Real.sqrt W)) *
    ((a - Real.sqrt V) + (b - Real.sqrt W)) ≤ q (x + y) ∧
    q (x + y) ≤ ((a + Real.sqrt V) + (b - Real.sqrt W)) *
    ((a - Real.sqrt V) + (b + Real.sqrt W))
  rw [hq]
  constructor <;> nlinarith only [hzhi, hzlo, hsx, hsy]


/-- The variance condition is equivalent to the actual normalized quadratic
pencil having two real roots, counted with multiplicity. -/
theorem quadraticPencil_hasRealRoots_iff (q : QuadraticForm ℝ E) (e x : E)
    (he : q e = 1) :
    (∃ a b : ℝ, ∀ t : ℝ, q (t • e - x) = (t - a) * (t - b)) ↔
      0 ≤ quadraticSpectralVariance q e x := by
  constructor
  · rintro ⟨a, b, h⟩
    have hq (t : ℝ) : q (t • e - x) = t ^ 2 - 2 * t * quadraticSpectralMean q e x + q x := by
      have hadd : q (t • e + -x) =
          q (t • e) + q (-x) + QuadraticMap.polar q (t • e) (-x) := by
        unfold QuadraticMap.polar
        ring
      rw [sub_eq_add_neg, hadd, q.map_smul, he, QuadraticMap.polar_smul_left,
        QuadraticMap.polar_neg_right, ← neg_one_smul ℝ x, q.map_smul]
      simp only [smul_eq_mul]
      unfold quadraticSpectralMean
      ring
    have hp : q x = a * b := by
      have hz := (hq 0).symm.trans (h 0)
      nlinarith only [hz]
    have hs : 2 * quadraticSpectralMean q e x = a + b := by
      have ho := (hq 1).symm.trans (h 1)
      nlinarith only [hp, ho]
    unfold quadraticSpectralVariance
    nlinarith only [hp, hs, sq_nonneg (a - b),
      congrArg (fun z : ℝ => z ^ 2) hs]
  · intro hx
    refine ⟨quadraticSpectralMean q e x + Real.sqrt (quadraticSpectralVariance q e x),
      quadraticSpectralMean q e x - Real.sqrt (quadraticSpectralVariance q e x),
      quadraticPencil_factor q e he x hx⟩

end

end MOC.Reformulations
