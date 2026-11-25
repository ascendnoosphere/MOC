import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! A four-point cross ratio bounds the spread of the squared spectral moduli. -/

open scoped ComplexConjugate

namespace MOC

noncomputable def spectralCrossRatio (a b c d : ℂ) : ℂ :=
  ((a - c) * (b - d)) / ((a - d) * (b - c))

/-- The cross ratio is invariant under the regular Möbius chart used for spectral transport. -/
theorem spectralCrossRatio_mobius (a b c d t s : ℂ)
    (ha : 1 - t * a ≠ 0) (hb : 1 - t * b ≠ 0) (hc : 1 - t * c ≠ 0)
    (hd : 1 - t * d ≠ 0) :
    let f (z : ℂ) := z / (1 - t * z) + s
    spectralCrossRatio (f a) (f b) (f c) (f d) = spectralCrossRatio a b c d := by
  intro f
  have hdiff (x y : ℂ) (hx : 1 - t * x ≠ 0) (hy : 1 - t * y ≠ 0) :
      f x - f y = (x - y) / ((1 - t * x) * (1 - t * y)) := by
    dsimp only [f]
    field_simp [hx, hy] <;> ring
  unfold spectralCrossRatio
  rw [hdiff a c ha hc, hdiff b d hb hd, hdiff a d ha hd, hdiff b c hb hc,
    div_mul_div_comm, div_mul_div_comm]
  rw [show (1 - t * a) * (1 - t * c) * ((1 - t * b) * (1 - t * d)) =
      (1 - t * a) * (1 - t * d) * ((1 - t * b) * (1 - t * c)) by ring]
  exact div_div_div_cancel_right₀ (mul_ne_zero (mul_ne_zero ha hd) (mul_ne_zero hb hc)) _ _

/-- The imaginary cross product is the signed area expression for four points
with the differences of their squared moduli as coefficients. -/
theorem circle_defect_eq_modulus_differences (a b c d : ℂ) :
    (((a - c) * (b - d)) * conj ((a - d) * (b - c))).im =
      (Complex.normSq b - Complex.normSq a) * ((c - a) * conj (d - a)).im -
      (Complex.normSq c - Complex.normSq a) * ((b - a) * conj (d - a)).im +
      (Complex.normSq d - Complex.normSq a) * ((b - a) * conj (c - a)).im := by
  simp only [Complex.mul_im, Complex.mul_re, Complex.sub_im, Complex.sub_re,
    Complex.conj_im, Complex.conj_re, Complex.normSq_apply]
  ring

/-- A nonreal cross ratio forces a quantitative spread of the squared moduli.
Here `δ` may be taken to be the maximum modulus squared minus the minimum. -/
theorem crossRatio_im_le_modulus_spread (a b c d : ℂ) (δ : ℝ)
    (hnz : (a - d) * (b - c) ≠ 0)
    (hb : |Complex.normSq b - Complex.normSq a| ≤ δ)
    (hc : |Complex.normSq c - Complex.normSq a| ≤ δ)
    (hd : |Complex.normSq d - Complex.normSq a| ≤ δ) :
    |(spectralCrossRatio a b c d).im| * Complex.normSq ((a - d) * (b - c)) ≤
      δ * (|((c - a) * conj (d - a)).im| + |((b - a) * conj (d - a)).im| +
        |((b - a) * conj (c - a)).im|) := by
  let N := (a - c) * (b - d)
  let D := (a - d) * (b - c)
  have hD : Complex.normSq D ≠ 0 := (Complex.normSq_pos.mpr hnz).ne'
  have him : (N / D).im * Complex.normSq D = (N * conj D).im := by
    rw [Complex.div_im, ← sub_div, div_mul_cancel₀ _ hD]
    simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im]
    ring
  change |(N / D).im| * Complex.normSq D ≤ _
  rw [← abs_of_nonneg (Complex.normSq_nonneg D), ← abs_mul, him]
  dsimp only [N, D]
  rw [circle_defect_eq_modulus_differences]
  let x := (Complex.normSq b - Complex.normSq a) * ((c - a) * conj (d - a)).im
  let y := (Complex.normSq c - Complex.normSq a) * ((b - a) * conj (d - a)).im
  let z := (Complex.normSq d - Complex.normSq a) * ((b - a) * conj (c - a)).im
  change |x - y + z| ≤ _
  calc
    _ ≤ |x - y| + |z| := abs_add_le _ _
    _ ≤ |x| + |y| + |z| := add_le_add_right (abs_sub _ _) _
    _ ≤ δ * |((c - a) * conj (d - a)).im| +
        δ * |((b - a) * conj (d - a)).im| +
        δ * |((b - a) * conj (c - a)).im| := by
      dsimp only [x, y, z]
      simp only [abs_mul]
      exact add_le_add
        (add_le_add (mul_le_mul_of_nonneg_right hb (abs_nonneg _))
          (mul_le_mul_of_nonneg_right hc (abs_nonneg _)))
        (mul_le_mul_of_nonneg_right hd (abs_nonneg _))
    _ = _ := by ring

end MOC
