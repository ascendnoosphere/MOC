import MOC.Small
import MOC.Support
import MOC.TwoValues
import Mathlib.Data.Fintype.Perm
import Mathlib.Algebra.Polynomial.Eval.Defs

/-! An order-four spectral family with a free real parameter.
The nine-edge certificate is checked with integer polynomials. -/

open BigOperators Matrix Polynomial
open scoped Topology Polynomial

namespace MOC

noncomputable section

/-- The first spectrum of the real-parameter family. -/
def fourRealParameterLeft (t : ℝ) : Fin 4 → ℂ :=
  ![(t : ℂ) + Complex.I, -(t : ℂ) + Complex.I, 1, 2 + Complex.I]

/-- The fixed spectrum of the real-parameter family. -/
def fourRealParameterRight : Fin 4 → ℂ :=
  ![-1 + Complex.I, -2 - 2 * Complex.I, 2 - Complex.I, 1 + 2 * Complex.I]

private def planeCross (u v : ℂ) : ℝ :=
  u.re * v.im - u.im * v.re

private theorem planeCross_edge_direction (a b z : ℂ) :
    planeCross (b - a) (z - a) =
      ((⟨-(b - a).im, -(b - a).re⟩ : ℂ) * z).re -
        ((⟨-(b - a).im, -(b - a).re⟩ : ℂ) * a).re := by
  simp only [planeCross, Complex.sub_re, Complex.sub_im, Complex.mul_re]
  ring

/-- At a projection-maximizing vertex with a positive turn, its two incident
edge inequalities bound that projection of the test point. -/
private theorem planeProjection_le_of_incident_edges (u v w z η : ℂ)
    (ht : 0 < planeCross (v - u) (w - v))
    (hin : 0 ≤ planeCross (v - u) (z - u))
    (hout : 0 ≤ planeCross (w - v) (z - v))
    (hu : (η * u).re ≤ (η * v).re) (hw : (η * w).re ≤ (η * v).re) :
    (η * z).re ≤ (η * v).re := by
  let d := u - v
  let e := w - v
  let y := z - v
  have hdet : planeCross e d = planeCross (v - u) (w - v) := by
    simp only [e, d, planeCross, Complex.sub_re, Complex.sub_im]
    ring
  have hbefore : -planeCross d y = planeCross (v - u) (z - u) := by
    simp only [d, y, planeCross, Complex.sub_re, Complex.sub_im]
    ring
  have hleft : 0 ≤ -planeCross d y := hbefore.symm ▸ hin
  have hd : (η * d).re ≤ 0 := by
    simpa only [d, mul_sub, Complex.sub_re, sub_nonpos] using hu
  have he : (η * e).re ≤ 0 := by
    simpa only [e, mul_sub, Complex.sub_re, sub_nonpos] using hw
  have hidentity : planeCross e d * (η * y).re =
      planeCross e y * (η * d).re + (-planeCross d y) * (η * e).re := by
    simp only [planeCross, Complex.mul_re]
    ring
  have hmul : planeCross e d * (η * y).re ≤ planeCross e d * 0 := by
    rw [hidentity, mul_zero]
    exact add_nonpos (mul_nonpos_of_nonneg_of_nonpos hout hd)
      (mul_nonpos_of_nonneg_of_nonpos hleft he)
  have hy := (mul_le_mul_left (hdet.symm ▸ ht)).mp hmul
  simpa only [y, mul_sub, Complex.sub_re, sub_nonpos] using hy

/-- If each vertex has two incident supporting edges with positive turn,
meeting all their half-planes suffices for membership in the vertex hull. -/
private theorem mem_planeHull_of_edges {ι : Type*} [Fintype ι] [Nonempty ι]
    (v : ι → ℂ) (prev next : ι → ι) (z : ℂ) (hcycle : ∀ i, next (prev i) = i)
    (hturn : ∀ i, 0 < planeCross (v i - v (prev i)) (v (next i) - v i))
    (hedge : ∀ i, 0 ≤ planeCross (v (next i) - v i) (z - v i)) :
    z ∈ convexHull ℝ (Set.range v) := by
  apply mem_hull_of_directional_bound v z
  intro η
  obtain ⟨i, _, hmax⟩ := Finset.exists_max_image Finset.univ
    (fun i => (η * v i).re) Finset.univ_nonempty
  have hin := hedge (prev i)
  rw [hcycle i] at hin
  exact ⟨i, planeProjection_le_of_incident_edges (v (prev i)) (v i) (v (next i)) z η
    (hturn i) hin (hedge i) (hmax (prev i) (Finset.mem_univ _)) (hmax (next i) (Finset.mem_univ _))⟩

private abbrev ParameterPermutation := Equiv.Perm (Fin 4)

-- The one-line images are lexicographically ordered as row-to-column maps.
private def parameterPermutation (i : Fin 24) : ParameterPermutation :=
  ![1,
    Equiv.swap 2 3,
    Equiv.swap 1 2,
    Equiv.swap 1 3 * Equiv.swap 1 2,
    Equiv.swap 2 1 * Equiv.swap 1 3,
    Equiv.swap 1 3,
    Equiv.swap 0 1,
    Equiv.swap 2 3 * Equiv.swap 0 1,
    Equiv.swap 0 2 * Equiv.swap 0 1,
    Equiv.swap 0 3 * Equiv.swap 0 2 * Equiv.swap 0 1,
    Equiv.swap 2 0 * Equiv.swap 0 3 * Equiv.swap 0 1,
    Equiv.swap 0 3 * Equiv.swap 0 1,
    Equiv.swap 1 0 * Equiv.swap 0 2,
    Equiv.swap 1 3 * Equiv.swap 1 0 * Equiv.swap 0 2,
    Equiv.swap 0 2,
    Equiv.swap 0 3 * Equiv.swap 0 2,
    Equiv.swap 1 3 * Equiv.swap 0 2,
    Equiv.swap 0 1 * Equiv.swap 1 3 * Equiv.swap 0 2,
    Equiv.swap 2 1 * Equiv.swap 1 0 * Equiv.swap 0 3,
    Equiv.swap 1 0 * Equiv.swap 0 3,
    Equiv.swap 2 0 * Equiv.swap 0 3,
    Equiv.swap 0 3,
    Equiv.swap 1 0 * Equiv.swap 1 2 * Equiv.swap 0 3,
    Equiv.swap 1 2 * Equiv.swap 0 3] i

private def parameterPermutationIndex (σ : ParameterPermutation) : Fin 24 :=
  let a := (σ 0).val
  let b := (σ 1).val
  let c := (σ 2).val
  let k := 6 * a + 2 * (b - if a < b then 1 else 0) +
    (c - (if a < c then 1 else 0) - (if b < c then 1 else 0))
  ⟨k % 24, Nat.mod_lt _ (by decide)⟩

private theorem parameterPermutation_surjective : Function.Surjective parameterPermutation := by
  have hleft : Function.LeftInverse parameterPermutationIndex parameterPermutation := by
    change ∀ i : Fin 24, parameterPermutationIndex (parameterPermutation i) = i
    decide +kernel
  have hcards : Fintype.card (Fin 24) = Fintype.card ParameterPermutation := by
    rw [Fintype.card_perm, Fintype.card_fin, Fintype.card_fin]
    decide
  exact (Finite.injective_iff_surjective_of_equiv (Fintype.equivOfCardEq hcards)).mp hleft.injective

private abbrev IntegerPlanePolynomial := ℤ[X] × ℤ[X]

private def polynomialPlaneMul (a b : IntegerPlanePolynomial) : IntegerPlanePolynomial :=
  (a.1 * b.1 - a.2 * b.2, a.1 * b.2 + a.2 * b.1)

private def polynomialPlaneSub (a b : IntegerPlanePolynomial) : IntegerPlanePolynomial :=
  (a.1 - b.1, a.2 - b.2)

private def polynomialPlaneCross (a b : IntegerPlanePolynomial) : ℤ[X] :=
  a.1 * b.2 - a.2 * b.1

private def evaluateParameterPolynomial (t : ℝ) : ℤ[X] →+* ℝ :=
  Polynomial.eval₂RingHom (Int.castRingHom ℝ) t

private def evaluateParameterPlane (t : ℝ) (a : IntegerPlanePolynomial) : ℂ :=
  ⟨evaluateParameterPolynomial t a.1, evaluateParameterPolynomial t a.2⟩

private theorem evaluateParameterPlane_mul (t : ℝ) (a b : IntegerPlanePolynomial) :
    evaluateParameterPlane t (polynomialPlaneMul a b) =
      evaluateParameterPlane t a * evaluateParameterPlane t b := by
  apply Complex.ext
  · simp only [evaluateParameterPlane, polynomialPlaneMul, map_sub, map_mul, Complex.mul_re]
  · simp only [evaluateParameterPlane, polynomialPlaneMul, map_add, map_mul, Complex.mul_im]

private theorem evaluateParameterPlane_sub (t : ℝ) (a b : IntegerPlanePolynomial) :
    evaluateParameterPlane t (polynomialPlaneSub a b) =
      evaluateParameterPlane t a - evaluateParameterPlane t b := by
  apply Complex.ext
  · simp only [evaluateParameterPlane, polynomialPlaneSub, map_sub, Complex.sub_re]
  · simp only [evaluateParameterPlane, polynomialPlaneSub, map_sub, Complex.sub_im]

private theorem evaluateParameterPlane_cross (t : ℝ) (a b : IntegerPlanePolynomial) :
    evaluateParameterPolynomial t (polynomialPlaneCross a b) =
      planeCross (evaluateParameterPlane t a) (evaluateParameterPlane t b) := by
  simp only [evaluateParameterPlane, polynomialPlaneCross, planeCross, map_mul, map_sub]

private def parameterPairSum (i j : Fin 4) : IntegerPlanePolynomial :=
  (![X, -X, 1, 2] i + ![-1, -2, 2, 1] j, ![1, 1, 0, 1] i + ![1, -2, -1, 2] j)

private theorem evaluateParameterPairSum (t : ℝ) (i j : Fin 4) :
    evaluateParameterPlane t (parameterPairSum i j) =
      fourRealParameterLeft t i + fourRealParameterRight j := by
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    norm_num [evaluateParameterPlane, evaluateParameterPolynomial, parameterPairSum,
      fourRealParameterLeft, fourRealParameterRight, Complex.mul_re, Complex.mul_im] <;> ring

private def parameterVertex (p : ParameterPermutation) : IntegerPlanePolynomial :=
  polynomialPlaneMul
    (polynomialPlaneMul (parameterPairSum (p 0) 0) (parameterPairSum (p 1) 1))
    (polynomialPlaneMul (parameterPairSum (p 2) 2) (parameterPairSum (p 3) 3))

private theorem evaluateParameterVertex (t : ℝ) (p : ParameterPermutation) :
    evaluateParameterPlane t (parameterVertex p) =
      matchingProduct (fourRealParameterLeft t) fourRealParameterRight p := by
  simp only [parameterVertex, evaluateParameterPlane_mul, evaluateParameterPairSum,
    matchingProduct, Fin.prod_univ_four, mul_assoc]

private def parameterPrev : Fin 9 → Fin 9 := ![8, 0, 1, 2, 3, 4, 5, 6, 7]

private def parameterNext : Fin 9 → Fin 9 := ![1, 2, 3, 4, 5, 6, 7, 8, 0]

private def parameterHullIndex : Fin 9 → Fin 24 := ![16, 22, 15, 21, 0, 6, 7, 18, 19]

private def parameterHullVertex (i : Fin 9) : IntegerPlanePolynomial :=
  parameterVertex (parameterPermutation (parameterHullIndex i)).symm

private def parameterEdgePolynomial (i : Fin 9) (p : IntegerPlanePolynomial) : ℤ[X] :=
  polynomialPlaneCross
    (polynomialPlaneSub (parameterHullVertex (parameterNext i)) (parameterHullVertex i))
    (polynomialPlaneSub p (parameterHullVertex i))

-- A positive first coefficient times (X^power), with at most four residual powers.
private structure ParameterWeight where
  power : ℕ
  constant : ℤ
  linear : ℤ
  quadratic : ℤ
  cubic : ℤ
  quartic : ℤ

private def ParameterWeight.polynomial (w : ParameterWeight) : ℤ[X] :=
  X ^ w.power * (C w.constant + C w.linear * X + C w.quadratic * X ^ 2 +
    C w.cubic * X ^ 3 + C w.quartic * X ^ 4)

private def ParameterWeight.lowerNumerator (w : ParameterWeight) : ℤ :=
  160000 * w.constant + 8000 * min w.linear 0 + 400 * min w.quadratic 0 +
    20 * min w.cubic 0 + min w.quartic 0

private theorem signedMonomialLower (m : ℤ) {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    ((min m 0 : ℤ) : ℝ) * y ≤ (m : ℝ) * x := by
  have hsign : ((min m 0 : ℤ) : ℝ) ≤ 0 := by exact_mod_cast min_le_right m (0 : ℤ)
  have hmin : ((min m 0 : ℤ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast min_le_left m (0 : ℤ)
  exact (mul_le_mul_of_nonpos_left hxy hsign).trans (mul_le_mul_of_nonneg_right hmin hx)

private theorem parameterWeight_sign (w : ParameterWeight) (h : 0 < w.lowerNumerator)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1 / 20) :
    0 < (w.constant : ℝ) + (w.linear : ℝ) * t + (w.quadratic : ℝ) * t ^ 2 +
      (w.cubic : ℝ) * t ^ 3 + (w.quartic : ℝ) * t ^ 4 := by
  have hm₁ := signedMonomialLower w.linear ht0 ht1
  have hm₂ := signedMonomialLower w.quadratic (pow_nonneg ht0 2) (pow_le_pow_left₀ ht0 ht1 2)
  have hm₃ := signedMonomialLower w.cubic (pow_nonneg ht0 3) (pow_le_pow_left₀ ht0 ht1 3)
  have hm₄ := signedMonomialLower w.quartic (pow_nonneg ht0 4) (pow_le_pow_left₀ ht0 ht1 4)
  have hi : (0 : ℝ) < 160000 * (w.constant : ℝ) + 8000 * ((min w.linear 0 : ℤ) : ℝ) +
      400 * ((min w.quadratic 0 : ℤ) : ℝ) + 20 * ((min w.cubic 0 : ℤ) : ℝ) +
      ((min w.quartic 0 : ℤ) : ℝ) := by
    unfold ParameterWeight.lowerNumerator at h
    exact_mod_cast h
  norm_num at hm₂ hm₃ hm₄
  linarith only [hi, hm₁, hm₂, hm₃, hm₄]

private theorem evaluateParameterWeight (t : ℝ) (w : ParameterWeight) :
    evaluateParameterPolynomial t w.polynomial =
      t ^ w.power * ((w.constant : ℝ) + (w.linear : ℝ) * t + (w.quadratic : ℝ) * t ^ 2 +
        (w.cubic : ℝ) * t ^ 3 + (w.quartic : ℝ) * t ^ 4) := by
  simp [ParameterWeight.polynomial, evaluateParameterPolynomial]

private structure ParameterMinorTerm where
  rows : Finset (Fin 4)
  columns : Finset (Fin 4)
  weight : ParameterWeight

private def parameterTerms : Fin 9 → Fin 12 → ParameterMinorTerm :=
 ![
  ![⟨{0}, {0}, ⟨1, 24, -8, -2, 0, 0⟩⟩,
    ⟨{1}, {0}, ⟨1, 24, 8, -2, 0, 0⟩⟩,
    ⟨{1}, {1}, ⟨2, 144, 0, 0, 0, 0⟩⟩,
    ⟨{2}, {1}, ⟨1, 40, 40, 50, 0, 0⟩⟩,
    ⟨{2}, {2}, ⟨1, 20, 0, 20, 0, 0⟩⟩,
    ⟨{3}, {0}, ⟨1, 56, -104, 6, 0, 0⟩⟩,
    ⟨{3}, {2}, ⟨1, 152, -72, -2, 0, 0⟩⟩,
    ⟨{3}, {3}, ⟨1, 72, -72, 18, 0, 0⟩⟩,
    ⟨{0, 1}, {0, 1}, ⟨1, 152, -32, -54, 0, 0⟩⟩,
    ⟨{0, 2}, {1, 2}, ⟨1, 80, 144, -60, 0, 0⟩⟩,
    ⟨{0, 2}, {1, 3}, ⟨2, 64, 0, 0, 0, 0⟩⟩,
    ⟨{0, 3}, {0, 3}, ⟨1, 80, -80, -60, 0, 0⟩⟩],
  ![⟨{0}, {0}, ⟨0, 160, 16, -32, -8, 0⟩⟩,
    ⟨{1}, {0}, ⟨0, 160, 272, 152, 28, 0⟩⟩,
    ⟨{1}, {3}, ⟨1, 56, 40, 6, 0, 0⟩⟩,
    ⟨{2}, {1}, ⟨0, 640, 400, 360, 240, 60⟩⟩,
    ⟨{2}, {2}, ⟨0, 180, 102, 106, 67, 21⟩⟩,
    ⟨{3}, {2}, ⟨0, 640, 240, -64, -96, -6⟩⟩,
    ⟨{3}, {3}, ⟨0, 200, -52, -38, -23, 15⟩⟩,
    ⟨{0, 1}, {0, 1}, ⟨0, 640, 664, 8, -130, -60⟩⟩,
    ⟨{0, 2}, {1, 2}, ⟨0, 160, 624, 160, -136, -60⟩⟩,
    ⟨{0, 2}, {1, 3}, ⟨1, 64, 40, -36, 0, 0⟩⟩,
    ⟨{0, 3}, {0, 3}, ⟨0, 160, -320, -520, -280, -60⟩⟩,
    ⟨{0, 3}, {2, 3}, ⟨1, 456, 336, 126, 0, 0⟩⟩],
  ![⟨{0}, {0}, ⟨0, 140, -158, 62, 17, -13⟩⟩,
    ⟨{0}, {1}, ⟨1, 600, -760, -280, 0, 0⟩⟩,
    ⟨{1}, {0}, ⟨0, 140, 642, -298, -263, -13⟩⟩,
    ⟨{2}, {1}, ⟨0, 700, -190, -450, -195, -65⟩⟩,
    ⟨{3}, {1}, ⟨0, 340, -658, -286, -69, -39⟩⟩,
    ⟨{3}, {2}, ⟨0, 560, -332, -92, 28, -12⟩⟩,
    ⟨{3}, {3}, ⟨0, 260, -422, 78, 78, -22⟩⟩,
    ⟨{0, 1}, {0, 1}, ⟨0, 220, 86, -98, 55, 49⟩⟩,
    ⟨{0, 1}, {0, 3}, ⟨0, 200, -140, 20, 50, -10⟩⟩,
    ⟨{0, 2}, {0, 2}, ⟨1, 540, -208, -184, 0, 0⟩⟩,
    ⟨{0, 2}, {0, 3}, ⟨1, 440, -128, -144, 0, 0⟩⟩,
    ⟨{0, 2}, {1, 2}, ⟨1, 700, 0, -200, 0, 0⟩⟩],
  ![⟨{0}, {2}, ⟨1, 192, -8, -44, 0, 0⟩⟩,
    ⟨{1}, {0}, ⟨1, 2240, -160, -480, 0, 0⟩⟩,
    ⟨{2}, {1}, ⟨0, 1220, 794, -168, -145, -61⟩⟩,
    ⟨{3}, {1}, ⟨0, 1620, 674, -228, -195, -31⟩⟩,
    ⟨{3}, {2}, ⟨0, 700, 30, -194, -34, 18⟩⟩,
    ⟨{0, 1}, {0, 2}, ⟨0, 120, -2020, 190, 425, -15⟩⟩,
    ⟨{0, 1}, {0, 3}, ⟨0, 380, -1914, 88, 425, -19⟩⟩,
    ⟨{0, 1}, {1, 2}, ⟨0, 620, -146, -158, 10, 14⟩⟩,
    ⟨{0, 2}, {0, 1}, ⟨0, 400, 1520, -220, -280, -20⟩⟩,
    ⟨{0, 2}, {1, 2}, ⟨1, 160, 160, -120, 0, 0⟩⟩,
    ⟨{0, 3}, {0, 1}, ⟨1, 1840, -160, -380, 0, 0⟩⟩,
    ⟨{0, 3}, {2, 3}, ⟨0, 400, 320, -20, -80, -20⟩⟩],
  ![⟨{0}, {2}, ⟨1, 360, -912, -276, 0, 0⟩⟩,
    ⟨{0}, {3}, ⟨1, 840, -1920, -852, 0, 0⟩⟩,
    ⟨{1}, {2}, ⟨1, 360, -1008, -276, 0, 0⟩⟩,
    ⟨{1}, {3}, ⟨1, 840, -1920, -852, 0, 0⟩⟩,
    ⟨{2}, {0}, ⟨2, 960, 480, 0, 0, 0⟩⟩,
    ⟨{2}, {3}, ⟨1, 600, -960, -312, 0, 0⟩⟩,
    ⟨{3}, {0}, ⟨1, 1560, 1920, 252, 0, 0⟩⟩,
    ⟨{3}, {1}, ⟨1, 3960, 1920, -348, 0, 0⟩⟩,
    ⟨{0, 1}, {1, 2}, ⟨1, 1440, -960, -840, 0, 0⟩⟩,
    ⟨{0, 2}, {0, 1}, ⟨1, 2160, 2160, -660, 0, 0⟩⟩,
    ⟨{0, 2}, {1, 3}, ⟨2, 1920, 0, 0, 0, 0⟩⟩,
    ⟨{0, 3}, {2, 3}, ⟨1, 2160, -240, -660, 0, 0⟩⟩],
  ![⟨{0}, {3}, ⟨1, 620, 80, -140, 0, 0⟩⟩,
    ⟨{1}, {1}, ⟨2, 960, -192, 0, 0, 0⟩⟩,
    ⟨{2}, {0}, ⟨0, 600, -1060, -552, 260, 32⟩⟩,
    ⟨{3}, {0}, ⟨0, 500, -590, 176, -96, 58⟩⟩,
    ⟨{3}, {1}, ⟨0, 500, -70, 656, -236, 14⟩⟩,
    ⟨{0, 1}, {0, 2}, ⟨0, 300, -990, 6, -66, 78⟩⟩,
    ⟨{0, 1}, {0, 3}, ⟨0, 200, -1700, -64, 84, 88⟩⟩,
    ⟨{0, 1}, {1, 2}, ⟨0, 300, 10, -90, 10, 10⟩⟩,
    ⟨{0, 2}, {0, 1}, ⟨1, 1020, 480, -300, 0, 0⟩⟩,
    ⟨{0, 2}, {0, 2}, ⟨1, 600, 0, -120, 0, 0⟩⟩,
    ⟨{0, 2}, {2, 3}, ⟨0, 200, 440, -610, 202, -40⟩⟩,
    ⟨{0, 3}, {0, 1}, ⟨0, 200, 560, -370, 130, -40⟩⟩],
  ![⟨{0}, {2}, ⟨0, 560, -1296, 124, -56, 124⟩⟩,
    ⟨{1}, {1}, ⟨1, 640, -640, -1280, 0, 0⟩⟩,
    ⟨{1}, {2}, ⟨0, 560, 576, -508, -80, 124⟩⟩,
    ⟨{2}, {0}, ⟨0, 320, -320, 80, 80, -40⟩⟩,
    ⟨{2}, {2}, ⟨0, 200, -1080, 16, -56, 88⟩⟩,
    ⟨{3}, {0}, ⟨0, 720, 400, -380, -320, -60⟩⟩,
    ⟨{3}, {1}, ⟨0, 2000, -560, 260, -480, -100⟩⟩,
    ⟨{0, 1}, {1, 2}, ⟨0, 1600, -1600, 400, 400, -200⟩⟩,
    ⟨{0, 1}, {1, 3}, ⟨0, 1280, -800, 80, 320, -40⟩⟩,
    ⟨{0, 2}, {0, 1}, ⟨1, 1440, -640, -480, 0, 0⟩⟩,
    ⟨{0, 2}, {0, 2}, ⟨1, 1760, -560, 80, 0, 0⟩⟩,
    ⟨{0, 2}, {2, 3}, ⟨1, 1360, -360, 280, 0, 0⟩⟩],
  ![⟨{0}, {0}, ⟨1, 300, 40, 52, 0, 0⟩⟩,
    ⟨{0}, {1}, ⟨0, 100, -850, 290, -55, 55⟩⟩,
    ⟨{1}, {1}, ⟨0, 100, 918, 698, 217, 55⟩⟩,
    ⟨{2}, {0}, ⟨0, 180, 54, 14, -11, -1⟩⟩,
    ⟨{3}, {0}, ⟨0, 1180, 366, -86, -33, -23⟩⟩,
    ⟨{3}, {3}, ⟨0, 700, 102, -162, -46, -26⟩⟩,
    ⟨{0, 1}, {0, 1}, ⟨0, 2100, 570, -374, -201, -67⟩⟩,
    ⟨{0, 1}, {0, 2}, ⟨0, 160, -76, -84, -52, -12⟩⟩,
    ⟨{0, 1}, {1, 3}, ⟨0, 920, 136, -256, -98, -38⟩⟩,
    ⟨{0, 2}, {0, 1}, ⟨1, 340, 0, 68, 0, 0⟩⟩,
    ⟨{0, 2}, {0, 3}, ⟨1, 172, 32, 28, 0, 0⟩⟩,
    ⟨{0, 2}, {1, 2}, ⟨1, 268, 208, 12, 0, 0⟩⟩],
  ![⟨{0}, {0}, ⟨1, 60, 8, 34, 0, 0⟩⟩,
    ⟨{0}, {1}, ⟨0, 280, -172, 86, -38, 18⟩⟩,
    ⟨{1}, {1}, ⟨0, 280, 344, 206, 88, 18⟩⟩,
    ⟨{2}, {1}, ⟨0, 40, 36, 54, 10, 6⟩⟩,
    ⟨{2}, {3}, ⟨0, 20, -22, -30, -21, -7⟩⟩,
    ⟨{3}, {0}, ⟨0, 40, 20, 58, -6, 10⟩⟩,
    ⟨{3}, {2}, ⟨0, 140, 18, -40, -21, -7⟩⟩,
    ⟨{0, 1}, {0, 1}, ⟨0, 420, 94, -14, -51, -9⟩⟩,
    ⟨{0, 2}, {0, 3}, ⟨1, 44, 8, 18, 0, 0⟩⟩,
    ⟨{0, 2}, {1, 2}, ⟨0, 360, 176, -28, -48, -30⟩⟩,
    ⟨{0, 3}, {0, 2}, ⟨1, 20, -8, 46, 0, 0⟩⟩,
    ⟨{0, 3}, {0, 3}, ⟨0, 360, -40, -108, -4, -30⟩⟩]]

private def parameterTurnWeight : Fin 9 → ParameterWeight :=
  ![⟨1, 44, 8, 18, 0, 0⟩,
    ⟨1, 56, 40, 6, 0, 0⟩,
    ⟨0, 340, -218, -414, -213, -39⟩,
    ⟨0, 620, 46, -166, -34, 14⟩,
    ⟨1, 2400, 0, -600, 0, 0⟩,
    ⟨1, 600, 960, -312, 0, 0⟩,
    ⟨0, 200, -1080, 16, -56, 88⟩,
    ⟨0, 2200, -280, -84, -256, -12⟩,
    ⟨0, 180, 54, 14, -11, -1⟩]

private def parameterMinorPolynomial (i : Fin 9) (p : ParameterPermutation) : ℤ[X] :=
  ∑ j : Fin 12,
    let term := parameterTerms i j
    if term.columns.map p.toEmbedding = term.rows then term.weight.polynomial else 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem parameterEdgePolynomial_eq (i : Fin 9) (p : ParameterPermutation) :
    parameterEdgePolynomial i (parameterVertex p) = parameterMinorPolynomial i p := by
  obtain ⟨j, hj⟩ := parameterPermutation_surjective p.symm
  have hp : p = (parameterPermutation j).symm := by
    rw [hj, Equiv.symm_symm]
  rw [hp]
  fin_cases i <;> fin_cases j <;> decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
private theorem parameterTurnPolynomial_eq (i : Fin 9) :
    polynomialPlaneCross
        (polynomialPlaneSub (parameterHullVertex i) (parameterHullVertex (parameterPrev i)))
        (polynomialPlaneSub (parameterHullVertex (parameterNext i)) (parameterHullVertex i)) =
      (parameterTurnWeight i).polynomial := by
  fin_cases i <;> decide +kernel

private theorem parameterWeight_lower (i : Fin 9) (j : Fin 12) :
    0 < (parameterTerms i j).weight.lowerNumerator :=
  (by decide +kernel : ∀ k l, 0 < (parameterTerms k l).weight.lowerNumerator) i j

private theorem parameterTurn_lower (i : Fin 9) :
    0 < (parameterTurnWeight i).lowerNumerator :=
  (by decide +kernel : ∀ k, 0 < (parameterTurnWeight k).lowerNumerator) i

private def parameterHull (t : ℝ) (i : Fin 9) : ℂ :=
  matchingProduct (fourRealParameterLeft t) fourRealParameterRight
    (parameterPermutation (parameterHullIndex i)).symm

private theorem evaluateParameterHullVertex (t : ℝ) (i : Fin 9) :
    evaluateParameterPlane t (parameterHullVertex i) = parameterHull t i :=
  evaluateParameterVertex t (parameterPermutation (parameterHullIndex i)).symm

private theorem parameterHull_turn (t : ℝ) (ht0 : 0 < t) (ht1 : t ≤ 1 / 20) (i : Fin 9) :
    0 < planeCross (parameterHull t i - parameterHull t (parameterPrev i))
      (parameterHull t (parameterNext i) - parameterHull t i) := by
  have he := congrArg (evaluateParameterPolynomial t) (parameterTurnPolynomial_eq i)
  simp only [evaluateParameterPlane_cross, evaluateParameterPlane_sub,
    evaluateParameterHullVertex] at he
  rw [he, evaluateParameterWeight]
  exact mul_pos (pow_pos ht0 _) (parameterWeight_sign (parameterTurnWeight i)
    (parameterTurn_lower i) t ht0.le ht1)

private theorem parameterHull_edge (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1 / 20)
    (U : Matrix (Fin 4) (Fin 4) ℂ) (hU : IsUnitary U) (i : Fin 9) :
    0 ≤ planeCross (parameterHull t (parameterNext i) - parameterHull t i)
      (determinantValue (fourRealParameterLeft t) fourRealParameterRight U - parameterHull t i) := by
  let l := parameterHull t i
  let r := parameterHull t (parameterNext i)
  let η : ℂ := ⟨-(r - l).im, -(r - l).re⟩
  let w (j : Fin 12) := evaluateParameterPolynomial t (parameterTerms i j).weight.polynomial
  have hw (j : Fin 12) : 0 ≤ w j := by
    dsimp only [w]
    rw [evaluateParameterWeight]
    exact mul_nonneg (pow_nonneg ht0 _) (parameterWeight_sign (parameterTerms i j).weight
      (parameterWeight_lower i j) t ht0 ht1).le
  have hidentity (p : ParameterPermutation) :
      (η * matchingProduct (fourRealParameterLeft t) fourRealParameterRight p).re -
          (η * l).re =
        ∑ j, if (parameterTerms i j).columns.map p.toEmbedding = (parameterTerms i j).rows
          then w j else 0 := by
    have hp := congrArg (evaluateParameterPolynomial t) (parameterEdgePolynomial_eq i p)
    simp only [parameterEdgePolynomial, evaluateParameterPlane_cross, evaluateParameterPlane_sub,
      evaluateParameterHullVertex, evaluateParameterVertex, parameterMinorPolynomial, map_sum,
      apply_ite, map_zero] at hp
    rw [← planeCross_edge_direction l r]
    exact hp
  rw [planeCross_edge_direction l r]
  exact sub_nonneg.mpr (support_of_minor_gap_decomposition (fourRealParameterLeft t)
    fourRealParameterRight η (η * l).re U hU
    (fun j => (parameterTerms i j).rows) (fun j => (parameterTerms i j).columns) w hw hidentity)

private theorem holds_fourRealParameter_positive_small (t : ℝ) (ht0 : 0 < t)
    (ht1 : t ≤ 1 / 20) (U : Matrix (Fin 4) (Fin 4) ℂ) (hU : IsUnitary U) :
    Holds (fourRealParameterLeft t) fourRealParameterRight U := by
  have hpolygon := mem_planeHull_of_edges (parameterHull t) parameterPrev parameterNext
    (determinantValue (fourRealParameterLeft t) fourRealParameterRight U)
    (by decide +kernel) (parameterHull_turn t ht0 ht1) (parameterHull_edge t ht0.le ht1 U hU)
  apply convexHull_mono ?_ hpolygon
  rintro _ ⟨i, rfl⟩
  exact ⟨(parameterPermutation (parameterHullIndex i)).symm, rfl⟩

/-- The finite matching-hull property is closed in the real parameter. -/
theorem isClosed_fourRealParameter_holds (U : Matrix (Fin 4) (Fin 4) ℂ) :
    IsClosed {t : ℝ | Holds (fourRealParameterLeft t) fourRealParameterRight U} := by
  have he : {t : ℝ | Holds (fourRealParameterLeft t) fourRealParameterRight U} =
      ⋂ k : ℂ, ⋃ p : ParameterPermutation, {t : ℝ |
        (k * determinantValue (fourRealParameterLeft t) fourRealParameterRight U).re ≤
          (k * matchingProduct (fourRealParameterLeft t) fourRealParameterRight p).re} := by
    ext t
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_iUnion]
    exact holds_iff_directional _ _ U
  have ha : Continuous fourRealParameterLeft := continuous_pi fun j => by
    fin_cases j <;> dsimp [fourRealParameterLeft] <;> fun_prop
  rw [he]
  refine isClosed_iInter fun k => isClosed_iUnion_of_finite fun p => isClosed_le ?_ ?_
  · unfold determinantValue
    fun_prop
  · have hp : Continuous (fun t : ℝ =>
        matchingProduct (fourRealParameterLeft t) fourRealParameterRight p) := by
      unfold matchingProduct
      exact continuous_finset_prod _ fun j _ =>
        ((continuous_apply (p j)).comp ha).add continuous_const
    exact Complex.continuous_re.comp (continuous_const.mul hp)

private theorem fourRealParameterLeft_neg (t : ℝ) :
    fourRealParameterLeft (-t) =
      fourRealParameterLeft t ∘ Equiv.swap (0 : Fin 4) 1 := by
  funext j
  fin_cases j <;> simp [fourRealParameterLeft, Equiv.swap_apply_def]

private theorem holds_fourRealParameter_neg (t : ℝ) (U : Matrix (Fin 4) (Fin 4) ℂ)
    (hU : IsUnitary U)
    (h : ∀ V : Matrix (Fin 4) (Fin 4) ℂ, IsUnitary V →
      Holds (fourRealParameterLeft t) fourRealParameterRight V) :
    Holds (fourRealParameterLeft (-t)) fourRealParameterRight U := by
  let e : ParameterPermutation := Equiv.swap 0 1
  have hzero_right :
      fourRealParameterLeft (-t) ∘ e = fourRealParameterLeft t := by
    rw [fourRealParameterLeft_neg]
    funext j
    simpa only [Function.comp_apply, e, Equiv.symm_swap] using
      congrArg (fourRealParameterLeft t) (e.symm_apply_apply j)
  have hV := h (U.submatrix e (Equiv.refl (Fin 4))) (unitary_reindex e (Equiv.refl (Fin 4)) hU)
  apply (holds_reindex_iff e (Equiv.refl (Fin 4)) (fourRealParameterLeft (-t)) _ U).mp
  rw [hzero_right]
  exact hV

/-- The entire closed interval of radius one twentieth about zero satisfies
the determinant inclusion for every relative unitary. -/
theorem holds_fourRealParameter_of_abs_le_twentieth (t : ℝ) (ht : |t| ≤ 1 / 20)
    (U : Matrix (Fin 4) (Fin 4) ℂ) (hU : IsUnitary U) :
    Holds (fourRealParameterLeft t) fourRealParameterRight U := by
  rcases lt_trichotomy t 0 with hneg | rfl | hpos
  · have hn : 0 < -t := neg_pos.mpr hneg
    have hle : -t ≤ 1 / 20 := by simpa only [abs_of_neg hneg] using ht
    simpa only [neg_neg] using holds_fourRealParameter_neg (-t) U hU
      (fun V hV => holds_fourRealParameter_positive_small (-t) hn hle V hV)
  · let S := {s : ℝ | Holds (fourRealParameterLeft s) fourRealParameterRight U}
    have hcl : (0 : ℝ) ∈ closure S := by
      apply Metric.mem_closure_iff.mpr
      intro δ hδ
      let s : ℝ := min (δ / 2) (1 / 20)
      have hs0 : 0 < s := lt_min (div_pos hδ (by norm_num)) (by norm_num)
      have hs1 : s ≤ 1 / 20 := min_le_right _ _
      have hsδ : s < δ := (min_le_left _ _).trans_lt (by linarith)
      refine ⟨s, holds_fourRealParameter_positive_small s hs0 hs1 U hU, ?_⟩
      simpa only [dist_comm (0 : ℝ) s, Real.dist_eq, sub_zero, abs_of_pos hs0] using hsδ
    have hclosed : IsClosed S := isClosed_fourRealParameter_holds U
    rw [hclosed.closure_eq] at hcl
    exact hcl
  · exact holds_fourRealParameter_positive_small t hpos
      (by simpa only [abs_of_pos hpos] using ht) U hU

/-- Testing all positive parameters outside any finite exceptional set
suffices for the full real line. It is enough to cover the open cells. -/
theorem holds_fourRealParameter_of_positive_cells (exceptional : Set ℝ) (hfin : exceptional.Finite)
    (hcells : ∀ s : ℝ, 0 < s → s ∉ exceptional →
      ∀ V : Matrix (Fin 4) (Fin 4) ℂ, IsUnitary V →
        Holds (fourRealParameterLeft s) fourRealParameterRight V)
    (t : ℝ) (U : Matrix (Fin 4) (Fin 4) ℂ) (hU : IsUnitary U) :
    Holds (fourRealParameterLeft t) fourRealParameterRight U := by
  have hnonneg (r : ℝ) (hr : 0 ≤ r) (V : Matrix (Fin 4) (Fin 4) ℂ) (hV : IsUnitary V) :
      Holds (fourRealParameterLeft r) fourRealParameterRight V := by
    let S := {s : ℝ | Holds (fourRealParameterLeft s) fourRealParameterRight V}
    have hcl : r ∈ closure S := by
      apply Metric.mem_closure_iff.mpr
      intro δ hδ
      have hinterval : (Set.Ioo r (r + δ)).Infinite :=
        Set.Ioo_infinite (lt_add_of_pos_right r hδ)
      obtain ⟨s, hs, hsex⟩ := hinterval.exists_not_mem_finite hfin
      have hsr : 0 < s - r := sub_pos.mpr hs.1
      refine ⟨s, hcells s (hr.trans_lt hs.1) hsex V hV, ?_⟩
      rw [dist_comm, Real.dist_eq, abs_of_pos hsr]
      exact sub_lt_iff_lt_add.mpr (by simpa only [add_comm] using hs.2)
    have hclosed : IsClosed S := isClosed_fourRealParameter_holds V
    rw [hclosed.closure_eq] at hcl
    exact hcl
  by_cases ht : 0 ≤ t
  · exact hnonneg t ht U hU
  · have ht' : 0 ≤ -t := neg_nonneg.mpr (le_of_not_ge ht)
    simpa only [neg_neg] using holds_fourRealParameter_neg (-t) U hU (hnonneg (-t) ht')

end

end MOC
