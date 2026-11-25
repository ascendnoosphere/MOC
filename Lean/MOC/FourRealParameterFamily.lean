import MOC.Small
import MOC.PlaneHullEdges
import MOC.SparsePolynomialCertificate
import MOC.TwoValues
import Mathlib.Data.Fintype.Perm
import Mathlib.Algebra.Polynomial.Eval.Defs

/-! An order-four spectral family with a free real parameter.
Integer-polynomial certificates cover a bounded interval and both tails. -/

open BigOperators Matrix Polynomial
open MOC.SparsePolynomialCertificate (Univariate)
open scoped Topology Polynomial

namespace MOC

noncomputable section

/-- The first spectrum of the real-parameter family. -/
def fourRealParameterLeft (t : ℝ) : Fin 4 → ℂ :=
  ![(t : ℂ) + Complex.I, -(t : ℂ) + Complex.I, 1, 2 + Complex.I]

/-- The fixed spectrum of the real-parameter family. -/
def fourRealParameterRight : Fin 4 → ℂ :=
  ![-1 + Complex.I, -2 - 2 * Complex.I, 2 - Complex.I, 1 + 2 * Complex.I]

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

private abbrev IntegerPlanePolynomial := Univariate × Univariate

private def polynomialPlaneMul (a b : IntegerPlanePolynomial) : IntegerPlanePolynomial :=
  (a.1 * b.1 - a.2 * b.2, a.1 * b.2 + a.2 * b.1)

private def polynomialPlaneSub (a b : IntegerPlanePolynomial) : IntegerPlanePolynomial :=
  (a.1 - b.1, a.2 - b.2)

private def polynomialPlaneCross (a b : IntegerPlanePolynomial) : Univariate :=
  a.1 * b.2 - a.2 * b.1

private abbrev evaluateParameterPolynomial (t : ℝ) : Univariate → ℝ := Univariate.eval t

private def evaluateParameterPlane (t : ℝ) (a : IntegerPlanePolynomial) : ℂ :=
  ⟨evaluateParameterPolynomial t a.1, evaluateParameterPolynomial t a.2⟩

private theorem evaluateParameterPlane_mul (t : ℝ) (a b : IntegerPlanePolynomial) :
    evaluateParameterPlane t (polynomialPlaneMul a b) =
      evaluateParameterPlane t a * evaluateParameterPlane t b := by
  apply Complex.ext
  · simp only [evaluateParameterPlane, polynomialPlaneMul, Univariate.eval_sub,
      Univariate.eval_mul, Complex.mul_re]
  · simp only [evaluateParameterPlane, polynomialPlaneMul, Univariate.eval_add,
      Univariate.eval_mul, Complex.mul_im]

private theorem evaluateParameterPlane_sub (t : ℝ) (a b : IntegerPlanePolynomial) :
    evaluateParameterPlane t (polynomialPlaneSub a b) =
      evaluateParameterPlane t a - evaluateParameterPlane t b := by
  apply Complex.ext
  · simp only [evaluateParameterPlane, polynomialPlaneSub, Univariate.eval_sub, Complex.sub_re]
  · simp only [evaluateParameterPlane, polynomialPlaneSub, Univariate.eval_sub, Complex.sub_im]

private theorem evaluateParameterPlane_cross (t : ℝ) (a b : IntegerPlanePolynomial) :
    evaluateParameterPolynomial t (polynomialPlaneCross a b) =
      planeCross (evaluateParameterPlane t a) (evaluateParameterPlane t b) := by
  simp only [evaluateParameterPlane, polynomialPlaneCross, planeCross, Univariate.eval_mul,
    Univariate.eval_sub]

private def parameterPairSum (i j : Fin 4) : IntegerPlanePolynomial :=
  let x := Univariate.X
  (![x, -x, 1, 2] i + ![-1, -2, 2, 1] j, ![1, 1, 0, 1] i + ![1, -2, -1, 2] j)

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

private def parameterEdgePolynomial (i : Fin 9) (p : IntegerPlanePolynomial) : Univariate :=
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

private def ParameterWeight.polynomial (w : ParameterWeight) : Univariate :=
  let x := Univariate.X
  let c := Univariate.ofInt
  x ^ w.power * (c w.constant + c w.linear * x + c w.quadratic * x ^ 2 +
    c w.cubic * x ^ 3 + c w.quartic * x ^ 4)

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
  norm_num at hi hm₁ hm₂ hm₃ hm₄
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

private def parameterMinorPolynomial (i : Fin 9) (p : ParameterPermutation) : Univariate :=
  Univariate.sum fun j : Fin 12 =>
    let term := parameterTerms i j
    if term.columns.map p.toEmbedding = term.rows then term.weight.polynomial else 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem parameterEdgePolynomial_eq (t : ℝ) (i : Fin 9) (p : ParameterPermutation) :
    evaluateParameterPolynomial t (parameterEdgePolynomial i (parameterVertex p)) =
      evaluateParameterPolynomial t (parameterMinorPolynomial i p) := by
  apply Univariate.eval_eq
  obtain ⟨j, hj⟩ := parameterPermutation_surjective p.symm
  have hp : p = (parameterPermutation j).symm := by
    rw [hj, Equiv.symm_symm]
  rw [hp]
  fin_cases i <;> fin_cases j <;> decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
private theorem parameterTurnPolynomial_eq (t : ℝ) (i : Fin 9) :
    evaluateParameterPolynomial t (polynomialPlaneCross
        (polynomialPlaneSub (parameterHullVertex i) (parameterHullVertex (parameterPrev i)))
        (polynomialPlaneSub (parameterHullVertex (parameterNext i)) (parameterHullVertex i))) =
      evaluateParameterPolynomial t (parameterTurnWeight i).polynomial := by
  apply Univariate.eval_eq
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
  have he := parameterTurnPolynomial_eq t i
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
    have hp := parameterEdgePolynomial_eq t i p
    simp only [parameterEdgePolynomial, evaluateParameterPlane_cross, evaluateParameterPlane_sub,
      evaluateParameterHullVertex, evaluateParameterVertex, parameterMinorPolynomial,
      Univariate.eval_sum, apply_ite, Univariate.eval_ofNat, Nat.cast_zero] at hp
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
  unfold Holds
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

private theorem holds_of_scaled_minor_polygon {ι κ : Type*} [Fintype ι] [Nonempty ι] [Fintype κ]
    (a b : Fin 4 → ℂ) (U : Matrix (Fin 4) (Fin 4) ℂ) (hU : IsUnitary U)
    (c : ℂ) (hc : c ≠ 0) (label : ι → ParameterPermutation) (prev next : ι → ι)
    (hcycle : ∀ i, next (prev i) = i) (rows columns : ι → κ → Finset (Fin 4))
    (weights : ι → κ → ℝ) (hw : ∀ i j, 0 ≤ weights i j)
    (hturn : ∀ i, 0 < planeCross
      (c * matchingProduct a b (label i) - c * matchingProduct a b (label (prev i)))
      (c * matchingProduct a b (label (next i)) - c * matchingProduct a b (label i)))
    (hpolynomial : ∀ i σ,
      planeCross (c * matchingProduct a b (label (next i)) - c * matchingProduct a b (label i))
        (c * matchingProduct a b σ - c * matchingProduct a b (label i)) =
      ∑ j, if (columns i j).map σ.toEmbedding = rows i j then weights i j else 0) :
    Holds a b U := by
  let v (i : ι) := c * matchingProduct a b (label i)
  have hedge (i : ι) : 0 ≤ planeCross (v (next i) - v i) (c * determinantValue a b U - v i) := by
    let d := v (next i) - v i
    let η : ℂ := ⟨-d.im, -d.re⟩
    have hmatch (σ : ParameterPermutation) :
        (η * c * matchingProduct a b σ).re -
            (η * c * matchingProduct a b (label i)).re =
          ∑ j, if (columns i j).map σ.toEmbedding = rows i j then weights i j else 0 := by
      have he := hpolynomial i σ
      rw [planeCross_edge_direction] at he
      simpa only [d, v, η, mul_assoc] using he
    have hbound := support_of_minor_gap_decomposition a b (η * c)
      (η * c * matchingProduct a b (label i)).re U hU
      (rows i) (columns i) (weights i) (hw i) hmatch
    rw [planeCross_edge_direction]
    simpa only [d, v, η, mul_assoc] using sub_nonneg.mpr hbound
  have hscaled := mem_planeHull_of_edges v prev next (c * determinantValue a b U)
    hcycle hturn hedge
  let L : ℂ →ₗ[ℝ] ℂ := LinearMap.mulLeft ℝ c
  have hsubset : Set.range v ⊆ L '' Set.range (matchingProduct a b) := by
    rintro _ ⟨i, rfl⟩
    exact ⟨matchingProduct a b (label i), ⟨label i, rfl⟩, rfl⟩
  have he := convexHull_mono hsubset hscaled
  rw [← LinearMap.image_convexHull] at he
  obtain ⟨w, hwHull, heq⟩ := he
  change c * w = c * determinantValue a b U at heq
  change determinantValue a b U ∈ convexHull ℝ (Set.range (matchingProduct a b))
  rwa [← mul_left_cancel₀ hc heq]

private def parameterTailPairSum (i j : Fin 4) : IntegerPlanePolynomial :=
  let x := Univariate.X
  let scale : Univariate := ![x, x, 1, 1] i
  (![5 - x, x - 5, 1, 2] i + scale * ![-1, -2, 2, 1] j,
    ![x, x, 0, 1] i + scale * ![1, -2, -1, 2] j)

private def parameterTailScale (s : ℝ) (i : Fin 4) : ℂ :=
  ![(s : ℂ), (s : ℂ), 1, 1] i

private theorem evaluateParameterTailPairSum (s t : ℝ) (h : s * t = 5 - s) (i j : Fin 4) :
    evaluateParameterPlane s (parameterTailPairSum i j) =
      parameterTailScale s i * (fourRealParameterLeft t i + fourRealParameterRight j) := by
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    norm_num [evaluateParameterPlane, evaluateParameterPolynomial, parameterTailPairSum,
      parameterTailScale, fourRealParameterLeft, fourRealParameterRight, Complex.mul_re,
      Complex.mul_im] <;> nlinarith only [h]

private def parameterTailVertex (p : ParameterPermutation) : IntegerPlanePolynomial :=
  polynomialPlaneMul
    (polynomialPlaneMul (parameterTailPairSum (p 0) 0) (parameterTailPairSum (p 1) 1))
    (polynomialPlaneMul (parameterTailPairSum (p 2) 2) (parameterTailPairSum (p 3) 3))

private theorem evaluateParameterTailVertex (s t : ℝ) (h : s * t = 5 - s)
    (p : ParameterPermutation) :
    evaluateParameterPlane s (parameterTailVertex p) =
      (s : ℂ) ^ 2 * matchingProduct (fourRealParameterLeft t) fourRealParameterRight p := by
  have hprod : evaluateParameterPlane s (parameterTailVertex p) =
      ∏ j : Fin 4, parameterTailScale s (p j) *
        (fourRealParameterLeft t (p j) + fourRealParameterRight j) := by
    simp only [parameterTailVertex, evaluateParameterPlane_mul, evaluateParameterTailPairSum s t h,
      Fin.prod_univ_four, mul_assoc]
  rw [hprod, Finset.prod_mul_distrib, Equiv.prod_comp p (parameterTailScale s)]
  simp [parameterTailScale, matchingProduct, Fin.prod_univ_four, pow_two]

private def parameterTailPrev : Fin 8 → Fin 8 := ![7, 0, 1, 2, 3, 4, 5, 6]

private def parameterTailNext : Fin 8 → Fin 8 := ![1, 2, 3, 4, 5, 6, 7, 0]

private def parameterTailIndex : Fin 8 → Fin 24 := ![0, 1, 15, 14, 4, 18, 12, 6]

private def parameterTailLabel (i : Fin 8) : ParameterPermutation :=
  (parameterPermutation (parameterTailIndex i)).symm

private def parameterTailHullVertex (i : Fin 8) : IntegerPlanePolynomial :=
  parameterTailVertex (parameterTailLabel i)

private def parameterTailTerms : Fin 8 → Fin 12 → ParameterMinorTerm :=
 ![
  ![⟨{0}, {2}, ⟨1, 2500, 500, -600, 80, 0⟩⟩,
    ⟨{1}, {0}, ⟨1, 24000, 9600, -6720, 768, 0⟩⟩,
    ⟨{2}, {0}, ⟨0, 20000, -11000, 0, 880, 480⟩⟩,
    ⟨{2}, {1}, ⟨0, 25000, -3750, 5500, 250, -480⟩⟩,
    ⟨{3}, {0}, ⟨0, 11250, -13250, 400, 1220, 528⟩⟩,
    ⟨{3}, {1}, ⟨0, 8750, 0, 2300, 1250, 144⟩⟩,
    ⟨{0, 1}, {0, 2}, ⟨0, 23750, -31000, -10200, 7190, -320⟩⟩,
    ⟨{0, 1}, {0, 3}, ⟨0, 30000, -37250, -7700, 7190, -480⟩⟩,
    ⟨{0, 1}, {1, 2}, ⟨0, 6250, -8750, -500, 1100, 160⟩⟩,
    ⟨{0, 2}, {0, 1}, ⟨1, 4000, 11600, -3120, 128, 0⟩⟩,
    ⟨{0, 2}, {1, 2}, ⟨1, 15000, -9000, -1200, 480, 0⟩⟩,
    ⟨{0, 3}, {0, 1}, ⟨1, 17500, 9500, -5400, 560, 0⟩⟩],
  ![⟨{1}, {0}, ⟨1, 88000, -48000, -7360, 2688, 0⟩⟩,
    ⟨{1}, {3}, ⟨1, 8000, -4600, -480, 216, 0⟩⟩,
    ⟨{2}, {1}, ⟨0, 68750, -34250, 3850, -5270, 264⟩⟩,
    ⟨{3}, {1}, ⟨0, 41250, -3750, -5450, -3290, -600⟩⟩,
    ⟨{3}, {3}, ⟨0, 17500, -19500, 400, 1720, 768⟩⟩,
    ⟨{0, 1}, {0, 2}, ⟨0, 13750, -81250, 39650, 6530, -2424⟩⟩,
    ⟨{0, 1}, {0, 3}, ⟨0, 16250, -91250, 48650, 4630, -2688⟩⟩,
    ⟨{0, 1}, {1, 3}, ⟨0, 15000, -17500, 500, 1600, 696⟩⟩,
    ⟨{0, 2}, {0, 1}, ⟨1, 49500, -15300, -9600, 576, 0⟩⟩,
    ⟨{0, 2}, {1, 2}, ⟨1, 20000, -18000, 4000, -240, 0⟩⟩,
    ⟨{0, 3}, {0, 1}, ⟨1, 62000, -32400, -6320, 2064, 0⟩⟩,
    ⟨{0, 3}, {2, 3}, ⟨1, 19500, -3900, -3120, -936, 0⟩⟩],
  ![⟨{0}, {1}, ⟨1, 13500, 2100, -540, -84, 0⟩⟩,
    ⟨{1}, {0}, ⟨1, 2500, -500, -100, 20, 0⟩⟩,
    ⟨{2}, {1}, ⟨0, 1875, 1875, 4125, 75, -138⟩⟩,
    ⟨{3}, {1}, ⟨0, 7500, 3500, 2850, 210, -56⟩⟩,
    ⟨{3}, {2}, ⟨0, 3125, -1875, -125, -475, -110⟩⟩,
    ⟨{0, 1}, {0, 1}, ⟨0, 12500, 0, -2500, -1000, -120⟩⟩,
    ⟨{0, 1}, {0, 2}, ⟨0, 3125, -1875, 125, -25, -30⟩⟩,
    ⟨{0, 2}, {0, 3}, ⟨0, 1875, 1875, -875, 75, 62⟩⟩,
    ⟨{0, 2}, {1, 2}, ⟨0, 13750, 1250, -6000, -700, 88⟩⟩,
    ⟨{0, 2}, {1, 3}, ⟨1, 2500, -1500, -100, 60, 0⟩⟩,
    ⟨{0, 3}, {0, 3}, ⟨0, 13750, 2250, -1400, -740, -96⟩⟩,
    ⟨{0, 3}, {1, 2}, ⟨0, 1875, 3375, -975, 15, 66⟩⟩],
  ![⟨{0}, {1}, ⟨1, 43500, -41100, 21300, -2964, 0⟩⟩,
    ⟨{1}, {0}, ⟨1, 5000, -18000, 7000, -720, 0⟩⟩,
    ⟨{2}, {2}, ⟨0, 8125, -14375, 17875, -6975, 42⟩⟩,
    ⟨{3}, {0}, ⟨0, 5000, 0, 4000, -400, -248⟩⟩,
    ⟨{3}, {1}, ⟨0, 9375, 5375, -3925, 4085, 1002⟩⟩,
    ⟨{0, 1}, {0, 1}, ⟨0, 52500, -48000, 29100, -6520, -1400⟩⟩,
    ⟨{0, 1}, {0, 2}, ⟨0, 8125, -14375, 20125, -6925, 562⟩⟩,
    ⟨{0, 2}, {0, 3}, ⟨0, 20000, -20000, 11000, -3200, -312⟩⟩,
    ⟨{0, 2}, {1, 2}, ⟨0, 40625, -46875, 10625, 375, -790⟩⟩,
    ⟨{0, 3}, {0, 1}, ⟨1, 500, -9500, 3340, -292, 0⟩⟩,
    ⟨{0, 3}, {0, 3}, ⟨0, 40625, -25375, 2525, 6715, -1906⟩⟩,
    ⟨{0, 3}, {1, 2}, ⟨0, 20000, -16500, 6100, -940, -596⟩⟩],
  ![⟨{0}, {1}, ⟨1, 5000, 10000, -4200, 400, 0⟩⟩,
    ⟨{1}, {1}, ⟨1, 5000, -18000, 7000, -720, 0⟩⟩,
    ⟨{2}, {3}, ⟨1, 5000, -2000, -200, 80, 0⟩⟩,
    ⟨{3}, {1}, ⟨1, 15000, -10000, 5400, -800, 0⟩⟩,
    ⟨{0, 1}, {0, 1}, ⟨1, 40000, -24000, -2800, 1200, 0⟩⟩,
    ⟨{0, 1}, {1, 3}, ⟨1, 5000, -2000, -2200, 480, 0⟩⟩,
    ⟨{0, 2}, {0, 3}, ⟨1, 10000, -8000, 2400, -240, 0⟩⟩,
    ⟨{0, 2}, {1, 2}, ⟨1, 35000, -30000, 5800, -240, 0⟩⟩,
    ⟨{0, 3}, {0, 3}, ⟨1, 35000, -12000, -1400, 480, 0⟩⟩,
    ⟨{0, 3}, {1, 2}, ⟨1, 10000, -4000, 800, -80, 0⟩⟩,
    ⟨{0, 3}, {1, 3}, ⟨2, 2000, -800, 80, 0, 0⟩⟩,
    ⟨∅, ∅, ⟨0, 0, 0, 0, 0, 0⟩⟩],
  ![⟨{0}, {1}, ⟨0, 40625, -81875, 55625, -13425, 450⟩⟩,
    ⟨{1}, {1}, ⟨0, 40625, -9875, -10375, 1935, -558⟩⟩,
    ⟨{1}, {2}, ⟨1, 37000, -26000, 1560, 432, 0⟩⟩,
    ⟨{1}, {3}, ⟨1, 12000, -11000, 2560, -168, 0⟩⟩,
    ⟨{2}, {0}, ⟨0, 8125, -16375, 11125, -2685, 90⟩⟩,
    ⟨{2}, {2}, ⟨1, 25000, -18750, 750, 900, 0⟩⟩,
    ⟨{3}, {0}, ⟨0, 21875, -17625, 6875, -2835, 198⟩⟩,
    ⟨{3}, {1}, ⟨0, 23750, -33250, 18950, -2070, -1476⟩⟩,
    ⟨{0, 1}, {0, 1}, ⟨0, 30625, -8375, -11975, 2235, 810⟩⟩,
    ⟨{0, 2}, {0, 1}, ⟨1, 23000, -19000, 3240, -72, 0⟩⟩,
    ⟨{0, 2}, {0, 3}, ⟨0, 6250, 1250, -7750, 2550, 180⟩⟩,
    ⟨{0, 3}, {1, 2}, ⟨0, 6250, 21250, -17750, 150, 900⟩⟩],
  ![⟨{1}, {1}, ⟨1, 117000, -41400, -10080, 2736, 0⟩⟩,
    ⟨{1}, {2}, ⟨1, 30000, -11400, -1800, 576, 0⟩⟩,
    ⟨{1}, {3}, ⟨1, 19500, -6900, -1680, 456, 0⟩⟩,
    ⟨{2}, {0}, ⟨0, 20625, -23625, 6675, 1095, -630⟩⟩,
    ⟨{3}, {0}, ⟨0, 28125, -25125, 23025, -14895, 1494⟩⟩,
    ⟨{3}, {1}, ⟨0, 48750, -21750, 1500, -3480, -1008⟩⟩,
    ⟨{3}, {2}, ⟨0, 48750, -47250, 16800, -7560, 1440⟩⟩,
    ⟨{0, 1}, {0, 3}, ⟨0, 22500, -18000, 8100, -2880, 720⟩⟩,
    ⟨{0, 1}, {1, 2}, ⟨0, 103125, -118125, 33375, 5475, -3150⟩⟩,
    ⟨{0, 1}, {1, 3}, ⟨0, 31875, -42375, 3225, 14145, -3690⟩⟩,
    ⟨{0, 2}, {0, 1}, ⟨1, 10500, 15900, -20520, 3384, 0⟩⟩,
    ⟨{0, 3}, {0, 2}, ⟨1, 15000, -21000, 14400, -2160, 0⟩⟩],
  ![⟨{0}, {3}, ⟨1, 46500, -51900, 10980, -492, 0⟩⟩,
    ⟨{1}, {2}, ⟨2, 2400, -960, 96, 0, 0⟩⟩,
    ⟨{1}, {3}, ⟨1, 46500, -51900, 10980, -492, 0⟩⟩,
    ⟨{2}, {1}, ⟨1, 34500, -45900, 12420, -924, 0⟩⟩,
    ⟨{2}, {3}, ⟨1, 39000, -47400, 11280, -672, 0⟩⟩,
    ⟨{3}, {0}, ⟨1, 28500, 6900, -13980, 2292, 0⟩⟩,
    ⟨{3}, {1}, ⟨1, 78000, -24000, -21360, 4608, 0⟩⟩,
    ⟨{0, 1}, {0, 3}, ⟨1, 25500, -14100, 4380, -516, 0⟩⟩,
    ⟨{0, 1}, {1, 2}, ⟨1, 79500, -72900, 10620, 156, 0⟩⟩,
    ⟨{0, 2}, {0, 1}, ⟨1, 82500, -55500, 1500, 1260, 0⟩⟩,
    ⟨{0, 3}, {0, 2}, ⟨2, 48000, -19200, 1920, 0, 0⟩⟩,
    ⟨{0, 3}, {2, 3}, ⟨1, 82500, 4500, -22500, 3660, 0⟩⟩]]

private def parameterTailTurnWeight : Fin 8 → ParameterWeight :=
  ![⟨1, 39000, 600, -7920, 1248, 0⟩,
    ⟨0, 17500, -19500, 400, 1720, 768⟩,
    ⟨0, 17500, 0, -3500, -1400, -168⟩,
    ⟨0, 5000, 0, 4000, -400, -248⟩,
    ⟨1, 5000, -18000, 7000, -720, 0⟩,
    ⟨1, 35000, -30000, 5800, -240, 0⟩,
    ⟨0, 71250, -65250, 24900, -10440, 2160⟩,
    ⟨1, 117000, -41400, -10080, 2736, 0⟩]

private def parameterTailMinorPolynomial (i : Fin 8) (p : ParameterPermutation) : Univariate :=
  Univariate.sum fun j : Fin 12 =>
    let term := parameterTailTerms i j
    if term.columns.map p.toEmbedding = term.rows then term.weight.polynomial else 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem parameterTailEdge_eq (t : ℝ) (i : Fin 8) (p : ParameterPermutation) :
    evaluateParameterPolynomial t (polynomialPlaneCross
        (polynomialPlaneSub (parameterTailHullVertex (parameterTailNext i)) (parameterTailHullVertex i))
        (polynomialPlaneSub (parameterTailVertex p) (parameterTailHullVertex i))) =
      evaluateParameterPolynomial t (parameterTailMinorPolynomial i p) := by
  apply Univariate.eval_eq
  obtain ⟨j, hj⟩ := parameterPermutation_surjective p.symm
  have hp : p = (parameterPermutation j).symm := by rw [hj, Equiv.symm_symm]
  rw [hp]
  fin_cases i <;> fin_cases j <;> decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
private theorem parameterTailTurn_eq (t : ℝ) (i : Fin 8) :
    evaluateParameterPolynomial t (polynomialPlaneCross
        (polynomialPlaneSub (parameterTailHullVertex i) (parameterTailHullVertex (parameterTailPrev i)))
        (polynomialPlaneSub (parameterTailHullVertex (parameterTailNext i)) (parameterTailHullVertex i))) =
      evaluateParameterPolynomial t (parameterTailTurnWeight i).polynomial := by
  apply Univariate.eval_eq
  fin_cases i <;> decide +kernel

private theorem parameterTailBudget_lower (i : Fin 8) (j : Fin 12) :
    Univariate.same (parameterTailTerms i j).weight.polynomial 0 = true ∨
      0 < (parameterTailTerms i j).weight.lowerNumerator :=
  (by decide +kernel : ∀ k l,
    Univariate.same (parameterTailTerms k l).weight.polynomial 0 = true ∨
      0 < (parameterTailTerms k l).weight.lowerNumerator) i j

private theorem parameterTailTurn_lower (i : Fin 8) :
    0 < (parameterTailTurnWeight i).lowerNumerator :=
  (by decide +kernel : ∀ k, 0 < (parameterTailTurnWeight k).lowerNumerator) i

private theorem holds_fourRealParameter_positive_tail (t : ℝ) (ht : 99 ≤ t)
    (U : Matrix (Fin 4) (Fin 4) ℂ) (hU : IsUnitary U) :
    Holds (fourRealParameterLeft t) fourRealParameterRight U := by
  let s : ℝ := 5 / (1 + t)
  have hden : 0 < 1 + t := by linarith only [ht]
  have hs0 : 0 < s := div_pos (by norm_num) hden
  have hs1 : s ≤ 1 / 20 := (div_le_iff₀ hden).mpr (by linarith only [ht])
  have hst : s * t = 5 - s := by
    have he : s * (1 + t) = 5 := div_mul_cancel₀ 5 hden.ne'
    rw [mul_add, mul_one] at he
    linarith only [he]
  let w (i : Fin 8) (j : Fin 12) :=
    evaluateParameterPolynomial s (parameterTailTerms i j).weight.polynomial
  have hw (i : Fin 8) (j : Fin 12) : 0 ≤ w i j := by
    rcases parameterTailBudget_lower i j with hzero | hpos
    · simpa [w] using (Univariate.eval_eq s hzero).le
    · dsimp only [w]
      rw [evaluateParameterWeight]
      exact mul_nonneg (pow_nonneg hs0.le _) (parameterWeight_sign (parameterTailTerms i j).weight
        hpos s hs0.le hs1).le
  have hc : (s : ℂ) ^ 2 ≠ 0 := pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr hs0.ne')
  have hv (i : Fin 8) : evaluateParameterPlane s (parameterTailHullVertex i) =
      (s : ℂ) ^ 2 * matchingProduct (fourRealParameterLeft t) fourRealParameterRight
        (parameterTailLabel i) :=
    evaluateParameterTailVertex s t hst (parameterTailLabel i)
  apply holds_of_scaled_minor_polygon (fourRealParameterLeft t) fourRealParameterRight U hU
    ((s : ℂ) ^ 2) hc parameterTailLabel parameterTailPrev parameterTailNext
    (by decide +kernel) (fun i j => (parameterTailTerms i j).rows)
    (fun i j => (parameterTailTerms i j).columns) w hw
  · intro i
    have he := parameterTailTurn_eq s i
    simp only [evaluateParameterPlane_cross, evaluateParameterPlane_sub, hv] at he
    rw [he, evaluateParameterWeight]
    exact mul_pos (pow_pos hs0 _) (parameterWeight_sign (parameterTailTurnWeight i)
      (parameterTailTurn_lower i) s hs0.le hs1)
  · intro i p
    have he := parameterTailEdge_eq s i p
    simp only [evaluateParameterPlane_cross, evaluateParameterPlane_sub, hv,
      evaluateParameterTailVertex s t hst, parameterTailMinorPolynomial, Univariate.eval_sum,
      apply_ite, Univariate.eval_ofNat, Nat.cast_zero, w] at he
    exact he

/-- Both unbounded tails of the real-parameter family satisfy the
matching-hull inclusion for every relative unitary. -/
theorem holds_fourRealParameter_of_ninetyNine_le_abs (t : ℝ) (ht : 99 ≤ |t|)
    (U : Matrix (Fin 4) (Fin 4) ℂ) (hU : IsUnitary U) :
    Holds (fourRealParameterLeft t) fourRealParameterRight U := by
  by_cases hn : t < 0
  · have htail : 99 ≤ -t := by simpa only [abs_of_neg hn] using ht
    simpa only [neg_neg] using holds_fourRealParameter_neg (-t) U hU
      (fun V hV => holds_fourRealParameter_positive_tail (-t) htail V hV)
  · have htail : 99 ≤ t := by simpa only [abs_of_nonneg (le_of_not_gt hn)] using ht
    exact holds_fourRealParameter_positive_tail t htail U hU

/-- A polynomial written in the unnormalized Bernstein basis is strictly
positive inside the interval if its coefficients are nonnegative and at
least one is positive. A rational coefficient identity can be cast to this
statement. -/
theorem polynomial_eval_pos_of_open_bernstein {d : ℕ} (p : ℝ[X]) (b : Fin (d + 1) → ℝ)
    (l r x : ℝ) (hl : l < x) (hr : x < r)
    (hb : ∀ j, 0 ≤ b j) (hpos : ∃ j, 0 < b j)
    (hp : p = ∑ j : Fin (d + 1), C (b j) * (X - C l) ^ j.val * (C r - X) ^ (d - j.val)) :
    0 < p.eval x := by
  rw [hp]
  simp only [eval_finset_sum, eval_mul, eval_C, eval_pow, eval_sub, eval_X]
  have hleft := sub_pos.mpr hl
  have hright := sub_pos.mpr hr
  apply Finset.sum_pos' (fun j _ => mul_nonneg
    (mul_nonneg (hb j) (pow_nonneg hleft.le _)) (pow_nonneg hright.le _))
  obtain ⟨j, hj⟩ := hpos
  exact ⟨j, Finset.mem_univ j, mul_pos (mul_pos hj (pow_pos hleft _)) (pow_pos hright _)⟩

/-- Matching vertices after the compact substitution, scaled by
the two varying row factors. -/
def fourRealParameterCompactVertex (x : ℝ) (σ : Equiv.Perm (Fin 4)) : ℂ :=
  ((1 - x : ℝ) : ℂ) ^ 2 *
    matchingProduct (fourRealParameterLeft (x / (1 - x))) fourRealParameterRight σ

/-- Data and sign conditions for one finite polygon in the compact
parameter. The identities are on permutations and the coefficients
need only be nonnegative at the parameter of the chart. -/
structure FourRealParameterMinorChart (x : ℝ) where
  vertices : ℕ
  vertices_pos : 0 < vertices
  label : Fin vertices → Equiv.Perm (Fin 4)
  prev : Fin vertices → Fin vertices
  next : Fin vertices → Fin vertices
  incident : ∀ i, next (prev i) = i
  terms : ℕ
  rows : Fin vertices → Fin terms → Finset (Fin 4)
  columns : Fin vertices → Fin terms → Finset (Fin 4)
  weights : Fin vertices → Fin terms → ℝ
  weights_nonneg : ∀ i j, 0 ≤ weights i j
  turn_pos : ∀ i, 0 < planeCross
    (fourRealParameterCompactVertex x (label i) - fourRealParameterCompactVertex x (label (prev i)))
    (fourRealParameterCompactVertex x (label (next i)) - fourRealParameterCompactVertex x (label i))
  edge_identity : ∀ i σ, planeCross
    (fourRealParameterCompactVertex x (label (next i)) - fourRealParameterCompactVertex x (label i))
    (fourRealParameterCompactVertex x σ - fourRealParameterCompactVertex x (label i)) =
      ∑ j, if (columns i j).map σ.toEmbedding = rows i j then weights i j else 0

/-- Compact charts away from finitely many cut points imply the whole
real-line theorem. No unitary-dependent test is required in each chart. -/
theorem holds_fourRealParameter_of_compact_minor_cells
    (cuts : Set ℝ) (hfin : cuts.Finite)
    (charts : ∀ x : ℝ, 0 < x → x < 1 → x ∉ cuts → Nonempty (FourRealParameterMinorChart x))
    (t : ℝ) (U : Matrix (Fin 4) (Fin 4) ℂ) (hU : IsUnitary U) :
    Holds (fourRealParameterLeft t) fourRealParameterRight U := by
  let exceptional := (fun x : ℝ => x / (1 - x)) '' cuts
  have hf : exceptional.Finite := hfin.image _
  apply holds_fourRealParameter_of_positive_cells exceptional hf ?_ t U hU
  intro r hr hcut V hV
  let x := r / (1 + r)
  have hden : 0 < 1 + r := by linarith only [hr]
  have hx0 : 0 < x := div_pos hr hden
  have hx1 : x < 1 := (div_lt_one hden).mpr (by linarith)
  have hquotient : x / (1 - x) = r := by
    have he : x * (1 + r) = r := div_mul_cancel₀ r hden.ne'
    exact (div_eq_iff (sub_ne_zero.mpr (ne_of_gt hx1))).mpr (by nlinarith only [he])
  obtain ⟨chart⟩ := charts x hx0 hx1 (fun hx => hcut ⟨x, hx, hquotient⟩)
  letI : Nonempty (Fin chart.vertices) := ⟨⟨0, chart.vertices_pos⟩⟩
  have hc : ((1 - x : ℝ) : ℂ) ^ 2 ≠ 0 :=
    pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr (sub_ne_zero.mpr (ne_of_gt hx1)))
  have h := holds_of_scaled_minor_polygon (fourRealParameterLeft (x / (1 - x)))
    fourRealParameterRight V hV _ hc chart.label chart.prev chart.next chart.incident
    chart.rows chart.columns chart.weights chart.weights_nonneg chart.turn_pos chart.edge_identity
  simpa only [hquotient] using h

end

end MOC
