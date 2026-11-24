import MOC.Core
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.Matrix.Notation
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum

/-! An exact algebraic certificate against the native additive resultant
test of atlas 021 in binary symmetric cubic order. -/

open BigOperators Polynomial

namespace MOC.Reformulations
noncomputable section

/-- The homogeneous Sylvester resultant of binary forms
`a x² + b xy + c y²` and `d x² + e xy + f y²`, in expanded form. -/
def binaryQuadraticResultant {R : Type*} [CommRing R] (a b c d e f : R) : R :=
  (a * f - c * d) ^ 2 - (a * e - b * d) * (b * f - c * e)

/-- Resultant for the cubics `(x-y)³`, `(x+y)³` and their sum, using the
two partial derivatives divided by 3 and subtracting `t x², t y²`. -/
def binaryCubicMinusResultant : ℂ[X] :=
  binaryQuadraticResultant (1 - X) (-2) 1 (-1) 2 (-1 - X)

def binaryCubicPlusResultant : ℂ[X] :=
  binaryQuadraticResultant (1 - X) 2 1 1 2 (1 - X)

def binaryCubicSumResultant : ℂ[X] :=
  binaryQuadraticResultant (2 - X) 0 2 0 4 (-X)

theorem binaryCubicMinus_factor :
    binaryCubicMinusResultant = X ^ 2 * (X ^ 2 + 4) := by
  unfold binaryCubicMinusResultant binaryQuadraticResultant
  ring

theorem binaryCubicPlus_factor :
    binaryCubicPlusResultant = X ^ 3 * (X - 4) := by
  unfold binaryCubicPlusResultant binaryQuadraticResultant
  ring

theorem binaryCubicSum_factor :
    binaryCubicSumResultant = (X - 4) * (X - 2) * (X ^ 2 + 2 * X + 8) := by
  unfold binaryCubicSumResultant binaryQuadraticResultant
  ring

private def cubicMinusRoots : Fin 4 → ℂ := ![0, 0, 2 * Complex.I, -2 * Complex.I]

private def cubicPlusRoots (i : Fin 4) : ℂ := if i = 3 then 4 else 0

theorem binaryCubic_rootLists :
    (∏ i, (X - C (cubicMinusRoots i))) = binaryCubicMinusResultant ∧
      (∏ i, (X - C (cubicPlusRoots i))) = binaryCubicPlusResultant := by
  rw [binaryCubicMinus_factor, binaryCubicPlus_factor]
  constructor
  · norm_num [Fin.prod_univ_succ, cubicMinusRoots, map_neg, map_mul, Fin.succ]
    have hC2 : (C (2 : ℂ) : ℂ[X]) = 2 := C_eq_natCast 2
    try rw [hC2]
    have hi : (C Complex.I : ℂ[X]) ^ 2 = -1 := by
      simpa only [map_pow, map_neg, map_one] using congrArg
        (C : ℂ →+* ℂ[X]) Complex.I_sq
    linear_combination -(4 * X ^ 2) * hi
  · rw [Fin.prod_univ_four]
    have h0 : (0 : Fin 4) ≠ 3 := by decide
    have h1 : (1 : Fin 4) ≠ 3 := by decide
    have h2 : (2 : Fin 4) ≠ 3 := by decide
    simp only [cubicPlusRoots, if_neg h0, if_neg h1, if_neg h2, if_pos rfl,
      if_true, map_zero, sub_zero, map_ofNat]
    have hC4 : (C (4 : ℂ) : ℂ[X]) = 4 := C_eq_natCast 4
    try rw [hC4]
    ring

private theorem cubicMatchingProduct_zero (σ : Equiv.Perm (Fin 4)) :
    matchingProduct cubicMinusRoots cubicPlusRoots σ = 0 := by
  have h01 : σ.symm 0 ≠ σ.symm 1 := fun he =>
    (by decide : (0 : Fin 4) ≠ 1) (σ.symm.injective he)
  unfold matchingProduct
  by_cases h0 : σ.symm 0 = 3
  · have h1 : σ.symm 1 ≠ 3 := fun he => h01 (h0.trans he.symm)
    refine Finset.prod_eq_zero (Finset.mem_univ (σ.symm 1)) ?_
    simp [cubicPlusRoots, h1, cubicMinusRoots]
  · refine Finset.prod_eq_zero (Finset.mem_univ (σ.symm 0)) ?_
    simp [cubicPlusRoots, h0, cubicMinusRoots]

/-- The sum's even-degree determinant sign is positive. Its constant
resultant coefficient is 64, whereas all permutation products vanish. -/
theorem binaryCubic_additiveResultantCounterexample :
    binaryCubicSumResultant.eval 0 ∉
      convexHull ℝ (Set.range (matchingProduct cubicMinusRoots cubicPlusRoots)) := by
  have he : binaryCubicSumResultant.eval 0 = 64 := by
    rw [binaryCubicSum_factor]
    norm_num
  have hr : Set.range (matchingProduct cubicMinusRoots cubicPlusRoots) = {0} := by
    ext z
    constructor
    · rintro ⟨σ, rfl⟩
      exact Set.mem_singleton_iff.mpr (cubicMatchingProduct_zero σ)
    · intro hz
      exact ⟨1, (cubicMatchingProduct_zero 1).trans (Set.mem_singleton_iff.mp hz).symm⟩
  rw [he, hr, convexHull_singleton, Set.mem_singleton_iff]
  norm_num

end
end MOC.Reformulations
