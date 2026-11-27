import MOC.Support
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Tactic.FinCases

/-! Three Hermitian involutions can add to zero although every matching of
their spectral lists has determinant at most minus one. -/

open BigOperators Matrix Polynomial

namespace MOC.ThreeHermitianSummands

noncomputable section

private def plane (u v : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(u : ℂ), (v : ℂ); (v : ℂ), -(u : ℂ)]

private theorem plane_hermitian (u v : ℝ) : (plane u v).IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [plane, Matrix.conjTranspose_apply]

private theorem plane_charpoly (u v : ℝ) :
    (plane u v).charpoly = X^2 - C ((u : ℂ)^2 + (v : ℂ)^2) := by
  have h01 : (0 : Fin 2) ≠ 1 := by decide
  simp [Matrix.charpoly, Matrix.det_fin_two, Matrix.charmatrix_apply_eq,
    Matrix.charmatrix_apply_ne, h01, h01.symm, plane] <;> ring

private theorem plane_sq (u v : ℝ) (h : u^2 + v^2 = 1) : (plane u v)^2 = 1 := by
  have hc : (u : ℂ)^2 + (v : ℂ)^2 = 1 := by exact_mod_cast h
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sq, plane, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]
  · linear_combination hc
  · ring
  · ring
  · linear_combination hc

def first := plane 1 0
def second := plane (-1/2) (Real.sqrt 3/2)
def third := plane (-1/2) (-Real.sqrt 3/2)

private theorem coefficients :
    (-1/2 : ℝ)^2 + (Real.sqrt 3/2)^2 = 1 ∧
    (-1/2 : ℝ)^2 + (-Real.sqrt 3/2)^2 = 1 := by
  have h := Real.sq_sqrt (by norm_num : 0 ≤ (3 : ℝ))
  constructor <;> nlinarith

/-- The three displayed matrices are Hermitian involutions with eigenvalues +1 and -1. -/
theorem three_involutions :
    ∀ A ∈ ({first, second, third} : Set (Matrix (Fin 2) (Fin 2) ℂ)),
      A.IsHermitian ∧ A^2 = 1 ∧ A.charpoly = (X:Polynomial ℂ)^2-1 := by
  intro A hA
  have hplane (u v : ℝ) (h : u^2 + v^2 = 1) :
      (plane u v).IsHermitian ∧ (plane u v)^2 = 1 ∧
        (plane u v).charpoly = (X:Polynomial ℂ)^2-1 := by
    have hc : (u : ℂ)^2 + (v : ℂ)^2 = 1 := by exact_mod_cast h
    exact ⟨plane_hermitian _ _, plane_sq _ _ h, by rw [plane_charpoly, hc, map_one]⟩
  rcases hA with h | h | h
  · subst A
    exact hplane _ _ (by norm_num)
  · subst A
    exact hplane _ _ coefficients.1
  · change A = third at h
    subst A
    exact hplane _ _ coefficients.2

theorem sum_eq_zero : first + second + third = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [first, second, third, plane] <;> ring

private def signList : Fin 2 → ℤ := ![1,-1]

def matchingScore (p : Equiv.Perm (Fin 2) × Equiv.Perm (Fin 2)) : ℤ :=
  ∏ i, (signList i + signList (p.1 i) + signList (p.2 i))

theorem matching_scores (p : Equiv.Perm (Fin 2) × Equiv.Perm (Fin 2)) :
    matchingScore p = -1 ∨ matchingScore p = -9 := by
  have hall : ∀ p : Equiv.Perm (Fin 2) × Equiv.Perm (Fin 2),
      matchingScore p = -1 ∨ matchingScore p = -9 := by decide +kernel
  exact hall p

/-- The sum determinant lies outside the convex hull of the three-list matching products. -/
theorem det_sum_outside_hull :
    (first + second + third).det ∉ convexHull ℝ
      (Set.range fun p : Equiv.Perm (Fin 2) × Equiv.Perm (Fin 2) => (matchingScore p : ℂ)) := by
  intro hh
  have hsub : (Set.range fun p : Equiv.Perm (Fin 2) × Equiv.Perm (Fin 2) =>
      (matchingScore p : ℂ)) ⊆ {z : ℂ | z.re ≤ -1} := by
    rintro _ ⟨p, rfl⟩
    change (matchingScore p : ℂ).re ≤ -1
    rcases matching_scores p with h | h <;> rw [h] <;> norm_num
  have h := convexHull_min hsub (convex_halfSpace_le Complex.reLm.isLinear (-1)) hh
  change (first + second + third).det.re ≤ -1 at h
  rw [sum_eq_zero, Matrix.det_zero ⟨0⟩] at h
  norm_num at h

end

end MOC.ThreeHermitianSummands
