import MOC.FourMatchingRelations
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Data.Matrix.Block
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Matrix.Notation

/-! The matching Hessian is obtained by polarizing each quadratic monomial. -/

namespace MOC

open BigOperators Matrix

private structure GradientTerm where
  coefficient : ℤ
  left : Fin 14
  right : Fin 14

private def gradientTerms : Fin 14 → List GradientTerm :=
  ![[⟨-2, 0, 9⟩, ⟨-1, 1, 9⟩, ⟨-1, 2, 9⟩, ⟨-1, 3, 9⟩, ⟨-1, 3, 10⟩, ⟨-1, 5, 9⟩, ⟨1, 6, 13⟩, ⟨-1, 7, 9⟩, ⟨-1, 7, 11⟩, ⟨-1, 9, 9⟩, ⟨-1, 9, 10⟩, ⟨-1, 9, 11⟩, ⟨-1, 9, 12⟩],
    [⟨-1, 0, 9⟩, ⟨1, 2, 10⟩, ⟨-1, 5, 9⟩, ⟨-1, 5, 13⟩, ⟨1, 7, 10⟩, ⟨1, 7, 12⟩],
    [⟨-1, 0, 9⟩, ⟨1, 1, 10⟩, ⟨1, 5, 11⟩, ⟨-1, 6, 12⟩, ⟨-1, 9, 12⟩, ⟨1, 10, 11⟩],
    [⟨-1, 0, 9⟩, ⟨-1, 0, 10⟩, ⟨1, 5, 11⟩, ⟨1, 5, 12⟩, ⟨1, 7, 12⟩, ⟨-1, 8, 10⟩],
    [⟨-1, 7, 11⟩, ⟨1, 8, 9⟩],
    [⟨-1, 0, 9⟩, ⟨-1, 1, 9⟩, ⟨-1, 1, 13⟩, ⟨1, 2, 11⟩, ⟨1, 3, 11⟩, ⟨1, 3, 12⟩],
    [⟨1, 0, 13⟩, ⟨-1, 2, 12⟩],
    [⟨-1, 0, 9⟩, ⟨-1, 0, 11⟩, ⟨1, 1, 10⟩, ⟨1, 1, 12⟩, ⟨1, 3, 12⟩, ⟨-1, 4, 11⟩],
    [⟨-1, 3, 10⟩, ⟨1, 4, 9⟩],
    [⟨-1, 0, 0⟩, ⟨-1, 0, 1⟩, ⟨-1, 0, 2⟩, ⟨-1, 0, 3⟩, ⟨-1, 0, 5⟩, ⟨-1, 0, 7⟩, ⟨-2, 0, 9⟩, ⟨-1, 0, 10⟩, ⟨-1, 0, 11⟩, ⟨-1, 0, 12⟩, ⟨-1, 1, 5⟩, ⟨-1, 2, 12⟩, ⟨1, 4, 8⟩],
    [⟨-1, 0, 3⟩, ⟨-1, 0, 9⟩, ⟨1, 1, 2⟩, ⟨1, 1, 7⟩, ⟨1, 2, 11⟩, ⟨-1, 3, 8⟩],
    [⟨-1, 0, 7⟩, ⟨-1, 0, 9⟩, ⟨1, 2, 5⟩, ⟨1, 2, 10⟩, ⟨1, 3, 5⟩, ⟨-1, 4, 7⟩],
    [⟨-1, 0, 9⟩, ⟨1, 1, 7⟩, ⟨-1, 2, 6⟩, ⟨-1, 2, 9⟩, ⟨1, 3, 5⟩, ⟨1, 3, 7⟩],
    [⟨1, 0, 6⟩, ⟨-1, 1, 5⟩]]

private def GradientTerm.value {R : Type*} [CommRing R]
    (t : GradientTerm) (m : Fin 14 → R) : R :=
  (t.coefficient : R) * (m t.left * m t.right)

private def GradientTerm.hessianEntry {R : Type*} [CommRing R]
    (t : GradientTerm) (m : Fin 14 → R) (j : Fin 14) : R :=
  (t.coefficient : R) *
    ((if j = t.right then m t.left else 0) + (if j = t.left then m t.right else 0))

private theorem gradient_eq_term_sum {R : Type*} [CommRing R]
    (m : Fin 14 → R) (i : Fin 14) :
    fourMatchingGradient m i = ((gradientTerms i).map (fun t => t.value m)).sum := by
  fin_cases i <;> norm_num [fourMatchingGradient, gradientTerms, GradientTerm.value] <;> ring

/-- The Hessian matrix is the sum of the Hessians of the quadratic gradient terms. -/
def fourMatchingHessian {R : Type*} [CommRing R] (m : Fin 14 → R) :
    Matrix (Fin 14) (Fin 14) R :=
  fun i j => ((gradientTerms i).map (fun t => t.hessianEntry m j)).sum

private theorem GradientTerm.hessianEntry_scale {R : Type*} [CommRing R]
    (t : GradientTerm) (z : R) (m : Fin 14 → R) (j : Fin 14) :
    t.hessianEntry (fun i => z * m i) j = z * t.hessianEntry m j := by
  unfold GradientTerm.hessianEntry
  split_ifs <;> ring

/-- The matching Hessian is linear under scaling of its coordinates. -/
theorem fourMatchingHessian_scale {R : Type*} [CommRing R] (z : R) (m : Fin 14 → R) :
    fourMatchingHessian (fun i => z * m i) = z • fourMatchingHessian m := by
  ext i j
  simp only [fourMatchingHessian, Matrix.smul_apply, smul_eq_mul, GradientTerm.hessianEntry_scale]
  exact List.sum_map_mul_left _ _ _

private theorem term_hessian_sum {R : Type*} [CommRing R]
    (t : GradientTerm) (m n : Fin 14 → R) :
    (∑ j, t.hessianEntry m j * n j) =
      (t.coefficient : R) * (m t.left * n t.right + m t.right * n t.left) := by
  calc
    _ = ∑ j : Fin 14,
        ((if j = t.right then (t.coefficient : R) * m t.left * n j else 0) +
          (if j = t.left then (t.coefficient : R) * m t.right * n j else 0)) := by
      apply Finset.sum_congr rfl
      intro j _
      unfold GradientTerm.hessianEntry
      split_ifs <;> ring
    _ = _ := by
      simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      ring

theorem fourMatchingHessian_mulVec_apply {R : Type*} [CommRing R]
    (m n : Fin 14 → R) (i : Fin 14) :
    (fourMatchingHessian m).mulVec n i =
      fourMatchingGradient (fun j => m j + n j) i -
        fourMatchingGradient m i - fourMatchingGradient n i := by
  change (∑ j, ((gradientTerms i).map (fun t => t.hessianEntry m j)).sum * n j) = _
  simp only [gradient_eq_term_sum]
  generalize gradientTerms i = ts
  induction ts with
  | nil => simp
  | cons t ts ih =>
      simp only [List.map_cons, List.sum_cons, add_mul, Finset.sum_add_distrib]
      rw [term_hessian_sum, ih]
      simp only [GradientTerm.value]
      ring

/-- The indices of the first eight T34 Hessian pivots in two four-by-four blocks. -/
def t34HessianPivotIndices : Fin 4 ⊕ Fin 4 → Fin 14 :=
  Sum.elim (![1, 4, 11, 13]) (![3, 7, 2, 12])

def t34HessianPivotUnit : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0, 0, 0, -1;
     0, 0, 1, 0;
     0, 1, 0, 0;
     -1, 0, 0, 0]

def t34HessianPivotCross (a b q : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0, b - q - 1, -q - 1, -1;
     0, a + b + 1, 0, 0;
     1, b - q, -q, 0;
     0, 0, 0, 0]

def t34HessianPivotTail (b q s : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0, b, 0, 0;
     b, 0, 0, b - q;
     0, 0, 0, -q - s - 1;
     0, b - q, -q - s - 1, 0]

set_option maxRecDepth 3000 in
set_option maxHeartbeats 2000000 in
/-- The leading eight Hessian indices give a block independent of the height. -/
theorem t34Hessian_pivotBlock (p r a b c q s h : ℝ) :
    (fourMatchingHessian (t34HeightLift p r a b c q 1 s h)).submatrix
        t34HessianPivotIndices t34HessianPivotIndices =
      Matrix.fromBlocks t34HessianPivotUnit (t34HessianPivotCross a b q)
        (t34HessianPivotCross a b q)ᵀ (t34HessianPivotTail b q s) := by
  ext i j : 1
  rcases i with i | i <;> rcases j with j | j <;>
    fin_cases i <;> fin_cases j <;>
    simp only [Matrix.submatrix_apply, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.transpose_apply,
      t34HessianPivotIndices, Sum.elim_inl, Sum.elim_inr, t34HessianPivotUnit,
      t34HessianPivotCross, t34HessianPivotTail, Matrix.of_apply, Matrix.cons_val] <;>
    simp (config := { decide := true }) only [fourMatchingHessian, gradientTerms,
      Matrix.cons_val, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      GradientTerm.hessianEntry, t34HeightLift] <;>
    norm_num [Fin.ext_iff, Matrix.cons_val, Matrix.cons_val_succ', Matrix.cons_val_zero'] <;> ring

/-- The entries joining the leading pivots and the ninth pivot. -/
def t34HessianNinthColumn (p b c : ℝ) : Fin 4 ⊕ Fin 4 → ℝ :=
  Sum.elim (![0, 0, 0, -b - c - 1]) (![0, 0, -b, p - c])

set_option maxRecDepth 3000 in
set_option maxHeartbeats 1000000 in
theorem t34Hessian_ninth_entries (p r a b c q s h : ℝ) :
    let H := fourMatchingHessian (t34HeightLift p r a b c q 1 s h)
    H 6 6 = 0 ∧
      (∀ i, H (t34HessianPivotIndices i) 6 = t34HessianNinthColumn p b c i) ∧
      ∀ i, H 6 (t34HessianPivotIndices i) = t34HessianNinthColumn p b c i := by
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · simp (config := { decide := true }) only [fourMatchingHessian, gradientTerms,
      Matrix.cons_val, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      GradientTerm.hessianEntry, t34HeightLift] <;> norm_num
  all_goals
    intro i
    rcases i with i | i <;> fin_cases i <;>
      simp only [t34HessianPivotIndices, t34HessianNinthColumn, Sum.elim_inl, Sum.elim_inr,
        Matrix.cons_val] <;>
      simp (config := { decide := true }) only [fourMatchingHessian, gradientTerms,
        Matrix.cons_val, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        GradientTerm.hessianEntry, t34HeightLift] <;>
      norm_num [Fin.ext_iff, Matrix.cons_val, Matrix.cons_val_succ', Matrix.cons_val_zero'] <;> ring

end MOC
