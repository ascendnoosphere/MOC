import Mathlib.Algebra.BigOperators.Fin
import Mathlib.LinearAlgebra.Matrix.PosDef

/-! The squared-norm bound for deleting a coordinate from exterior coefficients.
The recursive blocks record whether the first coordinate is present. -/

open BigOperators Matrix
open scoped ComplexOrder

namespace MOC

noncomputable section

/-- Subsets of the first (n) coordinates in two branches at each coordinate. -/
def SubsetCube : ℕ → Type
  | 0 => Unit
  | n + 1 => SubsetCube n ⊕ SubsetCube n

instance subsetCubeFintype (n : ℕ) : Fintype (SubsetCube n) :=
  match n with
  | 0 => inferInstanceAs (Fintype Unit)
  | n + 1 =>
    letI : Fintype (SubsetCube n) := subsetCubeFintype n
    inferInstanceAs (Fintype (SubsetCube n ⊕ SubsetCube n))

instance subsetCubeDecidableEq (n : ℕ) : DecidableEq (SubsetCube n) :=
  match n with
  | 0 => inferInstanceAs (DecidableEq Unit)
  | n + 1 =>
    letI : DecidableEq (SubsetCube n) := subsetCubeDecidableEq n
    inferInstanceAs (DecidableEq (SubsetCube n ⊕ SubsetCube n))

/-- Coefficient matrix of contraction by a vector in coordinate order. -/
def subsetContraction : (n : ℕ) → (Fin n → ℂ) → Matrix (SubsetCube n) (SubsetCube n) ℂ
  | 0, _ => 0
  | n + 1, u =>
    let C := subsetContraction n (fun j => u j.succ)
    fromBlocks C ((star (u 0)) • 1) 0 (-C)

private theorem contractionBlock_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C D : Matrix ι ι ℂ) (u x : ℂ) :
    let A := fromBlocks C (star u • (1 : Matrix ι ι ℂ)) 0 (-C)
    let B := fromBlocks D (star x • (1 : Matrix ι ι ℂ)) 0 (-D)
    let G := C * Dᴴ + Dᴴ * C + (star u * x) • (1 : Matrix ι ι ℂ)
    A * Bᴴ + Bᴴ * A = fromBlocks G 0 0 G := by
  dsimp only
  simp only [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, Matrix.fromBlocks_add,
    Matrix.conjTranspose_zero, Matrix.conjTranspose_smul, Matrix.conjTranspose_one, star_star,
    Matrix.conjTranspose_neg, Matrix.mul_zero, Matrix.zero_mul, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.one_mul, Matrix.mul_one, smul_smul, zero_add, add_zero, neg_mul, mul_neg,
    neg_neg, smul_neg, neg_add_cancel, add_neg_cancel, mul_comm x (star u)]
  abel_nf

/-- Contraction and exterior insertion have a scalar anticommutator. -/
theorem subsetContraction_adjoint_anticommutator (n : ℕ) (u x : Fin n → ℂ) :
    let C := subsetContraction n u
    let D := subsetContraction n x
    C * Dᴴ + Dᴴ * C = (∑ j, star (u j) * x j) • (1 : Matrix _ _ ℂ) := by
  induction n with
  | zero => simp [subsetContraction]
  | succ n ih =>
    let C := subsetContraction n (fun j => u j.succ)
    let D := subsetContraction n (fun j => x j.succ)
    let q := ∑ j : Fin n, star (u j.succ) * x j.succ
    have hD : C * Dᴴ + Dᴴ * C = q • (1 : Matrix (SubsetCube n) (SubsetCube n) ℂ) :=
      ih (fun j => u j.succ) (fun j => x j.succ)
    let z := star (u 0) * x 0
    have hstep : C * Dᴴ + Dᴴ * C + z • (1 : Matrix (SubsetCube n) (SubsetCube n) ℂ) =
        (z + q) • (1 : Matrix (SubsetCube n) (SubsetCube n) ℂ) := by
      rw [hD, add_smul, add_comm]
    have hone : (1 : Matrix (SubsetCube n ⊕ SubsetCube n) (SubsetCube n ⊕ SubsetCube n) ℂ) =
        fromBlocks (1 : Matrix (SubsetCube n) (SubsetCube n) ℂ) 0 0 1 := by
      ext (i | i) (j | j) : 1 <;> simp [Matrix.one_apply]
    change (fromBlocks C (star (u 0) • 1) 0 (-C)) *
        (fromBlocks D (star (x 0) • 1) 0 (-D))ᴴ +
      (fromBlocks D (star (x 0) • 1) 0 (-D))ᴴ *
        (fromBlocks C (star (u 0) • 1) 0 (-C)) = _
    rw [contractionBlock_eq, hstep, Fin.sum_univ_succ, hone, Matrix.fromBlocks_smul, smul_zero]

/-- The two Gram matrices add to a scalar identity, giving the contraction bound. -/
theorem subsetContraction_anticommutator (n : ℕ) (u : Fin n → ℂ) :
    let C := subsetContraction n u
    C * Cᴴ + Cᴴ * C = (∑ j, (Complex.normSq (u j) : ℂ)) • (1 : Matrix _ _ ℂ) := by
  have hu (j : Fin n) : star (u j) * u j = (Complex.normSq (u j) : ℂ) := by
    rw [mul_comm]
    exact Complex.mul_conj _
  simpa only [hu] using subsetContraction_adjoint_anticommutator n u u

private theorem complex_sum_normSq {ι : Type*} [Fintype ι] (v : ι → ℂ) :
    (((∑ j, Complex.normSq (v j)) : ℝ) : ℂ) = star v ⬝ᵥ v := by
  rw [Complex.ofReal_sum]
  unfold dotProduct
  apply Finset.sum_congr rfl
  intro j _
  simpa only [Pi.star_apply, mul_comm] using (Complex.mul_conj (v j)).symm

/-- Contraction by a unit vector cannot increase the total squared coefficient mass. -/
theorem subsetContraction_normSq_bound (n : ℕ) (u : Fin n → ℂ) (v : SubsetCube n → ℂ) :
    ∑ j, Complex.normSq ((subsetContraction n u *ᵥ v) j) ≤
      (∑ j, Complex.normSq (u j)) * ∑ j, Complex.normSq (v j) := by
  let C := subsetContraction n u
  have hpositive := (Matrix.posSemidef_self_mul_conjTranspose C).2 v
  have hle : star (C *ᵥ v) ⬝ᵥ (C *ᵥ v) ≤
      (∑ j, (Complex.normSq (u j) : ℂ)) * (star v ⬝ᵥ v) := calc
    _ = star v ⬝ᵥ ((Cᴴ * C) *ᵥ v) := by
      simp only [Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul]
    _ ≤ star v ⬝ᵥ ((C * Cᴴ + Cᴴ * C) *ᵥ v) := by
      rw [Matrix.add_mulVec, dotProduct_add]
      exact le_add_of_nonneg_left hpositive
    _ = _ := by
      rw [subsetContraction_anticommutator n u, Matrix.smul_mulVec_assoc, Matrix.one_mulVec,
        dotProduct_smul, smul_eq_mul]
  rw [← complex_sum_normSq (C *ᵥ v), ← complex_sum_normSq v, ← Complex.ofReal_sum,
    ← Complex.ofReal_mul] at hle
  exact Complex.real_le_real.mp hle

/-- The ordinary finite set represented by a subset-cube coordinate. -/
def subsetCubeLabels : (n : ℕ) → SubsetCube n → Finset (Fin n)
  | 0, _ => ∅
  | n + 1, Sum.inl I => (subsetCubeLabels n I).map (Fin.succEmb n)
  | n + 1, Sum.inr I => insert 0 ((subsetCubeLabels n I).map (Fin.succEmb n))

/-- A nonzero matrix entry can only delete a label. -/
theorem subsetContraction_labels_subset (n : ℕ) (u : Fin n → ℂ) (I J : SubsetCube n)
    (h : subsetContraction n u I J ≠ 0) :
    subsetCubeLabels n I ⊆ subsetCubeLabels n J := by
  induction n with
  | zero => simp [subsetContraction] at h
  | succ n ih =>
    cases I with
    | inl I =>
      cases J with
      | inl J =>
        exact Finset.map_subset_map.mpr (ih (fun j => u j.succ) I J h)
      | inr J =>
        have hIJ : I = J := by
          by_cases hEq : I = J
          · exact hEq
          · simp [subsetContraction, Matrix.one_apply, hEq] at h
        subst J
        exact Finset.subset_insert _ _
    | inr I =>
      cases J with
      | inl J => simp [subsetContraction] at h
      | inr J =>
        have h' : subsetContraction n (fun j => u j.succ) I J ≠ 0 := by
          simpa [subsetContraction] using h
        exact Finset.insert_subset_insert _ (Finset.map_subset_map.mpr (ih _ I J h'))

/-- The mass of the contraction on a family is bounded by the original mass on its upper
shadow. This holds for arbitrary exterior coefficient vectors. -/
theorem subsetContraction_shadow_bound (n : ℕ) (u : Fin n → ℂ)
    (hu : ∑ j, Complex.normSq (u j) = 1) (v : SubsetCube n → ℂ)
    (S : Finset (SubsetCube n)) :
    ∑ I ∈ S, Complex.normSq ((subsetContraction n u *ᵥ v) I) ≤
      ∑ J ∈ Finset.univ.filter
        (fun J => ∃ I ∈ S, subsetCubeLabels n I ⊆ subsetCubeLabels n J), Complex.normSq (v J) := by
  classical
  let C := subsetContraction n u
  let T := Finset.univ.filter (fun J => ∃ I ∈ S, subsetCubeLabels n I ⊆ subsetCubeLabels n J)
  let w (J : SubsetCube n) := if J ∈ T then v J else 0
  have hmatch (I : SubsetCube n) (hI : I ∈ S) : (C *ᵥ v) I = (C *ᵥ w) I := by
    unfold Matrix.mulVec dotProduct
    apply Finset.sum_congr rfl
    intro J _
    by_cases hJ : J ∈ T
    · simp [w, hJ]
    · by_cases hC : C I J = 0
      · simp [hC]
      · exact False.elim (hJ (Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, I, hI, subsetContraction_labels_subset n u I J hC⟩))
  calc
    _ = ∑ I ∈ S, Complex.normSq ((C *ᵥ w) I) := Finset.sum_congr rfl (fun I hi => by rw [hmatch I hi])
    _ ≤ ∑ I, Complex.normSq ((C *ᵥ w) I) := Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ S) (fun _ _ _ => Complex.normSq_nonneg _)
    _ ≤ ∑ J, Complex.normSq (w J) := by
      simpa only [hu, one_mul] using subsetContraction_normSq_bound n u w
    _ = ∑ J ∈ T, Complex.normSq (v J) := by
      dsimp only [w, T]
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro J _
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      split_ifs <;> simp

private def subsetCubeEmpty : (n : ℕ) → SubsetCube n
  | 0 => ()
  | n + 1 => Sum.inl (subsetCubeEmpty n)

private theorem subsetContraction_empty_column (n : ℕ) (u : Fin n → ℂ) (I : SubsetCube n) :
    subsetContraction n u I (subsetCubeEmpty n) = 0 := by
  induction n with
  | zero => simp [subsetContraction]
  | succ n ih =>
    cases I with
    | inl I => simpa [subsetContraction, subsetCubeEmpty] using ih (fun j => u j.succ) I
    | inr I => simp [subsetContraction, subsetCubeEmpty]

/-- Exterior coefficients obtained by inserting each column before its successors. -/
def exteriorColumnVector (n : ℕ) : List (Fin n → ℂ) → SubsetCube n → ℂ
  | [] => Pi.single (subsetCubeEmpty n) 1
  | x :: columns => (subsetContraction n x)ᴴ *ᵥ exteriorColumnVector n columns

@[simp] theorem exteriorColumnVector_nil_zero : exteriorColumnVector 0 [] () = 1 := by
  simp [exteriorColumnVector, subsetCubeEmpty]

@[simp] theorem exteriorColumnVector_nil_skip (I : SubsetCube n) :
    exteriorColumnVector (n + 1) [] (.inl I) = exteriorColumnVector n [] I := by
  by_cases h : I = subsetCubeEmpty n
  · subst I
    simp [exteriorColumnVector, subsetCubeEmpty]
  · have h' : (Sum.inl I : SubsetCube (n + 1)) ≠ Sum.inl (subsetCubeEmpty n) :=
      fun he => h (Sum.inl.inj he)
    simp only [exteriorColumnVector, subsetCubeEmpty, Pi.single_apply, h, h', if_false]

@[simp] theorem exteriorColumnVector_nil_take (I : SubsetCube n) :
    exteriorColumnVector (n + 1) [] (.inr I) = 0 := by
  simp [exteriorColumnVector, subsetCubeEmpty]

/-- Contraction by a vector orthogonal to every factor kills the exterior product. -/
theorem subsetContraction_mulVec_exteriorColumnVector_orthogonal (n : ℕ)
    (u : Fin n → ℂ) (columns : List (Fin n → ℂ))
    (ho : ∀ x ∈ columns, (∑ j, star (u j) * x j) = 0) :
    subsetContraction n u *ᵥ exteriorColumnVector n columns = 0 := by
  induction columns with
  | nil =>
    funext I
    rw [exteriorColumnVector, Matrix.mulVec_single_one]
    exact subsetContraction_empty_column n u I
  | cons x columns ih =>
    have hx := ho x List.mem_cons_self
    have hcols : ∀ y ∈ columns, (∑ j, star (u j) * y j) = 0 :=
      fun y hy => ho y (List.mem_cons_of_mem x hy)
    have hz : subsetContraction n u * (subsetContraction n x)ᴴ +
        (subsetContraction n x)ᴴ * subsetContraction n u = 0 := by
      simpa only [hx, zero_smul] using subsetContraction_adjoint_anticommutator n u x
    have hz' : subsetContraction n u * (subsetContraction n x)ᴴ =
        -((subsetContraction n x)ᴴ * subsetContraction n u) := eq_neg_iff_add_eq_zero.mpr hz
    rw [exteriorColumnVector, Matrix.mulVec_mulVec, hz', Matrix.neg_mulVec,
      ← Matrix.mulVec_mulVec, ih hcols, Matrix.mulVec_zero, neg_zero]

/-- Contraction deletes the first exterior column if it has norm one and is orthogonal to the rest. -/
theorem subsetContraction_exteriorColumnVector (n : ℕ) (u : Fin n → ℂ)
    (hu : ∑ j, Complex.normSq (u j) = 1) (columns : List (Fin n → ℂ))
    (ho : ∀ x ∈ columns, (∑ j, star (u j) * x j) = 0) :
    subsetContraction n u *ᵥ exteriorColumnVector n (u :: columns) =
      exteriorColumnVector n columns := by
  let C := subsetContraction n u
  let v := exteriorColumnVector n columns
  have hz : C *ᵥ v = 0 := subsetContraction_mulVec_exteriorColumnVector_orthogonal n u columns ho
  have hId : C * Cᴴ + Cᴴ * C = 1 := by
    rw [subsetContraction_anticommutator n u, ← Complex.ofReal_sum, hu, Complex.ofReal_one, one_smul]
  change C *ᵥ (Cᴴ *ᵥ v) = v
  calc
    _ = (C * Cᴴ) *ᵥ v := Matrix.mulVec_mulVec _ _ _
    _ = (C * Cᴴ + Cᴴ * C) *ᵥ v := by
      rw [Matrix.add_mulVec, ← Matrix.mulVec_mulVec _ Cᴴ C, hz, Matrix.mulVec_zero, add_zero]
    _ = _ := by rw [hId, Matrix.one_mulVec]

/-- The squared exterior coefficients of orthogonal columns satisfy the upper-shadow inequality
when one more orthogonal unit column is prepended. -/
theorem exteriorColumnVector_shadow_bound (n : ℕ) (u : Fin n → ℂ)
    (hu : ∑ j, Complex.normSq (u j) = 1) (columns : List (Fin n → ℂ))
    (ho : ∀ x ∈ columns, (∑ j, star (u j) * x j) = 0) (S : Finset (SubsetCube n)) :
    ∑ I ∈ S, Complex.normSq (exteriorColumnVector n columns I) ≤
      ∑ J ∈ Finset.univ.filter
        (fun J => ∃ I ∈ S, subsetCubeLabels n I ⊆ subsetCubeLabels n J),
          Complex.normSq (exteriorColumnVector n (u :: columns) J) := by
  have h := subsetContraction_shadow_bound n u hu (exteriorColumnVector n (u :: columns)) S
  rwa [subsetContraction_exteriorColumnVector n u hu columns ho] at h

end

end MOC
