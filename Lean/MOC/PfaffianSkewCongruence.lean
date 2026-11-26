import MOC.PfaffianMatchingModulus
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! Reduction of a nonsingular skew matrix to symplectic blocks. -/

open Matrix

namespace MOC

private def standardSymplecticPair : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; -1, 0]

/-- The standard skew matrix, with one symplectic block on each pair. -/
def standardSymplecticMatrix (n : ℕ) : Matrix (PfaffianIndex n) (PfaffianIndex n) ℂ :=
  fun i j => if i.1 = j.1 then standardSymplecticPair i.2 j.2 else 0

private def firstPairEquiv (n : ℕ) : Fin 2 ⊕ PfaffianIndex n ≃ PfaffianIndex (n + 1) where
  toFun := Sum.elim (fun j => (0, j)) (fun j => (j.1.succ, j.2))
  invFun i := Fin.cases (.inl i.2) (fun j => .inr (j, i.2)) i.1
  left_inv := by
    rintro (j | ⟨i, j⟩)
    · simp only [Sum.elim_inl, Fin.cases_zero]
    · simp only [Sum.elim_inr, Fin.cases_succ]
  right_inv := by
    rintro ⟨i, j⟩
    refine Fin.cases ?_ (fun k => ?_) i
    · simp only [Fin.cases_zero, Sum.elim_inl]
    · simp only [Fin.cases_succ, Sum.elim_inr]

private theorem standardSymplecticMatrix_split (n : ℕ) :
    (standardSymplecticMatrix (n + 1)).submatrix (firstPairEquiv n) (firstPairEquiv n) =
      fromBlocks standardSymplecticPair 0 0 (standardSymplecticMatrix n) := by
  ext (i | ⟨i, r⟩) (j | ⟨j, s⟩)
  · simp [firstPairEquiv, standardSymplecticMatrix]
  · simp [firstPairEquiv, standardSymplecticMatrix]
  · simp [firstPairEquiv, standardSymplecticMatrix]
  · simp [firstPairEquiv, standardSymplecticMatrix]

/-- Every standard symplectic block has determinant one. -/
theorem standardSymplecticMatrix_det (n : ℕ) : (standardSymplecticMatrix n).det = 1 := by
  induction n with
  | zero => exact Matrix.det_isEmpty
  | succ n ih =>
      rw [← Matrix.det_submatrix_equiv_self (firstPairEquiv n), standardSymplecticMatrix_split,
        Matrix.det_fromBlocks_zero₂₁, ih, mul_one, Matrix.det_fin_two]
      norm_num [standardSymplecticPair]

private theorem skew_congruence {ι : Type*} [Fintype ι]
    (K S : Matrix ι ι ℂ) (hK : Kᵀ = -K) : (Sᵀ * K * S)ᵀ = -(Sᵀ * K * S) := by
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, hK, Matrix.mul_neg,
    Matrix.neg_mul, Matrix.mul_assoc]

private theorem split_off_skew_pair {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : Matrix (Fin 2 ⊕ ι) (Fin 2 ⊕ ι) ℂ) (hK : Kᵀ = -K)
    (hA : K.toBlocks₁₁.det ≠ 0) :
    ∃ S : Matrix (Fin 2 ⊕ ι) (Fin 2 ⊕ ι) ℂ, ∃ L : Matrix ι ι ℂ,
      S.det = 1 ∧ Lᵀ = -L ∧ Sᵀ * K * S = fromBlocks K.toBlocks₁₁ 0 0 L := by
  let A := K.toBlocks₁₁
  let B := K.toBlocks₁₂
  let C := K.toBlocks₂₁
  let D := K.toBlocks₂₂
  let X := -(A⁻¹ * B)
  let S : Matrix (Fin 2 ⊕ ι) (Fin 2 ⊕ ι) ℂ := fromBlocks 1 X 0 1
  let L := C * X + D
  have hshape : K = fromBlocks A B C D := (Matrix.fromBlocks_toBlocks K).symm
  have hAX : A * X + B = 0 := by
    rw [show X = -(A⁻¹ * B) from rfl, Matrix.mul_neg, ← Matrix.mul_assoc,
      Matrix.mul_nonsing_inv A (isUnit_iff_ne_zero.mpr hA), Matrix.one_mul, neg_add_cancel]
  have hKS : K * S = fromBlocks A 0 C L := by
    rw [hshape, show S = fromBlocks 1 X 0 1 from rfl, Matrix.fromBlocks_multiply]
    simp only [Matrix.mul_one, Matrix.mul_zero, add_zero, hAX, L]
  have hS : Sᵀ * K * S = fromBlocks A 0 (Xᵀ * A + C) L := by
    rw [Matrix.mul_assoc, hKS, show S = fromBlocks 1 X 0 1 from rfl,
      Matrix.fromBlocks_transpose, Matrix.transpose_one, Matrix.transpose_zero,
      Matrix.fromBlocks_multiply]
    simp only [Matrix.one_mul, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
  have hs := skew_congruence K S hK
  rw [hS] at hs
  have hcross : Xᵀ * A + C = 0 := by
    ext i j
    have he := congrArg (fun M : Matrix (Fin 2 ⊕ ι) (Fin 2 ⊕ ι) ℂ =>
      M (.inl j) (.inr i)) hs
    simpa only [Matrix.transpose_apply, Matrix.neg_apply, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₁₂, Matrix.zero_apply, neg_zero] using he
  have hL : Lᵀ = -L := by
    ext i j
    have he := congrArg (fun M : Matrix (Fin 2 ⊕ ι) (Fin 2 ⊕ ι) ℂ =>
      M (.inr i) (.inr j)) hs
    simpa only [Matrix.transpose_apply, Matrix.neg_apply, Matrix.fromBlocks_apply₂₂] using he
  refine ⟨S, L, ?_, hL, ?_⟩
  · simp only [S, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, one_mul]
  · rw [hS, hcross]

private theorem normalize_skew_pair (A : Matrix (Fin 2) (Fin 2) ℂ)
    (hA : ∀ i j, A j i = -A i j) (hc : A 0 1 ≠ 0) :
    A.det ≠ 0 ∧ ∃ P : Matrix (Fin 2) (Fin 2) ℂ, Pᵀ * A * P = standardSymplecticPair := by
  let c := A 0 1
  have hc' : c ≠ 0 := hc
  have hz (i : Fin 2) : A i i = 0 := by
    linear_combination (1 / 2 : ℂ) * hA i i
  have he : A = !![0, c; -c, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [c, hz, hA 0 1]
  refine ⟨?_, diagonal ![1, c⁻¹], ?_⟩
  · rw [he, Matrix.det_fin_two]
    simpa using mul_ne_zero hc' hc'
  · rw [Matrix.diagonal_transpose, he]
    ext i j
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    fin_cases i <;> fin_cases j <;>
      simp [standardSymplecticPair, hc', inv_mul_cancel₀, mul_inv_cancel₀, mul_neg]

/-- A nonsingular skew matrix is congruent to the standard symplectic matrix. -/
theorem exists_congr_standardSymplecticMatrix {n : ℕ}
    (K : Matrix (PfaffianIndex n) (PfaffianIndex n) ℂ)
    (hskew : ∀ i j, K j i = -K i j) (hdet : K.det ≠ 0) :
    ∃ S : Matrix (PfaffianIndex n) (PfaffianIndex n) ℂ,
      S.det ≠ 0 ∧ Sᵀ * K * S = standardSymplecticMatrix n := by
  classical
  induction n with
  | zero =>
      refine ⟨1, by simp, ?_⟩
      ext i j
      exact Fin.elim0 i.1
  | succ n ih =>
      let p : PfaffianIndex (n + 1) := (0, 0)
      let r : PfaffianIndex (n + 1) := (0, 1)
      have hp : K p p = 0 := by linear_combination (1 / 2 : ℂ) * hskew p p
      obtain ⟨q, hq⟩ : ∃ q, K p q ≠ 0 := by
        by_contra! h
        exact hdet (Matrix.det_eq_zero_of_row_eq_zero p h)
      have hpq : p ≠ q := fun h => hq (h ▸ hp)
      have hpr : p ≠ r := fun h => (by decide : (0 : Fin 2) ≠ 1) (congrArg Prod.snd h)
      let e₀ := firstPairEquiv n
      let e := e₀.trans (Equiv.swap r q)
      have he₀ : e (.inl 0) = p := Equiv.swap_apply_of_ne_of_ne hpr hpq
      have he₁ : e (.inl 1) = q := Equiv.swap_apply_left r q
      let M := K.submatrix e e
      have hM : Mᵀ = -M := by
        ext i j
        exact hskew (e i) (e j)
      have hdM : M.det ≠ 0 := by
        rw [show M = K.submatrix e e from rfl, Matrix.det_submatrix_equiv_self]
        exact hdet
      let A := M.toBlocks₁₁
      have hAs (i j : Fin 2) : A j i = -A i j := hskew (e (.inl i)) (e (.inl j))
      have hc : A 0 1 ≠ 0 := by
        change K (e (.inl 0)) (e (.inl 1)) ≠ 0
        rwa [he₀, he₁]
      obtain ⟨hA, P, hP⟩ := normalize_skew_pair A hAs hc
      obtain ⟨R, L, hR, hLs, hRL⟩ := split_off_skew_pair M hM hA
      have hLd : L.det ≠ 0 := by
        have h := congrArg Matrix.det hRL
        rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hR, one_mul, mul_one,
          Matrix.det_fromBlocks_zero₂₁] at h
        intro hz
        exact hdM (by rw [h, hz, mul_zero])
      have hLskew (i j : PfaffianIndex n) : L j i = -L i j :=
        congrArg (fun A : Matrix (PfaffianIndex n) (PfaffianIndex n) ℂ => A i j) hLs
      obtain ⟨Q, _, hQ⟩ := ih L hLskew hLd
      let T : Matrix (Fin 2 ⊕ PfaffianIndex n) (Fin 2 ⊕ PfaffianIndex n) ℂ := fromBlocks P 0 0 Q
      have hT : Tᵀ * (Rᵀ * M * R) * T = fromBlocks standardSymplecticPair 0 0
          (standardSymplecticMatrix n) := by
        rw [hRL, show T = fromBlocks P 0 0 Q from rfl, Matrix.fromBlocks_transpose,
          Matrix.transpose_zero, Matrix.transpose_zero, Matrix.fromBlocks_multiply,
          Matrix.fromBlocks_multiply]
        simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, hP, hQ]
      let S : Matrix (PfaffianIndex (n + 1)) (PfaffianIndex (n + 1)) ℂ :=
        (R * T).submatrix e.symm e₀.symm
      have hS : S.submatrix e e₀ = R * T := by
        ext i j
        change (R * T) (e.symm (e i)) (e₀.symm (e₀ j)) = (R * T) i j
        rw [e.symm_apply_apply, e₀.symm_apply_apply]
      have hsub : (Sᵀ * K * S).submatrix e₀ e₀ =
          (S.submatrix e e₀)ᵀ * M * S.submatrix e e₀ := by
        symm
        rw [Matrix.transpose_submatrix, show M = K.submatrix e e from rfl,
          Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv]
      have hsplit : (Sᵀ * K * S).submatrix e₀ e₀ = (standardSymplecticMatrix (n + 1)).submatrix e₀ e₀ := by
        rw [hsub, hS, Matrix.transpose_mul, standardSymplecticMatrix_split, ← hT]
        simp only [Matrix.mul_assoc]
      have he : Sᵀ * K * S = standardSymplecticMatrix (n + 1) := by
        ext i j
        have hij := congrArg (fun A : Matrix (Fin 2 ⊕ PfaffianIndex n) (Fin 2 ⊕ PfaffianIndex n) ℂ =>
          A (e₀.symm i) (e₀.symm j)) hsplit
        simpa only [Matrix.submatrix_apply, e₀.apply_symm_apply] using hij
      refine ⟨S, ?_, he⟩
      intro hs
      have hd := congrArg Matrix.det he
      rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hs, zero_mul, zero_mul,
        standardSymplecticMatrix_det] at hd
      exact zero_ne_one hd

end MOC
