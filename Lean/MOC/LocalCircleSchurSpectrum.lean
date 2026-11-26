import MOC.NormalCompressionReduction
import MOC.Normal
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import MOC.WeakHermitianCompressionInterlacing

open BigOperators Matrix

namespace MOC

noncomputable section

variable {n : ℕ}

/-- The coordinate equivalence that puts the pivot first. -/
def scalarSchurIndex (n : ℕ) : Unit ⊕ Fin n ≃ Fin (n + 1) where
  toFun := Sum.elim (fun _ => 0) Fin.succ
  invFun := Fin.cases (Sum.inl ()) Sum.inr
  left_inv := by
    rintro (i | i)
    · cases i
      rfl
    · rfl
  right_inv := by intro i; refine Fin.cases ?_ (fun j => ?_) i <;> rfl

/-- A one-by-one matrix with its single entry set to `t`. -/
def scalarBlock (t : ℂ) : Matrix Unit Unit ℂ := fun _ _ => t

private theorem det_scalarBlock (t : ℂ) : (scalarBlock t).det = t := by
  rw [Matrix.det_unique]
  rfl

private theorem inv_scalarBlock (t : ℂ) (ht : t ≠ 0) :
    (scalarBlock t)⁻¹ = scalarBlock t⁻¹ := by
  apply Matrix.inv_eq_right_inv
  ext i j : 1
  cases i
  cases j
  simp [Matrix.mul_apply, scalarBlock, ht]

section ScalarSchur

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Delete one coordinate after adding the scalar partner at that coordinate. -/
def scalarSchurComplement (C : Matrix (Unit ⊕ ι) (Unit ⊕ ι) ℂ) (r : ℂ) :
    Matrix ι ι ℂ :=
  C.toBlocks₂₂ -
    C.toBlocks₂₁ * scalarBlock (C (Sum.inl ()) (Sum.inl ()) + r)⁻¹ * C.toBlocks₁₂

theorem det_scalarSchurComplement
    (C : Matrix (Unit ⊕ ι) (Unit ⊕ ι) ℂ) (r : ℂ)
    (B : Matrix ι ι ℂ) (ht : C (Sum.inl ()) (Sum.inl ()) + r ≠ 0) :
    (C + fromBlocks (scalarBlock r) 0 0 B).det =
      (C (Sum.inl ()) (Sum.inl ()) + r) * (scalarSchurComplement C r + B).det := by
  let t := C (Sum.inl ()) (Sum.inl ()) + r
  have hsplit : C + fromBlocks (scalarBlock r) 0 0 B =
      fromBlocks (scalarBlock t) C.toBlocks₁₂ C.toBlocks₂₁ (C.toBlocks₂₂ + B) := by
    conv_lhs => rw [← Matrix.fromBlocks_toBlocks C]
    rw [Matrix.fromBlocks_add, add_zero, add_zero]
    congr 1
  haveI := Matrix.invertibleOfIsUnitDet (A := scalarBlock t) (by
    rw [det_scalarBlock]
    exact isUnit_iff_ne_zero.mpr ht)
  rw [hsplit, Matrix.det_fromBlocks₁₁, det_scalarBlock, Matrix.invOf_eq_nonsing_inv,
    inv_scalarBlock t ht]
  unfold scalarSchurComplement
  rw [add_sub_right_comm]

omit [Fintype ι] in
private theorem shift_identity_blocks (r : ℂ) :
    r • (1 : Matrix (Unit ⊕ ι) (Unit ⊕ ι) ℂ) =
      fromBlocks (scalarBlock r) 0 0 (r • (1 : Matrix ι ι ℂ)) := by
  ext (i | i) (j | j) : 1
  · cases i
    cases j
    simp [scalarBlock]
  · simp
  · simp
  · simp [Matrix.one_apply]

/-- The inverse of the shifted Schur complement is the principal block of
the inverse of the shifted input matrix. -/
theorem scalarSchurComplement_inverse
    (C : Matrix (Unit ⊕ ι) (Unit ⊕ ι) ℂ) (r : ℂ)
    (ht : C (Sum.inl ()) (Sum.inl ()) + r ≠ 0)
    (hC : (C + r • 1).det ≠ 0) :
    let S := scalarSchurComplement C r + r • 1
    S.det ≠ 0 ∧ S⁻¹ = ((C + r • 1)⁻¹).toBlocks₂₂ := by
  let t := C (Sum.inl ()) (Sum.inl ()) + r
  let D := C.toBlocks₂₂ + r • 1
  let Q := fromBlocks (scalarBlock t) C.toBlocks₁₂ C.toBlocks₂₁ D
  have hsplit : C + r • 1 = Q := by
    rw [shift_identity_blocks]
    conv_lhs => rw [← Matrix.fromBlocks_toBlocks C]
    rw [Matrix.fromBlocks_add, add_zero, add_zero]
    congr 1
  have hQ : Q.det ≠ 0 := hsplit ▸ hC
  haveI := Matrix.invertibleOfIsUnitDet (A := scalarBlock t) (by
    rw [det_scalarBlock]
    exact isUnit_iff_ne_zero.mpr ht)
  haveI := Matrix.invertibleOfIsUnitDet (A := Q) (isUnit_iff_ne_zero.mpr hQ)
  let S := scalarSchurComplement C r + r • 1
  let E := D - C.toBlocks₂₁ * ⅟ (scalarBlock t) * C.toBlocks₁₂
  haveI : Invertible E := Matrix.invertibleOfFromBlocks₁₁Invertible _ _ _ _
  have hE : E = S := by
    dsimp only [E, D, S, scalarSchurComplement]
    rw [Matrix.invOf_eq_nonsing_inv, inv_scalarBlock t ht, add_sub_right_comm]
  have hformula := Matrix.invOf_fromBlocks₁₁_eq (scalarBlock t) C.toBlocks₁₂ C.toBlocks₂₁ D
  have hinv : Q⁻¹.toBlocks₂₂ = E⁻¹ := by
    have he := congrArg Matrix.toBlocks₂₂ hformula
    simp only [Matrix.toBlocks_fromBlocks₂₂, Matrix.invOf_eq_nonsing_inv] at he
    simpa only [Q, E, Matrix.invOf_eq_nonsing_inv] using he
  change S.det ≠ 0 ∧ S⁻¹ = ((C + r • 1)⁻¹).toBlocks₂₂
  refine ⟨?_, ?_⟩
  · rw [← hE]
    exact isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det E).mp (isUnit_of_invertible E))
  · rw [hsplit, hinv, hE]

end ScalarSchur

private theorem conjugated_affine_diagonal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ℂ) (W : Matrix ι ι ℂ) (hW : IsUnitary W) (c d : ℂ) :
    W * diagonal (fun j => c + d * a j) * Wᴴ =
      c • (1 : Matrix ι ι ℂ) + d • (W * diagonal a * Wᴴ) := by
  have hc : diagonal (fun _ : ι => c) = c • (1 : Matrix ι ι ℂ) := by
    ext i j : 1
    by_cases hij : i = j <;> simp [Matrix.diagonal_apply, Matrix.one_apply, hij]
  rw [← Matrix.diagonal_add (fun _ => c) (fun j => d * a j),
    hc, show diagonal (fun j => d * a j) = d • diagonal a from
      Matrix.diagonal_smul d a]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hW.1]

private theorem conjugated_diagonal_inverse {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ℂ) (W : Matrix ι ι ℂ) (hW : IsUnitary W) (ha : ∀ i, a i ≠ 0) :
    (W * diagonal a * Wᴴ)⁻¹ = W * diagonal (fun i => (a i)⁻¹) * Wᴴ := by
  apply Matrix.inv_eq_right_inv
  calc
    _ = W * (diagonal a * diagonal (fun i => (a i)⁻¹)) * Wᴴ := by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc Wᴴ W, hW.2, Matrix.one_mul]
    _ = 1 := by
      rw [Matrix.diagonal_mul_diagonal]
      simp only [mul_inv_cancel₀ (ha _), Matrix.diagonal_one, Matrix.mul_one, hW.1]

private theorem conjugated_diagonal_shift {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ℂ) (W : Matrix ι ι ℂ) (hW : IsUnitary W) (r : ℂ) :
    W * diagonal a * Wᴴ + r • (1 : Matrix ι ι ℂ) =
      W * diagonal (fun i => a i + r) * Wᴴ := by
  simpa only [one_mul, one_smul, add_comm] using
    (conjugated_affine_diagonal a W hW r 1).symm

/-- A regular pivot gives a unitary diagonalization of the Schur complement.
Its reciprocal spectrum interlaces the input on the same affine line. -/
theorem exists_scalarSchurComplement_interlacing
    (h : Fin (n + 1) → ℂ) (W : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (hW : IsUnitary W) (r c d : ℂ) (lam : Fin (n + 1) → ℝ) (hmono : Monotone lam)
    (hh : ∀ i, h i + r ≠ 0)
    (hhl : ∀ i, (h i + r)⁻¹ = c + d * (lam i : ℂ))
    (ht : (W * diagonal h * Wᴴ) 0 0 + r ≠ 0) :
    let e := scalarSchurIndex n
    let C := (W * diagonal h * Wᴴ).submatrix e e
    let t := C (Sum.inl ()) (Sum.inl ()) + r
    ∃ (a : Fin n → ℂ) (δ : Fin n → ℝ) (V : Matrix (Fin n) (Fin n) ℂ),
      IsUnitary V ∧ (∀ i, lam i.castSucc ≤ δ i ∧ δ i ≤ lam i.succ) ∧
      (∀ i, a i + r ≠ 0) ∧ (∀ i, (a i + r)⁻¹ = c + d * (δ i : ℂ)) ∧
      scalarSchurComplement C r = V * diagonal a * Vᴴ ∧
      (∏ i, (h i + r)) = t * ∏ i, (a i + r) := by
  intro e C t
  let N := W * diagonal (fun i => h i + r) * Wᴴ
  let S := scalarSchurComplement C r + r • 1
  have hCshift : C + r • 1 = N.submatrix e e := by
    dsimp only [N]
    rw [← conjugated_diagonal_shift h W hW r]
    change _ = C + r • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ).submatrix e e
    rw [Matrix.submatrix_one_equiv]
  have hNdet : (C + r • 1).det = ∏ i, (h i + r) := by
    rw [hCshift, Matrix.det_submatrix_equiv_self, det_unitary_conjugation _ _ hW, Matrix.det_diagonal]
  have ht' : t ≠ 0 := ht
  obtain ⟨hS, hSinv⟩ : S.det ≠ 0 ∧ S⁻¹ = ((C + r • 1)⁻¹).toBlocks₂₂ :=
    scalarSchurComplement_inverse C r ht'
      (by rw [hNdet]; exact Finset.prod_ne_zero_iff.mpr (fun i _ => hh i))
  obtain ⟨δ, V, hV, hδ, hcomp⟩ := exists_interlacing_of_hermitian_compression lam hmono W hW 0
  rw [Fin.succAbove_zero] at hcomp
  let γ (i : Fin n) : ℂ := c + d * (δ i : ℂ)
  have hγ : S⁻¹ = V * diagonal γ * Vᴴ := by
    rw [hSinv, hCshift, Matrix.inv_submatrix_equiv]
    change N⁻¹.submatrix Fin.succ Fin.succ = _
    rw [conjugated_diagonal_inverse _ W hW hh, funext hhl,
      conjugated_affine_diagonal _ W hW c d, conjugated_affine_diagonal _ V hV c d]
    change c • ((1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ).submatrix Fin.succ Fin.succ) +
      d • ((W * diagonal (fun i => (lam i : ℂ)) * Wᴴ).submatrix Fin.succ Fin.succ) = _
    rw [Matrix.submatrix_one _ (Fin.succ_injective n), hcomp]
  have hγnz (i : Fin n) : γ i ≠ 0 := by
    have hn := isUnit_iff_ne_zero.mp (Matrix.isUnit_nonsing_inv_det (A := S)
      (isUnit_iff_ne_zero.mpr hS))
    rw [hγ, det_unitary_conjugation _ _ hV, Matrix.det_diagonal] at hn
    exact Finset.prod_ne_zero_iff.mp hn i (Finset.mem_univ _)
  let a (i : Fin n) := (γ i)⁻¹ - r
  have har (i : Fin n) : a i + r = (γ i)⁻¹ := sub_add_cancel _ _
  have hspec : S = V * diagonal (fun i => a i + r) * Vᴴ := by
    calc
      S = S⁻¹⁻¹ := (Matrix.nonsing_inv_nonsing_inv S (isUnit_iff_ne_zero.mpr hS)).symm
      _ = _ := by rw [hγ, conjugated_diagonal_inverse _ V hV hγnz, funext har]
  have hspec' : scalarSchurComplement C r = V * diagonal a * Vᴴ := by
    apply add_right_cancel (b := r • (1 : Matrix (Fin n) (Fin n) ℂ))
    rw [conjugated_diagonal_shift a V hV r]
    exact hspec
  have hSdet : S.det = ∏ i, (a i + r) := by
    rw [hspec, det_unitary_conjugation _ _ hV, Matrix.det_diagonal]
  refine ⟨a, δ, V, hV, hδ, fun i => by rw [har]; exact inv_ne_zero (hγnz i),
    fun i => by rw [har, inv_inv], hspec', ?_⟩
  rw [← hSdet, ← hNdet, shift_identity_blocks, det_scalarSchurComplement C r _ ht']

end

end MOC
