import MOC.Normal
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Real.Sqrt
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! The real form of the exterior square in order four. -/

open BigOperators Matrix

namespace MOC

abbrev HodgeIndex := Fin 3 × Fin 2

/-- The three oriented complementary pairs, with positive volume pairing. -/
def fourHodgePair (p : HodgeIndex) : Fin 2 → Fin 4 :=
  if p.2 = 0 then ![0, p.1.succ] else ![![2, 3], ![3, 1], ![1, 2]] p.1

private def hodgeOther (s : Fin 2) : Fin 2 := if s = 0 then 1 else 0

private theorem hodgeOther_involutive (s : Fin 2) : hodgeOther (hodgeOther s) = s := by
  fin_cases s <;> decide

/-- Exchange a coordinate pair and its oriented complement. -/
def fourHodgeFlip : Equiv.Perm HodgeIndex where
  toFun p := (p.1, hodgeOther p.2)
  invFun p := (p.1, hodgeOther p.2)
  left_inv p := Prod.ext rfl (hodgeOther_involutive p.2)
  right_inv p := Prod.ext rfl (hodgeOther_involutive p.2)

@[simp] theorem fourHodgeFlip_zero (i : Fin 3) : fourHodgeFlip (i, 0) = (i, 1) := rfl
@[simp] theorem fourHodgeFlip_one (i : Fin 3) : fourHodgeFlip (i, 1) = (i, 0) := rfl

/-- The second compound in the oriented pair coordinates. -/
def fourHodgeCompound {R : Type*} [CommRing R] (U : Matrix (Fin 4) (Fin 4) R) :
    Matrix HodgeIndex HodgeIndex R :=
  fun p q => U (fourHodgePair p 0) (fourHodgePair q 0) * U (fourHodgePair p 1) (fourHodgePair q 1) -
    U (fourHodgePair p 0) (fourHodgePair q 1) * U (fourHodgePair p 1) (fourHodgePair q 0)

private theorem fourHodgePair_binet {R : Type*} [CommRing R] (u v x y : Fin 4 → R) :
    (∑ p : HodgeIndex,
      (u (fourHodgePair p 0) * v (fourHodgePair p 1) -
        u (fourHodgePair p 1) * v (fourHodgePair p 0)) *
      (x (fourHodgePair p 0) * y (fourHodgePair p 1) -
        y (fourHodgePair p 0) * x (fourHodgePair p 1))) =
      (u ⬝ᵥ x) * (v ⬝ᵥ y) - (u ⬝ᵥ y) * (v ⬝ᵥ x) := by
  simp [Fintype.sum_prod_type, Fin.sum_univ_three, Fin.sum_univ_two, dotProduct, Fin.sum_univ_four,
    fourHodgePair, Matrix.cons_val]
  ring

theorem fourHodgeCompound_mul {R : Type*} [CommRing R] (U V : Matrix (Fin 4) (Fin 4) R) :
    fourHodgeCompound (U * V) = fourHodgeCompound U * fourHodgeCompound V := by
  ext p q
  exact (fourHodgePair_binet (U (fourHodgePair p 0)) (U (fourHodgePair p 1))
    (fun i => V i (fourHodgePair q 0)) (fun i => V i (fourHodgePair q 1))).symm

theorem fourHodgeCompound_diagonal {R : Type*} [CommRing R] (d : Fin 4 → R) :
    fourHodgeCompound (diagonal d) =
      diagonal (fun p => d (fourHodgePair p 0) * d (fourHodgePair p 1)) := by
  ext ⟨i,s⟩ ⟨j,t⟩
  fin_cases i <;> fin_cases j <;> fin_cases s <;> fin_cases t <;>
    simp [fourHodgeCompound, fourHodgePair, Matrix.diagonal_apply, Matrix.cons_val]

@[simp] theorem fourHodgeCompound_one {R : Type*} [CommRing R] :
    fourHodgeCompound (1 : Matrix (Fin 4) (Fin 4) R) = 1 := by
  have h := fourHodgeCompound_diagonal (1 : Fin 4 → R)
  simpa only [Pi.one_apply, one_mul, Matrix.diagonal_one] using h

theorem fourHodgeCompound_conjTranspose (U : Matrix (Fin 4) (Fin 4) ℂ) :
    fourHodgeCompound Uᴴ = (fourHodgeCompound U)ᴴ := by
  ext p q
  simp only [fourHodgeCompound, Matrix.conjTranspose_apply, star_sub, star_mul]
  ring

theorem fourHodgeCompound_unitary {U : Matrix (Fin 4) (Fin 4) ℂ} (hU : IsUnitary U) :
    IsUnitary (fourHodgeCompound U) := by
  constructor
  · rw [← fourHodgeCompound_conjTranspose, ← fourHodgeCompound_mul, hU.1, fourHodgeCompound_one]
  · rw [← fourHodgeCompound_conjTranspose, ← fourHodgeCompound_mul, hU.2, fourHodgeCompound_one]

private theorem four_det_wedge {R : Type*} [CommRing R] (U : Matrix (Fin 4) (Fin 4) R) :
    (∑ p : HodgeIndex,
      (U (fourHodgePair p 0) 0 * U (fourHodgePair p 1) 1 -
        U (fourHodgePair p 0) 1 * U (fourHodgePair p 1) 0) *
      (U (fourHodgePair (fourHodgeFlip p) 0) 2 * U (fourHodgePair (fourHodgeFlip p) 1) 3 -
        U (fourHodgePair (fourHodgeFlip p) 0) 3 * U (fourHodgePair (fourHodgeFlip p) 1) 2)) = U.det := by
  rw [Matrix.det_succ_column_zero]
  simp [Fintype.sum_prod_type, Fin.sum_univ_three, Fin.sum_univ_two, Fin.sum_univ_four,
    fourHodgePair, Matrix.cons_val, Matrix.det_fin_three, Matrix.submatrix_apply,
    Fin.succAbove, Fin.castSucc, Fin.succ]
  ring

private def hodgeFrameLabels (p q : HodgeIndex) : Fin 4 → Fin 4 :=
  ![fourHodgePair p 0, fourHodgePair p 1, fourHodgePair q 0, fourHodgePair q 1]

private theorem fourHodgeCompound_wedge_frame {R : Type*} [CommRing R]
    (U : Matrix (Fin 4) (Fin 4) R) (p q : HodgeIndex) :
    (∑ r, fourHodgeCompound U r p * fourHodgeCompound U (fourHodgeFlip r) q) =
      (U.submatrix id (hodgeFrameLabels p q)).det := by
  simpa only [fourHodgeCompound, Matrix.submatrix_apply, id_eq, hodgeFrameLabels,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three] using
    four_det_wedge (U.submatrix id (hodgeFrameLabels p q))

theorem fourHodgeCompound_wedge_pairing {R : Type*} [CommRing R]
    (U : Matrix (Fin 4) (Fin 4) R) (p q : HodgeIndex) :
    (∑ r, fourHodgeCompound U r p * fourHodgeCompound U (fourHodgeFlip r) q) =
      U.det * if fourHodgeFlip p = q then 1 else 0 := by
  have h := fourHodgeCompound_wedge_frame (1 : Matrix (Fin 4) (Fin 4) R) p q
  have hI : ((1 : Matrix (Fin 4) (Fin 4) R).submatrix id (hodgeFrameLabels p q)).det =
      if fourHodgeFlip p = q then 1 else 0 := by
    simpa [Matrix.one_apply, ite_mul, zero_mul, one_mul, Finset.sum_ite_eq'] using h.symm
  have he : U.submatrix id (hodgeFrameLabels p q) =
      U * (1 : Matrix (Fin 4) (Fin 4) R).submatrix id (hodgeFrameLabels p q) := by
    ext i j
    simp [Matrix.submatrix_apply, Matrix.mul_apply, Matrix.one_apply, mul_ite, Finset.sum_ite_eq']
  rw [fourHodgeCompound_wedge_frame, he, Matrix.det_mul, hI]

/-- For determinant-one unitaries, the entries on complementary pair
coordinates are conjugate. -/
theorem fourHodgeCompound_complement (U : Matrix (Fin 4) (Fin 4) ℂ)
    (hU : IsUnitary U) (hdet : U.det = 1) (p q : HodgeIndex) :
    fourHodgeCompound U (fourHodgeFlip p) (fourHodgeFlip q) = star (fourHodgeCompound U p q) := by
  let C := fourHodgeCompound U
  let J := fourHodgeFlip.permMatrix ℂ
  let D := (Cᴴ)ᵀ
  have hC := fourHodgeCompound_unitary hU
  have hprod : D * Cᵀ = 1 := by
    simpa only [D, Matrix.transpose_mul, Matrix.transpose_one] using congrArg Matrix.transpose hC.1
  have hpair : Cᵀ * C.submatrix fourHodgeFlip id = J := by
    ext r s
    have he := fourHodgeCompound_wedge_pairing U r s
    rw [hdet, one_mul] at he
    simpa [C, J, Matrix.mul_apply, Matrix.transpose_apply, Matrix.submatrix_apply,
      Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply] using he
  have he := congrArg (fun X : Matrix HodgeIndex HodgeIndex ℂ => D * X) hpair
  rw [← Matrix.mul_assoc, hprod, Matrix.one_mul] at he
  have hJ : D * J = D.submatrix id fourHodgeFlip.symm :=
    PEquiv.mul_toMatrix_toPEquiv D fourHodgeFlip
  rw [hJ] at he
  simpa only [Matrix.submatrix_apply, id_eq, Equiv.symm_apply_apply, D,
    Matrix.transpose_apply, Matrix.conjTranspose_apply, C] using
    congrArg (fun X : Matrix HodgeIndex HodgeIndex ℂ => X p (fourHodgeFlip q)) he

def hodgeBlock (r s : Fin 2) : ℂ := if s = 0 then 1 else if r = 0 then Complex.I else -Complex.I

/-- Change from the real Hodge coordinates to the two complex coordinates
in each complementary pair, before division by the square root of two. -/
def fourHodgeBasisRaw : Matrix HodgeIndex HodgeIndex ℂ := fun p q =>
  if p.1 = q.1 then hodgeBlock p.2 q.2 else 0

private noncomputable def hodgeScale : ℂ := ((Real.sqrt 2)⁻¹ : ℝ)

private theorem hodgeScale_sq : hodgeScale ^ 2 = 1 / 2 := by
  rw [hodgeScale, ← Complex.ofReal_pow, inv_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

private theorem hodgeScale_star : star hodgeScale = hodgeScale := Complex.conj_ofReal _

/-- Orthonormal real Hodge basis in the complex exterior square. -/
noncomputable def fourHodgeBasis : Matrix HodgeIndex HodgeIndex ℂ := hodgeScale • fourHodgeBasisRaw

theorem fourHodgeBasis_unitary : IsUnitary fourHodgeBasis := by
  have hraw : fourHodgeBasisRawᴴ * fourHodgeBasisRaw = (2 : ℂ) • 1 := by
    ext ⟨i,s⟩ ⟨j,t⟩
    fin_cases i <;> fin_cases j <;> fin_cases s <;> fin_cases t <;>
      norm_num [fourHodgeBasisRaw, hodgeBlock, Matrix.mul_apply, Fintype.sum_prod_type,
        Fin.sum_univ_three, Fin.sum_univ_two, Matrix.conjTranspose_apply, Matrix.one_apply,
        Matrix.smul_apply, Complex.star_def, Complex.conj_I, Complex.I_sq, ← pow_two]
  have hleft : fourHodgeBasisᴴ * fourHodgeBasis = 1 := by
    simp only [fourHodgeBasis, Matrix.conjTranspose_smul, hodgeScale_star, Matrix.smul_mul,
      Matrix.mul_smul, hraw, smul_smul]
    have h : hodgeScale * (hodgeScale * 2) = 1 := by
      rw [← mul_assoc, ← pow_two, hodgeScale_sq]
      norm_num
    rw [h, one_smul]
  exact ⟨Matrix.mul_eq_one_comm.mp hleft, hleft⟩

/-- Exterior-square change into the Hodge basis, still over the complex numbers. -/
noncomputable def fourHodgeComplexRepresentation (U : Matrix (Fin 4) (Fin 4) ℂ) :
    Matrix HodgeIndex HodgeIndex ℂ := fourHodgeBasisᴴ * fourHodgeCompound U * fourHodgeBasis

theorem fourHodgeComplexRepresentation_eq_raw (U : Matrix (Fin 4) (Fin 4) ℂ) :
    fourHodgeComplexRepresentation U =
      (1 / 2 : ℂ) • (fourHodgeBasisRawᴴ * fourHodgeCompound U * fourHodgeBasisRaw) := by
  simp only [fourHodgeComplexRepresentation, fourHodgeBasis, Matrix.conjTranspose_smul, hodgeScale_star,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← pow_two, hodgeScale_sq]

/-- The real matrix of the exterior-square action on the fixed Hodge space. -/
noncomputable def fourHodgeRealRepresentation (U : Matrix (Fin 4) (Fin 4) ℂ) :
    Matrix HodgeIndex HodgeIndex ℝ := fun p q => (fourHodgeComplexRepresentation U p q).re

theorem fourHodgeRealRepresentation_eq_raw (U : Matrix (Fin 4) (Fin 4) ℂ) (p q : HodgeIndex) :
    fourHodgeRealRepresentation U p q =
      (((1 / 2 : ℂ) • (fourHodgeBasisRawᴴ * fourHodgeCompound U * fourHodgeBasisRaw)) p q).re := by
  simp only [fourHodgeRealRepresentation, fourHodgeComplexRepresentation_eq_raw]

private theorem hodgeBasisRaw_block_entry (C : Matrix HodgeIndex HodgeIndex ℂ)
    (i j : Fin 3) (s t : Fin 2) : (fourHodgeBasisRawᴴ * C * fourHodgeBasisRaw) (i,s) (j,t) =
      ∑ b : Fin 2, ∑ a : Fin 2, star (hodgeBlock a s) * C (i,a) (j,b) * hodgeBlock b t := by
  have h₁ (k : Fin 3) (b : Fin 2) : (fourHodgeBasisRawᴴ * C) (i,s) (k,b) =
      ∑ a : Fin 2, star (hodgeBlock a s) * C (i,a) (k,b) := by
    rw [Matrix.mul_apply, Fintype.sum_prod_type, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    simp [fourHodgeBasisRaw, Matrix.conjTranspose_apply, apply_ite, ite_mul, Finset.sum_ite_eq']
  rw [Matrix.mul_apply, Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  simp only [fourHodgeBasisRaw, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [h₁, Finset.sum_mul]

def hodgeRealBlock (a b : ℂ) (s t : Fin 2) : ℝ :=
  if s = 0 then (if t = 0 then a.re + b.re else b.im - a.im)
  else (if t = 0 then a.im + b.im else a.re - b.re)

theorem fourHodgeComplexRepresentation_block (U : Matrix (Fin 4) (Fin 4) ℂ)
    (hU : IsUnitary U) (hd : U.det = 1) (i j : Fin 3) (s t : Fin 2) :
    fourHodgeComplexRepresentation U (i,s) (j,t) =
      (hodgeRealBlock (fourHodgeCompound U (i,0) (j,0)) (fourHodgeCompound U (i,0) (j,1)) s t : ℂ) := by
  have h₀ : fourHodgeCompound U (i,1) (j,1) = star (fourHodgeCompound U (i,0) (j,0)) :=
    fourHodgeCompound_complement U hU hd (i,0) (j,0)
  have h₁ : fourHodgeCompound U (i,1) (j,0) = star (fourHodgeCompound U (i,0) (j,1)) :=
    fourHodgeCompound_complement U hU hd (i,0) (j,1)
  rw [fourHodgeComplexRepresentation_eq_raw, Matrix.smul_apply, smul_eq_mul, hodgeBasisRaw_block_entry]
  fin_cases s <;> fin_cases t <;> apply Complex.ext <;>
    norm_num [hodgeRealBlock, hodgeBlock, Fin.sum_univ_two, h₀, h₁, Complex.star_def,
      Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.div_re, Complex.div_im] <;> ring

theorem fourHodgeRealRepresentation_block (U : Matrix (Fin 4) (Fin 4) ℂ)
    (hU : IsUnitary U) (hd : U.det = 1) (i j : Fin 3) (s t : Fin 2) :
    fourHodgeRealRepresentation U (i,s) (j,t) =
      hodgeRealBlock (fourHodgeCompound U (i,0) (j,0)) (fourHodgeCompound U (i,0) (j,1)) s t := by
  rw [fourHodgeRealRepresentation, fourHodgeComplexRepresentation_block U hU hd, Complex.ofReal_re]

/-- The complex exterior-square action is the complexification of the
real Hodge matrix for determinant-one unitaries. -/
theorem fourHodgeRealRepresentation_cast (U : Matrix (Fin 4) (Fin 4) ℂ)
    (hU : IsUnitary U) (hd : U.det = 1) :
    Complex.ofRealHom.mapMatrix (fourHodgeRealRepresentation U) = fourHodgeComplexRepresentation U := by
  ext ⟨i,s⟩ ⟨j,t⟩
  change ((fourHodgeComplexRepresentation U (i,s) (j,t)).re : ℂ) = _
  rw [fourHodgeComplexRepresentation_block U hU hd, Complex.ofReal_re]

/-- Recover the two independent complex entries from one real two-plane block. -/
theorem fourHodgeCompound_block_entry (U : Matrix (Fin 4) (Fin 4) ℂ)
    (hU : IsUnitary U) (hd : U.det = 1) (i j : Fin 3) :
    let R := fourHodgeRealRepresentation U
    fourHodgeCompound U (i,0) (j,0) = ((R (i,0) (j,0) + R (i,1) (j,1) : ℝ) : ℂ) / 2 +
      Complex.I * ((R (i,1) (j,0) - R (i,0) (j,1) : ℝ) : ℂ) / 2 ∧
    fourHodgeCompound U (i,0) (j,1) = ((R (i,0) (j,0) - R (i,1) (j,1) : ℝ) : ℂ) / 2 +
      Complex.I * ((R (i,1) (j,0) + R (i,0) (j,1) : ℝ) : ℂ) / 2 := by
  simp only [fourHodgeRealRepresentation, fourHodgeComplexRepresentation_block U hU hd, Complex.ofReal_re]
  constructor <;> apply Complex.ext <;>
    norm_num [hodgeRealBlock, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.div_re, Complex.div_im] <;> ring

private theorem hodge_unitary_mul {ι : Type*} [Fintype ι] [DecidableEq ι]
    {U V : Matrix ι ι ℂ} (hU : IsUnitary U) (hV : IsUnitary V) : IsUnitary (U * V) := by
  have h : (U * V) * (U * V)ᴴ = 1 := by
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc V, hV.1, Matrix.one_mul, hU.1]
  exact ⟨h, Matrix.mul_eq_one_comm.mp h⟩

theorem fourHodgeComplexRepresentation_unitary {U : Matrix (Fin 4) (Fin 4) ℂ}
    (hU : IsUnitary U) : IsUnitary (fourHodgeComplexRepresentation U) := by
  have hB := fourHodgeBasis_unitary
  have hBt : IsUnitary fourHodgeBasisᴴ := by
    exact ⟨by simpa using hB.2, by simpa using hB.1⟩
  exact hodge_unitary_mul (hodge_unitary_mul hBt (fourHodgeCompound_unitary hU)) hB

/-- The real Hodge matrix of a determinant-one unitary is orthogonal. -/
theorem fourHodgeRealRepresentation_orthogonal (U : Matrix (Fin 4) (Fin 4) ℂ)
    (hU : IsUnitary U) (hd : U.det = 1) :
    fourHodgeRealRepresentation U * (fourHodgeRealRepresentation U)ᵀ = 1 := by
  let R := fourHodgeRealRepresentation U
  let f : Matrix HodgeIndex HodgeIndex ℝ →+* Matrix HodgeIndex HodgeIndex ℂ :=
    Complex.ofRealHom.mapMatrix
  have hR : f R = fourHodgeComplexRepresentation U := fourHodgeRealRepresentation_cast U hU hd
  have ht : f Rᵀ = (f R)ᴴ := by
    ext i j
    change (R j i : ℂ) = star (R j i : ℂ)
    exact (Complex.conj_ofReal _).symm
  have he : f (R * Rᵀ) = f 1 := by
    rw [f.map_mul, ht, hR, (fourHodgeComplexRepresentation_unitary hU).1, f.map_one]
  ext i j
  exact Complex.ofReal_injective (congrArg (fun M : Matrix HodgeIndex HodgeIndex ℂ => M i j) he)

theorem fourHodgeCompound_det (U : Matrix (Fin 4) (Fin 4) ℂ) (hU : IsUnitary U) :
    (fourHodgeCompound U).det = U.det ^ 3 := by
  have hN : IsStarNormal U := by
    constructor
    change Uᴴ * U = U * Uᴴ
    exact hU.2.trans hU.1.symm
  obtain ⟨d, V, hV, hUV⟩ := exists_unitary_diagonalization U hN
  have hv : V.det * Vᴴ.det = 1 := by
    simpa only [Matrix.det_mul, Matrix.det_one] using congrArg Matrix.det hV.1
  have hcv : (fourHodgeCompound V).det * (fourHodgeCompound Vᴴ).det = 1 := by
    rw [← Matrix.det_mul, ← fourHodgeCompound_mul, hV.1, fourHodgeCompound_one, Matrix.det_one]
  have hD : (fourHodgeCompound (diagonal d)).det = (diagonal d).det ^ 3 := by
    rw [fourHodgeCompound_diagonal, Matrix.det_diagonal, Matrix.det_diagonal]
    simp [Fintype.prod_prod_type, Fin.prod_univ_three, Fin.prod_univ_two, Fin.prod_univ_four,
      fourHodgePair, Matrix.cons_val]
    ring
  rw [hUV]
  simp only [fourHodgeCompound_mul, Matrix.det_mul, hD]
  calc
    _ = ((fourHodgeCompound V).det * (fourHodgeCompound Vᴴ).det) * (diagonal d).det ^ 3 := by ring
    _ = (diagonal d).det ^ 3 := by rw [hcv, one_mul]
    _ = (V.det * (diagonal d).det * Vᴴ.det) ^ 3 := by
      rw [show V.det * (diagonal d).det * Vᴴ.det = (V.det * Vᴴ.det) * (diagonal d).det by ring,
        hv, one_mul]

/-- The real exterior-square matrix has determinant one. -/
theorem fourHodgeRealRepresentation_det (U : Matrix (Fin 4) (Fin 4) ℂ)
    (hU : IsUnitary U) (hd : U.det = 1) : (fourHodgeRealRepresentation U).det = 1 := by
  have hb : (fourHodgeBasisᴴ).det * fourHodgeBasis.det = 1 := by
    simpa only [Matrix.det_mul, Matrix.det_one] using congrArg Matrix.det fourHodgeBasis_unitary.2
  have he := congrArg Matrix.det (fourHodgeRealRepresentation_cast U hU hd)
  change ((fourHodgeRealRepresentation U).map Complex.ofRealHom).det = _ at he
  rw [← RingHom.map_det, fourHodgeComplexRepresentation, Matrix.det_mul, Matrix.det_mul,
    fourHodgeCompound_det U hU, hd, one_pow, mul_one, hb] at he
  exact Complex.ofReal_injective (by simpa only [Complex.ofRealHom_apply, Complex.ofReal_one] using he)

theorem fourHodgeRealRepresentation_mul (U V : Matrix (Fin 4) (Fin 4) ℂ)
    (hU : IsUnitary U) (hV : IsUnitary V) (hdU : U.det = 1) (hdV : V.det = 1) :
    fourHodgeRealRepresentation (U * V) = fourHodgeRealRepresentation U * fourHodgeRealRepresentation V := by
  let f : Matrix HodgeIndex HodgeIndex ℝ →+* Matrix HodgeIndex HodgeIndex ℂ :=
    Complex.ofRealHom.mapMatrix
  have hdet : (U * V).det = 1 := by rw [Matrix.det_mul, hdU, hdV, one_mul]
  have he : f (fourHodgeRealRepresentation (U * V)) =
      f (fourHodgeRealRepresentation U * fourHodgeRealRepresentation V) := by
    rw [f.map_mul, fourHodgeRealRepresentation_cast _ (hodge_unitary_mul hU hV) hdet,
      fourHodgeRealRepresentation_cast U hU hdU, fourHodgeRealRepresentation_cast V hV hdV]
    simp only [fourHodgeComplexRepresentation, fourHodgeCompound_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc fourHodgeBasis fourHodgeBasisᴴ, fourHodgeBasis_unitary.1, Matrix.one_mul]
  ext i j
  exact Complex.ofReal_injective (congrArg (fun M : Matrix HodgeIndex HodgeIndex ℂ => M i j) he)

@[simp] theorem fourHodgeRealRepresentation_one :
    fourHodgeRealRepresentation (1 : Matrix (Fin 4) (Fin 4) ℂ) = 1 := by
  have h : fourHodgeComplexRepresentation (1 : Matrix (Fin 4) (Fin 4) ℂ) = 1 := by
    simp only [fourHodgeComplexRepresentation, fourHodgeCompound_one, Matrix.mul_one,
      fourHodgeBasis_unitary.2]
  ext i j
  change (fourHodgeComplexRepresentation (1 : Matrix (Fin 4) (Fin 4) ℂ) i j).re = _
  rw [h]
  simp [Matrix.one_apply, apply_ite]

/-- The kernel of the real exterior-square representation on special
unitary matrices of order four consists of the two scalar signs. -/
theorem fourHodgeRealRepresentation_eq_one_iff (U : Matrix (Fin 4) (Fin 4) ℂ)
    (hU : IsUnitary U) (hd : U.det = 1) :
    fourHodgeRealRepresentation U = 1 ↔ U = 1 ∨ U = -1 := by
  constructor
  · intro h
    have hc := fourHodgeRealRepresentation_cast U hU hd
    rw [h, map_one] at hc
    have hC : fourHodgeCompound U = 1 := by
      let B := fourHodgeBasis
      have hb : B * Bᴴ = 1 := fourHodgeBasis_unitary.1
      change 1 = Bᴴ * fourHodgeCompound U * B at hc
      calc
        _ = (B * Bᴴ) * fourHodgeCompound U * (B * Bᴴ) := by
          rw [hb, Matrix.one_mul, Matrix.mul_one]
        _ = B * (Bᴴ * fourHodgeCompound U * B) * Bᴴ := by simp only [Matrix.mul_assoc]
        _ = 1 := by rw [← hc, Matrix.mul_one, hb]
    have hN : IsStarNormal U := ⟨hU.2.trans hU.1.symm⟩
    obtain ⟨d, V, hV, hUV⟩ := exists_unitary_diagonalization U hN
    have hconj : Vᴴ * U * V = diagonal d := by
      calc
        _ = (Vᴴ * V) * diagonal d * (Vᴴ * V) := by rw [hUV]; simp only [Matrix.mul_assoc]
        _ = _ := by rw [hV.2, Matrix.one_mul, Matrix.mul_one]
    have hCd : fourHodgeCompound (diagonal d) = 1 := by
      rw [← hconj, fourHodgeCompound_mul, fourHodgeCompound_mul, hC, Matrix.mul_one,
        ← fourHodgeCompound_mul, hV.2, fourHodgeCompound_one]
    have hp (p : HodgeIndex) : d (fourHodgePair p 0) * d (fourHodgePair p 1) = 1 := by
      rw [fourHodgeCompound_diagonal] at hCd
      simpa only [Matrix.diagonal_apply_eq, Matrix.one_apply_eq] using
        congrArg (fun M : Matrix HodgeIndex HodgeIndex ℂ => M p p) hCd
    have h01 : d 0 * d 1 = 1 := by exact hp (0, 0)
    have h02 : d 0 * d 2 = 1 := by exact hp (1, 0)
    have h03 : d 0 * d 3 = 1 := by exact hp (2, 0)
    have h12 : d 1 * d 2 = 1 := by exact hp (2, 1)
    have h0 : d 0 ≠ 0 := by intro hz; simp [hz] at h01
    have h21 : d 2 = d 1 := mul_left_cancel₀ h0 (h02.trans h01.symm)
    have h31 : d 3 = d 1 := mul_left_cancel₀ h0 (h03.trans h01.symm)
    rw [h21] at h12
    have h1 : d 1 ≠ 0 := by intro hz; simp [hz] at h01
    have h01' : d 0 = d 1 := mul_right_cancel₀ h1 (h01.trans h12.symm)
    have hx : d 1 = 1 ∨ d 1 = -1 := by
      have hprod : (d 1 - 1) * (d 1 + 1) = 0 := by
        calc
          _ = d 1 * d 1 - 1 := by ring
          _ = 0 := by rw [h12, sub_self]
      rcases mul_eq_zero.mp hprod with hplus | hminus
      · exact Or.inl (sub_eq_zero.mp hplus)
      · exact Or.inr (eq_neg_of_add_eq_zero_left hminus)
    have hu : U = d 1 • (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
      have hdconst : d = fun _ => d 1 := by
        funext i
        fin_cases i
        · exact h01'
        · rfl
        · exact h21
        · exact h31
      have hdiag : diagonal (fun _ : Fin 4 => d 1) = d 1 • (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
        ext i j : 1
        by_cases he : i = j <;> simp [Matrix.diagonal_apply, Matrix.one_apply, he]
      rw [hUV, hdconst, hdiag, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hV.1]
    rcases hx with hx | hx
    · exact Or.inl (by simp [hu, hx])
    · exact Or.inr (by simp [hu, hx])
  · rintro (rfl | rfl)
    · exact fourHodgeRealRepresentation_one
    · have hC : fourHodgeCompound (-(1 : Matrix (Fin 4) (Fin 4) ℂ)) = 1 := by
        rw [← fourHodgeCompound_one]
        ext p q : 1
        simp only [fourHodgeCompound, Matrix.neg_apply, neg_mul_neg]
      simpa only [fourHodgeRealRepresentation, fourHodgeComplexRepresentation, hC,
        fourHodgeCompound_one] using fourHodgeRealRepresentation_one

end MOC
