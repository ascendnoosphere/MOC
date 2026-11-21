import MOC.Weights
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-! One-coordinate unitary Schur transfer. The rectangular graph of the feedback
equation gives an isometry on the smaller block. -/

open Matrix

namespace MOC

noncomputable section

variable {ι : Type*}

/-- The Schur transfer after feeding back the first coordinate with scalar `z`. -/
def schurTransfer (α : ℂ) (r : Matrix (Fin 1) ι ℂ) (c : Matrix ι (Fin 1) ℂ)
    (D : Matrix ι ι ℂ) (z : ℂ) : Matrix ι ι ℂ :=
  D + (z / (1 - z * α)) • (c * r)

/-- The transfer family in a parameter that enters affinely. -/
def affineSchurTransfer (α : ℂ) (r : Matrix (Fin 1) ι ℂ) (c : Matrix ι (Fin 1) ℂ)
    (D : Matrix ι ι ℂ) (z : ℂ) : Matrix ι ι ℂ :=
  D + ((z + star α) / (1 - (Complex.normSq α : ℂ))) • (c * r)

variable [Fintype ι] [DecidableEq ι]

/-- A modulus-one feedback phase preserves unitarity wherever the transfer is defined. -/
theorem schurTransfer_unitary_of_ne (α : ℂ) (r : Matrix (Fin 1) ι ℂ)
    (c : Matrix ι (Fin 1) ℂ) (D : Matrix ι ι ℂ) (z : ℂ)
    (hU : IsUnitary (fromBlocks (scalar (Fin 1) α) r c D))
    (hz : ‖z‖ = 1) (hden : 1 - z * α ≠ 0) : IsUnitary (schurTransfer α r c D z) := by
  let U := fromBlocks (scalar (Fin 1) α) r c D
  let V := schurTransfer α r c D z
  let s := (1 - z * α)⁻¹
  let X := fromRows ((z * s) • r) (1 : Matrix ι ι ℂ)
  let Y := fromRows (s • r) V
  have ha : α * (z * s) + 1 = s := by
    dsimp [s]
    field_simp
    ring
  have htop : scalar (Fin 1) α * ((z * s) • r) + r = s • r := by
    calc
      _ = (α * (z * s)) • r + (1 : ℂ) • r := by
        rw [scalar_apply, ← smul_eq_diagonal_mul, smul_smul, one_smul]
      _ = _ := by rw [← add_smul, ha]
  have hUX : U * X = Y := by
    dsimp only [U, X, Y]
    rw [fromBlocks_mul_fromRows, Matrix.mul_one, Matrix.mul_one, htop, Matrix.mul_smul]
    simp [V, schurTransfer, div_eq_mul_inv, s, add_comm]
  have hu : Uᴴ * U = 1 := hU.2
  have hgram : Yᴴ * Y = Xᴴ * X := by
    rw [← hUX, conjTranspose_mul]
    calc
      _ = Xᴴ * (Uᴴ * U) * X := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hu, Matrix.mul_one]
  have hphase : star z * z = (1 : ℂ) := by
    simpa [Complex.star_def, hz] using Complex.conj_mul' z
  have hrow : ((z * s) • r)ᴴ * ((z * s) • r) = (s • r)ᴴ * (s • r) := by
    rw [← smul_smul z s r, conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul,
      smul_smul, hphase, one_smul]
  simp only [Y, X, conjTranspose_fromRows_eq_fromCols_conjTranspose,
    fromCols_mul_fromRows, hrow, conjTranspose_one, Matrix.one_mul] at hgram
  have hV : Vᴴ * V = 1 := add_left_cancel hgram
  exact ⟨Matrix.mul_eq_one_comm.mp hV, hV⟩

theorem schurTransfer_unitary (α : ℂ) (r : Matrix (Fin 1) ι ℂ) (c : Matrix ι (Fin 1) ℂ)
    (D : Matrix ι ι ℂ) (z : ℂ) (hU : IsUnitary (fromBlocks (scalar (Fin 1) α) r c D))
    (hz : ‖z‖ = 1) (hα : ‖α‖ < 1) : IsUnitary (schurTransfer α r c D z) := by
  apply schurTransfer_unitary_of_ne α r c D z hU hz
  intro h
  have he := congrArg norm ((sub_eq_zero.mp h).symm)
  rw [norm_mul, hz, one_mul, norm_one] at he
  exact hα.ne he

open scoped ComplexOrder in
/-- A modulus-one anchor in a unitary is decoupled from the remaining coordinates. -/
theorem schurTransfer_boundary (α : ℂ) (r : Matrix (Fin 1) ι ℂ) (c : Matrix ι (Fin 1) ℂ)
    (D : Matrix ι ι ℂ) (hU : IsUnitary (fromBlocks (scalar (Fin 1) α) r c D))
    (hα : ‖α‖ = 1) : r = 0 ∧ c = 0 ∧ IsUnitary D := by
  let A := scalar (Fin 1) α
  have ha : Aᴴ * A = 1 := by
    ext i j
    have hi : i = 0 := Subsingleton.elim _ _
    have hj : j = 0 := Subsingleton.elim _ _
    subst i
    subst j
    simpa [A, scalar_apply, Matrix.mul_apply, conjTranspose_apply, Complex.star_def, hα]
      using Complex.conj_mul' α
  have ha' : A * Aᴴ = 1 := Matrix.mul_eq_one_comm.mp ha
  have hl := hU.2
  have hr := hU.1
  change (fromBlocks A r c D)ᴴ * fromBlocks A r c D = 1 at hl
  change fromBlocks A r c D * (fromBlocks A r c D)ᴴ = 1 at hr
  rw [fromBlocks_conjTranspose, fromBlocks_multiply, ← fromBlocks_one, fromBlocks_inj] at hl hr
  have hcg := hl.1
  have hrg := hr.1
  rw [ha] at hcg
  rw [ha'] at hrg
  have hc : c = 0 := conjTranspose_mul_self_eq_zero.mp (add_left_cancel (hcg.trans (add_zero _).symm))
  have hr' : r = 0 := self_mul_conjTranspose_eq_zero.mp (add_left_cancel (hrg.trans (add_zero _).symm))
  refine ⟨hr', hc, ?_⟩
  exact ⟨by simpa [hc] using hr.2.2.2, by simpa [hr'] using hl.2.2.2⟩

/-- Totalized division agrees with direct deletion at the degenerate feedback phase. -/
theorem schurTransfer_unitary_of_phase (α : ℂ) (r : Matrix (Fin 1) ι ℂ)
    (c : Matrix ι (Fin 1) ℂ) (D : Matrix ι ι ℂ) (z : ℂ)
    (hU : IsUnitary (fromBlocks (scalar (Fin 1) α) r c D)) (hz : ‖z‖ = 1) :
    IsUnitary (schurTransfer α r c D z) := by
  by_cases hden : 1 - z * α = 0
  · have hα := congrArg norm ((sub_eq_zero.mp hden).symm)
    rw [norm_mul, hz, one_mul, norm_one] at hα
    obtain ⟨hr, hc, hD⟩ := schurTransfer_boundary α r c D hU hα
    simpa [schurTransfer, hr, hc] using hD
  · exact schurTransfer_unitary_of_ne α r c D z hU hz hden

private theorem affine_feedback (α z : ℂ) (hα : Complex.normSq α < 1)
    (hz : Complex.normSq z = 1) :
    let w := (z + star α) / (1 + α * z)
    ‖w‖ = 1 ∧ w / (1 - w * α) = (z + star α) / (1 - (Complex.normSq α : ℂ)) := by
  let p := z + star α
  let s := 1 + α * z
  let q := 1 - (Complex.normSq α : ℂ)
  let w := p / s
  change ‖w‖ = 1 ∧ w / (1 - w * α) = p / q
  have hs : s ≠ 0 := by
    intro h
    have hm : α * z = -1 := by
      calc
        α * z = s - 1 := by dsimp [s]; ring
        _ = -1 := by rw [h, zero_sub]
    have hn := congrArg Complex.normSq hm
    rw [Complex.normSq_mul, hz, mul_one, Complex.normSq_neg, Complex.normSq_one] at hn
    exact hα.ne hn
  have hzz : z * star z = (1 : ℂ) := by
    rw [Complex.star_def, Complex.mul_conj, hz, Complex.ofReal_one]
  have hp : p = z * star s := by
    dsimp only [p, s]
    simp only [star_add, star_one, StarMul.star_mul, mul_add, mul_one, ← mul_assoc, hzz, one_mul]
  have hp_norm : Complex.normSq p = Complex.normSq s := by
    simp [hp, Complex.normSq_mul, hz, Complex.star_def]
  have hw_norm : Complex.normSq w = 1 := by
    change Complex.normSq (p / s) = 1
    rw [Complex.normSq_div, hp_norm, div_self (Complex.normSq_pos.mpr hs).ne']
  refine ⟨(sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp (by
    simpa [Complex.normSq_eq_norm_sq] using hw_norm), ?_⟩
  have hden : 1 - w * α = q / s := by
    apply (eq_div_iff hs).mpr
    calc
      (1 - w * α) * s = s - (w * s) * α := by ring
      _ = s - p * α := by rw [show w * s = p from div_mul_cancel₀ _ hs]
      _ = q := by
        dsimp only [s, p, q]
        rw [Complex.normSq_eq_conj_mul_self, ← Complex.star_def]
        ring
  rw [hden]
  exact div_div_div_cancel_right₀ hs p q

omit [Fintype ι] [DecidableEq ι] in
/-- The affine and feedback parametrizations agree on the unit circle. -/
theorem affineSchurTransfer_eq_schurTransfer (α : ℂ) (r : Matrix (Fin 1) ι ℂ)
    (c : Matrix ι (Fin 1) ℂ) (D : Matrix ι ι ℂ) (z : ℂ)
    (hα : Complex.normSq α < 1) (hz : Complex.normSq z = 1) :
    affineSchurTransfer α r c D z = schurTransfer α r c D ((z + star α) / (1 + α * z)) := by
  simp only [affineSchurTransfer, schurTransfer, (affine_feedback α z hα hz).2]

/-- The affine completion is unitary at every modulus-one parameter. -/
theorem affineSchurTransfer_unitary (α : ℂ) (r : Matrix (Fin 1) ι ℂ)
    (c : Matrix ι (Fin 1) ℂ) (D : Matrix ι ι ℂ) (z : ℂ)
    (hU : IsUnitary (fromBlocks (scalar (Fin 1) α) r c D))
    (hα : Complex.normSq α < 1) (hz : Complex.normSq z = 1) :
    IsUnitary (affineSchurTransfer α r c D z) := by
  rw [affineSchurTransfer_eq_schurTransfer α r c D z hα hz]
  exact schurTransfer_unitary_of_phase α r c D _ hU (affine_feedback α z hα hz).1

/-- Applying the anchored spectral factors before transfer introduces one outer product.
Here `x` and `y` omit their zero anchor entries. -/
theorem schurTransfer_anchored_factor (α : ℂ) (r : Matrix (Fin 1) ι ℂ)
    (c : Matrix ι (Fin 1) ℂ) (D : Matrix ι ι ℂ) (z : ℂ) (x y : ι → ℂ) :
    schurTransfer α r c (D - diagonal x * D * diagonal y) z =
      (schurTransfer α r c D z - diagonal x * schurTransfer α r c D z * diagonal y) +
        (z / (1 - z * α)) • ((diagonal x * c) * (r * diagonal y)) := by
  simp only [schurTransfer, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul,
    Matrix.smul_mul, Matrix.mul_assoc]
  abel

private theorem det_affine_border (α : ℂ) (r : Matrix (Fin 1) ι ℂ) (c : Matrix ι (Fin 1) ℂ)
    (D : Matrix ι ι ℂ) (z : ℂ) :
    (fromBlocks (scalar (Fin 1) (1 - z * α)) (-z • r) c D).det =
      D.det - z * (fromBlocks (scalar (Fin 1) α) r c D).det := by
  let U := fromBlocks (scalar (Fin 1) α) r c D
  let E := fromBlocks (1 : Matrix (Fin 1) (Fin 1) ℂ) (0 : Matrix (Fin 1) ι ℂ) c D
  let e : Fin 1 ⊕ ι := Sum.inl 0
  have hU : E.updateRow e (U e) = U := by
    ext (i | i) j
    · have hi : i = 0 := Subsingleton.elim _ _
      subst i
      exact congrFun Matrix.updateRow_self j
    · rcases j with j | j <;> simp [E, U, e]
  have hW : E.updateRow e (E e + (-z) • U e) =
      fromBlocks (scalar (Fin 1) (1 - z * α)) (-z • r) c D := by
    ext (i | i) (j | j)
    · have hi : i = 0 := Subsingleton.elim _ _
      have hj : j = 0 := Subsingleton.elim _ _
      subst i
      subst j
      simp [E, U, e, scalar_apply, smul_eq_mul, sub_eq_add_neg]
    · have hi : i = 0 := Subsingleton.elim _ _
      subst i
      simp [E, U, e, smul_eq_mul]
    · simp [E, e]
    · simp [E, e]
  rw [← hW, det_updateRow_add, det_updateRow_smul, updateRow_eq_self, hU]
  simp [E, U, det_fromBlocks_zero₁₂, sub_eq_add_neg]

/-- The bordered determinant formula also applies to any pair of equally sized submatrices. -/
theorem det_schurTransfer_mul (α : ℂ) (r : Matrix (Fin 1) ι ℂ) (c : Matrix ι (Fin 1) ℂ)
    (D : Matrix ι ι ℂ) (z : ℂ) (hden : 1 - z * α ≠ 0) :
    (1 - z * α) * (schurTransfer α r c D z).det =
      D.det - z * (fromBlocks (scalar (Fin 1) α) r c D).det := by
  let q := 1 - z * α
  let t := z / q
  let L := fromBlocks (scalar (Fin 1) q) 0 0 (1 : Matrix ι ι ℂ)
  let B := fromBlocks (1 : Matrix (Fin 1) (Fin 1) ℂ) ((-t) • r) c D
  have hqt : q * t = z := by
    dsimp [t]
    rw [mul_comm, div_mul_cancel₀ _ hden]
  have hLB : L * B = fromBlocks (scalar (Fin 1) q) (-z • r) c D := by
    simp only [L, B, fromBlocks_multiply, Matrix.mul_one, Matrix.one_mul, Matrix.zero_mul,
      Matrix.mul_zero, add_zero, zero_add]
    rw [scalar_apply, ← smul_eq_diagonal_mul, smul_smul, mul_neg, hqt]
  have hL : L.det = q := by
    simp [L, det_fromBlocks_zero₂₁, det_fin_one, scalar_apply]
  have hB : B.det = (schurTransfer α r c D z).det := by
    dsimp [B, schurTransfer, t, q]
    rw [det_fromBlocks_one₁₁, Matrix.mul_smul, neg_smul, sub_neg_eq_add]
  have hW := congrArg Matrix.det hLB
  rw [det_mul, hL, hB] at hW
  exact hW.trans (det_affine_border α r c D z)

/-- The determinant phase of the smaller unitary is a scalar Möbius factor times
the determinant of the original matrix. -/
theorem det_schurTransfer_of_unitary (α : ℂ) (r : Matrix (Fin 1) ι ℂ)
    (c : Matrix ι (Fin 1) ℂ) (D : Matrix ι ι ℂ) (z : ℂ)
    (hU : IsUnitary (fromBlocks (scalar (Fin 1) α) r c D)) (hden : 1 - z * α ≠ 0) :
    (schurTransfer α r c D z).det =
      (fromBlocks (scalar (Fin 1) α) r c D).det * ((star α - z) / (1 - z * α)) := by
  let U := fromBlocks (scalar (Fin 1) α) r c D
  let e : Fin 1 ⊕ ι := Sum.inl 0
  have he : U.updateRow e (Pi.single e 1) =
      fromBlocks (1 : Matrix (Fin 1) (Fin 1) ℂ) 0 c D := by
    ext (i | i) (j | j)
    · have hi : i = 0 := Subsingleton.elim _ _
      have hj : j = 0 := Subsingleton.elim _ _
      subst i
      subst j
      simp [e]
    · have hi : i = 0 := Subsingleton.elim _ _
      subst i
      simp [e, Pi.single_apply]
    · simp [U, e]
    · simp [U, e]
  have hAdj : U.adjugate e e = D.det := by
    rw [Matrix.adjugate_apply, he, det_fromBlocks_zero₁₂, det_one, one_mul]
  have hD : D.det = U.det * star α := by
    have hm := congrArg (fun M : Matrix (Fin 1 ⊕ ι) (Fin 1 ⊕ ι) ℂ => M e e)
      (adjugate_unitary U hU)
    change U.adjugate e e = (U.det • Uᴴ) e e at hm
    rwa [hAdj, Matrix.smul_apply, Matrix.conjTranspose_apply, smul_eq_mul,
      show U e e = α by simp [U, e, scalar_apply]] at hm
  rw [← mul_div_assoc]
  apply (eq_div_iff hden).mpr
  rw [mul_comm _ (1 - z * α), det_schurTransfer_mul α r c D z hden]
  change D.det - z * U.det = U.det * (star α - z)
  rw [hD]
  ring

private theorem normSq_parallelogram (x y : ℂ) :
    Complex.normSq (x - y) + Complex.normSq (x + y) =
      2 * (Complex.normSq x + Complex.normSq y) := by
  rw [Complex.normSq_sub, Complex.normSq_add]
  ring

/-- Positive weights for the two endpoint transfers are independent of the minor. -/
theorem schurTransfer_trace_weights (α : ℂ) :
    0 ≤ Complex.normSq (1 - α) / (2 * (1 + Complex.normSq α)) ∧
    0 ≤ Complex.normSq (1 + α) / (2 * (1 + Complex.normSq α)) ∧
    Complex.normSq (1 - α) / (2 * (1 + Complex.normSq α)) +
      Complex.normSq (1 + α) / (2 * (1 + Complex.normSq α)) = 1 := by
  have hp : 0 < 2 * (1 + Complex.normSq α) := by
    linarith only [Complex.normSq_nonneg α]
  refine ⟨div_nonneg (Complex.normSq_nonneg _) hp.le, div_nonneg (Complex.normSq_nonneg _) hp.le, ?_⟩
  rw [← add_div, normSq_parallelogram, Complex.normSq_one, div_self hp.ne']

/-- Pair the unbordered and bordered squared minors. The right-hand side uses the
same two weights for every choice of remaining row and column subsets. -/
theorem schurTransfer_trace_pair (α : ℂ) (r : Matrix (Fin 1) ι ℂ) (c : Matrix ι (Fin 1) ℂ)
    (D : Matrix ι ι ℂ) (hminus : 1 - α ≠ 0) (hplus : 1 + α ≠ 0) :
    let τ := 1 + Complex.normSq α
    let U := fromBlocks (scalar (Fin 1) α) r c D
    (Complex.normSq D.det + Complex.normSq U.det) / τ =
      (Complex.normSq (1 - α) / (2 * τ)) * Complex.normSq (schurTransfer α r c D 1).det +
      (Complex.normSq (1 + α) / (2 * τ)) * Complex.normSq (schurTransfer α r c D (-1)).det := by
  intro τ U
  have h₁ : Complex.normSq (1 - α) * Complex.normSq (schurTransfer α r c D 1).det =
      Complex.normSq (D.det - U.det) := by
    simpa [Complex.normSq_mul, U] using congrArg Complex.normSq
      (det_schurTransfer_mul α r c D 1 (by simpa using hminus))
  have h₂ : Complex.normSq (1 + α) * Complex.normSq (schurTransfer α r c D (-1)).det =
      Complex.normSq (D.det + U.det) := by
    simpa [Complex.normSq_mul, U] using congrArg Complex.normSq
      (det_schurTransfer_mul α r c D (-1) (by simpa using hplus))
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, h₁, h₂, ← add_div, normSq_parallelogram]
  have hτ : 0 < τ := by
    dsimp [τ]
    linarith only [Complex.normSq_nonneg α]
  field_simp [hτ.ne']
  ring

omit [Fintype ι] [DecidableEq ι] in
theorem schurTransfer_submatrix {κ : Type*} (α : ℂ) (r : Matrix (Fin 1) ι ℂ)
    (c : Matrix ι (Fin 1) ℂ) (D : Matrix ι ι ℂ) (z : ℂ) (e f : κ → ι) :
    (schurTransfer α r c D z).submatrix e f =
      schurTransfer α (r.submatrix id f) (c.submatrix e id) (D.submatrix e f) z := by
  unfold schurTransfer
  change D.submatrix e f + (z / (1 - z * α)) • (c * r).submatrix e f = _
  rw [Matrix.submatrix_mul c r e id f Function.bijective_id]

omit [Fintype ι] [DecidableEq ι] in
/-- The two-phase trace equality simultaneously covers every pair of equally sized minors.
The anchor is kept first in the bordered submatrix. -/
theorem schurTransfer_minor_trace {κ : Type*} [Fintype κ] [DecidableEq κ]
    (α : ℂ) (r : Matrix (Fin 1) ι ℂ) (c : Matrix ι (Fin 1) ℂ) (D : Matrix ι ι ℂ)
    (e f : κ → ι) (hminus : 1 - α ≠ 0) (hplus : 1 + α ≠ 0) :
    let τ := 1 + Complex.normSq α
    let U := fromBlocks (scalar (Fin 1) α) r c D
    (Complex.normSq (D.submatrix e f).det +
      Complex.normSq (U.submatrix (Sum.map id e) (Sum.map id f)).det) / τ =
    (Complex.normSq (1 - α) / (2 * τ)) *
        Complex.normSq ((schurTransfer α r c D 1).submatrix e f).det +
    (Complex.normSq (1 + α) / (2 * τ)) *
        Complex.normSq ((schurTransfer α r c D (-1)).submatrix e f).det := by
  intro τ U
  have hU : U.submatrix (Sum.map id e) (Sum.map id f) =
      fromBlocks (scalar (Fin 1) α) (r.submatrix id f) (c.submatrix e id) (D.submatrix e f) := by
    ext (i | i) (j | j) <;> rfl
  rw [hU, schurTransfer_submatrix, schurTransfer_submatrix]
  exact schurTransfer_trace_pair α _ _ _ hminus hplus

end

end MOC
