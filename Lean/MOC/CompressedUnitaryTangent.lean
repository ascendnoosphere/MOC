import MOC.Core
import Mathlib.Data.Matrix.Basis
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Trace

/-! Compression of unitary conjugation tangents to the relative eigenspaces. -/

open BigOperators Matrix

namespace MOC

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq κ]

/-- Keep exactly those entries belonging to a common eigenspace. -/
def compressEigenspaces (label : ι → κ) : Matrix ι ι ℂ →ₗ[ℂ] Matrix ι ι ℂ where
  toFun X := fun i j => if label i = label j then X i j else 0
  map_add' X Y := by
    ext i j : 1
    by_cases h : label i = label j <;> simp [h, Matrix.add_apply]
  map_smul' k X := by
    ext i j : 1
    by_cases h : label i = label j <;> simp [h, Matrix.smul_apply]

theorem compressEigenspaces_apply (label : ι → κ) (X : Matrix ι ι ℂ) (i j : ι) :
    compressEigenspaces label X i j = if label i = label j then X i j else 0 := rfl

private theorem compress_idem (label : ι → κ) (X : Matrix ι ι ℂ) :
    compressEigenspaces label (compressEigenspaces label X) = compressEigenspaces label X := by
  ext i j : 1
  by_cases h : label i = label j <;> simp [compressEigenspaces_apply, h]

private theorem compress_star (label : ι → κ) (X : Matrix ι ι ℂ) :
    (compressEigenspaces label X)ᴴ = compressEigenspaces label Xᴴ := by
  ext i j : 1
  by_cases h : label i = label j
  · simp only [Matrix.conjTranspose_apply, compressEigenspaces_apply, if_pos h, if_pos h.symm]
  · simp only [Matrix.conjTranspose_apply, compressEigenspaces_apply, if_neg h, if_neg (Ne.symm h), star_zero]

private theorem trace_mul_compress (label : ι → κ) (X Y : Matrix ι ι ℂ) :
    (X * compressEigenspaces label Y).trace = (compressEigenspaces label X * Y).trace := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, compressEigenspaces_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : label i = label j
  · simp only [if_pos h, if_pos h.symm]
  · simp only [if_neg h, if_neg (Ne.symm h), mul_zero, zero_mul]

private theorem trace_mul_stdBasis (X : Matrix ι ι ℂ) (i j : ι) :
    (X * Matrix.stdBasisMatrix i j (1 : ℂ)).trace = X j i := by
  have he (k l : ι) :
      (X * Matrix.stdBasisMatrix i j (1 : ℂ)) k l = if j = l then X k i else 0 := by
    by_cases h : j = l
    · subst l
      simp [Matrix.mul_apply, Matrix.stdBasisMatrix, mul_ite]
    · simp [Matrix.mul_apply, Matrix.stdBasisMatrix, h]
  simp [Matrix.trace, Matrix.diag_apply, he]

private theorem trace_pairing_represents (φ : Matrix ι ι ℂ →ₗ[ℂ] ℂ) :
    ∃ Y : Matrix ι ι ℂ, ∀ X, φ X = (Y * X).trace := by
  let Y : Matrix ι ι ℂ := fun i j => φ (Matrix.stdBasisMatrix j i 1)
  refine ⟨Y, fun X => ?_⟩
  have hX : X = ∑ i, ∑ j, X i j • Matrix.stdBasisMatrix i j 1 := by
    simpa only [Matrix.smul_stdBasisMatrix, smul_eq_mul, mul_one] using
      Matrix.matrix_eq_sum_stdBasisMatrix X
  conv_lhs => rw [hX]
  conv_rhs => rw [hX]
  simp only [map_sum, map_smul, smul_eq_mul, Matrix.mul_sum, Matrix.mul_smul,
    Matrix.trace_sum, Matrix.trace_smul, trace_mul_stdBasis, Y]

/-- If the only matrices in the relative eigenspaces that commute with the
first unitary are scalars, every traceless Hermitian compression is realized
by a Hermitian conjugation generator. -/
theorem exists_hermitian_for_compressed_unitary_tangent (label : ι → κ)
    (U : Matrix ι ι ℂ) (hU : IsUnitary U)
    (hcomm : ∀ Y : Matrix ι ι ℂ, compressEigenspaces label Y = Y → Commute U Y →
      ∃ c : ℂ, Y = c • (1 : Matrix ι ι ℂ))
    (D : Matrix ι ι ℂ) (hD : D.IsHermitian) (hcomp : compressEigenspaces label D = D)
    (htr : D.trace = 0) :
    ∃ L : Matrix ι ι ℂ, L.IsHermitian ∧ compressEigenspaces label (Uᴴ * L * U - L) = D := by
  let compress := compressEigenspaces label
  let F : Matrix ι ι ℂ →ₗ[ℂ] Matrix ι ι ℂ :=
    { toFun := fun X => compress (Uᴴ * X * U - X)
      map_add' := fun X Y => by simp [Matrix.mul_add, Matrix.add_mul, add_sub_add_comm, map_add]
      map_smul' := fun k X => by simp [Matrix.mul_smul, Matrix.smul_mul, ← smul_sub] }
  have hDRange : D ∈ LinearMap.range F := by
    apply (Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff _ _).mp
    intro φ hφ
    obtain ⟨Y, hY⟩ := trace_pairing_represents φ
    have hcyclic (X : Matrix ι ι ℂ) :
        (compress Y * (Uᴴ * X * U)).trace = ((U * compress Y * Uᴴ) * X).trace := by
      calc
        _ = ((compress Y * Uᴴ * X) * U).trace := by simp only [Matrix.mul_assoc]
        _ = (U * (compress Y * Uᴴ * X)).trace := Matrix.trace_mul_comm _ _
        _ = _ := by simp only [Matrix.mul_assoc]
    have hvan (X : Matrix ι ι ℂ) : ((U * compress Y * Uᴴ - compress Y) * X).trace = 0 := by
      have hv := (Submodule.mem_dualAnnihilator φ).mp hφ (F X) ⟨X, rfl⟩
      change φ (compress (Uᴴ * X * U - X)) = 0 at hv
      rw [hY, trace_mul_compress label, Matrix.mul_sub, Matrix.trace_sub, hcyclic] at hv
      simpa only [Matrix.sub_mul, Matrix.trace_sub] using hv
    have hYeq : U * compress Y * Uᴴ - compress Y = 0 := by
      ext i j : 1
      simpa only [trace_mul_stdBasis, Matrix.zero_apply] using hvan (Matrix.stdBasisMatrix j i 1)
    have hUY : Commute U (compress Y) := by
      change U * compress Y = compress Y * U
      have he := congrArg (fun M : Matrix ι ι ℂ => M * U) (sub_eq_zero.mp hYeq)
      simpa only [Matrix.mul_assoc, hU.2, Matrix.mul_one] using he
    obtain ⟨c, hc⟩ := hcomm (compress Y) (compress_idem label Y) hUY
    rw [hY, ← hcomp, trace_mul_compress label, hc, Matrix.smul_mul, Matrix.one_mul,
      Matrix.trace_smul, htr, smul_zero]
  obtain ⟨X, hX⟩ := hDRange
  have hstar (Z : Matrix ι ι ℂ) : (F Z)ᴴ = F Zᴴ := by
    change (compress (Uᴴ * Z * U - Z))ᴴ = compress (Uᴴ * Zᴴ * U - Zᴴ)
    rw [compress_star label]
    simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc, compress]
  let L := (1 / 2 : ℂ) • (X + Xᴴ)
  have hhalf : star (1 / 2 : ℂ) = (1 / 2 : ℂ) := by norm_num [Complex.star_def]
  refine ⟨L, ?_, ?_⟩
  · change Lᴴ = L
    simp only [L, Matrix.conjTranspose_smul, hhalf, Matrix.conjTranspose_add,
      Matrix.conjTranspose_conjTranspose, add_comm Xᴴ X]
  · change F L = D
    simp only [L, map_smul, map_add, ← hstar, hX, hD.eq, ← two_smul ℂ D, smul_smul]
    norm_num

end MOC
