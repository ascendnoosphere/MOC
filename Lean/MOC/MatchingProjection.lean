import MOC.ProjectionConditioning
import MOC.TwoValues
import Mathlib.Data.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Tactic.FinCases

/-! The balanced projection associated to a unitary mixer, and a balanced
projection which fails the unrestricted matching comparison. -/

open BigOperators Matrix

namespace MOC

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The projection on the graph of the adjoint of the relative mixer. -/
noncomputable def matchingProjection (U : Matrix ι ι ℂ) :
    Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ :=
  (1 / 2 : ℂ) • Matrix.fromBlocks 1 U Uᴴ 1

theorem matchingProjection_isHermitian (U : Matrix ι ι ℂ) :
    (matchingProjection U).IsHermitian := by
  change (matchingProjection U)ᴴ = matchingProjection U
  simp [matchingProjection, Matrix.conjTranspose_smul, Matrix.fromBlocks_conjTranspose]

theorem matchingProjection_idempotent (U : Matrix ι ι ℂ) (hU : IsUnitary U) :
    matchingProjection U * matchingProjection U = matchingProjection U := by
  let T : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ := Matrix.fromBlocks 1 U Uᴴ 1
  have ht : T * T = (2 : ℂ) • T := by
    simp [T, Matrix.fromBlocks_multiply, Matrix.fromBlocks_smul, hU.1, hU.2, two_smul]
  change ((1 / 2 : ℂ) • T) * ((1 / 2 : ℂ) • T) = (1 / 2 : ℂ) • T
  rw [Matrix.smul_mul, Matrix.mul_smul, ht, smul_smul, smul_smul]
  congr 1
  norm_num

theorem matchingProjection_rank (U : Matrix ι ι ℂ) (hU : IsUnitary U) :
    (matchingProjection U).rank = Fintype.card ι := by
  have htrace : (matchingProjection U).trace = (Fintype.card ι : ℂ) := by
    simp only [matchingProjection, Matrix.trace_smul, Matrix.trace, Matrix.diag_apply,
      Fintype.sum_sum_type, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₂₂,
      Matrix.one_apply_eq, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, smul_eq_mul]
    ring
  have hr := trace_eq_rank_of_projection (matchingProjection_isHermitian U)
    (matchingProjection_idempotent U hU)
  exact_mod_cast hr.symm.trans htrace

/-- The size-rank principal minors of the projection are the squared mixer
minors scaled by one half for each selected coordinate. -/
theorem matchingProjection_principalMinor (U : Matrix ι ι ℂ) (hU : IsUnitary U)
    (I J : Finset ι) (e : I ≃ J) :
    let K := {i : ι // i ∉ I}
    let s : K ⊕ J → ι ⊕ ι :=
      Sum.elim (fun i => Sum.inl i.val) (fun j => Sum.inr j.val)
    ((matchingProjection U).submatrix s s).det =
      (1 / 2 : ℂ) ^ Fintype.card ι * (subsetMinorSq U I J : ℂ) := by
  classical
  intro K s
  let W : Matrix K J ℂ := U.submatrix Subtype.val Subtype.val
  let N : Matrix J J ℂ := U.submatrix (Subtype.val ∘ e.symm) Subtype.val
  let split : I ⊕ K ≃ ι := Equiv.sumCompl (fun i => i ∈ I)
  have hcard : Fintype.card (K ⊕ J) = Fintype.card ι :=
    Fintype.card_congr ((Equiv.sumCongr (Equiv.refl K) e.symm).trans
      ((Equiv.sumComm K I).trans split))
  have hblock :
      (Matrix.fromBlocks 1 U Uᴴ 1).submatrix s s = Matrix.fromBlocks 1 W Wᴴ 1 := by
    ext (i | i) (j | j) <;>
      simp [s, W, Matrix.one_apply, Matrix.submatrix_apply, Matrix.conjTranspose_apply,
        Subtype.ext_iff]
  have hgram : Nᴴ * N + Wᴴ * W = 1 := by
    ext i j : 1
    have hu := congrArg (fun A : Matrix ι ι ℂ => A i.val j.val) hU.2
    change (Uᴴ * U) i.val j.val = (1 : Matrix ι ι ℂ) i.val j.val at hu
    rw [Matrix.mul_apply, ← Equiv.sum_comp split
      (fun k => Uᴴ i.val k * U k j.val), Fintype.sum_sum_type,
      ← Equiv.sum_comp e.symm (fun k : I => Uᴴ i.val (split (.inl k)) * U (split (.inl k)) j.val)] at hu
    simpa [split, N, W, Matrix.add_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.submatrix_apply, Matrix.one_apply, Subtype.ext_iff] using hu
  have hg : (1 : Matrix J J ℂ) - Wᴴ * W = Nᴴ * N :=
    (eq_sub_iff_add_eq.mpr hgram).symm
  have hn := subsetMinorSq_eq_normSq_det_submatrix U hU I J e.symm (Equiv.refl J)
  rw [matchingProjection, Matrix.submatrix_smul, hblock, Matrix.det_smul, hcard,
    Matrix.det_fromBlocks_one₁₁, hg, Matrix.det_mul, Matrix.det_conjTranspose]
  change (1 / 2 : ℂ) ^ Fintype.card ι * (star N.det * N.det) = _
  rw [mul_comm (star N.det) N.det, Complex.star_def, Complex.mul_conj, hn]
  rfl

/-- A three-by-six frame with equal column norms. -/
noncomputable def balancedProjectionFrame : Matrix (Fin 3) (Fin 6) ℂ :=
  (1 / 2 : ℂ) • !![1, 1, 0, 1, 1, 0; 1, 0, 1, -1, 0, 1; 0, 1, 1, 0, -1, -1]

theorem balancedProjectionFrame_properties :
    balancedProjectionFrame * balancedProjectionFrameᴴ = 1 ∧
      ∀ j, (∑ i, Complex.normSq (balancedProjectionFrame i j)) = 1 / 2 := by
  constructor
  · ext i j : 1
    fin_cases i <;> fin_cases j <;>
      apply Complex.ext <;>
      norm_num [balancedProjectionFrame, Matrix.mul_apply, Matrix.conjTranspose_apply,
        Matrix.one_apply, Fin.sum_univ_succ, Matrix.smul_apply, smul_eq_mul,
        Complex.star_def, Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im,
        Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.neg_re, Complex.neg_im]
  · intro j
    fin_cases j <;> norm_num [balancedProjectionFrame, Fin.sum_univ_three, Matrix.smul_apply,
      smul_eq_mul, Complex.normSq_mul, Complex.normSq_ofNat, Complex.normSq_div]

private def balancedProjectionLabels (i : Fin 6) : ℂ :=
  if (i : ℕ) < 3 then 1 else Complex.I

theorem balancedProjectionFrame_determinant :
    8 * (balancedProjectionFrame * Matrix.diagonal balancedProjectionLabels *
        balancedProjectionFrameᴴ).det = -4 + 3 * Complex.I := by
  let x : ℂ := (1 + Complex.I) / 2
  let y : ℂ := (1 - Complex.I) / 4
  have ht : balancedProjectionFrame * Matrix.diagonal balancedProjectionLabels *
      balancedProjectionFrameᴴ = !![x, y, y; y, x, y; y, y, x] := by
    ext i j : 1
    fin_cases i <;> fin_cases j <;>
      apply Complex.ext <;>
      norm_num [balancedProjectionFrame, balancedProjectionLabels, x, y, Matrix.mul_apply,
        Matrix.mul_diagonal, Matrix.conjTranspose_apply, Fin.sum_univ_succ, Matrix.smul_apply,
        smul_eq_mul, Complex.star_def, Complex.mul_re, Complex.mul_im, Complex.div_re,
        Complex.div_im, Complex.normSq_apply, Complex.add_re, Complex.add_im,
        Complex.sub_re, Complex.sub_im]
  rw [ht, Matrix.det_fin_three]
  apply Complex.ext <;>
    norm_num [x, y, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
      Complex.sub_re, Complex.sub_im, Complex.div_re, Complex.div_im, Complex.normSq_apply]

/-- The matching products on three labels equal to one and three labels
equal to the imaginary unit have these two values. The variables count
edges within each label class and edges across the classes. -/
theorem balancedProjection_matching_products (a b c : ℕ)
    (ha : 2 * a + c = 3) (hb : 2 * b + c = 3) :
    (2 : ℂ) ^ a * (2 * Complex.I) ^ b * (1 + Complex.I) ^ c = -2 + 2 * Complex.I ∨
      (2 : ℂ) ^ a * (2 * Complex.I) ^ b * (1 + Complex.I) ^ c = -4 + 4 * Complex.I := by
  have h : (a = 0 ∧ b = 0 ∧ c = 3) ∨ (a = 1 ∧ b = 1 ∧ c = 1) := by omega
  rcases h with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · left
    apply Complex.ext <;>
      norm_num [pow_succ, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im]
  · right
    apply Complex.ext <;>
      norm_num [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im]

/-- The balanced frame gives a determinant outside the segment of the
two possible matching products. -/
theorem balancedProjection_determinant_outside_hull :
    8 * (balancedProjectionFrame * Matrix.diagonal balancedProjectionLabels *
        balancedProjectionFrameᴴ).det ∉
      convexHull ℝ ({-2 + 2 * Complex.I, -4 + 4 * Complex.I} : Set ℂ) := by
  rw [balancedProjectionFrame_determinant]
  let L : ℂ →ₗ[ℝ] ℝ := Complex.reLm + Complex.imLm
  have hL : ({-2 + 2 * Complex.I, -4 + 4 * Complex.I} : Set ℂ) ⊆ L.ker := by
    intro z hz
    rcases Set.mem_insert_iff.mp hz with rfl | hz
    · norm_num [L, LinearMap.mem_ker, Complex.reLm_coe, Complex.imLm_coe, Complex.mul_re,
        Complex.mul_im, Complex.add_re, Complex.add_im]
    · rw [Set.mem_singleton_iff] at hz
      subst z
      norm_num [L, LinearMap.mem_ker, Complex.reLm_coe, Complex.imLm_coe, Complex.mul_re,
        Complex.mul_im, Complex.add_re, Complex.add_im]
  intro h
  have hw := convexHull_min hL L.ker.convex h
  norm_num [L, LinearMap.mem_ker, Complex.reLm_coe, Complex.imLm_coe, Complex.mul_re,
    Complex.mul_im, Complex.add_re, Complex.add_im] at hw

end MOC
