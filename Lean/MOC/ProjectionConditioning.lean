import Mathlib.LinearAlgebra.Matrix.Spectrum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Conditioning an orthogonal projection on a single coordinate. -/

open BigOperators Matrix

namespace MOC

noncomputable section

variable {ι : Type*} [Fintype ι]

/-- The projection after selecting the first coordinate and deleting it. -/
def projectionConditionOne (p : ℝ) (q : Matrix ι (Fin 1) ℂ) (J : Matrix ι ι ℂ) :
    Matrix ι ι ℂ :=
  J + (-(p : ℂ)⁻¹) • (q * qᴴ)

/-- The projection after rejecting the first coordinate and deleting it. -/
def projectionConditionZero (p : ℝ) (q : Matrix ι (Fin 1) ℂ) (J : Matrix ι ι ℂ) :
    Matrix ι ι ℂ :=
  J + (1 - (p : ℂ))⁻¹ • (q * qᴴ)

private theorem scalar_fin_one (z : ℂ) : scalar (Fin 1) z = z • (1 : Matrix (Fin 1) (Fin 1) ℂ) := by
  ext i j
  have h : i = j := Subsingleton.elim _ _
  subst j
  simp [scalar_apply]

private theorem projection_border_equations (p : ℝ) (q : Matrix ι (Fin 1) ℂ)
    (J : Matrix ι ι ℂ)
    (hP : fromBlocks (scalar (Fin 1) (p : ℂ)) qᴴ q J *
      fromBlocks (scalar (Fin 1) (p : ℂ)) qᴴ q J =
      fromBlocks (scalar (Fin 1) (p : ℂ)) qᴴ q J) :
    qᴴ * q = ((p : ℂ) * (1 - (p : ℂ))) • (1 : Matrix (Fin 1) (Fin 1) ℂ) ∧
      J * q = (1 - (p : ℂ)) • q ∧
      J * J + q * qᴴ = J := by
  rw [fromBlocks_multiply] at hP
  have h11 := congrArg toBlocks₁₁ hP
  have h21 := congrArg toBlocks₂₁ hP
  have h22 := congrArg toBlocks₂₂ hP
  simp only [toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂,
    scalar_fin_one, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one,
    smul_smul] at h11 h21 h22
  refine ⟨?_, ?_, by simpa only [add_comm] using h22⟩
  · rw [add_comm] at h11
    rw [(eq_sub_iff_add_eq).mpr h11, ← sub_smul]
    ring_nf
  · rw [add_comm] at h21
    rw [(eq_sub_iff_add_eq).mpr h21, sub_smul, one_smul]

private theorem projection_border_normSq (p : ℝ) (q : Matrix ι (Fin 1) ℂ)
    (J : Matrix ι ι ℂ)
    (hP : fromBlocks (scalar (Fin 1) (p : ℂ)) qᴴ q J *
      fromBlocks (scalar (Fin 1) (p : ℂ)) qᴴ q J =
      fromBlocks (scalar (Fin 1) (p : ℂ)) qᴴ q J) :
    (∑ i, Complex.normSq (q i 0)) = p * (1 - p) := by
  have h := congrArg (fun A : Matrix (Fin 1) (Fin 1) ℂ => A 0 0)
    (projection_border_equations p q J hP).1
  apply Complex.ofReal_injective
  simpa only [Matrix.mul_apply, conjTranspose_apply, Matrix.smul_apply, Matrix.one_apply_eq,
    smul_eq_mul, mul_one, Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_sub,
    Complex.ofReal_one, Complex.normSq_eq_conj_mul_self] using h

/-- Each diagonal entry of a bordered projection lies between zero and one. -/
theorem projection_border_nonneg_le_one (p : ℝ) (q : Matrix ι (Fin 1) ℂ)
    (J : Matrix ι ι ℂ)
    (hP : fromBlocks (scalar (Fin 1) (p : ℂ)) qᴴ q J *
      fromBlocks (scalar (Fin 1) (p : ℂ)) qᴴ q J =
      fromBlocks (scalar (Fin 1) (p : ℂ)) qᴴ q J) :
    0 ≤ p ∧ p ≤ 1 := by
  have h : 0 ≤ p * (1 - p) := by
    rw [← projection_border_normSq p q J hP]
    exact Finset.sum_nonneg fun i _ => Complex.normSq_nonneg (q i 0)
  constructor <;> nlinarith

/-- At either endpoint of the diagonal interval the off-diagonal column is zero,
and the lower-right block is a projection. -/
theorem projection_border_endpoint (p : ℝ) (q : Matrix ι (Fin 1) ℂ)
    (J : Matrix ι ι ℂ)
    (hP : fromBlocks (scalar (Fin 1) (p : ℂ)) qᴴ q J *
      fromBlocks (scalar (Fin 1) (p : ℂ)) qᴴ q J =
      fromBlocks (scalar (Fin 1) (p : ℂ)) qᴴ q J)
    (hp : p = 0 ∨ p = 1) :
    q = 0 ∧ J * J = J := by
  have hn := projection_border_normSq p q J hP
  have hz : (∑ i, Complex.normSq (q i 0)) = 0 := by
    rcases hp with rfl | rfl <;> simpa using hn
  have hq : q = 0 := by
    ext i j
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    exact Complex.normSq_eq_zero.mp ((Finset.sum_eq_zero_iff_of_nonneg
      (fun i _ => Complex.normSq_nonneg (q i 0))).mp hz i (Finset.mem_univ i))
  refine ⟨hq, ?_⟩
  simpa only [hq, Matrix.zero_mul, add_zero] using (projection_border_equations p q J hP).2.2

private theorem projection_update_square {J : Matrix ι ι ℂ}
    (hJ : J.IsHermitian) {q : Matrix ι (Fin 1) ℂ} (p : ℝ)
    (h₁ : qᴴ * q = ((p : ℂ) * (1 - (p : ℂ))) • (1 : Matrix (Fin 1) (Fin 1) ℂ))
    (h₂ : J * q = (1 - (p : ℂ)) • q)
    (h₃ : J * J + q * qᴴ = J) (c : ℂ)
    (hc : -1 + c * (1 - (p : ℂ)) + c * (1 - (p : ℂ)) +
      (c * c) * ((p : ℂ) * (1 - (p : ℂ))) = c) :
    (J + c • (q * qᴴ)) * (J + c • (q * qᴴ)) = J + c • (q * qᴴ) := by
  let B := q * qᴴ
  have hJq : J * B = (1 - (p : ℂ)) • B := by
    dsimp only [B]
    rw [← Matrix.mul_assoc, h₂, Matrix.smul_mul]
  have hqJ : B * J = (1 - (p : ℂ)) • B := by
    have h := congrArg Matrix.conjTranspose hJq
    simpa only [B, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hJ.eq,
      Matrix.conjTranspose_smul, star_sub, star_one, Complex.star_def, Complex.conj_ofReal] using h
  have hB : B * B = ((p : ℂ) * (1 - (p : ℂ))) • B := by
    dsimp only [B]
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc qᴴ q qᴴ, h₁, Matrix.smul_mul, Matrix.one_mul,
      Matrix.mul_smul]
  have hJ₂ : J * J = J + (-1 : ℂ) • B := by
    rw [(eq_sub_iff_add_eq).mpr h₃, neg_smul, one_smul, sub_eq_add_neg]
  change (J + c • B) * (J + c • B) = _
  rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.smul_mul, Matrix.mul_smul, hJ₂, hJq, hqJ, hB]
  simp only [smul_smul, add_assoc, ← add_smul, ← mul_assoc]
  simp only [← mul_assoc] at hc
  rw [← add_assoc (-1 : ℂ), ← add_assoc (-1 + c * (1 - (p : ℂ))), hc]

omit [Fintype ι] in
private theorem projection_update_hermitian {J : Matrix ι ι ℂ} (hJ : J.IsHermitian)
    (q : Matrix ι (Fin 1) ℂ) (c : ℂ) (hc : star c = c) :
    (J + c • (q * qᴴ)).IsHermitian := by
  change (J + c • (q * qᴴ))ᴴ = J + c • (q * qᴴ)
  rw [Matrix.conjTranspose_add, hJ.eq, Matrix.conjTranspose_smul, hc,
    Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]

/-- The trace of a bordered matrix is the sum of the first diagonal entry and the remaining trace. -/
theorem trace_projection_border (p : ℝ) (q : Matrix ι (Fin 1) ℂ) (J : Matrix ι ι ℂ) :
    (fromBlocks (scalar (Fin 1) (p : ℂ)) qᴴ q J).trace = (p : ℂ) + J.trace := by
  simp only [Matrix.trace, Matrix.diag_apply, Fintype.sum_sum_type, fromBlocks_apply₁₁,
    fromBlocks_apply₂₂, Fintype.sum_unique, scalar_apply, Matrix.diagonal_apply_eq]

private theorem trace_projection_update (p : ℝ) (q : Matrix ι (Fin 1) ℂ) (J : Matrix ι ι ℂ)
    (hP : fromBlocks (scalar (Fin 1) (p : ℂ)) qᴴ q J *
      fromBlocks (scalar (Fin 1) (p : ℂ)) qᴴ q J =
      fromBlocks (scalar (Fin 1) (p : ℂ)) qᴴ q J) (c : ℂ) :
    (J + c • (q * qᴴ)).trace = J.trace + c * ((p : ℂ) * (1 - (p : ℂ))) := by
  rw [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_mul_comm,
    (projection_border_equations p q J hP).1, Matrix.trace_smul]
  simp

/-- Conditioning on selection of a coordinate of an orthogonal projection
gives an orthogonal projection with trace one smaller. -/
theorem projectionConditionOne_spec (p : ℝ) (q : Matrix ι (Fin 1) ℂ) (J : Matrix ι ι ℂ)
    (hJ : J.IsHermitian)
    (hP : fromBlocks (scalar (Fin 1) (p : ℂ)) qᴴ q J *
      fromBlocks (scalar (Fin 1) (p : ℂ)) qᴴ q J =
      fromBlocks (scalar (Fin 1) (p : ℂ)) qᴴ q J)
    (hp : p ≠ 0) :
    (projectionConditionOne p q J).IsHermitian ∧
      projectionConditionOne p q J * projectionConditionOne p q J = projectionConditionOne p q J ∧
      (projectionConditionOne p q J).trace =
        (fromBlocks (scalar (Fin 1) (p : ℂ)) qᴴ q J).trace - 1 := by
  have hp' : (p : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hp
  obtain ⟨h₁, h₂, h₃⟩ := projection_border_equations p q J hP
  refine ⟨projection_update_hermitian hJ q _ ?_, projection_update_square hJ p h₁ h₂ h₃ _ ?_, ?_⟩
  · simp only [star_neg, star_inv₀, Complex.star_def, Complex.conj_ofReal]
  · field_simp [hp']
    ring
  · rw [projectionConditionOne, trace_projection_update p q J hP, trace_projection_border]
    field_simp [hp']
    ring

/-- Conditioning on rejection of a coordinate of an orthogonal projection
gives an orthogonal projection with the same trace. -/
theorem projectionConditionZero_spec (p : ℝ) (q : Matrix ι (Fin 1) ℂ) (J : Matrix ι ι ℂ)
    (hJ : J.IsHermitian)
    (hP : fromBlocks (scalar (Fin 1) (p : ℂ)) qᴴ q J *
      fromBlocks (scalar (Fin 1) (p : ℂ)) qᴴ q J =
      fromBlocks (scalar (Fin 1) (p : ℂ)) qᴴ q J)
    (hp : p ≠ 1) :
    (projectionConditionZero p q J).IsHermitian ∧
      projectionConditionZero p q J * projectionConditionZero p q J = projectionConditionZero p q J ∧
      (projectionConditionZero p q J).trace =
        (fromBlocks (scalar (Fin 1) (p : ℂ)) qᴴ q J).trace := by
  have hp' : 1 - (p : ℂ) ≠ 0 := sub_ne_zero.mpr (fun h => hp (Complex.ofReal_injective h.symm))
  obtain ⟨h₁, h₂, h₃⟩ := projection_border_equations p q J hP
  refine ⟨projection_update_hermitian hJ q _ ?_, projection_update_square hJ p h₁ h₂ h₃ _ ?_, ?_⟩
  · simp only [star_inv₀, star_sub, star_one, Complex.star_def, Complex.conj_ofReal]
  · field_simp [hp']
    ring
  · rw [projectionConditionZero, trace_projection_update p q J hP, trace_projection_border]
    field_simp [hp']
    ring


omit [Fintype ι] in
/-- The rank-one update is supported on the nonzero entries of the border column. -/
theorem projection_border_outer_apply (q : Matrix ι (Fin 1) ℂ) (i j : ι) :
    (q * qᴴ) i j = q i 0 * star (q j 0) := by
  simp only [Matrix.mul_apply, Fintype.sum_unique, Matrix.conjTranspose_apply]
  rfl

variable [DecidableEq ι]

/-- Every eigenvalue of an orthogonal projection is zero or one. -/
theorem projection_eigenvalues_zero_or_one {P : Matrix ι ι ℂ} (hP : P.IsHermitian)
    (hPP : P * P = P) (i : ι) : hP.eigenvalues i = 0 ∨ hP.eigenvalues i = 1 := by
  let W : Matrix ι ι ℂ := hP.eigenvectorUnitary
  let d (j : ι) : ℂ := hP.eigenvalues j
  have hW : W * Wᴴ = 1 := unitary.coe_mul_star_self hP.eigenvectorUnitary
  have hD : Wᴴ * P * W = diagonal d := hP.star_mul_self_mul_eq_diagonal
  have hDD : diagonal d * diagonal d = diagonal d := by
    calc
      _ = Wᴴ * (P * P) * W := by
        rw [← hD]
        simp only [Matrix.mul_assoc, ← Matrix.mul_assoc W Wᴴ, hW, Matrix.one_mul]
      _ = _ := by rw [hPP, hD]
  have h := congrArg (fun A : Matrix ι ι ℂ => A i i) hDD
  simp only [Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply_eq, Pi.mul_apply] at h
  have hroots : d i * (d i - 1) = 0 := by
    rw [mul_sub, h, mul_one, sub_self]
  rcases mul_eq_zero.mp hroots with hzero | hone
  · exact Or.inl (Complex.ofReal_injective hzero)
  · exact Or.inr (Complex.ofReal_injective (sub_eq_zero.mp hone))

/-- The trace of an orthogonal projection is its rank. -/
theorem trace_eq_rank_of_projection {P : Matrix ι ι ℂ} (hP : P.IsHermitian)
    (hPP : P * P = P) : P.trace = (P.rank : ℂ) := by
  classical
  let W := hP.eigenvectorUnitary
  let S := Finset.univ.filter (fun i => hP.eigenvalues i ≠ 0)
  have hcard : P.rank = S.card := by
    rw [hP.rank_eq_card_non_zero_eigs, Fintype.card_of_subtype S (by simp [S])]
  have hP' : P = W.val * diagonal (fun i => (hP.eigenvalues i : ℂ)) * W.valᴴ :=
    hP.spectral_theorem
  have hW : W.valᴴ * W.val = 1 := unitary.coe_star_mul_self W
  calc
    P.trace = ∑ i, (hP.eigenvalues i : ℂ) := by
      conv_lhs => rw [hP']
      rw [Matrix.trace_mul_cycle, hW, Matrix.one_mul, Matrix.trace_diagonal]
    _ = ∑ i ∈ S, (hP.eigenvalues i : ℂ) := by
      symm
      apply Finset.sum_subset (Finset.subset_univ S)
      intro i _ hi
      have hz : hP.eigenvalues i = 0 := by simpa [S] using hi
      rw [hz, Complex.ofReal_zero]
    _ = ∑ _i ∈ S, (1 : ℂ) := by
      apply Finset.sum_congr rfl
      intro i hi
      have hn : hP.eigenvalues i ≠ 0 := (Finset.mem_filter.mp hi).2
      rw [(projection_eigenvalues_zero_or_one hP hPP i).resolve_left hn, Complex.ofReal_one]
    _ = (P.rank : ℂ) := by simp [hcard]


omit [Fintype ι] [DecidableEq ι] in
private theorem projection_border_isHermitian (p : ℝ) (q : Matrix ι (Fin 1) ℂ)
    {J : Matrix ι ι ℂ} (hJ : J.IsHermitian) :
    (fromBlocks (scalar (Fin 1) (p : ℂ)) qᴴ q J).IsHermitian := by
  apply IsHermitian.fromBlocks _ (Matrix.conjTranspose_conjTranspose q) hJ
  rw [scalar_apply, isHermitian_diagonal_iff]
  intro i
  exact Complex.conj_ofReal p

/-- Selecting and deleting the first coordinate reduces the rank by one. -/
theorem projectionConditionOne_rank (p : ℝ) (q : Matrix ι (Fin 1) ℂ) (J : Matrix ι ι ℂ)
    (hJ : J.IsHermitian)
    (hP : fromBlocks (scalar (Fin 1) (p : ℂ)) qᴴ q J *
      fromBlocks (scalar (Fin 1) (p : ℂ)) qᴴ q J =
      fromBlocks (scalar (Fin 1) (p : ℂ)) qᴴ q J)
    (hp : p ≠ 0) :
    (projectionConditionOne p q J).rank + 1 =
      (fromBlocks (scalar (Fin 1) (p : ℂ)) qᴴ q J).rank := by
  obtain ⟨hH, hI, hT⟩ := projectionConditionOne_spec p q J hJ hP hp
  rw [trace_eq_rank_of_projection hH hI,
    trace_eq_rank_of_projection (projection_border_isHermitian p q hJ) hP] at hT
  exact_mod_cast (eq_sub_iff_add_eq.mp hT)

/-- Rejecting and deleting the first coordinate preserves the rank. -/
theorem projectionConditionZero_rank (p : ℝ) (q : Matrix ι (Fin 1) ℂ) (J : Matrix ι ι ℂ)
    (hJ : J.IsHermitian)
    (hP : fromBlocks (scalar (Fin 1) (p : ℂ)) qᴴ q J *
      fromBlocks (scalar (Fin 1) (p : ℂ)) qᴴ q J =
      fromBlocks (scalar (Fin 1) (p : ℂ)) qᴴ q J)
    (hp : p ≠ 1) :
    (projectionConditionZero p q J).rank =
      (fromBlocks (scalar (Fin 1) (p : ℂ)) qᴴ q J).rank := by
  obtain ⟨hH, hI, hT⟩ := projectionConditionZero_spec p q J hJ hP hp
  rw [trace_eq_rank_of_projection hH hI,
    trace_eq_rank_of_projection (projection_border_isHermitian p q hJ) hP] at hT
  exact_mod_cast hT

end

end MOC
