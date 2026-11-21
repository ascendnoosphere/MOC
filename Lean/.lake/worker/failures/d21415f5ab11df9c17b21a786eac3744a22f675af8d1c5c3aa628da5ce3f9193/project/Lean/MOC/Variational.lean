import MOC.Jacobi
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.LinearAlgebra.Matrix.Trace

/-! Compactness and first variation of the determinant support on a unitary orbit. -/

open BigOperators Matrix

namespace MOC

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem isCompact_setOf_isUnitary : IsCompact {U : Matrix ι ι ℂ | IsUnitary U} := by
  let K : Set (Matrix ι ι ℂ) := Set.univ.pi fun _ =>
    Set.univ.pi fun _ => Metric.closedBall 0 1
  have hK : IsCompact K := isCompact_univ_pi fun _ =>
    isCompact_univ_pi fun _ => isCompact_closedBall _ _
  have hclosed : IsClosed {U : Matrix ι ι ℂ | IsUnitary U} := by
    change IsClosed ({U : Matrix ι ι ℂ | U * Uᴴ = 1} ∩ {U : Matrix ι ι ℂ | Uᴴ * U = 1})
    exact (isClosed_eq (by fun_prop) continuous_const).inter
      (isClosed_eq (by fun_prop) continuous_const)
  refine hK.of_isClosed_subset hclosed ?_
  intro U hU
  refine Set.mem_pi.mpr (fun i _ => Set.mem_pi.mpr (fun j _ => ?_))
  have hr := congrArg (fun M : Matrix ι ι ℂ => (M i i).re) hU.1
  have hsum : ∑ k, Complex.normSq (U i k) = 1 := by
    simpa only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply_eq,
      Complex.re_sum, Complex.star_def, Complex.mul_conj, Complex.ofReal_re, Complex.one_re] using hr
  have hle : Complex.normSq (U i j) ≤ 1 := hsum ▸ Finset.single_le_sum
    (f := fun k => Complex.normSq (U i k)) (fun k _ => Complex.normSq_nonneg _) (Finset.mem_univ j)
  rw [Metric.mem_closedBall, dist_zero_right]
  apply (sq_le_sq₀ (norm_nonneg _) zero_le_one).mp
  simpa only [← Complex.normSq_eq_norm_sq, one_pow] using hle

/-- A real determinant support always achieves its maximum on the unitary group. -/
theorem exists_support_maximizer (a b : ι → ℂ) (η : ℂ) :
    ∃ U : Matrix ι ι ℂ, IsUnitary U ∧ ∀ V : Matrix ι ι ℂ, IsUnitary V →
      (η * determinantValue a b V).re ≤ (η * determinantValue a b U).re := by
  have hne : {U : Matrix ι ι ℂ | IsUnitary U}.Nonempty := ⟨1, by simp [IsUnitary]⟩
  have hc : Continuous (fun U : Matrix ι ι ℂ => (η * determinantValue a b U).re) := by
    unfold determinantValue
    fun_prop
  obtain ⟨U, hU, hmax⟩ := isCompact_setOf_isUnitary.exists_isMaxOn hne hc.continuousOn
  exact ⟨U, hU, fun V hV => hmax hV⟩

section Derivative

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

private theorem hasDerivAt_det_one {M : ℝ → Matrix ι ι ℂ} {D : Matrix ι ι ℂ}
    (hM : HasDerivAt M D 0) (h₀ : M 0 = 1) : HasDerivAt (fun t => (M t).det) D.trace 0 := by
  have hvalue : M 0 = diagonal (fun _ => 1) := h₀.trans Matrix.diagonal_one.symm
  have hderiv (i j : ι) : HasDerivAt (fun t => M t i j) (D i j) 0 := by
    let eval : Matrix ι ι ℂ →L[ℝ] ℂ :=
      ⟨Matrix.entryLinearMap ℝ ℂ i j, continuous_apply_apply i j⟩
    exact eval.hasFDerivAt.comp_hasDerivAt 0 hM
  simpa [Matrix.trace] using hasDerivAt_det_diagonal M D 0 (fun _ => 1) hvalue hderiv

private theorem hasDerivAt_det {M : ℝ → Matrix ι ι ℂ} {D : Matrix ι ι ℂ}
    (hM : HasDerivAt M D 0) (h₀ : (M 0).det ≠ 0) :
    HasDerivAt (fun t => (M t).det) ((M 0).det * ((M 0)⁻¹ * D).trace) 0 := by
  let C := M 0
  have hC : IsUnit C.det := isUnit_iff_ne_zero.mpr h₀
  have hd := (hM.const_mul C⁻¹)
  have htrace := hasDerivAt_det_one hd (C.nonsing_inv_mul hC)
  have he (t : ℝ) : C.det * (C⁻¹ * M t).det = (M t).det := by
    rw [← Matrix.det_mul, ← Matrix.mul_assoc, C.mul_nonsing_inv hC, Matrix.one_mul]
  simpa only [he] using htrace.const_mul C.det

private theorem hasDerivAt_exp_orbit (A B X : Matrix ι ι ℂ) :
    HasDerivAt (fun t : ℝ => A + NormedSpace.exp ℝ (t • X) * B *
      NormedSpace.exp ℝ (t • (-X))) (X * B - B * X) 0 := by
  have hp : HasDerivAt (fun t : ℝ => NormedSpace.exp ℝ (t • X)) X 0 := by
    simpa only [zero_smul, NormedSpace.exp_zero, one_mul] using
      hasDerivAt_exp_smul_const X (0 : ℝ)
  have hn : HasDerivAt (fun t : ℝ => NormedSpace.exp ℝ (t • (-X))) (-X) 0 := by
    simpa only [zero_smul, NormedSpace.exp_zero, one_mul] using
      hasDerivAt_exp_smul_const (-X) (0 : ℝ)
  simpa only [zero_smul, NormedSpace.exp_zero, Matrix.one_mul, Matrix.mul_one,
    Matrix.mul_neg, sub_eq_add_neg, add_comm] using ((hp.mul_const B).mul hn).const_add A

/-- At a nonsingular unitary support maximum, the determinant-scaled inverse commutator
is Hermitian. The two fixed matrices need not be normal for this first variation. -/
theorem support_maximum_inverse_commutator (A B : Matrix ι ι ℂ) (η : ℂ)
    (hdet : (A + B).det ≠ 0)
    (hmax : ∀ V : Matrix ι ι ℂ, IsUnitary V →
      (η * (A + V * B * Vᴴ).det).re ≤ (η * (A + B).det).re) :
    let C := A + B
    let D := (η * C.det) • (B * C⁻¹ - C⁻¹ * B)
    Dᴴ = D := by
  let C := A + B
  let D := (η * C.det) • (B * C⁻¹ - C⁻¹ * B)
  change Dᴴ = D
  apply conjTranspose_eq_of_real_trace_mul_skew_eq_zero
  intro X hX
  rw [Matrix.trace_mul_comm D X]
  let V (t : ℝ) := NormedSpace.exp ℝ (t • X)
  have hu (t : ℝ) : IsUnitary (V t) := by
    have hs : t • X ∈ skewAdjoint (Matrix ι ι ℂ) := by
      rw [skewAdjoint.mem_iff, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_smul,
        star_trivial, hX, smul_neg]
    have he := unitary.mem_iff.mp (NormedSpace.exp_mem_unitary_of_mem_skewAdjoint ℝ hs)
    exact ⟨he.2, he.1⟩
  have hv (t : ℝ) : (V t)ᴴ = NormedSpace.exp ℝ (t • (-X)) := by
    change (NormedSpace.exp ℝ (t • X))ᴴ = _
    rw [← Matrix.exp_conjTranspose ℝ, Matrix.conjTranspose_smul, star_trivial, hX]
  let M (t : ℝ) := A + V t * B * (V t)ᴴ
  have hm₀ : M 0 = C := by simp [M, V, C, NormedSpace.exp_zero]
  have hm : HasDerivAt M (X * B - B * X) 0 := by
    change HasDerivAt (fun t => A + V t * B * (V t)ᴴ) _ _
    simp_rw [hv]
    exact hasDerivAt_exp_orbit A B X
  have hd := (hasDerivAt_det hm (by simpa only [hm₀] using hdet)).const_mul η
  have hr := Complex.reCLM.hasFDerivAt.comp_hasDerivAt 0 hd
  have hloc : IsLocalMax (fun t : ℝ => (η * (M t).det).re) 0 := by
    apply Filter.Eventually.of_forall
    intro t
    change (η * (M t).det).re ≤ (η * (M 0).det).re
    rw [hm₀]
    exact hmax (V t) (hu t)
  have hz := hloc.hasDerivAt_eq_zero hr
  simp only [Complex.reCLM_apply, hm₀] at hz
  rw [show X * D = (η * C.det) • (X * (B * C⁻¹ - C⁻¹ * B)) from
    Matrix.mul_smul _ _ _, Matrix.trace_smul, smul_eq_mul]
  have hc : (C⁻¹ * (X * B - B * X)).trace = (X * (B * C⁻¹ - C⁻¹ * B)).trace := by
    simp only [Matrix.mul_sub, Matrix.trace_sub]
    rw [← Matrix.trace_mul_cycle' X B C⁻¹, Matrix.trace_mul_cycle' C⁻¹ B X]
  rw [hc, ← mul_assoc] at hz
  exact hz

end Derivative

/-- At a support maximum with nonzero real support, a skew-Hermitian inverse
commutator forces the summands to commute. -/
theorem commute_of_support_maximum_of_skew_inverse_commutator (A B : Matrix ι ι ℂ)
    (η : ℂ) (hdet : (A + B).det ≠ 0) (hκ : (η * (A + B).det).re ≠ 0)
    (hskew : let C := A + B
      let D := B * C⁻¹ - C⁻¹ * B
      Dᴴ = -D)
    (hmax : ∀ V : Matrix ι ι ℂ, IsUnitary V →
      (η * (A + V * B * Vᴴ).det).re ≤ (η * (A + B).det).re) :
    Commute A B := by
  let C := A + B
  let κ := η * C.det
  let D := B * C⁻¹ - C⁻¹ * B
  change Dᴴ = -D at hskew
  have hHerm : (κ • D)ᴴ = κ • D :=
    support_maximum_inverse_commutator A B η hdet hmax
  have hsum : (κ + star κ) • D = 0 := by
    rw [Matrix.conjTranspose_smul, hskew, smul_neg] at hHerm
    rw [add_smul, ← hHerm, neg_add_cancel]
  have hnz : κ + star κ ≠ 0 := by
    intro hz
    have h := congrArg Complex.re hz
    simp only [Complex.add_re, Complex.star_def, Complex.conj_re, Complex.zero_re] at h
    exact hκ (by linarith only [h])
  have hi : B * C⁻¹ = C⁻¹ * B := sub_eq_zero.mp ((smul_eq_zero.mp hsum).resolve_left hnz)
  have hunit : IsUnit C.det := isUnit_iff_ne_zero.mpr hdet
  have hcomm : C * B = B * C := calc
    C * B = C * ((B * C⁻¹) * C) := by rw [C.nonsing_inv_mul_cancel_right B hunit]
    _ = C * ((C⁻¹ * B) * C) := by rw [hi]
    _ = B * C := by rw [← Matrix.mul_assoc C, C.mul_nonsing_inv_cancel_left B hunit]
  simp only [C, Matrix.add_mul, Matrix.mul_add] at hcomm
  exact add_right_cancel hcomm

/-- A support maximizer with nonzero support has commuting normal summands if its
sum has all singular values equal to the same positive number. -/
theorem commute_of_scalar_unitary_support_maximum (A B : Matrix ι ι ℂ) (η : ℂ)
    (r : ℝ) (hr : r ≠ 0)
    (hA : A * Aᴴ = Aᴴ * A) (hB : B * Bᴴ = Bᴴ * B)
    (hC : (A + B) * (A + B)ᴴ = (r : ℂ) • (1 : Matrix ι ι ℂ))
    (hκ : (η * (A + B).det).re ≠ 0)
    (hmax : ∀ V : Matrix ι ι ℂ, IsUnitary V →
      (η * (A + V * B * Vᴴ).det).re ≤ (η * (A + B).det).re) :
    Commute A B := by
  let C := A + B
  let D := B * C⁻¹ - C⁻¹ * B
  let E := B * Cᴴ - Cᴴ * B
  change C * Cᴴ = _ at hC
  have hdet : C.det ≠ 0 := by
    change (η * C.det).re ≠ 0 at hκ
    intro hz
    exact hκ (by simp [hz])
  have hunit : IsUnit C.det := isUnit_iff_ne_zero.mpr hdet
  have hcstar : Cᴴ = (r : ℂ) • C⁻¹ := calc
    Cᴴ = C⁻¹ * (C * Cᴴ) := (C.nonsing_inv_mul_cancel_left Cᴴ hunit).symm
    _ = _ := by rw [hC, Matrix.mul_smul, Matrix.mul_one]
  have hnormal : C * Cᴴ = Cᴴ * C := by
    rw [hC, hcstar, Matrix.smul_mul, C.nonsing_inv_mul hunit]
  have hskew : Eᴴ = -E := by
    apply eq_neg_of_add_eq_zero_left
    have hdecomp : Eᴴ + E =
        (C * Cᴴ - Cᴴ * C) - (A * Aᴴ - Aᴴ * A) + (B * Bᴴ - Bᴴ * B) := by
      simp only [E, C, Matrix.conjTranspose_sub, Matrix.conjTranspose_add,
        Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_add,
        Matrix.add_mul]
      abel
    simp only [hdecomp, hnormal, hA, hB, sub_self, sub_zero, add_zero]
  have hscale : E = (r : ℂ) • D := by
    simp only [E, D, hcstar, Matrix.mul_smul, Matrix.smul_mul, smul_sub]
  rw [hscale, Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal, ← smul_neg] at hskew
  exact commute_of_support_maximum_of_skew_inverse_commutator A B η hdet hκ
    (smul_right_injective _ (Complex.ofReal_ne_zero.mpr hr) hskew) hmax

end

end MOC
