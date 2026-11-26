import MOC.Transfer
import MOC.CircleSpectra
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Complex.Circle
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset

/-! Unitary Schur feedback on several coordinates and exact quadrature of
the squared determinant over independently chosen opposite phases.

One common rotation avoids the singular denominators at every point
of a finite phase grid. -/

open Matrix BigOperators Finset

namespace MOC

noncomputable section

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- Feed a unitary block back through the matrix Z. -/
def blockFeedback (V : Matrix ι ι ℂ) (B : Matrix ι κ ℂ) (C : Matrix κ ι ℂ)
    (D Z : Matrix κ κ ℂ) : Matrix ι ι ℂ := V + B * (Z - D)⁻¹ * C

theorem blockFeedback_unitary (V : Matrix ι ι ℂ) (B : Matrix ι κ ℂ) (C : Matrix κ ι ℂ)
    (D Z : Matrix κ κ ℂ) (hU : IsUnitary (fromBlocks V B C D)) (hZ : IsUnitary Z)
    (hinv : IsUnit (Z - D).det) : IsUnitary (blockFeedback V B C D Z) := by
  let F := (Z - D)⁻¹ * C
  let W := blockFeedback V B C D Z
  let X := fromRows (1 : Matrix ι ι ℂ) F
  let Y := fromRows W (Z * F)
  have hF : (Z - D) * F = C := Matrix.mul_nonsing_inv_cancel_left _ _ hinv
  rw [Matrix.sub_mul] at hF
  have htop : V + B * F = W := by simp only [F, W, blockFeedback, Matrix.mul_assoc]
  have hbottom : C + D * F = Z * F := by rw [← hF]; abel
  have hUX : fromBlocks V B C D * X = Y := by
    simp only [X, Y, fromBlocks_mul_fromRows, Matrix.mul_one, htop, hbottom]
  have hg : Yᴴ * Y = Xᴴ * X := by
    rw [← hUX, conjTranspose_mul, ← Matrix.mul_assoc _ _ X,
      Matrix.mul_assoc _ (fromBlocks V B C D)ᴴ, hU.2, Matrix.mul_one]
  have hz : (Z * F)ᴴ * (Z * F) = Fᴴ * F := by
    rw [conjTranspose_mul, ← Matrix.mul_assoc _ Z F, Matrix.mul_assoc _ Zᴴ,
      hZ.2, Matrix.mul_one]
  simp only [X, Y, conjTranspose_fromRows_eq_fromCols_conjTranspose,
    fromCols_mul_fromRows, Matrix.conjTranspose_one, Matrix.one_mul, hz] at hg
  have hW : Wᴴ * W = 1 := add_right_cancel hg
  exact ⟨Matrix.mul_eq_one_comm.mp hW, hW⟩

/-- Schur's formula applies to an arbitrary selected square submatrix in the
upper left block. Its row and column labelings can differ. -/
theorem det_blockFeedback_minor {τ : Type*} [Fintype τ] [DecidableEq τ]
    (V : Matrix ι ι ℂ) (B : Matrix ι κ ℂ) (C : Matrix κ ι ℂ)
    (D Z : Matrix κ κ ℂ) (r c : τ → ι) (hinv : IsUnit (Z - D).det) :
    (Z - D).det * ((blockFeedback V B C D Z).submatrix r c).det =
      (fromBlocks (V.submatrix r c) (B.submatrix r id) (-(C.submatrix id c)) (Z - D)).det := by
  letI : Invertible (Z - D) := (Z - D).invertibleOfIsUnitDet hinv
  rw [Matrix.det_fromBlocks₂₂, Matrix.invOf_eq_nonsing_inv, Matrix.mul_neg, sub_neg_eq_add]
  congr 2
  ext i j
  simp [blockFeedback, Matrix.mul_apply, Matrix.submatrix_apply]

/-- On rows in t, choose independently between A+B and A-B. -/
def signedFeedbackRows (A B : Matrix ι ι ℂ) (t s : Finset ι) : Matrix ι ι ℂ :=
  Matrix.of fun i j => if i ∈ t then
    if i ∈ s then A i j + B i j else A i j - B i j else A i j

/-- Use B on the selected rows and A on their complement. -/
def selectedFeedbackRows (A B : Matrix ι ι ℂ) (s : Finset ι) : Matrix ι ι ℂ :=
  Matrix.of fun i j => if i ∈ s then B i j else A i j

private theorem normSq_updated_row_pair (X : Matrix ι ι ℂ) (i : ι) (a b : ι → ℂ) :
    Complex.normSq (X.updateRow i (a - b)).det + Complex.normSq (X.updateRow i (a + b)).det =
      2 * (Complex.normSq (X.updateRow i a).det + Complex.normSq (X.updateRow i b).det) := by
  have hs : a - b = a + (-1 : ℂ) • b := by ext j; simp [sub_eq_add_neg]
  rw [hs, Matrix.det_updateRow_add, Matrix.det_updateRow_smul, Matrix.det_updateRow_add,
    neg_one_mul, ← sub_eq_add_neg, Complex.normSq_sub, Complex.normSq_add]
  ring

/-- Exact positive quadrature for the squared determinant on any set of rows.
There are two signs per row. The right side sums the squared coefficient moduli. -/
theorem feedback_rows_quadrature (A B : Matrix ι ι ℂ) (t : Finset ι) :
    ∑ s ∈ t.powerset, Complex.normSq (signedFeedbackRows A B t s).det =
      (2 : ℝ)^t.card * ∑ s ∈ t.powerset, Complex.normSq (selectedFeedbackRows A B s).det := by
  induction t using Finset.induction_on generalizing A with
  | empty => simp [signedFeedbackRows, selectedFeedbackRows]
  | @insert i t hi ih =>
    let A' := A.updateRow i (B i)
    have hpair (s : Finset ι) (hs : s ∈ t.powerset) :
        Complex.normSq (signedFeedbackRows A B (insert i t) s).det +
          Complex.normSq (signedFeedbackRows A B (insert i t) (insert i s)).det =
        2 * (Complex.normSq (signedFeedbackRows A B t s).det +
             Complex.normSq (signedFeedbackRows A' B t s).det) := by
      have his : i ∉ s := fun h => hi (Finset.mem_powerset.mp hs h)
      let X := signedFeedbackRows A B t s
      have he₁ : signedFeedbackRows A B (insert i t) s = X.updateRow i (A i - B i) := by
        ext k l
        by_cases hk : k = i
        · subst k; simp [signedFeedbackRows, his]
        · simp [X, signedFeedbackRows, Matrix.updateRow_apply, hk]
      have he₂ : signedFeedbackRows A B (insert i t) (insert i s) = X.updateRow i (A i + B i) := by
        ext k l
        by_cases hk : k = i
        · subst k; simp [signedFeedbackRows]
        · simp [X, signedFeedbackRows, Matrix.updateRow_apply, hk]
      have he₃ : X.updateRow i (A i) = X := by
        ext k l
        by_cases hk : k = i
        · subst k; simp [X, signedFeedbackRows, hi]
        · simp [Matrix.updateRow_apply, hk]
      have he₄ : X.updateRow i (B i) = signedFeedbackRows A' B t s := by
        ext k l
        by_cases hk : k = i
        · subst k; simp [A', signedFeedbackRows, hi]
        · simp [A', X, signedFeedbackRows, Matrix.updateRow_apply, hk]
      rw [he₁, he₂, normSq_updated_row_pair, he₃, he₄]
    have hsel (s : Finset ι) : selectedFeedbackRows A B (insert i s) = selectedFeedbackRows A' B s := by
      ext k l
      by_cases hk : k = i
      · subst k; by_cases h : i ∈ s <;> simp [A', selectedFeedbackRows, h]
      · simp [A', selectedFeedbackRows, Matrix.updateRow_apply, hk]
    rw [Finset.sum_powerset_insert hi, ← Finset.sum_add_distrib,
      Finset.sum_congr rfl hpair, ← Finset.mul_sum, Finset.sum_add_distrib, ih A, ih A',
      Finset.sum_powerset_insert hi, Finset.card_insert_of_not_mem hi, pow_succ]
    simp_rw [hsel]
    ring

private theorem det_selected_phase_rows (A : Matrix ι ι ℂ) (z : ι → ℂ) (s : Finset ι)
    (hz : ∀ i, Complex.normSq (z i) = 1) :
    Complex.normSq (selectedFeedbackRows A (diagonal z) s).det =
      Complex.normSq (A.submatrix (Subtype.val : ↥(sᶜ) → ι) Subtype.val).det := by
  let P := selectedFeedbackRows A (1 : Matrix ι ι ℂ) s
  have hfactor : selectedFeedbackRows A (diagonal z) s =
      diagonal (fun i => if i ∈ s then z i else 1) * P := by
    ext i j
    by_cases hi : i ∈ s <;> by_cases hij : i = j <;>
      simp [P, selectedFeedbackRows, Matrix.diagonal_mul, Matrix.diagonal_apply,
        Matrix.one_apply, hi, hij]
  have hdet : P.det = (A.submatrix (Subtype.val : ↥(sᶜ) → ι) Subtype.val).det := by
    have hzero (i : ι) (hi : i ∉ sᶜ) (j : ι) (hj : j ∈ sᶜ) : P i j = 0 := by
      have hi' : i ∈ s := by simpa using hi
      have hne : i ≠ j := fun h => hi (h ▸ hj)
      simp [P, selectedFeedbackRows, hi', Matrix.one_apply_ne hne]
    have hx : P.toSquareBlockProp (· ∈ sᶜ) = A.submatrix Subtype.val Subtype.val := by
      ext i j
      have hi : i.val ∉ s := Finset.mem_compl.mp i.property
      simp [P, Matrix.toSquareBlockProp, selectedFeedbackRows, hi]
    have hy : P.toSquareBlockProp (· ∉ sᶜ) = 1 := by
      ext i j
      have hi : i.val ∈ s := by simpa using i.property
      simp [P, Matrix.toSquareBlockProp, selectedFeedbackRows, hi, Matrix.one_apply, Subtype.ext_iff]
    rw [Matrix.twoBlockTriangular_det P (· ∈ sᶜ) hzero, hx, hy, Matrix.det_one, mul_one]
    exact congrArg (fun F : Fintype ↥(sᶜ) =>
      @Matrix.det ↥(sᶜ) inferInstance F ℂ inferInstance (A.submatrix Subtype.val Subtype.val))
      (Subsingleton.elim _ _)
  rw [hfactor, Matrix.det_mul, Matrix.det_diagonal, Complex.normSq_mul, map_prod, hdet]
  have each (i : ι) : Complex.normSq (if i ∈ s then z i else 1) = 1 := by
    by_cases hi : i ∈ s <;> simp [hi, hz]
  simp only [each, Finset.prod_const_one, one_mul]

/-- The average over two opposite unit phases on each selected diagonal entry
equals the sum of the squared complementary principal minors. -/
theorem diagonal_feedback_quadrature (A : Matrix ι ι ℂ) (t : Finset ι)
    (z : ι → ℂ) (hz : ∀ i, Complex.normSq (z i) = 1) :
    (∑ s ∈ t.powerset, Complex.normSq (signedFeedbackRows A (diagonal z) t s).det) =
      (2 : ℝ)^t.card * ∑ s ∈ t.powerset,
        Complex.normSq (A.submatrix (Subtype.val : ↥(sᶜ) → ι) Subtype.val).det := by
  rw [feedback_rows_quadrature]
  simp_rw [det_selected_phase_rows A z _ hz]

/-- One unit phase rotates a finite family of invertible feedback matrices
away from all singular denominators. -/
theorem exists_common_feedback_rotation {β : Type*} [Finite β]
    (D : Matrix κ κ ℂ) (Z : β → Matrix κ κ ℂ) (hZ : ∀ b, (Z b).det ≠ 0) :
    ∃ u : ℂ, Complex.normSq u = 1 ∧ ∀ b, (u • Z b - D).det ≠ 0 := by
  classical
  let A (b : β) := (Z b)⁻¹ * D
  let P (b : β) : Polynomial ℂ :=
    (1 - (Polynomial.X : Polynomial ℂ) • Polynomial.C.mapMatrix (A b)).det
  have he (b : β) (r : ℂ) : (P b).eval r = (1 - r • A b).det := by
    rw [← Polynomial.coe_evalRingHom]
    change Polynomial.evalRingHom r ((1 - (Polynomial.X : Polynomial ℂ) •
      Polynomial.C.mapMatrix (A b)).det) = _
    rw [RingHom.map_det]
    apply congrArg Matrix.det
    ext i j : 1
    by_cases h : i = j <;>
      simp [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.sub_apply, Matrix.one_apply,
        Matrix.smul_apply, smul_eq_mul, h]
  have hp (b : β) : P b ≠ 0 := by
    intro hz
    have h := he b 0
    simp only [hz, Polynomial.eval_zero, zero_smul, sub_zero, Matrix.det_one, zero_ne_one] at h
  have hbad : (⋃ b : β, circleRotation ⁻¹' {r | (P b).IsRoot r}).Finite :=
    Set.finite_iUnion fun b => (Polynomial.finite_setOf_isRoot (hp b)).preimage
      circleRotation_injective.injOn
  obtain ⟨t, ht⟩ := hbad.exists_not_mem
  let r := circleRotation t
  have hr : Complex.normSq r = 1 := circleRotation_normSq t
  have hrne : r ≠ 0 := by
    intro hz
    simp only [hz, map_zero, zero_ne_one] at hr
  refine ⟨r⁻¹, by rw [Complex.normSq_inv, hr, inv_one], fun b => ?_⟩
  have hi : IsUnit (Z b).det := isUnit_iff_ne_zero.mpr (hZ b)
  have hP : (1 - r • A b).det ≠ 0 := by
    intro hz
    apply ht
    exact Set.mem_iUnion.mpr ⟨b, (he b r).trans hz⟩
  have hprod : (r⁻¹ • Z b) * (r • A b) = D := by
    rw [Matrix.mul_smul, Matrix.smul_mul, smul_smul, mul_inv_cancel₀ hrne, one_smul,
      A, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hi, Matrix.one_mul]
  have hfact : (r⁻¹ • Z b) * (1 - r • A b) = r⁻¹ • Z b - D := by
    rw [Matrix.mul_sub, Matrix.mul_one, hprod]
  rw [← hfact, Matrix.det_mul, Matrix.det_smul]
  exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ (inv_ne_zero hrne)) (hZ b)) hP

/-- Independently choosing opposite phases in each coordinate gives a
regular feedback grid after a single common unit rotation. -/
theorem exists_regular_signed_feedback_grid (D : Matrix κ κ ℂ)
    (z : κ → ℂ) (hz : ∀ i, Complex.normSq (z i) = 1) :
    ∃ u : ℂ, Complex.normSq u = 1 ∧ ∀ s : Finset κ,
      (Matrix.diagonal (fun i => u * (if i ∈ s then z i else -z i)) - D).det ≠ 0 := by
  let Z (s : Finset κ) := Matrix.diagonal (fun i => if i ∈ s then z i else -z i)
  have hZ (s : Finset κ) : (Z s).det ≠ 0 := by
    rw [Z, Matrix.det_diagonal]
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    have hz' : z i ≠ 0 := by
      intro h
      simpa only [h, map_zero, zero_ne_one] using hz i
    by_cases hi : i ∈ s
    · simpa only [if_pos hi] using hz'
    · simpa only [if_neg hi] using neg_ne_zero.mpr hz'
  obtain ⟨u, hu, h⟩ := exists_common_feedback_rotation D Z hZ
  refine ⟨u, hu, fun s => ?_⟩
  have he : u • Z s = Matrix.diagonal (fun i => u * (if i ∈ s then z i else -z i)) := by
    ext i j : 1
    by_cases hij : i = j <;> simp [Z, Matrix.diagonal_apply, Matrix.smul_apply, smul_eq_mul, hij]
  exact he ▸ h s

open MeasureTheory

local instance : MeasurableSpace Circle := borel Circle
local instance : BorelSpace Circle := ⟨rfl⟩

/-- Squared modulus of the bordered determinant, including at singular phases. -/
def feedbackTorusValue (A : Matrix ι ι ℂ) (t : Finset ι) (z : ι → Circle) : ℝ :=
  Complex.normSq (A + diagonal (fun i => if i ∈ t then (z i : ℂ) else 0)).det

private theorem feedbackTorusValue_continuous (A : Matrix ι ι ℂ) (t : Finset ι) :
    Continuous (feedbackTorusValue A t) := by
  apply Complex.continuous_normSq.comp
  apply Continuous.matrix_det
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  by_cases hij : i = j <;> by_cases hi : i ∈ t <;>
    simp [Matrix.add_apply, Matrix.diagonal_apply, hij, hi] <;> fun_prop

/-- The normalized Haar integral equals the sum of squared complementary
minors. Only the coordinates in t affect the integrand. -/
theorem feedback_torus_integral (A : Matrix ι ι ℂ) (t : Finset ι)
    (μ : Measure (ι → Circle)) [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant] :
    ∫ z, feedbackTorusValue A t z ∂μ =
      ∑ s ∈ t.powerset, Complex.normSq (A.submatrix (Subtype.val : ↥(sᶜ) → ι) Subtype.val).det := by
  let minus : Circle := ⟨-1, by change (-1 : ℂ) ∈ Metric.sphere 0 1; simp⟩
  let sign (s : Finset ι) (i : ι) : Circle := if i ∈ s then 1 else minus
  have hpoint (s : Finset ι) (z : ι → Circle) :
      signedFeedbackRows A (diagonal fun i => (z i : ℂ)) t s =
        A + diagonal (fun i => if i ∈ t then (((sign s * z) i : Circle) : ℂ) else 0) := by
    ext i j
    by_cases hi : i ∈ t <;> by_cases hs : i ∈ s <;> by_cases hij : i = j <;>
      simp [signedFeedbackRows, Matrix.diagonal_apply, hi, hs, hij, sign, minus, sub_eq_add_neg]
  let value := ∑ s ∈ t.powerset, Complex.normSq (A.submatrix (Subtype.val : ↥(sᶜ) → ι) Subtype.val).det
  have hquad (z : ι → Circle) :
      (∑ s ∈ t.powerset, feedbackTorusValue A t (sign s * z)) = (2 : ℝ)^t.card * value := by
    simpa only [value, feedbackTorusValue, ← hpoint] using
      diagonal_feedback_quadrature A t (fun i => (z i : ℂ)) (fun i => Circle.normSq_coe _)
  have ic (s : Finset ι) : Integrable (fun z => feedbackTorusValue A t (sign s * z)) μ :=
    ((feedbackTorusValue_continuous A t).comp (continuous_const.mul continuous_id)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have he := congrArg (fun f : (ι → Circle) → ℝ => ∫ z, f z ∂μ) (funext hquad)
  change (∫ z, ∑ s ∈ t.powerset, feedbackTorusValue A t (sign s * z) ∂μ) =
      ∫ _ : ι → Circle, (2 : ℝ)^t.card * value ∂μ at he
  rw [integral_finset_sum _ (fun s _ => ic s)] at he
  simp only [integral_mul_left_eq_self, integral_const, measureReal_univ_eq_one, one_smul,
    Finset.sum_const, Finset.card_powerset, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat] at he
  exact mul_left_cancel₀ (pow_ne_zero _ (by norm_num : (2 : ℝ) ≠ 0)) he

end

end MOC
