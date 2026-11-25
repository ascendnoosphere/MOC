import MOC.FourKleinChartSymmetry
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! The explicit inverse quadratic pencil on the normal Klein-four chart. -/

open BigOperators Matrix

namespace MOC

noncomputable section

def kleinTetrahedralColumns : Matrix (Fin 4) (Fin 3) ℝ :=
  (1 / 2 : ℝ) • !![1, 1, 1; 1, -1, -1; -1, 1, -1; -1, -1, 1]

def kleinCenteredMatrix (K : Matrix (Fin 3) (Fin 3) ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  kleinTetrahedralColumns * K * kleinTetrahedralColumnsᵀ

def kleinPermutationSign : Fin 24 → ℤ :=
  ![1,-1,-1,1,1,-1,-1,1,1,-1,-1,1,1,-1,-1,1,1,-1,-1,1,1,-1,-1,1]

theorem kleinPermutationSign_eq (i : Fin 24) :
    kleinPermutationSign i = (Equiv.Perm.sign (fourPerm i) : ℤ) := by
  revert i
  decide +kernel

/-- The signed Leibniz evaluation in the source chart's row convention. -/
def kleinSignedCost (g : Fin 24 → ℝ) (S : Matrix (Fin 4) (Fin 4) ℝ) : ℝ :=
  ∑ i : Fin 24, (kleinPermutationSign i : ℝ) * g i * ∏ k : Fin 4, S k (fourPerm i k)

def kleinPrismInput (H : Matrix (Fin 3) (Fin 3) ℝ) : KleinPrismSpace :=
  (![H 2 2, H 1 1, H 0 0], ![H 0 1, H 2 0, H 1 2], ![H 1 0, H 0 2, H 2 1])

/-- Each coordinate of the prism input is a matrix entry. -/
def kleinPrismInputLinear : Matrix (Fin 3) (Fin 3) ℝ →ₗ[ℝ] KleinPrismSpace where
  toFun := kleinPrismInput
  map_add' H K := by
    apply Prod.ext
    · funext i; fin_cases i <;> rfl
    · apply Prod.ext <;> (funext i; fin_cases i <;> rfl)
  map_smul' c H := by
    apply Prod.ext
    · funext i; fin_cases i <;> rfl
    · apply Prod.ext <;> (funext i; fin_cases i <;> rfl)

def kleinPrismOutputLinear : KleinPrismSpace →ₗ[ℝ] Matrix (Fin 3) (Fin 3) ℝ where
  toFun x := !![x.1 2, x.2.1 0, x.2.2 1; x.2.2 0, x.1 1, x.2.1 2;
    x.2.1 1, x.2.2 2, x.1 0]
  map_add' x y := by ext i j; fin_cases i <;> fin_cases j <;> rfl
  map_smul' r x := by ext i j; fin_cases i <;> fin_cases j <;> rfl

theorem kleinPrismInput_output (x : KleinPrismSpace) :
    kleinPrismInput (kleinPrismOutputLinear x) = x := by
  apply Prod.ext
  · funext i; fin_cases i <;> rfl
  · apply Prod.ext <;> (funext i; fin_cases i <;> rfl)

def kleinCofactor (K : Matrix (Fin 3) (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![K 1 1 * K 2 2 - K 1 2 * K 2 1, K 1 2 * K 2 0 - K 1 0 * K 2 2,
      K 1 0 * K 2 1 - K 1 1 * K 2 0;
    K 0 2 * K 2 1 - K 0 1 * K 2 2, K 0 0 * K 2 2 - K 0 2 * K 2 0,
      K 0 1 * K 2 0 - K 0 0 * K 2 1;
    K 0 1 * K 1 2 - K 0 2 * K 1 1, K 0 2 * K 1 0 - K 0 0 * K 1 2,
      K 0 0 * K 1 1 - K 0 1 * K 1 0]

private theorem transpose_mul_kleinCofactor (K : Matrix (Fin 3) (Fin 3) ℝ) :
    Kᵀ * kleinCofactor K = K.det • 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [kleinCofactor, Matrix.det_fin_three, Matrix.mul_apply, Matrix.transpose_apply,
      Matrix.smul_apply, Matrix.of_apply, Matrix.one_apply, Matrix.cons_val,
      Fin.sum_univ_three, smul_eq_mul] <;> ring

theorem kleinCofactor_eq_det_smul (K H : Matrix (Fin 3) (Fin 3) ℝ)
    (hKH : K * Hᵀ = 1) :
    kleinCofactor K = K.det • H := by
  have he : H * Kᵀ = 1 := by
    simpa only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_one] using
      congrArg Matrix.transpose hKH
  calc
    _ = (H * Kᵀ) * kleinCofactor K := by rw [he, Matrix.one_mul]
    _ = H * (Kᵀ * kleinCofactor K) := Matrix.mul_assoc _ _ _
    _ = _ := by rw [transpose_mul_kleinCofactor, Matrix.mul_smul, Matrix.mul_one]

private def kleinPrismFeature (x : KleinPrismSpace) : Fin 10 → ℝ :=
  let w := x.1
  let r := x.2.1
  let s := x.2.2
  ![r 0 ^ 2 + r 1 ^ 2 + r 2 ^ 2 - (s 0 ^ 2 + s 1 ^ 2 + s 2 ^ 2),
    -w 0 ^ 2 + r 1 ^ 2 + r 2 ^ 2 - s 0 ^ 2,
    -w 1 ^ 2 + r 0 ^ 2 + r 2 ^ 2 - s 1 ^ 2,
    -w 2 ^ 2 + r 0 ^ 2 + r 1 ^ 2 - s 2 ^ 2,
    -2 * w 0 * s 0 + 2 * r 1 * r 2,
    -2 * w 1 * s 1 + 2 * r 0 * r 2,
    -2 * w 2 * s 2 + 2 * r 0 * r 1,
    -2 * w 0 * r 0 + 2 * s 1 * s 2,
    -2 * w 1 * r 1 + 2 * s 0 * s 2,
    -2 * w 2 * r 2 + 2 * s 0 * s 1]

private def kleinChartWeights (β p q : Fin 3 → ℝ) (c₋ : ℝ) : Fin 10 → ℝ :=
  ![-c₋, β 0, β 1, β 2, p 0, p 1, p 2, q 0, q 1, q 2]

private theorem klein_cost_weighted_features (β p q : Fin 3 → ℝ) (c₋ : ℝ) (j : Fin 24) :
    kleinMatchingCost β p q c₋ j =
      ∑ i : Fin 10, kleinChartWeights β p q c₋ i * (kleinMatchingFeatureTable i j : ℝ) := by
  simp [kleinMatchingCost, kleinChartWeights, kleinCycle, kleinFaceIndicator,
    kleinFaceSignPlus, kleinFaceSignMinus, Fin.sum_univ_succ, Matrix.cons_val]
  <;> ring

private theorem klein_prism_weighted_features (β p q : Fin 3 → ℝ) (c₋ : ℝ)
    (x : KleinPrismSpace) :
    kleinPrismForm β p q c₋ x =
      ∑ i : Fin 10, kleinChartWeights β p q c₋ i * kleinPrismFeature x i := by
  simp [kleinPrismForm, kleinChartWeights, kleinPrismFeature, kleinPrismOff, Fin.sum_univ_succ,
    Matrix.cons_val]
  <;> ring

set_option maxHeartbeats 16000000 in
private theorem klein_prism_basis_identity (K : Matrix (Fin 3) (Fin 3) ℝ) (i : Fin 10) :
    8 * kleinSignedCost (fun j => (kleinMatchingFeatureTable i j : ℝ)) (kleinCenteredMatrix K) =
      kleinPrismFeature (kleinPrismInput (kleinCofactor K)) i := by
  fin_cases i <;>
    norm_num [kleinSignedCost, kleinPermutationSign, kleinMatchingFeatureTable,
      kleinCenteredMatrix, kleinTetrahedralColumns, kleinPrismFeature, kleinPrismInput,
      kleinCofactor, fourPerm, Equiv.Perm.mul_apply, Equiv.swap_apply_def,
      Matrix.mul_apply, Matrix.smul_apply, Matrix.transpose_apply, Matrix.of_apply, smul_eq_mul,
      Fin.sum_univ_succ, Fin.prod_univ_four, Matrix.cons_val] <;> ring

/-- Exact polynomial identity between the signed matching cost and its
quadratic prism in the cofactor entries. This includes singular matrices. -/
theorem klein_signedCost_eq_prism (β p q : Fin 3 → ℝ) (c₋ : ℝ) (K : Matrix (Fin 3) (Fin 3) ℝ) :
    8 * kleinSignedCost (kleinMatchingCost β p q c₋) (kleinCenteredMatrix K) =
      kleinPrismForm β p q c₋ (kleinPrismInput (kleinCofactor K)) := by
  rw [klein_prism_weighted_features]
  have he :
      kleinSignedCost (kleinMatchingCost β p q c₋) (kleinCenteredMatrix K) =
        ∑ i : Fin 10, kleinChartWeights β p q c₋ i *
          kleinSignedCost (fun j => (kleinMatchingFeatureTable i j : ℝ)) (kleinCenteredMatrix K) := by
    simp only [kleinSignedCost, klein_cost_weighted_features, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [← klein_prism_basis_identity K i]
  ring

private theorem klein_prismInput_smul (c : ℝ) (H : Matrix (Fin 3) (Fin 3) ℝ) :
    kleinPrismInput (c • H) = c • kleinPrismInput H := map_smul kleinPrismInputLinear c H

private theorem klein_prism_smul (β p q : Fin 3 → ℝ) (c₋ c : ℝ) (x : KleinPrismSpace) :
    kleinPrismForm β p q c₋ (c • x) = c ^ 2 * kleinPrismForm β p q c₋ x := by
  rcases x with ⟨w, r, s⟩
  simp [kleinPrismForm, kleinPrismOff, Fin.sum_univ_three, Pi.smul_apply, smul_eq_mul] <;> ring

/-- The cofactor identity in inverse entries, with the determinant factor
kept explicit. -/
theorem klein_signedCost_eq_inversePrism (β p q : Fin 3 → ℝ) (c₋ : ℝ)
    (K H : Matrix (Fin 3) (Fin 3) ℝ) (hKH : K * Hᵀ = 1) :
    8 * kleinSignedCost (kleinMatchingCost β p q c₋) (kleinCenteredMatrix K) =
      K.det ^ 2 * kleinPrismForm β p q c₋ (kleinPrismInput H) := by
  rw [klein_signedCost_eq_prism, kleinCofactor_eq_det_smul K H hKH, klein_prismInput_smul,
    klein_prism_smul]

end
end MOC
