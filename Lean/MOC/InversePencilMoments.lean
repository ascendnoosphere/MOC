import MOC.FourInversePencilRankLift
import Mathlib.Data.Real.StarOrdered
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic.Linarith

/-! The quadratic inverse-pencil condition has a positive semidefinite
moment relaxation. An affine moment plane can be excluded by test vectors. -/

open BigOperators Matrix

namespace MOC.SpectralProfile

noncomputable section

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- Linear expression in the entries of the moment matrix for the
equation `Y * D * Y = -X`. The matrices `B i` span the candidate space for `Y`. -/
def inversePencilMomentImage (D : Matrix ι ι ℝ) (B : κ → Matrix ι ι ℝ)
    (M : Matrix κ κ ℝ) : Matrix ι ι ℝ :=
  ∑ i, ∑ j, M i j • (B i * D * B j)

theorem inversePencilMomentImage_outerProduct
    (D : Matrix ι ι ℝ) (B : κ → Matrix ι ι ℝ) (x : κ → ℝ) :
    let Y := ∑ i, x i • B i
    inversePencilMomentImage D B (Matrix.vecMulVec x x) = Y * D * Y := by
  intro Y
  change inversePencilMomentImage D B (Matrix.vecMulVec x x) =
    (∑ i, x i • B i) * D * (∑ j, x j • B j)
  simp only [Finset.sum_mul]
  simp only [inversePencilMomentImage, Matrix.vecMulVec_apply, Finset.mul_sum,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_comm (x _) (x _)]

/-- A feasible quadratic lift supplies a positive semidefinite moment
matrix for the corresponding linear equations. -/
theorem exists_inversePencilMoment_of_quadraticLift
    (D X : Matrix ι ι ℝ) (B : κ → Matrix ι ι ℝ) (x : κ → ℝ)
    (h : (∑ i, x i • B i) * D * (∑ j, x j • B j) = -X) :
    ∃ M : Matrix κ κ ℝ, M.PosSemidef ∧ inversePencilMomentImage D B M = -X := by
  let row : Matrix (Fin 1) κ ℝ := fun _ i => x i
  have hrow : rowᴴ * row = Matrix.vecMulVec x x := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_one, row,
      star_trivial, Matrix.vecMulVec_apply]
  refine ⟨Matrix.vecMulVec x x, hrow ▸ Matrix.posSemidef_conjTranspose_mul_self row, ?_⟩
  rw [inversePencilMomentImage_outerProduct]
  exact h

/-- On an invertible block of size eight, a complex rank-four lift gives
the real positive semidefinite moment condition. -/
theorem exists_inversePencilMoment_of_rank_eight_lift [DecidableEq ι]
    (X : Matrix ι ι ℝ) (B : κ → Matrix ι ι ℝ) (x : κ → ℝ)
    (hcard : Fintype.card ι = 8) (hunit : IsUnit X.det) (hX : Xᵀ = X) :
    let Y := ∑ i, x i • B i
    Yᵀ = Y →
    (Complex.ofRealHom.mapMatrix X + Complex.I • Complex.ofRealHom.mapMatrix Y).rank ≤ 4 →
    ∃ M : Matrix κ κ ℝ, M.PosSemidef ∧ inversePencilMomentImage X⁻¹ B M = -X := by
  intro Y hY hrank
  let lift : Matrix ι ι ℝ →+* Matrix ι ι ℂ := Complex.ofRealHom.mapMatrix
  have hherm (T : Matrix ι ι ℝ) (hT : Tᵀ = T) : (lift T).IsHermitian := by
    change (lift T)ᴴ = lift T
    ext i j : 1
    change star (↑(T j i) : ℂ) = (↑(T i j) : ℂ)
    rw [Complex.star_def, Complex.conj_ofReal]
    exact congrArg (fun M : Matrix ι ι ℝ => (M i j : ℂ)) hT
  have hlu : IsUnit (lift X).det := by
    have hd : (lift X).det = Complex.ofRealHom X.det := (Complex.ofRealHom.map_det X).symm
    rw [hd]
    exact hunit.map Complex.ofRealHom
  have hinv : lift X⁻¹ = (lift X)⁻¹ := by
    calc
      lift X⁻¹ = lift X⁻¹ * (lift X * (lift X)⁻¹) := by
        rw [(lift X).mul_nonsing_inv hlu, Matrix.mul_one]
      _ = (lift X)⁻¹ := by
        rw [← Matrix.mul_assoc, ← map_mul, X.nonsing_inv_mul hunit, map_one, Matrix.one_mul]
  have hlift := rank_eight_lift_inverse_identity (lift X) (lift Y)
    (hherm X hX) (hherm Y hY) hcard hlu hrank
  have he : lift (Y * X⁻¹ * Y) = lift (-X) := by
    simpa only [map_mul, map_neg, hinv] using hlift
  apply exists_inversePencilMoment_of_quadraticLift X⁻¹ X B x
  change Y * X⁻¹ * Y = -X
  ext i j : 1
  exact Complex.ofReal_injective (congrArg (fun M : Matrix ι ι ℂ => M i j) he)

/-- A certificate for a moment plane whose evaluations on three chosen
vectors have the indicated affine coefficients. -/
theorem fourMomentPlane_13_17_18_23_27_30_not_posSemidef
    (M : Matrix (Fin 4) (Fin 4) ℝ) (t z : ℝ)
    (h₀ : dotProduct (![12, 9, 2, -26] : Fin 4 → ℝ) (M *ᵥ ![12, 9, 2, -26]) =
      -960741 / 361 + (13215 / 56) * t + (4345 / 16) * z)
    (h₁ : dotProduct (![16, 11, 4, -25] : Fin 4 → ℝ) (M *ᵥ ![16, 11, 4, -25]) =
      -63352287 / 12635 + (3054441 / 9800) * t - (150013 / 560) * z)
    (h₂ : dotProduct (![17, 9, 7, -29] : Fin 4 → ℝ) (M *ᵥ ![17, 9, 7, -29]) =
      -54375516 / 12635 - (1244623 / 2450) * t + (19499 / 140) * z) :
    ¬ M.PosSemidef := by
  intro hm
  have h₀' := hm.2 (![12, 9, 2, -26] : Fin 4 → ℝ)
  have h₁' := hm.2 (![16, 11, 4, -25] : Fin 4 → ℝ)
  have h₂' := hm.2 (![17, 9, 7, -29] : Fin 4 → ℝ)
  simp only [star_trivial, h₀, h₁, h₂] at h₀' h₁' h₂'
  linarith only [h₀', h₁', h₂']

/-- The test for the moment plane with ordinary ray indices 7, 13, 20,
27 and 31. The equations are the three test-vector evaluations. -/
theorem fourMomentPlane_7_13_20_27_31_not_posSemidef
    (M : Matrix (Fin 4) (Fin 4) ℝ) (t z : ℝ)
    (h₀ : dotProduct (![0, 21, -19, -15] : Fin 4 → ℝ) (M *ᵥ ![0, 21, -19, -15]) =
      -492730 / 17 - (475904 / 26265) * t + (77506 / 5253) * z)
    (h₁ : dotProduct (![1, -27, 21, 21] : Fin 4 → ℝ) (M *ᵥ ![1, -27, 21, 21]) =
      -60405485 / 1326 + (7843852 / 78795) * t - (29801659 / 409734) * z)
    (h₂ : dotProduct (![2, -30, 25, 18] : Fin 4 → ℝ) (M *ᵥ ![2, -30, 25, 18]) =
      -33202115 / 663 + (24787376 / 78795) * t - (59969644 / 204867) * z) :
    ¬ M.PosSemidef := by
  intro hm
  have h₀' := hm.2 (![0, 21, -19, -15] : Fin 4 → ℝ)
  have h₁' := hm.2 (![1, -27, 21, 21] : Fin 4 → ℝ)
  have h₂' := hm.2 (![2, -30, 25, 18] : Fin 4 → ℝ)
  simp only [star_trivial, h₀, h₁, h₂] at h₀' h₁' h₂'
  linarith only [h₀', h₁', h₂']

/-- The test for the moment plane with ordinary ray indices 7, 13, 18,
27 and 31. The equations are the three test-vector evaluations. -/
theorem fourMomentPlane_7_13_18_27_31_not_posSemidef
    (M : Matrix (Fin 4) (Fin 4) ℝ) (t z : ℝ)
    (h₀ : dotProduct (![16, -4, -15, -5] : Fin 4 → ℝ) (M *ᵥ ![16, -4, -15, -5]) =
      -23298452528 / 681835 - (6461585875 / 94131548) * t + (7244733547 / 117664435) * z)
    (h₁ : dotProduct (![22, -1, -21, -11] : Fin 4 → ℝ) (M *ᵥ ![22, -1, -21, -11]) =
      -69132409 / 1265 + (10383692077 / 61473664) * t - (728239303 / 4802630) * z)
    (h₂ : dotProduct (![24, -2, -25, -10] : Fin 4 → ℝ) (M *ᵥ ![24, -2, -25, -10]) =
      -48307838732 / 681835 + (85480596465 / 376526192) * t - (23000079832 / 117664435) * z) :
    ¬ M.PosSemidef := by
  intro hm
  have h₀' := hm.2 (![16, -4, -15, -5] : Fin 4 → ℝ)
  have h₁' := hm.2 (![22, -1, -21, -11] : Fin 4 → ℝ)
  have h₂' := hm.2 (![24, -2, -25, -10] : Fin 4 → ℝ)
  simp only [star_trivial, h₀, h₁, h₂] at h₀' h₁' h₂'
  linarith only [h₀', h₁', h₂']

/-- The test for the moment plane with ordinary ray indices 7, 13, 18,
27, 30 and 31. The equations are the three test-vector evaluations. -/
theorem fourMomentPlane_7_13_18_27_30_31_not_posSemidef
    (M : Matrix (Fin 4) (Fin 4) ℝ) (t z : ℝ)
    (h₀ : dotProduct (![3, 10, -15, -6] : Fin 4 → ℝ) (M *ᵥ ![3, 10, -15, -6]) =
      -6367195312919075 / 152675101458 - (7302021400919 / 242261318016) * t +
        (108613367387 / 3785333094) * z)
    (h₁ : dotProduct (![4, 13, -21, -6] : Fin 4 → ℝ) (M *ᵥ ![4, 13, -21, -6]) =
      -2808092408368349809 / 48550682263644 + (6999610080479975 / 77039099129088) * t -
        (106400904131075 / 1203735923892) * z)
    (h₂ : dotProduct (![5, 17, -28, -8] : Fin 4 → ℝ) (M *ᵥ ![5, 17, -28, -8]) =
      -134074150127850314 / 1103424596901 + (479209475939189 / 19259774782272) * t -
        (6418502985593 / 300933980973) * z) :
    ¬ M.PosSemidef := by
  intro hm
  have h₀' := hm.2 (![3, 10, -15, -6] : Fin 4 → ℝ)
  have h₁' := hm.2 (![4, 13, -21, -6] : Fin 4 → ℝ)
  have h₂' := hm.2 (![5, 17, -28, -8] : Fin 4 → ℝ)
  simp only [star_trivial, h₀, h₁, h₂] at h₀' h₁' h₂'
  linarith only [h₀', h₁', h₂']

end

end MOC.SpectralProfile
