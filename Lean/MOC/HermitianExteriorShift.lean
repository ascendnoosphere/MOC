import MOC.DruryHermitianPencil
import MOC.ExtendedCases
import MOC.Variational
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Data.Quot
import Mathlib.Logic.Relation
import Mathlib.Tactic.FinCases

/-! Resolvent estimates for a scalar translate of a Hermitian-by-normal
support problem. Here all matrix operator norms are Euclidean. -/

open BigOperators Matrix
open scoped Matrix.L2OpNorm

namespace MOC

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The nonscalar part of the second-order resolvent expansion. -/
def exteriorRemainder (z : ℂ) (Y : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  (Y * Y) * (z • (1 : Matrix ι ι ℂ) + Y)⁻¹

/-- The Hermitian part of a complex matrix. -/
def exteriorHermitianPart (X : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  (1 / 2 : ℂ) • (X + Xᴴ)

private theorem exteriorHermitianPart_add (X Y : Matrix ι ι ℂ) :
    exteriorHermitianPart (X + Y) =
      exteriorHermitianPart X + exteriorHermitianPart Y := by
  unfold exteriorHermitianPart
  rw [Matrix.conjTranspose_add, ← smul_add]
  congr 1
  abel

private theorem exteriorHermitianPart_neg (X : Matrix ι ι ℂ) :
    exteriorHermitianPart (-X) = -exteriorHermitianPart X := by
  simp only [exteriorHermitianPart, Matrix.conjTranspose_neg, ← neg_add, smul_neg]

private theorem exteriorHermitianPart_sub (X Y : Matrix ι ι ℂ) :
    exteriorHermitianPart (X - Y) =
      exteriorHermitianPart X - exteriorHermitianPart Y := by
  simp only [sub_eq_add_neg, exteriorHermitianPart_add, exteriorHermitianPart_neg]

private theorem exteriorHermitianPart_smul_of_hermitian (c : ℂ)
    (X : Matrix ι ι ℂ) (hX : X.IsHermitian) :
    exteriorHermitianPart (c • X) = (c.re : ℂ) • X := by
  rw [exteriorHermitianPart, Matrix.conjTranspose_smul, hX.eq, ← add_smul, smul_smul]
  have hc : (1 / 2 : ℂ) * (c + star c) = (c.re : ℂ) := by
    rw [Complex.star_def, Complex.add_conj, Complex.ofReal_mul, Complex.ofReal_ofNat]
    ring
  rw [hc]

private theorem exteriorHermitianPart_diagonal (c : ℂ) (b : ι → ℂ) :
    exteriorHermitianPart (c • diagonal b) =
      diagonal (fun i => (((c * b i).re : ℝ) : ℂ)) := by
  have hd : c • diagonal b = diagonal (fun i => c * b i) := by
    rw [← Matrix.diagonal_smul]
    rfl
  rw [hd, exteriorHermitianPart, Matrix.diagonal_conjTranspose, Matrix.diagonal_add,
    ← Matrix.diagonal_smul]
  apply congrArg diagonal
  funext i
  change (1 / 2 : ℂ) * (c * b i + star (c * b i)) = ((c * b i).re : ℂ)
  rw [Complex.star_def, Complex.add_conj, Complex.ofReal_mul, Complex.ofReal_ofNat]
  ring

private theorem exteriorHermitianPart_opNorm (X : Matrix ι ι ℂ) :
    ‖exteriorHermitianPart X‖ ≤ ‖X‖ := by
  have hhalf : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num [norm_div]
  rw [exteriorHermitianPart, norm_smul, hhalf]
  calc
    _ ≤ (1 / 2) * (‖X‖ + ‖Xᴴ‖) := mul_le_mul_of_nonneg_left (norm_add_le _ _) (by norm_num)
    _ = ‖X‖ := by rw [Matrix.l2_opNorm_conjTranspose]; ring

/-- A scalar translate is nonsingular if the modulus of the translate
is larger than the operator norm of the summand. The inverse bound
uses the gap to that norm. -/
theorem exterior_resolvent_bound [Nonempty ι] (z : ℂ) (Y : Matrix ι ι ℂ)
    (h : ‖Y‖ < ‖z‖) :
    let C := z • (1 : Matrix ι ι ℂ) + Y
    IsUnit C.det ∧ ‖C⁻¹‖ ≤ (‖z‖ - ‖Y‖)⁻¹ := by
  intro C
  have hnz : z ≠ 0 := norm_pos_iff.mp ((norm_nonneg Y).trans_lt h)
  have hratio : ‖(-z⁻¹) • Y‖ < 1 := by
    rw [norm_smul, norm_neg, norm_inv, inv_mul_eq_div]
    exact (div_lt_one (norm_pos_iff.mpr hnz)).mpr h
  have hunit : IsUnit (z • (1 : Matrix ι ι ℂ)) := by
    rw [← Algebra.algebraMap_eq_smul_one]
    exact (isUnit_iff_ne_zero.mpr hnz).map (algebraMap ℂ (Matrix ι ι ℂ))
  have he : (z • (1 : Matrix ι ι ℂ)) * (1 - (-z⁻¹) • Y) = C := by
    change (z • (1 : Matrix ι ι ℂ)) * (1 - (-z⁻¹) • Y) = z • 1 + Y
    rw [Matrix.mul_sub, Matrix.mul_one, Matrix.mul_smul, Matrix.smul_mul, Matrix.one_mul,
      smul_smul, show -z⁻¹ * z = -1 by rw [neg_mul, inv_mul_cancel₀ hnz],
      neg_smul, one_smul, sub_neg_eq_add]
  have hs : IsUnit ((1 : Matrix ι ι ℂ) - (-z⁻¹) • Y) := by
    simpa only [Units.val_oneSub] using (Units.oneSub _ hratio).isUnit
  have hC : IsUnit C.det := (Matrix.isUnit_iff_isUnit_det C).mp (he ▸ hunit.mul hs)
  have hlin : z • C⁻¹ + Y * C⁻¹ = 1 := by
    have hc := C.mul_nonsing_inv hC
    change (z • (1 : Matrix ι ι ℂ) + Y) * C⁻¹ = 1 at hc
    simpa only [Matrix.add_mul, Matrix.smul_mul, Matrix.one_mul] using hc
  have heq : z • C⁻¹ = 1 - Y * C⁻¹ := eq_sub_of_add_eq hlin
  have hnorm : ‖z‖ * ‖C⁻¹‖ ≤ 1 + ‖Y‖ * ‖C⁻¹‖ := calc
    _ = ‖z • C⁻¹‖ := (norm_smul z C⁻¹).symm
    _ ≤ ‖(1 : Matrix ι ι ℂ)‖ + ‖Y * C⁻¹‖ := by
      rw [heq]
      exact norm_sub_le 1 (Y * C⁻¹)
    _ ≤ _ := by rw [norm_one]; exact add_le_add_left (norm_mul_le Y C⁻¹) 1
  have hd : 0 < ‖z‖ - ‖Y‖ := sub_pos.mpr h
  refine ⟨hC, ?_⟩
  rw [← one_div (‖z‖ - ‖Y‖)]
  apply (le_div_iff₀ hd).mpr
  rw [mul_comm ‖C⁻¹‖, sub_mul]
  linarith only [hnorm]

/-- Exact expansion of the resolvent through the linear term. -/
theorem exterior_resolvent_expansion (z : ℂ) (Y : Matrix ι ι ℂ)
    (h : IsUnit (z • (1 : Matrix ι ι ℂ) + Y).det) :
    z ^ 2 • (z • (1 : Matrix ι ι ℂ) + Y)⁻¹ =
      z • (1 : Matrix ι ι ℂ) - Y + exteriorRemainder z Y := by
  let Z : Matrix ι ι ℂ := z • 1
  let C := Z + Y
  have hc : C * C⁻¹ = 1 := C.mul_nonsing_inv h
  have hcomm : Z * Y = Y * Z := by
    simp only [Z, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]
  have hsq : Z * Z = (z ^ 2) • (1 : Matrix ι ι ℂ) := by
    simp only [Z, Matrix.smul_mul, Matrix.one_mul, smul_smul, pow_two]
  have he : (Z - Y) * C = (z ^ 2) • 1 - Y * Y := by
    change (Z - Y) * (Z + Y) = _
    rw [Matrix.mul_add, Matrix.sub_mul, Matrix.sub_mul, hcomm, hsq]
    abel
  have hp := congrArg (fun X : Matrix ι ι ℂ => X * C⁻¹) he
  simp only [Matrix.mul_assoc, hc, Matrix.mul_one, Matrix.sub_mul, Matrix.smul_mul,
    Matrix.one_mul] at hp
  change (z ^ 2) • C⁻¹ = Z - Y + (Y * Y) * C⁻¹
  exact eq_add_of_sub_eq (by simpa only [Matrix.mul_assoc] using hp.symm)

/-- The quadratic remainder has the operator norm bound used in the
exterior support comparison. -/
theorem exterior_remainder_bound [Nonempty ι] (z : ℂ) (Y : Matrix ι ι ℂ)
    (L : ℝ) (hY : ‖Y‖ ≤ L) (h : L < ‖z‖) :
    ‖exteriorRemainder z Y‖ ≤ L ^ 2 / (‖z‖ - L) := by
  obtain ⟨_, hinv⟩ := exterior_resolvent_bound z Y (hY.trans_lt h)
  have hL : 0 ≤ L := (norm_nonneg Y).trans hY
  have hgap : (‖z‖ - ‖Y‖)⁻¹ ≤ (‖z‖ - L)⁻¹ :=
    inv_anti₀ (sub_pos.mpr h) (sub_le_sub_left hY _)
  change ‖(Y * Y) * (z • (1 : Matrix ι ι ℂ) + Y)⁻¹‖ ≤ _
  calc
    _ ≤ ‖Y * Y‖ * ‖(z • (1 : Matrix ι ι ℂ) + Y)⁻¹‖ := norm_mul_le _ _
    _ ≤ L ^ 2 * (‖z‖ - L)⁻¹ := by
      apply mul_le_mul _ (hinv.trans hgap) (norm_nonneg _) (sq_nonneg L)
      exact (norm_mul_le Y Y).trans (by rw [pow_two]; exact mul_le_mul hY hY (norm_nonneg Y) hL)
    _ = _ := (div_eq_mul_inv _ _).symm

private theorem commute_hermitianPart_of_hermitian_commutator
    (H X : Matrix ι ι ℂ) (hH : H.IsHermitian)
    (h : (H * X - X * H)ᴴ = H * X - X * H) :
    Commute H (exteriorHermitianPart X) := by
  rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hH.eq] at h
  change H * ((1 / 2 : ℂ) • (X + Xᴴ)) = ((1 / 2 : ℂ) • (X + Xᴴ)) * H
  rw [Matrix.mul_smul, Matrix.smul_mul]
  congr 1
  rw [Matrix.mul_add, Matrix.add_mul]
  calc
    _ = (H * X - X * H) + X * H + H * Xᴴ := by abel
    _ = _ := by rw [← h]; abel

/-- The exterior stationarity equation at a nonsingular determinant-support
maximum. The displayed complex direction is the determinant phase divided
by the square of the scalar translate before real normalization. -/
theorem exterior_stationary_commute (z η : ℂ) (b : ι → ℂ) (H : Matrix ι ι ℂ)
    (hH : H.IsHermitian) (hz : z ≠ 0)
    (hC : IsUnit (z • (1 : Matrix ι ι ℂ) + (H + diagonal b)).det)
    (hmax : ∀ V : Matrix ι ι ℂ, IsUnitary V →
      (η * ((z • (1 : Matrix ι ι ℂ) + diagonal b) + V * H * Vᴴ).det).re ≤
        (η * ((z • (1 : Matrix ι ι ℂ) + diagonal b) + H).det).re) :
    let Y := H + diagonal b
    let C := z • (1 : Matrix ι ι ℂ) + Y
    let v := η * C.det / z ^ 2
    Commute H (diagonal (fun i => (((v * b i).re : ℝ) : ℂ)) -
      exteriorHermitianPart (v • exteriorRemainder z Y)) := by
  intro Y C v
  let Z : Matrix ι ι ℂ := z • 1
  let B : Matrix ι ι ℂ := diagonal b
  let κ := η * C.det
  have hmat : (Z + B) + H = C := by
    change Z + B + H = Z + (H + B)
    abel
  have h := support_maximum_inverse_commutator (Z + B) H η
    (by rw [hmat]; exact hC.ne_zero) hmax
  change ((η * ((Z + B) + H).det) • (H * ((Z + B) + H)⁻¹ -
    ((Z + B) + H)⁻¹ * H))ᴴ =
      (η * ((Z + B) + H).det) • (H * ((Z + B) + H)⁻¹ - ((Z + B) + H)⁻¹ * H) at h
  rw [hmat] at h
  have hcomm := commute_hermitianPart_of_hermitian_commutator H (κ • C⁻¹) hH
    (by simpa only [κ, Matrix.mul_smul, Matrix.smul_mul, ← smul_sub] using h)
  have hv : v * z ^ 2 = κ := div_mul_cancel₀ κ (pow_ne_zero 2 hz)
  have hres : κ • C⁻¹ = v • Z - (v • H + v • B) + v • exteriorRemainder z Y := by
    rw [← hv, ← smul_smul, exterior_resolvent_expansion z Y hC, smul_add, smul_sub]
    change v • Z - v • (H + B) + v • exteriorRemainder z Y = _
    rw [smul_add]
  rw [hres, exteriorHermitianPart_add, exteriorHermitianPart_sub, exteriorHermitianPart_add,
    exteriorHermitianPart_smul_of_hermitian v H hH, exteriorHermitianPart_diagonal] at hcomm
  have hZ : exteriorHermitianPart (v • Z) = (((v * z).re : ℝ) : ℂ) • (1 : Matrix ι ι ℂ) := by
    rw [show v • Z = (v * z) • (1 : Matrix ι ι ℂ) from smul_smul v z 1]
    exact exteriorHermitianPart_smul_of_hermitian _ _ Matrix.isHermitian_one
  have hfixed : Commute H (exteriorHermitianPart (v • Z) - (v.re : ℂ) • H) := by
    rw [hZ]
    exact ((Commute.one_right H).smul_right _).sub_right ((Commute.refl H).smul_right _)
  have hsplit :
      exteriorHermitianPart (v • Z) -
          ((v.re : ℂ) • H + diagonal (fun i => (((v * b i).re : ℝ) : ℂ))) +
          exteriorHermitianPart (v • exteriorRemainder z Y) =
        (exteriorHermitianPart (v • Z) - (v.re : ℂ) • H) -
          (diagonal (fun i => (((v * b i).re : ℝ) : ℂ)) -
            exteriorHermitianPart (v • exteriorRemainder z Y)) := by
    abel
  rw [hsplit] at hcomm
  simpa only [sub_sub_cancel] using hfixed.sub_right hcomm

/-- Frobenius norm, kept separate from the Euclidean operator norm. -/
def exteriorFrobenius (A : Matrix ι ι ℂ) : ℝ :=
  @Norm.norm _ (@SeminormedAddCommGroup.toNorm _ Matrix.frobeniusSeminormedAddCommGroup) A

private theorem exteriorFrobenius_nonneg (A : Matrix ι ι ℂ) : 0 ≤ exteriorFrobenius A := by
  exact @norm_nonneg _
    (@SeminormedAddCommGroup.toSeminormedAddGroup _ Matrix.frobeniusSeminormedAddCommGroup) A

private theorem exteriorFrobenius_sq (A : Matrix ι ι ℂ) :
    exteriorFrobenius A ^ 2 = ∑ i, ∑ j, ‖A i j‖ ^ 2 := by
  rw [exteriorFrobenius, Matrix.frobenius_norm_def]
  simp only [Real.rpow_two, ← Real.sqrt_eq_rpow]
  exact Real.sq_sqrt (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)

private theorem exteriorFrobenius_add (A B : Matrix ι ι ℂ) :
    exteriorFrobenius (A + B) ≤ exteriorFrobenius A + exteriorFrobenius B := by
  exact @norm_add_le _
    (@SeminormedAddCommGroup.toSeminormedAddGroup _ Matrix.frobeniusSeminormedAddCommGroup) A B

private theorem exteriorFrobenius_conjTranspose (A : Matrix ι ι ℂ) :
    exteriorFrobenius Aᴴ = exteriorFrobenius A := by
  exact Matrix.frobenius_norm_conjTranspose A

private theorem exteriorFrobenius_smul (c : ℂ) (X : Matrix ι ι ℂ) :
    exteriorFrobenius (c • X) = ‖c‖ * exteriorFrobenius X := by
  exact @norm_smul ℂ _ _
    (@SeminormedAddCommGroup.toSeminormedAddGroup _ Matrix.frobeniusSeminormedAddCommGroup)
    _ Matrix.frobeniusIsBoundedSMul c X

private theorem exteriorHermitianPart_frobenius (X : Matrix ι ι ℂ) :
    exteriorFrobenius (exteriorHermitianPart X) ≤ exteriorFrobenius X := by
  have hhalf : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num [norm_div]
  rw [exteriorHermitianPart, exteriorFrobenius_smul, hhalf]
  calc
    _ ≤ (1 / 2) * (exteriorFrobenius X + exteriorFrobenius Xᴴ) :=
      mul_le_mul_of_nonneg_left (exteriorFrobenius_add _ _) (by norm_num)
    _ = _ := by rw [exteriorFrobenius_conjTranspose]; ring

private theorem exteriorFrobenius_mul_left (A B : Matrix ι ι ℂ) :
    exteriorFrobenius (A * B) ≤ ‖A‖ * exteriorFrobenius B := by
  let column (X : Matrix ι ι ℂ) (j : ι) : EuclideanSpace ℂ ι :=
    (EuclideanSpace.equiv ι ℂ).symm (fun i => X i j)
  have hcolumn (X : Matrix ι ι ℂ) (j : ι) : ‖column X j‖ ^ 2 = ∑ i, ‖X i j‖ ^ 2 := by
    change ‖column X j‖ ^ 2 = ∑ i, ‖(column X j) i‖ ^ 2
    exact PiLp.norm_sq_eq_of_L2 _ _
  have hmul (j : ι) : column (A * B) j =
      (EuclideanSpace.equiv ι ℂ).symm (A *ᵥ column B j) := rfl
  apply (sq_le_sq₀ (exteriorFrobenius_nonneg _) (mul_nonneg (norm_nonneg _) (exteriorFrobenius_nonneg _))).mp
  calc
    exteriorFrobenius (A * B) ^ 2 = ∑ j, ‖column (A * B) j‖ ^ 2 := by
      simp only [exteriorFrobenius_sq, hcolumn]
      exact Finset.sum_comm
    _ ≤ ∑ j, (‖A‖ * ‖column B j‖) ^ 2 := by
      apply Finset.sum_le_sum
      intro j _
      rw [hmul]
      exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr
        (Matrix.l2_opNorm_mulVec A (column B j))
    _ = (‖A‖ * exteriorFrobenius B) ^ 2 := by
      simp only [mul_pow, ← Finset.mul_sum, hcolumn, exteriorFrobenius_sq]
      rw [Finset.sum_comm]

private theorem exteriorFrobenius_mul_right (A B : Matrix ι ι ℂ) :
    exteriorFrobenius (A * B) ≤ exteriorFrobenius A * ‖B‖ := by
  rw [← exteriorFrobenius_conjTranspose (A * B), Matrix.conjTranspose_mul]
  calc
    _ ≤ ‖Bᴴ‖ * exteriorFrobenius Aᴴ := exteriorFrobenius_mul_left Bᴴ Aᴴ
    _ = _ := by rw [Matrix.l2_opNorm_conjTranspose, exteriorFrobenius_conjTranspose, mul_comm]

private theorem exterior_inverse_sub (A B : Matrix ι ι ℂ)
    (hA : IsUnit A.det) (hB : IsUnit B.det) :
    A⁻¹ - B⁻¹ = (A⁻¹ * (B - A)) * B⁻¹ := by
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc A⁻¹ B, B.mul_nonsing_inv hB,
    Matrix.mul_one, A.nonsing_inv_mul hA, Matrix.one_mul]

/-- The sharp mixed-norm Lipschitz estimate for the quadratic
remainder on an operator-norm ball. -/
theorem exterior_remainder_frobenius_lipschitz [Nonempty ι]
    (z : ℂ) (Y Z : Matrix ι ι ℂ) (L : ℝ)
    (hY : ‖Y‖ ≤ L) (hZ : ‖Z‖ ≤ L) (hL : L < ‖z‖) :
    let d := ‖z‖ - L
    exteriorFrobenius (exteriorRemainder z Y - exteriorRemainder z Z) ≤
      (2 * L / d + L ^ 2 / d ^ 2) * exteriorFrobenius (Y - Z) := by
  intro d
  let C := z • (1 : Matrix ι ι ℂ) + Y
  let D := z • (1 : Matrix ι ι ℂ) + Z
  let p := exteriorFrobenius (Y - Z)
  have hLn : 0 ≤ L := (norm_nonneg Y).trans hY
  have hpn : 0 ≤ p := exteriorFrobenius_nonneg _
  have hd : 0 < d := sub_pos.mpr hL
  have hdi : 0 ≤ d⁻¹ := (inv_pos.mpr hd).le
  obtain ⟨hC, hCbound⟩ := exterior_resolvent_bound z Y (hY.trans_lt hL)
  obtain ⟨hD, hDbound⟩ := exterior_resolvent_bound z Z (hZ.trans_lt hL)
  have hC' : ‖C⁻¹‖ ≤ d⁻¹ := hCbound.trans
    (inv_anti₀ hd (sub_le_sub_left hY _))
  have hD' : ‖D⁻¹‖ ≤ d⁻¹ := hDbound.trans
    (inv_anti₀ hd (sub_le_sub_left hZ _))
  have hCD : D - C = -(Y - Z) := by dsimp only [C, D]; abel
  have hneg : exteriorFrobenius (-(Y - Z)) = p :=
    @norm_neg _
      (@SeminormedAddCommGroup.toSeminormedAddGroup _ Matrix.frobeniusSeminormedAddCommGroup) (Y - Z)
  have hinv : exteriorFrobenius (C⁻¹ - D⁻¹) ≤ d⁻¹ * p * d⁻¹ := by
    rw [exterior_inverse_sub C D hC hD, hCD]
    calc
      _ ≤ exteriorFrobenius (C⁻¹ * -(Y - Z)) * ‖D⁻¹‖ :=
        exteriorFrobenius_mul_right _ _
      _ ≤ ‖C⁻¹‖ * p * ‖D⁻¹‖ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        simpa only [hneg] using exteriorFrobenius_mul_left C⁻¹ (-(Y - Z))
      _ ≤ d⁻¹ * p * d⁻¹ :=
        mul_le_mul (mul_le_mul_of_nonneg_right hC' hpn) hD'
          (norm_nonneg _) (mul_nonneg hdi hpn)
  have hsq : (Y * Y) - (Z * Z) = Y * (Y - Z) + (Y - Z) * Z := by
    simp only [Matrix.mul_sub, Matrix.sub_mul]
    abel
  have hsqbound : exteriorFrobenius ((Y * Y) - (Z * Z)) ≤ 2 * L * p := by
    rw [hsq]
    calc
      _ ≤ exteriorFrobenius (Y * (Y - Z)) + exteriorFrobenius ((Y - Z) * Z) :=
        exteriorFrobenius_add _ _
      _ ≤ L * p + p * L := by
        exact add_le_add ((exteriorFrobenius_mul_left _ _).trans (mul_le_mul_of_nonneg_right hY hpn))
          ((exteriorFrobenius_mul_right _ _).trans (mul_le_mul_of_nonneg_left hZ hpn))
      _ = _ := by ring
  have hdiff : exteriorRemainder z Y - exteriorRemainder z Z =
      ((Y * Y) - (Z * Z)) * C⁻¹ + (Z * Z) * (C⁻¹ - D⁻¹) := by
    change (Y * Y) * C⁻¹ - (Z * Z) * D⁻¹ = _
    simp only [Matrix.sub_mul, Matrix.mul_sub]
    abel
  rw [hdiff]
  calc
    _ ≤ exteriorFrobenius (((Y * Y) - (Z * Z)) * C⁻¹) +
        exteriorFrobenius ((Z * Z) * (C⁻¹ - D⁻¹)) := exteriorFrobenius_add _ _
    _ ≤ (2 * L * p) * d⁻¹ + L ^ 2 * (d⁻¹ * p * d⁻¹) := by
      apply add_le_add
      · exact (exteriorFrobenius_mul_right _ _).trans
          (mul_le_mul hsqbound hC' (norm_nonneg _) (by positivity))
      · apply (exteriorFrobenius_mul_left _ _).trans
        apply mul_le_mul _ hinv (exteriorFrobenius_nonneg _) (sq_nonneg L)
        exact (norm_mul_le Z Z).trans (by rw [pow_two]; exact mul_le_mul hZ hZ (norm_nonneg Z) hLn)
    _ = _ := by rw [div_eq_mul_inv, div_eq_mul_inv, ← inv_pow]; ring

section Blocks

variable {κ : Type*} [DecidableEq κ]

/-- Keep the entries between different identified blocks. -/
def exteriorOffBlock (f : ι → κ) (X : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  fun i j => if f i = f j then 0 else X i j

private def exteriorComm (A B : Matrix ι ι ℂ) : Matrix ι ι ℂ := A * B - B * A

private theorem exteriorFrobenius_neg (A : Matrix ι ι ℂ) :
    exteriorFrobenius (-A) = exteriorFrobenius A := by
  exact @norm_neg _
    (@SeminormedAddCommGroup.toSeminormedAddGroup _ Matrix.frobeniusSeminormedAddCommGroup) A

private theorem exteriorOffBlock_frobenius (f : ι → κ) (A : Matrix ι ι ℂ) :
    exteriorFrobenius (exteriorOffBlock f A) ≤ exteriorFrobenius A := by
  apply (sq_le_sq₀ (exteriorFrobenius_nonneg _) (exteriorFrobenius_nonneg _)).mp
  simp only [exteriorFrobenius_sq]
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  by_cases h : f i = f j
  · simpa only [exteriorOffBlock, h, if_true, norm_zero, zero_pow two_ne_zero] using
      sq_nonneg ‖A i j‖
  · simp only [exteriorOffBlock, h, if_false, le_refl]

/-- Keeping only the diagonal blocks is a contraction in Euclidean operator norm. -/
theorem exterior_block_compression_opNorm (f : ι → κ) (A : Matrix ι ι ℂ) :
    ‖A - exteriorOffBlock f A‖ ≤ ‖A‖ := by
  let A₀ := A - exteriorOffBlock f A
  let s := Finset.univ.image f
  have hgroup (w : ι → ℝ) :
      (∑ k ∈ s, ∑ i, if f i = k then w i else 0) = ∑ i, w i := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    have hi : f i ∈ s := Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
    rw [Finset.sum_eq_single_of_mem (f i) hi (fun k _ hk => if_neg (Ne.symm hk)), if_pos rfl]
  rw [Matrix.cstar_norm_def (A - exteriorOffBlock f A)]
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg A)
  intro x
  let xk (k : κ) : EuclideanSpace ℂ ι :=
    (EuclideanSpace.equiv ι ℂ).symm (fun i => if f i = k then x i else 0)
  let y (B : Matrix ι ι ℂ) (v : EuclideanSpace ℂ ι) : EuclideanSpace ℂ ι :=
    (EuclideanSpace.equiv ι ℂ).symm (B *ᵥ v)
  have hy (i : ι) : y A₀ x i = y A (xk (f i)) i := by
    change (A₀ *ᵥ x) i = (A *ᵥ xk (f i)) i
    simp only [Matrix.mulVec, dotProduct]
    apply Finset.sum_congr rfl
    intro j _
    change (A i j - (if f i = f j then 0 else A i j)) * x j =
      A i j * (if f j = f i then x j else 0)
    by_cases hij : f i = f j
    · rw [if_pos hij, if_pos hij.symm, sub_zero]
    · rw [if_neg hij, if_neg (Ne.symm hij), sub_self, zero_mul, mul_zero]
  have hinput (k : κ) : ‖xk k‖ ^ 2 = ∑ i, if f i = k then ‖x i‖ ^ 2 else 0 := by
    rw [PiLp.norm_sq_eq_of_L2]
    apply Finset.sum_congr rfl
    intro i _
    change ‖(if f i = k then x i else 0 : ℂ)‖ ^ 2 = _
    by_cases hi : f i = k
    · rw [if_pos hi, if_pos hi]
    · rw [if_neg hi, if_neg hi, norm_zero, zero_pow two_ne_zero]
  have houtput (k : κ) :
      (∑ i, if f i = k then ‖y A₀ x i‖ ^ 2 else 0) ≤ ‖y A (xk k)‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    apply Finset.sum_le_sum
    intro i _
    by_cases hi : f i = k
    · rw [if_pos hi, hy i, hi]
    · rw [if_neg hi]
      exact sq_nonneg _
  change ‖y A₀ x‖ ≤ ‖A‖ * ‖x‖
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp
  calc
    ‖y A₀ x‖ ^ 2 = ∑ k ∈ s, ∑ i, if f i = k then ‖y A₀ x i‖ ^ 2 else 0 := by
      rw [PiLp.norm_sq_eq_of_L2]
      exact (hgroup _).symm
    _ ≤ ∑ k ∈ s, (‖A‖ * ‖xk k‖) ^ 2 := by
      apply Finset.sum_le_sum
      intro k _
      apply (houtput k).trans
      exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr
        (A.l2_opNorm_mulVec (xk k))
    _ = (‖A‖ * ‖x‖) ^ 2 := by
      simp only [mul_pow, ← Finset.mul_sum, hinput, hgroup]
      rw [PiLp.norm_sq_eq_of_L2]

private theorem exteriorComm_frobenius_le (A B : Matrix ι ι ℂ) :
    exteriorFrobenius (exteriorComm A B) ≤ 2 * ‖A‖ * exteriorFrobenius B := by
  change exteriorFrobenius (A * B + -(B * A)) ≤ _
  calc
    _ ≤ exteriorFrobenius (A * B) + exteriorFrobenius (-(B * A)) :=
      exteriorFrobenius_add _ _
    _ ≤ ‖A‖ * exteriorFrobenius B + exteriorFrobenius B * ‖A‖ := by
      rw [exteriorFrobenius_neg]
      exact add_le_add (exteriorFrobenius_mul_left _ _) (exteriorFrobenius_mul_right _ _)
    _ = _ := by ring

private theorem exteriorComm_frobenius_le_right (A B : Matrix ι ι ℂ) :
    exteriorFrobenius (exteriorComm A B) ≤ 2 * ‖B‖ * exteriorFrobenius A := by
  have h : exteriorComm A B = -exteriorComm B A := by
    unfold exteriorComm
    abel
  rw [h, exteriorFrobenius_neg]
  exact exteriorComm_frobenius_le B A

private theorem exterior_block_mul_zero (f : ι → κ) (A B : Matrix ι ι ℂ)
    (hA : ∀ i j, f i ≠ f j → A i j = 0) (hB : ∀ i j, f i ≠ f j → B i j = 0)
    (i j : ι) (hij : f i ≠ f j) : (A * B) i j = 0 := by
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro k _
  by_cases hik : f i = f k
  · rw [hB k j (fun h => hij (hik.trans h)), mul_zero]
  · rw [hA i k hik, zero_mul]

private theorem exterior_block_inverse_zero (f : ι → κ) (A : Matrix ι ι ℂ)
    (hdet : IsUnit A.det) (hA : ∀ i j, f i ≠ f j → A i j = 0)
    (i j : ι) (hij : f i ≠ f j) : A⁻¹ i j = 0 := by
  let p : ι → ℂ := fun k => if f i = f k then 1 else 0
  let P := diagonal p
  have hAP : A * P = P * A := by
    ext k l : 1
    change (A * diagonal p) k l = (diagonal p * A) k l
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    by_cases hkl : f k = f l
    · rw [show p l = p k by simp only [p, hkl], mul_comm]
    · rw [hA k l hkl, zero_mul, mul_zero]
  have hPi : P * A⁻¹ = A⁻¹ * P := calc
    _ = (A⁻¹ * (A * P)) * A⁻¹ := by rw [A.nonsing_inv_mul_cancel_left P hdet]
    _ = (A⁻¹ * (P * A)) * A⁻¹ := by rw [hAP]
    _ = _ := by rw [← Matrix.mul_assoc A⁻¹ P A, A.mul_nonsing_inv_cancel_right _ hdet]
  have hentry := congrArg (fun X : Matrix ι ι ℂ => X i j) hPi
  change (diagonal p * A⁻¹) i j = (A⁻¹ * diagonal p) i j at hentry
  simpa only [Matrix.diagonal_mul, Matrix.mul_diagonal, p, if_pos rfl, if_true, if_neg hij,
    one_mul, mul_zero] using hentry

private theorem exterior_block_remainder_zero [Nonempty ι] (f : ι → κ) (z : ℂ)
    (Y : Matrix ι ι ℂ) (hY : ‖Y‖ < ‖z‖)
    (hblock : ∀ i j, f i ≠ f j → Y i j = 0)
    (i j : ι) (hij : f i ≠ f j) : exteriorRemainder z Y i j = 0 := by
  let C := z • (1 : Matrix ι ι ℂ) + Y
  obtain ⟨hdet, _⟩ := exterior_resolvent_bound z Y hY
  have hC (k l : ι) (hkl : f k ≠ f l) : C k l = 0 := by
    have hne : k ≠ l := fun h => hkl (congrArg f h)
    simp only [C, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply_ne hne,
      hblock k l hkl, smul_zero, add_zero]
  exact exterior_block_mul_zero f (Y * Y) C⁻¹
    (exterior_block_mul_zero f Y Y hblock hblock)
    (exterior_block_inverse_zero f C hdet hC) i j hij

private theorem exterior_diag_gap_lower (f : ι → κ) (H : Matrix ι ι ℂ)
    (p : ι → ℝ) (g : ℝ) (hg : 0 ≤ g)
    (hgap : ∀ i j, f i ≠ f j → g ≤ |p j - p i|) :
    g * exteriorFrobenius (exteriorOffBlock f H) ≤
      exteriorFrobenius (exteriorComm (exteriorOffBlock f H) (diagonal fun i => (p i : ℂ))) := by
  let F := exteriorOffBlock f H
  let D := diagonal fun i => (p i : ℂ)
  have hentry (i j : ι) : exteriorComm F D i j = F i j * ((p j - p i : ℝ) : ℂ) := by
    simp only [exteriorComm, D, Matrix.sub_apply, Matrix.mul_diagonal, Matrix.diagonal_mul,
      Complex.ofReal_sub]
    ring
  change g * exteriorFrobenius F ≤ exteriorFrobenius (exteriorComm F D)
  apply (sq_le_sq₀ (mul_nonneg hg (exteriorFrobenius_nonneg _)) (exteriorFrobenius_nonneg _)).mp
  simp only [mul_pow, exteriorFrobenius_sq, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  rw [hentry, norm_mul, Complex.norm_real, mul_pow, mul_comm (g ^ 2)]
  by_cases h : f i = f j
  · simp only [F, exteriorOffBlock, h, if_true, norm_zero, zero_pow two_ne_zero, zero_mul, le_refl]
  · apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
    exact (sq_le_sq₀ hg (abs_nonneg _)).mpr (hgap i j h)

/-- A separated projected diagonal forces exact block preservation if the
stationary perturbation and its variation are small enough. -/
theorem exterior_offBlock_eq_zero (f : ι → κ) (H E E₀ : Matrix ι ι ℂ)
    (p : ι → ℝ) (g M K J : ℝ)
    (hgap : ∀ i j, f i ≠ f j → g ≤ |p j - p i|) (hg : 0 ≤ g)
    (hcomm : Commute H (diagonal (fun i => (p i : ℂ)) + E))
    (hE₀ : ∀ i j, f i ≠ f j → E₀ i j = 0)
    (hH : ‖H - exteriorOffBlock f H‖ ≤ M)
    (hE : ‖E‖ ≤ K)
    (hchange : exteriorFrobenius (E - E₀) ≤ J * exteriorFrobenius (exteriorOffBlock f H))
    (hsmall : 2 * K + 2 * M * J < g) :
    exteriorOffBlock f H = 0 := by
  let F := exteriorOffBlock f H
  let H₀ := H - F
  let D := diagonal fun i => (p i : ℂ)
  let G := exteriorComm F E + exteriorComm H₀ (E - E₀)
  have hH₀ (i j : ι) (hij : f i ≠ f j) : H₀ i j = 0 := by
    simp only [H₀, F, exteriorOffBlock, Matrix.sub_apply, hij, if_false, sub_self]
  have hD (i j : ι) (hij : f i ≠ f j) : D i j = 0 := by
    exact Matrix.diagonal_apply_ne _ (fun hij' => hij (congrArg f hij'))
  have hdecomp :
      exteriorComm H (D + E) =
        exteriorComm F D + G + exteriorComm H₀ D + exteriorComm H₀ E₀ := by
    have he : H = H₀ + F := by dsimp only [H₀]; abel
    conv_lhs => rw [he]
    simp only [exteriorComm, G, Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul]
    abel
  have hzero : exteriorComm H (D + E) = 0 := sub_eq_zero.mpr hcomm.eq
  have heq : exteriorComm F D = -exteriorOffBlock f G := by
    ext i j : 1
    by_cases hij : f i = f j
    · simp only [exteriorComm, Matrix.sub_apply, D, Matrix.mul_diagonal, Matrix.diagonal_mul,
        exteriorOffBlock, F, hij, if_true, mul_zero, zero_mul, sub_zero, Matrix.neg_apply, neg_zero]
    · have hblock (B : Matrix ι ι ℂ) (hB : ∀ i j, f i ≠ f j → B i j = 0) :
          exteriorComm H₀ B i j = 0 := by
        change (H₀ * B) i j - (B * H₀) i j = 0
        rw [exterior_block_mul_zero f H₀ B hH₀ hB i j hij,
          exterior_block_mul_zero f B H₀ hB hH₀ i j hij, sub_self]
      have he := congrArg (fun A : Matrix ι ι ℂ => A i j) (hdecomp.symm.trans hzero)
      simp only [Matrix.add_apply, Matrix.zero_apply, hblock D hD, hblock E₀ hE₀, add_zero] at he
      simpa only [Matrix.neg_apply, exteriorOffBlock, hij, if_false] using eq_neg_of_add_eq_zero_left he
  have hFn := exteriorFrobenius_nonneg F
  have hMn : 0 ≤ M := (norm_nonneg H₀).trans hH
  have hbound : g * exteriorFrobenius F ≤ (2 * K + 2 * M * J) * exteriorFrobenius F := calc
    _ ≤ exteriorFrobenius (exteriorComm F D) := exterior_diag_gap_lower f H p g hg hgap
    _ = exteriorFrobenius (exteriorOffBlock f G) := by rw [heq, exteriorFrobenius_neg]
    _ ≤ exteriorFrobenius G := exteriorOffBlock_frobenius f G
    _ ≤ exteriorFrobenius (exteriorComm F E) + exteriorFrobenius (exteriorComm H₀ (E - E₀)) :=
      exteriorFrobenius_add _ _
    _ ≤ 2 * K * exteriorFrobenius F + 2 * M * (J * exteriorFrobenius F) := by
      apply add_le_add
      · exact (exteriorComm_frobenius_le_right _ _).trans
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hE (by positivity)) hFn)
      · apply (exteriorComm_frobenius_le _ _).trans
        apply mul_le_mul (mul_le_mul_of_nonneg_left hH (by positivity)) hchange
          (exteriorFrobenius_nonneg _) (mul_nonneg (by positivity) hMn)
    _ = _ := by ring
  have hFzero : exteriorFrobenius F = 0 := by
    by_contra hne
    exact (not_lt_of_ge hbound) (mul_lt_mul_of_pos_right hsmall (lt_of_le_of_ne hFn (Ne.symm hne)))
  exact (@norm_eq_zero _
    (@NormedAddCommGroup.toNormedAddGroup _ Matrix.frobeniusNormedAddCommGroup) F).mp hFzero

/-- At an exterior support maximum, each partition separated in the normalized
projected direction is preserved exactly when the exterior bound holds. -/
theorem exterior_support_maximum_respects_blocks [Nonempty ι]
    (z η : ℂ) (b : ι → ℂ) (H : Matrix ι ι ℂ) (M L g : ℝ)
    (hH : H.IsHermitian) (hη : η ≠ 0) (hM : ‖H‖ ≤ M)
    (hL : M + ‖diagonal b‖ ≤ L) (hz : L < ‖z‖) (hg : 0 ≤ g)
    (hsmall : let d := ‖z‖ - L
      2 * (L ^ 2 / d) + 2 * M * (2 * L / d + L ^ 2 / d ^ 2) < g)
    (hmax : ∀ V : Matrix ι ι ℂ, IsUnitary V →
      (η * ((z • (1 : Matrix ι ι ℂ) + diagonal b) + V * H * Vᴴ).det).re ≤
        (η * ((z • (1 : Matrix ι ι ℂ) + diagonal b) + H).det).re) :
    ∃ u : ℂ, ‖u‖ = 1 ∧ ∀ f : ι → κ,
      (∀ i j, f i ≠ f j → g ≤ |(u * b j).re - (u * b i).re|) →
      exteriorOffBlock f H = 0 := by
  let Y := H + diagonal b
  let C := z • (1 : Matrix ι ι ℂ) + Y
  let v := η * C.det / z ^ 2
  let c : ℝ := ‖v‖⁻¹
  let η' : ℂ := (c : ℂ) * η
  let u : ℂ := η' * C.det / z ^ 2
  let d := ‖z‖ - L
  have hY : ‖Y‖ ≤ L := (norm_add_le _ _).trans ((add_le_add_right hM _).trans hL)
  have hz0 : z ≠ 0 := norm_pos_iff.mp ((norm_nonneg Y).trans_lt (hY.trans_lt hz))
  obtain ⟨hC, _⟩ := exterior_resolvent_bound z Y (hY.trans_lt hz)
  have hv : v ≠ 0 := div_ne_zero (mul_ne_zero hη hC.ne_zero) (pow_ne_zero 2 hz0)
  have hcn : 0 ≤ c := (inv_pos.mpr (norm_pos_iff.mpr hv)).le
  have hnorm : ‖u‖ = 1 := by
    have he : u = (c : ℂ) * v := by
      dsimp only [u, η', v]
      rw [mul_assoc, mul_div_assoc]
    rw [he, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hcn]
    exact inv_mul_cancel₀ (norm_pos_iff.mpr hv).ne'
  have hmax' (V : Matrix ι ι ℂ) (hV : IsUnitary V) :
      (η' * ((z • (1 : Matrix ι ι ℂ) + diagonal b) + V * H * Vᴴ).det).re ≤
        (η' * ((z • (1 : Matrix ι ι ℂ) + diagonal b) + H).det).re := by
    simp only [η', mul_assoc (c : ℂ), Complex.re_ofReal_mul]
    exact mul_le_mul_of_nonneg_left (hmax V hV) hcn
  have hstation := exterior_stationary_commute z η' b H hH hz0 hC hmax'
  change Commute H (diagonal (fun i => ((u * b i).re : ℂ)) -
    exteriorHermitianPart (u • exteriorRemainder z Y)) at hstation
  refine ⟨u, hnorm, ?_⟩
  intro f hgap
  let H₀ := H - exteriorOffBlock f H
  let Y₀ := H₀ + diagonal b
  let E := exteriorHermitianPart ((-u) • exteriorRemainder z Y)
  let E₀ := exteriorHermitianPart ((-u) • exteriorRemainder z Y₀)
  let p (i : ι) := (u * b i).re
  have hH₀ : ‖H₀‖ ≤ M := (exterior_block_compression_opNorm f H).trans hM
  have hY₀ : ‖Y₀‖ ≤ L := (norm_add_le _ _).trans ((add_le_add_right hH₀ _).trans hL)
  have hstation' : Commute H (diagonal (fun i => (p i : ℂ)) + E) := by
    simpa only [p, E, neg_smul, exteriorHermitianPart_neg, ← sub_eq_add_neg] using hstation
  have hY₀block (i j : ι) (hij : f i ≠ f j) : Y₀ i j = 0 := by
    have hne : i ≠ j := fun h => hij (congrArg f h)
    simp only [Y₀, H₀, Matrix.add_apply, Matrix.sub_apply, exteriorOffBlock, if_neg hij,
      Matrix.diagonal_apply_ne _ hne, sub_self, add_zero]
  have hE₀ (i j : ι) (hij : f i ≠ f j) : E₀ i j = 0 := by
    have hR := exterior_block_remainder_zero f z Y₀ (hY₀.trans_lt hz) hY₀block
    simp only [E₀, exteriorHermitianPart, Matrix.smul_apply, Matrix.add_apply,
      Matrix.conjTranspose_apply, hR i j hij, hR j i (Ne.symm hij), smul_zero, star_zero, add_zero]
  have hE : ‖E‖ ≤ L ^ 2 / d := calc
    _ ≤ ‖(-u) • exteriorRemainder z Y‖ := exteriorHermitianPart_opNorm _
    _ = ‖exteriorRemainder z Y‖ := by rw [norm_smul, norm_neg, hnorm, one_mul]
    _ ≤ _ := exterior_remainder_bound z Y L hY hz
  have hdiff : Y - Y₀ = exteriorOffBlock f H := by
    dsimp only [Y, Y₀, H₀]
    abel
  have hchange : exteriorFrobenius (E - E₀) ≤
      (2 * L / d + L ^ 2 / d ^ 2) * exteriorFrobenius (exteriorOffBlock f H) := by
    have he : E - E₀ = exteriorHermitianPart
        ((-u) • (exteriorRemainder z Y - exteriorRemainder z Y₀)) := by
      rw [smul_sub, exteriorHermitianPart_sub]
    rw [he]
    calc
      _ ≤ exteriorFrobenius ((-u) • (exteriorRemainder z Y - exteriorRemainder z Y₀)) :=
        exteriorHermitianPart_frobenius _
      _ = exteriorFrobenius (exteriorRemainder z Y - exteriorRemainder z Y₀) := by
        rw [exteriorFrobenius_smul, norm_neg, hnorm, one_mul]
      _ ≤ _ := by
        simpa only [hdiff] using exterior_remainder_frobenius_lipschitz z Y Y₀ L hY hY₀ hz
  exact exterior_offBlock_eq_zero f H E E₀ p g M (L ^ 2 / d)
    (2 * L / d + L ^ 2 / d ^ 2) hgap hg hstation' hE₀ hH₀ hE hchange hsmall

end Blocks

section ProjectedBlocks

variable {ι : Type*}

/-- Signed double area of the triangle with the given complex vertices. -/
def exteriorTriangleCross (x y z : ℂ) : ℝ := ((y - x) * star (z - x)).im

private theorem exterior_near_triple_on_line (u : ℂ) (hu : ‖u‖ = 1)
    (g : ℝ) (x y z : ℂ) (hxy : x ≠ y)
    (hy : |(u * y).re - (u * x).re| < g)
    (hz : |(u * z).re - (u * x).re| < g)
    (hcross : exteriorTriangleCross x y z ≠ 0 →
      g * (‖y - x‖ + ‖z - x‖) ≤ |exteriorTriangleCross x y z|) :
    ∃ t : ℝ, z = x + (t : ℂ) * (y - x) := by
  let A := u * (y - x)
  let B := u * (z - x)
  have hA : |A.re| < g := by simpa only [A, mul_sub, Complex.sub_re] using hy
  have hB : |B.re| < g := by simpa only [B, mul_sub, Complex.sub_re] using hz
  have hg : 0 ≤ g := (abs_nonneg _).trans hA.le
  have hyx : y - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hxy)
  have hu₀ : u ≠ 0 := by
    intro he
    rw [he, norm_zero] at hu
    exact zero_ne_one hu
  have hAn : 0 < ‖A‖ := norm_pos_iff.mpr (mul_ne_zero hu₀ hyx)
  have hphase : u * star u = 1 := by
    rw [Complex.star_def, Complex.mul_conj, ← Complex.sq_norm, hu, one_pow, Complex.ofReal_one]
  have hrotation : A * star B = (y - x) * star (z - x) := by
    dsimp only [A, B]
    rw [StarMul.star_mul]
    calc
      _ = (u * star u) * ((y - x) * star (z - x)) := by ring
      _ = _ := by rw [hphase, one_mul]
  have himag : (A * star B).im = A.im * B.re - A.re * B.im := by
    simp only [Complex.mul_im, Complex.star_def, Complex.conj_re, Complex.conj_im]
    ring
  have hnormA : ‖A‖ = ‖y - x‖ := by rw [show A = _ from rfl, norm_mul, hu, one_mul]
  have hnormB : ‖B‖ = ‖z - x‖ := by rw [show B = _ from rfl, norm_mul, hu, one_mul]
  have hfirst : |A.im| * |B.re| < ‖A‖ * g :=
    (mul_le_mul_of_nonneg_right (Complex.abs_im_le_norm A) (abs_nonneg _)).trans_lt
      (mul_lt_mul_of_pos_left hB hAn)
  have hsecond : |A.re| * |B.im| ≤ g * ‖B‖ :=
    mul_le_mul hA.le (Complex.abs_im_le_norm B) (abs_nonneg _) hg
  have hstrict : |exteriorTriangleCross x y z| < g * (‖y - x‖ + ‖z - x‖) := calc
    _ = |A.im * B.re - A.re * B.im| := by rw [exteriorTriangleCross, ← hrotation, himag]
    _ ≤ |A.im| * |B.re| + |A.re| * |B.im| := by
      simpa only [abs_mul] using abs_sub (A.im * B.re) (A.re * B.im)
    _ < ‖A‖ * g + g * ‖B‖ := add_lt_add_of_lt_of_le hfirst hsecond
    _ = _ := by rw [hnormA, hnormB]; ring
  have hzero : exteriorTriangleCross x y z = 0 := by
    by_cases hne : exteriorTriangleCross x y z = 0
    · exact hne
    · exact ((not_lt_of_ge (hcross hne)) hstrict).elim
  have hcoord : ((z - x) / (y - x)).im = 0 := by
    rw [Complex.div_im, ← sub_div]
    have he : (z - x).im * (y - x).re - (z - x).re * (y - x).im = 0 := by
      simp only [exteriorTriangleCross, Complex.mul_im, Complex.star_def,
        Complex.conj_re, Complex.conj_im] at hzero
      linarith only [hzero]
    rw [he, zero_div]
  have hreal : ((((z - x) / (y - x)).re : ℝ) : ℂ) = (z - x) / (y - x) :=
    Complex.ext (Complex.ofReal_re _) ((Complex.ofReal_im _).trans hcoord.symm)
  refine ⟨((z - x) / (y - x)).re, ?_⟩
  rw [hreal, div_mul_cancel₀ _ hyx]
  abel

/-- Join spectral labels whose projections differ by less than the gap.
If the triangle bound holds, each connected group lies on one affine line. -/
theorem exterior_projected_affine_partition (b : ι → ℂ) (u : ℂ) (hu : ‖u‖ = 1) (g : ℝ)
    (harea : ∀ i j k, exteriorTriangleCross (b i) (b j) (b k) ≠ 0 →
      g * (‖b j - b i‖ + ‖b k - b i‖) ≤ |exteriorTriangleCross (b i) (b j) (b k)|) :
    ∃ f : ι → ι,
      (∀ i j, f i ≠ f j → g ≤ |(u * b j).re - (u * b i).re|) ∧
      (∀ i, ∃ s q : ℂ, ∀ j, f j = f i → ∃ t : ℝ, b j = s + (t : ℂ) * q) := by
  let near (i j : ι) : Prop := |(u * b j).re - (u * b i).re| < g
  let reach := Relation.ReflTransGen near
  have hsym : Symmetric near := by
    intro i j h
    change |(u * b i).re - (u * b j).re| < g
    rw [abs_sub_comm]
    exact h
  let classes : Setoid ι := ⟨reach, ⟨fun _ => Relation.ReflTransGen.refl,
    fun h => Relation.ReflTransGen.symmetric hsym h, fun h₁ h₂ => h₁.trans h₂⟩⟩
  let f (i : ι) : ι := (Quotient.mk classes i).out
  have hclass (i j : ι) : f i = f j ↔ reach i j := by
    constructor
    · intro h
      apply Quotient.exact (s := classes)
      calc
        Quotient.mk classes i = Quotient.mk classes (f i) := (Quotient.out_eq _).symm
        _ = Quotient.mk classes (f j) := congrArg (Quotient.mk classes) h
        _ = Quotient.mk classes j := Quotient.out_eq _
    · intro h
      exact congrArg Quotient.out (Quotient.sound (s := classes) h)
  have htriple (i j k : ι) (hij : b i ≠ b j) (hnearj : near i j) (hneark : near i k) :
      ∃ t : ℝ, b k = b i + (t : ℂ) * (b j - b i) :=
    exterior_near_triple_on_line u hu g (b i) (b j) (b k) hij hnearj hneark (harea i j k)
  refine ⟨f, ?_, ?_⟩
  · intro i j hij
    exact le_of_not_gt (fun h => hij ((hclass i j).mpr (Relation.ReflTransGen.single h)))
  intro i
  by_cases hpair : ∃ j, b i ≠ b j ∧ near i j
  · obtain ⟨j, hj, hnear⟩ := hpair
    let q := b j - b i
    have hinv (k : ι) (hk : reach i k) :
        (∃ t : ℝ, b k = b i + (t : ℂ) * q) ∧
        ∃ l, b k ≠ b l ∧ near k l ∧ ∃ s : ℝ, b l = b i + (s : ℂ) * q := by
      induction hk with
      | refl =>
        exact ⟨⟨0, by simp only [Complex.ofReal_zero, zero_mul, add_zero]⟩,
          ⟨j, hj, hnear, ⟨1, by simp only [Complex.ofReal_one, one_mul, q]; abel⟩⟩⟩
      | @tail k l _ hkl ih =>
        obtain ⟨⟨a, ha⟩, m, hkm, hnearM, ⟨c, hc⟩⟩ := ih
        obtain ⟨d, hd⟩ := htriple k m l hkm hnearM hkl
        have hl : ∃ t : ℝ, b l = b i + (t : ℂ) * q := by
          refine ⟨a + d * (c - a), ?_⟩
          rw [hd, ha, hc, Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_sub]
          ring
        refine ⟨hl, ?_⟩
        by_cases he : b k = b l
        · exact ⟨m, by rw [← he]; exact hkm,
            by simpa only [near, ← he] using hnearM, ⟨c, hc⟩⟩
        · exact ⟨k, Ne.symm he, hsym hkl, ⟨a, ha⟩⟩
    exact ⟨b i, q, fun k hk => (hinv k ((hclass i k).mp hk.symm)).1⟩
  · have hconst (k : ι) (hk : reach i k) : b k = b i := by
      induction hk with
      | refl => rfl
      | @tail k l _ hkl ih =>
        by_cases hne : b l = b i
        · exact hne
        · exact (hpair ⟨l, Ne.symm hne, by simpa only [near, ih] using hkl⟩).elim
    refine ⟨b i, 0, fun k hk => ⟨0, ?_⟩⟩
    simpa only [mul_zero, add_zero] using hconst k ((hclass i k).mp hk.symm)

private theorem exterior_triangle_side_sum_pos (x y z : ℂ)
    (h : exteriorTriangleCross x y z ≠ 0) : 0 < ‖y - x‖ + ‖z - x‖ := by
  have hne : y - x ≠ 0 := by
    intro he
    apply h
    simp only [exteriorTriangleCross, he, zero_mul, Complex.zero_im]
  exact add_pos_of_pos_of_nonneg (norm_pos_iff.mpr hne) (norm_nonneg _)

/-- A single positive gap works for all projected directions of any finite spectrum. -/
theorem exterior_exists_positive_triangle_gap [Fintype ι] (b : ι → ℂ) :
    ∃ g : ℝ, 0 < g ∧ ∀ i j k, exteriorTriangleCross (b i) (b j) (b k) ≠ 0 →
      g * (‖b j - b i‖ + ‖b k - b i‖) ≤ |exteriorTriangleCross (b i) (b j) (b k)| := by
  classical
  let c (p : ι × ι × ι) := exteriorTriangleCross (b p.1) (b p.2.1) (b p.2.2)
  let r (p : ι × ι × ι) := if c p = 0 then 1 else
    |c p| / (‖b p.2.1 - b p.1‖ + ‖b p.2.2 - b p.1‖)
  let s := insert (1 : ℝ) (Finset.univ.image r)
  have hs : s.Nonempty := ⟨1, Finset.mem_insert_self _ _⟩
  let g := s.min' hs
  have hr (p : ι × ι × ι) : 0 < r p := by
    by_cases h : c p = 0
    · simp only [r, if_pos h, zero_lt_one]
    · rw [show r p = _ from if_neg h]
      exact div_pos (abs_pos.mpr h) (exterior_triangle_side_sum_pos _ _ _ h)
  have hg : 0 < g := by
    have hm : g ∈ s := Finset.min'_mem s hs
    rcases Finset.mem_insert.mp hm with h | h
    · exact h.symm ▸ zero_lt_one
    · obtain ⟨p, _, hp⟩ := Finset.mem_image.mp h
      exact hp ▸ hr p
  refine ⟨g, hg, ?_⟩
  intro i j k hijk
  let p : ι × ι × ι := (i, j, k)
  have hp : r p ∈ s := Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨p, Finset.mem_univ _, rfl⟩)
  have hle : g ≤ r p := Finset.min'_le s _ hp
  have hratio : r p = |c p| / (‖b j - b i‖ + ‖b k - b i‖) := if_neg hijk
  rw [hratio] at hle
  exact (le_div_iff₀ (exterior_triangle_side_sum_pos _ _ _ hijk)).mp hle

end ProjectedBlocks

/-- In every nonzero support direction the exterior bound provides a partition
that the maximizer preserves and on which the partner spectrum is collinear. -/
theorem exterior_support_maximum_has_affine_blocks [Nonempty ι]
    (z η : ℂ) (b : ι → ℂ) (H : Matrix ι ι ℂ) (M L g : ℝ)
    (hH : H.IsHermitian) (hη : η ≠ 0) (hM : ‖H‖ ≤ M)
    (hL : M + ‖diagonal b‖ ≤ L) (hz : L < ‖z‖) (hg : 0 ≤ g)
    (hsmall : let d := ‖z‖ - L
      2 * (L ^ 2 / d) + 2 * M * (2 * L / d + L ^ 2 / d ^ 2) < g)
    (harea : ∀ i j k, exteriorTriangleCross (b i) (b j) (b k) ≠ 0 →
      g * (‖b j - b i‖ + ‖b k - b i‖) ≤ |exteriorTriangleCross (b i) (b j) (b k)|)
    (hmax : ∀ V : Matrix ι ι ℂ, IsUnitary V →
      (η * ((z • (1 : Matrix ι ι ℂ) + diagonal b) + V * H * Vᴴ).det).re ≤
        (η * ((z • (1 : Matrix ι ι ℂ) + diagonal b) + H).det).re) :
    ∃ f : ι → ι, exteriorOffBlock f H = 0 ∧
      ∀ i, ∃ s q : ℂ, ∀ j, f j = f i → ∃ t : ℝ, b j = s + (t : ℂ) * q := by
  obtain ⟨u, hu, hblocks⟩ := exterior_support_maximum_respects_blocks (κ := ι)
    z η b H M L g hH hη hM hL hz hg hsmall hmax
  obtain ⟨f, hgap, hline⟩ := exterior_projected_affine_partition b u hu g harea
  exact ⟨f, hblocks f hgap, hline⟩

private theorem exterior_holds_of_affine_blocks (a : ι → ℝ) (β : ι → ℂ)
    (V : Matrix ι ι ℂ) (hV : IsUnitary V) (f : ι → ι)
    (hblock : exteriorOffBlock f (V * diagonal (fun i => (a i : ℂ)) * Vᴴ) = 0)
    (hline : ∀ i, ∃ s q : ℂ, ∀ j, f j = f i → ∃ t : ℝ, β j = s + (t : ℂ) * q) :
    Holds β (fun i => (a i : ℂ)) V := by
  classical
  let label := Fintype.equivFin ι
  let classify := label ∘ f
  let κ (k : Fin (Fintype.card ι)) := {i : ι // classify i = k}
  let m (k : Fin (Fintype.card ι)) := Fintype.card (κ k)
  let ef (k : Fin (Fintype.card ι)) : Fin (m k) ≃ κ k := (Fintype.equivFin _).symm
  let e : (Σ k, Fin (m k)) ≃ ι := (Equiv.sigmaCongrRight ef).trans (Equiv.sigmaFiberEquiv classify)
  have he (k : Fin (Fintype.card ι)) (i : Fin (m k)) : label (f (e ⟨k, i⟩)) = k :=
    (ef k i).property
  let A (i : ι) : ℂ := a i
  let H := V * diagonal A * Vᴴ
  have hH : H.IsHermitian := Matrix.isHermitian_mul_mul_conjTranspose V
    (Matrix.isHermitian_diagonal_iff.mpr fun i => by
      simp only [A, isSelfAdjoint_iff, Complex.star_def, Complex.conj_ofReal])
  let Hk (k : Fin (Fintype.card ι)) : Matrix (Fin (m k)) (Fin (m k)) ℂ :=
    H.submatrix (fun i => e ⟨k, i⟩) (fun i => e ⟨k, i⟩)
  have hHk (k : Fin (Fintype.card ι)) : (Hk k).IsHermitian := by
    apply Matrix.IsHermitian.submatrix
    exact hH
  let eigenvalues (k : Fin (Fintype.card ι)) (i : Fin (m k)) : ℝ := (hHk k).eigenvalues i
  let Qk (k : Fin (Fintype.card ι)) : Matrix (Fin (m k)) (Fin (m k)) ℂ := (hHk k).eigenvectorUnitary
  have hQk (k : Fin (Fintype.card ι)) : IsUnitary (Qk k) :=
    ⟨Matrix.mem_unitaryGroup_iff.mp (hHk k).eigenvectorUnitary.2,
      Matrix.mem_unitaryGroup_iff'.mp (hHk k).eigenvectorUnitary.2⟩
  have hdiag (k : Fin (Fintype.card ι)) :
      Hk k = Qk k * diagonal (fun i => (eigenvalues k i : ℂ)) * (Qk k)ᴴ := by
    simpa only [Qk, eigenvalues, Function.comp_apply, Matrix.star_eq_conjTranspose] using
      (hHk k).spectral_theorem
  have hsplit : H.submatrix e e = Matrix.blockDiagonal' Hk := by
    ext i j : 1
    rcases i with ⟨k, i⟩
    rcases j with ⟨l, j⟩
    by_cases hkl : k = l
    · subst l
      exact (Matrix.blockDiagonal'_apply_eq Hk k i j).symm
    · have hne : f (e ⟨k, i⟩) ≠ f (e ⟨l, j⟩) := by
        intro hh
        exact hkl ((he k i).symm.trans ((congrArg label hh).trans (he l j)))
      have hzero := congrArg (fun X : Matrix ι ι ℂ => X (e ⟨k, i⟩) (e ⟨l, j⟩)) hblock
      have hi : H (e ⟨k, i⟩) (e ⟨l, j⟩) = 0 := by
        simpa only [exteriorOffBlock, if_neg hne, Matrix.zero_apply] using hzero
      exact hi.trans (Matrix.blockDiagonal'_apply_ne Hk i j hkl).symm
  let Q := Matrix.blockDiagonal' Qk
  let A' (i : Σ k, Fin (m k)) : ℂ := eigenvalues i.1 i.2
  let B' (i : Σ k, Fin (m k)) : ℂ := β (e i)
  have hQ : IsUnitary Q := by
    constructor
    · simp only [Q, Matrix.blockDiagonal'_conjTranspose, ← Matrix.blockDiagonal'_mul,
        ← Matrix.blockDiagonal'_one]
      exact congrArg Matrix.blockDiagonal' (funext fun k => (hQk k).1)
    · simp only [Q, Matrix.blockDiagonal'_conjTranspose, ← Matrix.blockDiagonal'_mul,
        ← Matrix.blockDiagonal'_one]
      exact congrArg Matrix.blockDiagonal' (funext fun k => (hQk k).2)
  have hHs : H.submatrix e e = Q * diagonal A' * Qᴴ := by
    rw [hsplit, ← Matrix.blockDiagonal'_diagonal (fun k i => (eigenvalues k i : ℂ))]
    simp only [Q, Matrix.blockDiagonal'_conjTranspose, ← Matrix.blockDiagonal'_mul]
    exact congrArg Matrix.blockDiagonal' (funext hdiag)
  have hlocal (k : Fin (Fintype.card ι)) :
      Holds (fun i => B' ⟨k, i⟩) (fun i => (eigenvalues k i : ℂ)) (Qk k) := by
    by_cases hn : Nonempty (Fin (m k))
    · let i₀ := Classical.choice hn
      obtain ⟨s, q, hs⟩ := hline (e ⟨k, i₀⟩)
      have hcoords (i : Fin (m k)) : ∃ t : ℝ, B' ⟨k, i⟩ = q * (t : ℂ) + s := by
        obtain ⟨t, ht⟩ := hs (e ⟨k, i⟩) (label.injective ((he k i).trans (he k i₀).symm))
        refine ⟨t, ?_⟩
        change β (e ⟨k, i⟩) = _
        rw [ht, add_comm s, mul_comm (t : ℂ) q]
      choose t ht using hcoords
      have hB : (fun i => B' ⟨k, i⟩) = fun i => q * (t i : ℂ) + s := funext ht
      rw [hB]
      simpa only [one_mul, add_zero] using
        holds_of_affine_spectral_lines t (eigenvalues k) q 1 s 0 (Qk k) (hQk k)
    · letI : IsEmpty (Fin (m k)) := ⟨fun i => hn ⟨i⟩⟩
      exact conjecture_of_subsingleton _ _ _ (hQk k)
  have hholds : Holds B' A' Q := holds_of_finite_paired_blocks m (Equiv.refl _) (Equiv.refl _)
    B' A' Q Qk rfl hlocal
  apply (holds_reindex_iff e e β A V).mp
  let V' := V.submatrix e e
  have hV' : IsUnitary V' := unitary_reindex e e hV
  have hlo : V' * diagonal (A ∘ e) * (V')ᴴ = Q * diagonal A' * Qᴴ := by
    have hleft : H.submatrix e e = V' * diagonal (A ∘ e) * (V')ᴴ := by
      simp only [H, ← Matrix.submatrix_mul_equiv _ _ e e e, Matrix.submatrix_diagonal_equiv,
        Matrix.conjTranspose_submatrix, V']
    exact hleft.symm.trans hHs
  have hb : diagonal (β ∘ e) = (1 : Matrix (Σ k, Fin (m k)) (Σ k, Fin (m k)) ℂ) *
      diagonal B' * (1 : Matrix (Σ k, Fin (m k)) (Σ k, Fin (m k)) ℂ)ᴴ := by
    change diagonal B' = 1 * diagonal B' * (1 : Matrix (Σ k, Fin (m k)) (Σ k, Fin (m k)) ℂ)ᴴ
    rw [Matrix.one_mul, Matrix.conjTranspose_one, Matrix.mul_one]
  apply (holds_iff_relative_to_diagonalizations (β ∘ e) (A ∘ e) B' A'
    hV' isUnitary_one hQ hb hlo).mpr
  simpa only [Matrix.conjTranspose_one, Matrix.one_mul] using hholds

/-- The exterior support inequality implies determinant inclusion for a real
spectrum and any finite partner spectrum under the triangle gap bound. -/
theorem holds_of_exterior_scalar_shift [Nonempty ι] (a : ι → ℝ) (b : ι → ℂ)
    (z : ℂ) (M L g : ℝ) (hM : ‖diagonal (fun i => (a i : ℂ))‖ ≤ M)
    (hL : M + ‖diagonal b‖ ≤ L) (hz : L < ‖z‖) (hg : 0 ≤ g)
    (hsmall : let d := ‖z‖ - L
      2 * (L ^ 2 / d) + 2 * M * (2 * L / d + L ^ 2 / d ^ 2) < g)
    (harea : ∀ i j k, exteriorTriangleCross (b i) (b j) (b k) ≠ 0 →
      g * (‖b j - b i‖ + ‖b k - b i‖) ≤ |exteriorTriangleCross (b i) (b j) (b k)|)
    (U : Matrix ι ι ℂ) (hU : IsUnitary U) :
    Holds (fun i => (a i : ℂ)) (fun i => z + b i) U := by
  let A (i : ι) : ℂ := a i
  let β (i : ι) : ℂ := z + b i
  apply (holds_swap_iff A β hU).mp
  have hU' : IsUnitary Uᴴ := ⟨by simpa only [Matrix.conjTranspose_conjTranspose] using hU.2,
    by simpa only [Matrix.conjTranspose_conjTranspose] using hU.1⟩
  apply (holds_iff_directional β A Uᴴ).mpr
  intro η
  by_cases hη : η = 0
  · exact ⟨1, by simp only [hη, zero_mul, le_refl]⟩
  obtain ⟨V, hV, hmax⟩ := exists_support_maximizer β A η
  let H := V * diagonal A * Vᴴ
  have hB : z • (1 : Matrix ι ι ℂ) + diagonal b = diagonal β := by
    calc
      _ = diagonal (fun _ : ι => z) + diagonal b := by rw [Matrix.smul_one_eq_diagonal]
      _ = _ := Matrix.diagonal_add (fun _ => z) b
  have hH : H.IsHermitian := Matrix.isHermitian_mul_mul_conjTranspose V
    (Matrix.isHermitian_diagonal_iff.mpr fun i => by
      simp only [A, isSelfAdjoint_iff, Complex.star_def, Complex.conj_ofReal])
  have hVn : ‖V‖ = 1 := by
    apply (sq_eq_sq₀ (norm_nonneg V) zero_le_one).mp
    rw [pow_two, ← Matrix.l2_opNorm_conjTranspose_mul_self, hV.2, norm_one, one_pow]
  have hHn : ‖H‖ ≤ M := calc
    _ ≤ ‖V * diagonal A‖ * ‖Vᴴ‖ := norm_mul_le _ _
    _ = ‖V * diagonal A‖ := by rw [Matrix.l2_opNorm_conjTranspose, hVn, mul_one]
    _ ≤ ‖V‖ * ‖diagonal A‖ := norm_mul_le _ _
    _ ≤ M := by rw [hVn, one_mul]; exact hM
  have hmaxH (X : Matrix ι ι ℂ) (hX : IsUnitary X) :
      (η * ((z • (1 : Matrix ι ι ℂ) + diagonal b) + X * H * Xᴴ).det).re ≤
        (η * ((z • (1 : Matrix ι ι ℂ) + diagonal b) + H).det).re := by
    have hX' : IsUnitary Xᴴ := ⟨by simpa only [Matrix.conjTranspose_conjTranspose] using hX.2,
      by simpa only [Matrix.conjTranspose_conjTranspose] using hX.1⟩
    have hXV : IsUnitary (X * V) := by
      simpa only [Matrix.conjTranspose_conjTranspose] using relative_unitary Xᴴ V hX' hV
    simpa only [hB, determinantValue, H, Matrix.conjTranspose_mul, Matrix.mul_assoc] using hmax (X * V) hXV
  obtain ⟨f, hblock, hline⟩ := exterior_support_maximum_has_affine_blocks
    z η b H M L g hH hη hHn hL hz hg hsmall harea hmaxH
  have hlineβ (i : ι) : ∃ s q : ℂ, ∀ j, f j = f i → ∃ t : ℝ, β j = s + (t : ℂ) * q := by
    obtain ⟨s, q, hsq⟩ := hline i
    refine ⟨z + s, q, fun j hj => ?_⟩
    obtain ⟨t, ht⟩ := hsq j hj
    exact ⟨t, by simp only [β, ht, add_assoc]⟩
  have hhold := exterior_holds_of_affine_blocks a β V hV f hblock hlineβ
  obtain ⟨σ, hσ⟩ := (holds_iff_directional β A V).mp hhold η
  exact ⟨σ, (hmax Uᴴ hU').trans hσ⟩

/-- Half of a lower bound on the least altitude of each noncollinear
triangle is a valid projected gap. -/
theorem exterior_triangle_gap_of_altitudes (b : ι → ℂ) (w : ℝ) (hw : 0 ≤ w)
    (hAltitude : ∀ i j k, exteriorTriangleCross (b i) (b j) (b k) ≠ 0 →
      w * max ‖b j - b i‖ (max ‖b k - b i‖ ‖b k - b j‖) ≤
        |exteriorTriangleCross (b i) (b j) (b k)|) :
    ∀ i j k, exteriorTriangleCross (b i) (b j) (b k) ≠ 0 →
      (w / 2) * (‖b j - b i‖ + ‖b k - b i‖) ≤
        |exteriorTriangleCross (b i) (b j) (b k)| := by
  intro i j k hijk
  let m := max ‖b j - b i‖ (max ‖b k - b i‖ ‖b k - b j‖)
  have hj : w * ‖b j - b i‖ ≤ w * m := mul_le_mul_of_nonneg_left (le_max_left _ _) hw
  have hk : w * ‖b k - b i‖ ≤ w * m :=
    mul_le_mul_of_nonneg_left ((le_max_left _ _).trans (le_max_right _ _)) hw
  calc
    _ ≤ w * m := by nlinarith only [hj, hk]
    _ ≤ _ := hAltitude i j k hijk

/-- The explicit radius (2L+8L^2/g) implies the exterior support inequality. -/
theorem exterior_bound_of_simple_cutoff (M L g r : ℝ)
    (hM : 0 ≤ M) (hML : M ≤ L) (hg : 0 < g)
    (hr : 2 * L + 8 * L ^ 2 / g < r) :
    L < r ∧ 2 * (L ^ 2 / (r - L)) +
      2 * M * (2 * L / (r - L) + L ^ 2 / (r - L) ^ 2) < g := by
  let d := r - L
  have hL : 0 ≤ L := hM.trans hML
  have hnonneg : 0 ≤ 8 * L ^ 2 / g := by positivity
  have hd : 0 < d := by dsimp only [d]; linarith only [hL, hnonneg, hr]
  have hLd : L ≤ d := by dsimp only [d]; linarith only [hnonneg, hr]
  have hq : L ^ 2 / d ^ 2 ≤ L / d := by
    rw [← div_pow, pow_two]
    exact mul_le_of_le_one_right (div_nonneg hL hd.le) ((div_le_one hd).mpr hLd)
  have hstep : 2 * L / d + L ^ 2 / d ^ 2 ≤ 3 * L / d := calc
    _ ≤ 2 * L / d + L / d := add_le_add_left hq _
    _ = _ := by ring
  have heta : 0 ≤ 2 * L / d + L ^ 2 / d ^ 2 := by positivity
  refine ⟨sub_pos.mp hd, ?_⟩
  change 2 * (L ^ 2 / d) + 2 * M * (2 * L / d + L ^ 2 / d ^ 2) < g
  calc
    _ ≤ 2 * (L ^ 2 / d) + 2 * L * (3 * L / d) := by
      exact add_le_add_left (mul_le_mul (by linarith only [hML]) hstep heta (by positivity)) _
    _ = 8 * L ^ 2 / d := by ring
    _ < g := by
      apply (div_lt_iff₀ hd).mpr
      rw [mul_comm g d, ← div_lt_iff₀ hg]
      dsimp only [d]
      linarith only [hL, hr]

/-- The numerical strict inequality in the order-five exterior example. -/
theorem exterior_five_threshold_arithmetic (z : ℂ) (hz : 123 ≤ ‖z‖) :
    let d := ‖z‖ - 3
    42 / d + 36 / d ^ 2 < (2 * Real.sqrt 2)⁻¹ := by
  intro d
  have hd : 120 ≤ d := by dsimp only [d]; linarith only [hz]
  have hd₂ : (120 : ℝ) ^ 2 ≤ d ^ 2 :=
    (sq_le_sq₀ (by norm_num) ((by norm_num : (0 : ℝ) ≤ 120).trans hd)).mpr hd
  have hpos : 0 < 2 * Real.sqrt 2 := by positivity
  calc
    _ ≤ 42 / (120 : ℝ) + 36 / (120 : ℝ) ^ 2 :=
      add_le_add (div_le_div_of_nonneg_left (by norm_num) (by norm_num) hd)
        (div_le_div_of_nonneg_left (by norm_num) (by norm_num) hd₂)
    _ = 141 / 400 := by norm_num
    _ < (2 * Real.sqrt 2)⁻¹ := by
      rw [← one_div]
      apply (lt_div_iff₀ hpos).mpr
      apply (sq_lt_sq₀ (by positivity) zero_le_one).mp
      nlinarith only [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

private theorem exterior_diagonal_norm_bound (a : ι → ℂ) (R : ℝ)
    (hR : 0 ≤ R) (ha : ∀ i, ‖a i‖ ≤ R) : ‖diagonal a‖ ≤ R := by
  rw [Matrix.cstar_norm_def]
  apply ContinuousLinearMap.opNorm_le_bound _ hR
  intro x
  let y : EuclideanSpace ℂ ι := (EuclideanSpace.equiv ι ℂ).symm (diagonal a *ᵥ x)
  change ‖y‖ ≤ R * ‖x‖
  apply (sq_le_sq₀ (norm_nonneg y) (mul_nonneg hR (norm_nonneg x))).mp
  simp only [mul_pow, PiLp.norm_sq_eq_of_L2, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  change ‖(diagonal a *ᵥ x) i‖ ^ 2 ≤ R ^ 2 * ‖x i‖ ^ 2
  rw [Matrix.mulVec_diagonal, norm_mul, mul_pow]
  exact mul_le_mul_of_nonneg_right ((sq_le_sq₀ (norm_nonneg _) hR).mpr (ha i)) (sq_nonneg _)

/-- The real spectrum in the order-five exterior example. -/
def exteriorFiveRealSpectrum : Fin 5 → ℝ := ![-2, -1, 0, 1, 2]

/-- The partner spectrum before the common exterior shift. -/
def exteriorFivePartnerSpectrum : Fin 5 → ℂ := ![0, 1, -1, Complex.I, -Complex.I]

private theorem exterior_five_triangle_certificate (i j k : Fin 5)
    (h : exteriorTriangleCross (exteriorFivePartnerSpectrum i) (exteriorFivePartnerSpectrum j)
      (exteriorFivePartnerSpectrum k) ≠ 0) :
    Complex.normSq (exteriorFivePartnerSpectrum j - exteriorFivePartnerSpectrum i) +
      Complex.normSq (exteriorFivePartnerSpectrum k - exteriorFivePartnerSpectrum i) ≤
        4 * (exteriorTriangleCross (exteriorFivePartnerSpectrum i) (exteriorFivePartnerSpectrum j)
          (exteriorFivePartnerSpectrum k)) ^ 2 := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    norm_num [exteriorFivePartnerSpectrum, Matrix.cons_val, exteriorTriangleCross, Complex.star_def,
      Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.sub_re, Complex.sub_im,
      Complex.neg_re, Complex.neg_im, Complex.normSq_apply] at h ⊢

private theorem exterior_five_triangle_gap (i j k : Fin 5) :
    let b := exteriorFivePartnerSpectrum
    exteriorTriangleCross (b i) (b j) (b k) ≠ 0 →
      (2 * Real.sqrt 2)⁻¹ * (‖b j - b i‖ + ‖b k - b i‖) ≤
        |exteriorTriangleCross (b i) (b j) (b k)| := by
  intro b h
  let a := ‖b j - b i‖
  let d := ‖b k - b i‖
  let c := exteriorTriangleCross (b i) (b j) (b k)
  have hcap : a ^ 2 + d ^ 2 ≤ 4 * c ^ 2 := by
    simpa only [Complex.normSq_eq_norm_sq] using exterior_five_triangle_certificate i j k h
  have hsqrt : 0 < 2 * Real.sqrt 2 := by positivity
  rw [inv_mul_eq_div]
  apply (div_le_iff₀ hsqrt).mpr
  change a + d ≤ |c| * (2 * Real.sqrt 2)
  apply (sq_le_sq₀ (add_nonneg (norm_nonneg _) (norm_nonneg _))
    (mul_nonneg (abs_nonneg _) hsqrt.le)).mp
  calc
    _ ≤ 2 * (a ^ 2 + d ^ 2) := by nlinarith only [sq_nonneg (a - d)]
    _ ≤ 2 * (4 * c ^ 2) := mul_le_mul_of_nonneg_left hcap (by norm_num)
    _ = _ := by
      rw [mul_pow, sq_abs, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      ring

/-- The order-five exterior example holds for every unitary mixer whenever
the complex shift has modulus at least 123. -/
theorem holds_exterior_five (z : ℂ) (hz : 123 ≤ ‖z‖)
    (U : Matrix (Fin 5) (Fin 5) ℂ) (hU : IsUnitary U) :
    Holds (fun i => (exteriorFiveRealSpectrum i : ℂ)) (fun i => z + exteriorFivePartnerSpectrum i) U := by
  have ha : ‖diagonal (fun i => (exteriorFiveRealSpectrum i : ℂ))‖ ≤ 2 := by
    apply exterior_diagonal_norm_bound _ _ (by norm_num)
    intro i
    fin_cases i <;> norm_num [exteriorFiveRealSpectrum, Matrix.cons_val, Complex.norm_real, Real.norm_eq_abs]
  have hb : ‖diagonal exteriorFivePartnerSpectrum‖ ≤ 1 := by
    apply exterior_diagonal_norm_bound _ _ (by norm_num)
    intro i
    fin_cases i <;> norm_num [exteriorFivePartnerSpectrum, Matrix.cons_val, Complex.norm_I]
  have hnorms : 2 + ‖diagonal exteriorFivePartnerSpectrum‖ ≤ 3 := by linarith only [hb]
  have hz' : 3 < ‖z‖ := (by norm_num : (3 : ℝ) < 123).trans_le hz
  refine holds_of_exterior_scalar_shift exteriorFiveRealSpectrum exteriorFivePartnerSpectrum z
    2 3 ((2 * Real.sqrt 2)⁻¹) ha hnorms hz' (by positivity) ?_ exterior_five_triangle_gap U hU
  dsimp only
  convert exterior_five_threshold_arithmetic z hz using 1 <;> ring

/-- Every fixed real spectrum and complex partner spectrum satisfy the determinant
hull inclusion for all shifts outside one disk, uniformly over the mixer. -/
theorem exists_exterior_scalar_shift_radius (a : ι → ℝ) (b : ι → ℂ) :
    ∃ R : ℝ, 0 < R ∧ ∀ z : ℂ, R ≤ ‖z‖ → ∀ U : Matrix ι ι ℂ, IsUnitary U →
      Holds (fun i => (a i : ℂ)) (fun i => z + b i) U := by
  classical
  by_cases hι : Nonempty ι
  · letI : Nonempty ι := hι
    obtain ⟨g, hg, harea⟩ := exterior_exists_positive_triangle_gap b
    let M := ‖diagonal (fun i => (a i : ℂ))‖
    let L := M + ‖diagonal b‖
    let C := 2 * L + 8 * L ^ 2 / g
    have hML : M ≤ L := le_add_of_nonneg_right (norm_nonneg (diagonal b))
    have hM : 0 ≤ M := norm_nonneg _
    have hL : 0 ≤ L := hM.trans hML
    have hC : 0 ≤ C := by dsimp only [C]; positivity
    refine ⟨C + 1, add_pos_of_nonneg_of_pos hC zero_lt_one, ?_⟩
    intro z hz U hU
    have hcut : C < ‖z‖ := (lt_add_of_pos_right C zero_lt_one).trans_le hz
    obtain ⟨hlarge, hsmall⟩ := exterior_bound_of_simple_cutoff M L g ‖z‖ hM hML hg hcut
    exact holds_of_exterior_scalar_shift a b z M L g le_rfl le_rfl hlarge hg.le hsmall harea U hU
  · letI : IsEmpty ι := ⟨fun i => hι ⟨i⟩⟩
    exact ⟨1, zero_lt_one, fun z _ U hU => conjecture_of_subsingleton _ _ U hU⟩

end

end MOC
