import MOC.Variational
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Normed.Ring.Units

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
  congr 1
  funext i
  change (1 / 2 : ℂ) * (c * b i + star (c * b i)) = ((c * b i).re : ℂ)
  rw [Complex.star_def, Complex.add_conj, Complex.ofReal_mul, Complex.ofReal_ofNat]
  ring

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
  rw [← one_div]
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
    simp only [Z, Matrix.smul_mul, Matrix.mul_one, smul_smul, pow_two]
  have he : (Z - Y) * C = (z ^ 2) • 1 - Y * Y := by
    change (Z - Y) * (Z + Y) = _
    rw [Matrix.mul_add, Matrix.sub_mul, Matrix.sub_mul, hcomm, hsq]
    abel
  have hp := congrArg (fun X : Matrix ι ι ℂ => X * C⁻¹) he
  simp only [Matrix.mul_assoc, hc, Matrix.mul_one, Matrix.sub_mul, Matrix.smul_mul,
    Matrix.one_mul] at hp
  change (z ^ 2) • C⁻¹ = Z - Y + (Y * Y) * C⁻¹
  exact eq_add_of_sub_eq hp.symm

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
  letI : SeminormedAddCommGroup (Matrix ι ι ℂ) := Matrix.frobeniusSeminormedAddCommGroup
  ‖A‖

private theorem exteriorFrobenius_nonneg (A : Matrix ι ι ℂ) : 0 ≤ exteriorFrobenius A := by
  letI : SeminormedAddCommGroup (Matrix ι ι ℂ) := Matrix.frobeniusSeminormedAddCommGroup
  exact norm_nonneg A

private theorem exteriorFrobenius_sq (A : Matrix ι ι ℂ) :
    exteriorFrobenius A ^ 2 = ∑ i, ∑ j, ‖A i j‖ ^ 2 := by
  letI : SeminormedAddCommGroup (Matrix ι ι ℂ) := Matrix.frobeniusSeminormedAddCommGroup
  change ‖A‖ ^ 2 = _
  rw [Matrix.frobenius_norm_def]
  simp only [Real.rpow_two, ← Real.sqrt_eq_rpow]
  exact Real.sq_sqrt (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)

private theorem exteriorFrobenius_add (A B : Matrix ι ι ℂ) :
    exteriorFrobenius (A + B) ≤ exteriorFrobenius A + exteriorFrobenius B := by
  letI : SeminormedAddCommGroup (Matrix ι ι ℂ) := Matrix.frobeniusSeminormedAddCommGroup
  exact norm_add_le A B

private theorem exteriorFrobenius_conjTranspose (A : Matrix ι ι ℂ) :
    exteriorFrobenius Aᴴ = exteriorFrobenius A := by
  letI : SeminormedAddCommGroup (Matrix ι ι ℂ) := Matrix.frobeniusSeminormedAddCommGroup
  exact Matrix.frobenius_norm_conjTranspose A

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
  have hneg : exteriorFrobenius (-(Y - Z)) = p := by
    letI : SeminormedAddCommGroup (Matrix ι ι ℂ) := Matrix.frobeniusSeminormedAddCommGroup
    exact norm_neg _
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
  letI : SeminormedAddCommGroup (Matrix ι ι ℂ) := Matrix.frobeniusSeminormedAddCommGroup
  exact norm_neg A

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
  letI : NormedAddCommGroup (Matrix ι ι ℂ) := Matrix.frobeniusNormedAddCommGroup
  exact norm_eq_zero.mp hFzero

end Blocks

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

end

end MOC
