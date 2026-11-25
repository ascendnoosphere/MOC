import MOC.SpectralProfileDeterminant
import Mathlib.Tactic.Abel

/-! Rank constraints for the real and imaginary parts of the order-four inverse pencil. -/

open Matrix

namespace MOC
namespace SpectralProfile

noncomputable section

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- The intersection of the ranges uses the part of the rank budget that
the sum of the two matrices does not use. -/
theorem rank_add_range_inter_le (A B : Matrix ι ι ℂ) :
    (A + B).rank + Module.finrank ℂ (LinearMap.range A.mulVecLin ⊓
      LinearMap.range B.mulVecLin : Submodule ℂ (ι → ℂ)) ≤ A.rank + B.rank := by
  have hrange : LinearMap.range (A + B).mulVecLin ≤
      LinearMap.range A.mulVecLin ⊔ LinearMap.range B.mulVecLin := by
    rintro _ ⟨v, rfl⟩
    rw [Matrix.mulVecLin_add, LinearMap.add_apply]
    exact Submodule.add_mem_sup (LinearMap.mem_range_self A.mulVecLin v)
      (LinearMap.mem_range_self B.mulVecLin v)
  calc
    _ ≤ Module.finrank ℂ (LinearMap.range A.mulVecLin ⊔
          LinearMap.range B.mulVecLin : Submodule ℂ (ι → ℂ)) +
        Module.finrank ℂ (LinearMap.range A.mulVecLin ⊓
          LinearMap.range B.mulVecLin : Submodule ℂ (ι → ℂ)) :=
      Nat.add_le_add_right (Submodule.finrank_mono hrange) _
    _ = _ := Submodule.finrank_sup_add_finrank_inf_eq _ _

private theorem range_inter_eq_bot_of_rank_add_le (A B : Matrix ι ι ℂ)
    (h : A.rank + B.rank ≤ (A + B).rank) :
    LinearMap.range A.mulVecLin ⊓ LinearMap.range B.mulVecLin = ⊥ := by
  apply Submodule.finrank_eq_zero.mp
  have hbudget := rank_add_range_inter_le A B
  omega

private theorem rank_smul_ne_zero (X : Matrix ι ι ℂ) {c : ℂ} (hc : c ≠ 0) :
    (c • X).rank = X.rank := by
  have heq : (c • X).mulVecLin = c • X.mulVecLin := by
    apply LinearMap.ext
    intro v
    rw [Matrix.mulVecLin_apply, LinearMap.smul_apply, Matrix.mulVecLin_apply,
      Matrix.smul_mulVec_assoc]
  simp only [Matrix.rank, heq, LinearMap.range_smul _ _ hc]

private theorem complex_lift_conjTranspose (X Y : Matrix ι ι ℂ)
    (hX : X.IsHermitian) (hY : Y.IsHermitian) :
    (X + Complex.I • Y)ᴴ = X - Complex.I • Y := by
  simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, hX.eq, hY.eq,
    Complex.star_def, Complex.conj_I, neg_smul, sub_eq_add_neg]

private theorem complex_lift_range_inter_eq_bot (X Y : Matrix ι ι ℂ)
    (hX : X.IsHermitian) (hY : Y.IsHermitian)
    (hrank : 8 ≤ X.rank) (hlift : (X + Complex.I • Y).rank ≤ 4) :
    LinearMap.range (X + Complex.I • Y).mulVecLin ⊓
      LinearMap.range (X - Complex.I • Y).mulVecLin = ⊥ := by
  apply range_inter_eq_bot_of_rank_add_le
  have hconj : (X - Complex.I • Y).rank ≤ 4 := by
    rw [← complex_lift_conjTranspose X Y hX hY, Matrix.rank_conjTranspose]
    exact hlift
  have hsum : X + Complex.I • Y + (X - Complex.I • Y) = (2 : ℂ) • X := by
    rw [two_smul]
    abel
  rw [hsum, rank_smul_ne_zero X two_ne_zero]
  omega

/-- If the real part uses all eight ranks, every vector in its kernel
is also in the kernel of the imaginary part. Real symmetric input matrices
can be read as complex Hermitian matrices. -/
theorem rank_eight_lift_common_kernel (X Y : Matrix ι ι ℂ)
    (hX : X.IsHermitian) (hY : Y.IsHermitian)
    (hrank : 8 ≤ X.rank) (hlift : (X + Complex.I • Y).rank ≤ 4) :
    LinearMap.ker X.mulVecLin ≤ LinearMap.ker Y.mulVecLin := by
  intro v hv
  have hvX : X *ᵥ v = 0 := LinearMap.mem_ker.mp hv
  have hplus : (X + Complex.I • Y) *ᵥ v = Complex.I • (Y *ᵥ v) := by
    rw [Matrix.add_mulVec, hvX, zero_add, Matrix.smul_mulVec_assoc]
  have hminus : (X - Complex.I • Y) *ᵥ v = -(Complex.I • (Y *ᵥ v)) := by
    rw [Matrix.sub_mulVec, hvX, zero_sub, Matrix.smul_mulVec_assoc]
  have hl : Complex.I • (Y *ᵥ v) ∈ LinearMap.range (X + Complex.I • Y).mulVecLin :=
    ⟨v, hplus⟩
  have hr : Complex.I • (Y *ᵥ v) ∈ LinearMap.range (X - Complex.I • Y).mulVecLin := by
    have hz : -(Complex.I • (Y *ᵥ v)) ∈
        LinearMap.range (X - Complex.I • Y).mulVecLin := ⟨v, hminus⟩
    simpa only [neg_neg] using Submodule.neg_mem _ hz
  have hb := complex_lift_range_inter_eq_bot X Y hX hY hrank hlift
  have hi : Complex.I • (Y *ᵥ v) ∈ LinearMap.range (X + Complex.I • Y).mulVecLin ⊓
      LinearMap.range (X - Complex.I • Y).mulVecLin := ⟨hl, hr⟩
  rw [hb] at hi
  have hz := Submodule.mem_bot.mp hi
  exact LinearMap.mem_ker.mpr ((smul_eq_zero.mp hz).resolve_left Complex.I_ne_zero)

private theorem rank_submatrix_le (A : Matrix ι ι ℂ) (r c : κ → ι) :
    (A.submatrix r c).rank ≤ A.rank := by
  let L : Matrix κ ι ℂ := (1 : Matrix ι ι ℂ).submatrix r id
  let R : Matrix ι κ ℂ := (1 : Matrix ι ι ℂ).submatrix id c
  have hL : L * A = A.submatrix r id :=
    Matrix.one_submatrix_mul r (Equiv.refl ι) A
  have hR : A.submatrix r id * R = A.submatrix r c :=
    Matrix.mul_submatrix_one (Equiv.refl ι) c (A.submatrix r id)
  rw [← hR, ← hL]
  exact (Matrix.rank_mul_le_left (L * A) R).trans (Matrix.rank_mul_le_right L A)

/-- Every five-by-five minor of a lifted pencil vanishes. The implication
requires no hypothesis about the rank of its real part. -/
theorem rank_four_lift_minor_eq_zero (Z : Matrix ι ι ℂ) (hlift : Z.rank ≤ 4)
    (r c : Fin 5 → ι) : (Z.submatrix r c).det = 0 := by
  by_contra hn
  have hu : IsUnit (Z.submatrix r c) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hn)
  have hr := (rank_submatrix_le Z r c).trans hlift
  rw [Matrix.rank_of_isUnit _ hu, Fintype.card_fin] at hr
  omega

private theorem opposite_lifts_mul_inverse (X Y : Matrix ι ι ℂ) (hunit : IsUnit X.det) :
    (X + Complex.I • Y) * X⁻¹ * (X - Complex.I • Y) = X + Y * X⁻¹ * Y := by
  have hY : (Y * X⁻¹) * X = Y := by
    rw [Matrix.mul_assoc, X.nonsing_inv_mul hunit, Matrix.mul_one]
  simp only [Matrix.add_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul,
    X.mul_nonsing_inv hunit, Matrix.one_mul, hY, smul_sub, smul_smul, Complex.I_mul_I,
    neg_one_smul, sub_neg_eq_add]
  abel

/-- With eight coordinates and invertible real part, complex rank at most
four gives the inverse identity for the imaginary part. -/
theorem rank_eight_lift_inverse_identity (X Y : Matrix ι ι ℂ)
    (hX : X.IsHermitian) (hY : Y.IsHermitian) (hcard : Fintype.card ι = 8)
    (hunit : IsUnit X.det) (hlift : (X + Complex.I • Y).rank ≤ 4) :
    Y * X⁻¹ * Y = -X := by
  let A := X + Complex.I • Y
  let B := X - Complex.I • Y
  have hrank : 8 ≤ X.rank := by
    rw [Matrix.rank_of_isUnit X ((Matrix.isUnit_iff_isUnit_det X).mpr hunit), hcard]
  have hbot : LinearMap.range A.mulVecLin ⊓ LinearMap.range B.mulVecLin = ⊥ :=
    complex_lift_range_inter_eq_bot X Y hX hY hrank hlift
  have hB : B = (2 : ℂ) • X - A := by
    dsimp only [A, B]
    rw [two_smul]
    abel
  have hleft : A * X⁻¹ * ((2 : ℂ) • X) = (2 : ℂ) • A := by
    rw [Matrix.mul_smul, Matrix.mul_assoc, X.nonsing_inv_mul hunit, Matrix.mul_one]
  have hright : ((2 : ℂ) • X) * X⁻¹ * A = (2 : ℂ) • A := by
    rw [Matrix.smul_mul, Matrix.smul_mul, X.mul_nonsing_inv hunit, Matrix.one_mul]
  have heq : A * X⁻¹ * B = B * X⁻¹ * A := by
    rw [hB, Matrix.mul_sub, Matrix.sub_mul, Matrix.sub_mul, hleft, hright]
  have hz (v : ι → ℂ) : (A * X⁻¹ * B) *ᵥ v = 0 := by
    have hl : (A * X⁻¹ * B) *ᵥ v ∈ LinearMap.range A.mulVecLin := by
      refine ⟨X⁻¹ *ᵥ (B *ᵥ v), ?_⟩
      exact (Matrix.mulVec_mulVec (B *ᵥ v) A X⁻¹).trans
        (Matrix.mulVec_mulVec v (A * X⁻¹) B)
    have hr : (A * X⁻¹ * B) *ᵥ v ∈ LinearMap.range B.mulVecLin := by
      refine ⟨X⁻¹ *ᵥ (A *ᵥ v), ?_⟩
      rw [heq]
      exact (Matrix.mulVec_mulVec (A *ᵥ v) B X⁻¹).trans
        (Matrix.mulVec_mulVec v (B * X⁻¹) A)
    have hv : (A * X⁻¹ * B) *ᵥ v ∈
        LinearMap.range A.mulVecLin ⊓ LinearMap.range B.mulVecLin := ⟨hl, hr⟩
    rw [hbot] at hv
    exact Submodule.mem_bot.mp hv
  have hmul : A * X⁻¹ * B = 0 := by
    apply Matrix.ext_of_mulVec_single
    intro i
    rw [Matrix.zero_mulVec]
    exact hz _
  have hsum := (opposite_lifts_mul_inverse X Y hunit).symm.trans hmul
  exact eq_neg_of_add_eq_zero_right hsum

/-- On an invertible block of size eight, the inverse identity is also
sufficient for the complex rank bound on that block. -/
theorem rank_eight_lift_inverse_iff (X Y : Matrix ι ι ℂ)
    (hX : X.IsHermitian) (hY : Y.IsHermitian) (hcard : Fintype.card ι = 8)
    (hunit : IsUnit X.det) :
    (X + Complex.I • Y).rank ≤ 4 ↔ Y * X⁻¹ * Y = -X := by
  constructor
  · exact rank_eight_lift_inverse_identity X Y hX hY hcard hunit
  · intro hYinv
    have hz : (X + Complex.I • Y) * X⁻¹ * (X - Complex.I • Y) = 0 := by
      rw [opposite_lifts_mul_inverse X Y hunit, hYinv, add_neg_cancel]
    have hr := Matrix.rank_add_rank_le_card_of_mul_eq_zero hz
    rw [Matrix.rank_mul_eq_left_of_isUnit_det X⁻¹ _ (X.isUnit_nonsing_inv_det hunit),
      ← complex_lift_conjTranspose X Y hX hY, Matrix.rank_conjTranspose, hcard] at hr
    omega

/-- A principal block of size eight inherits the inverse identity from
the rank bound on the full lifted pencil. -/
theorem rank_eight_lift_principal_identity (X Y : Matrix ι ι ℂ)
    (hX : X.IsHermitian) (hY : Y.IsHermitian) (e : Fin 8 → ι)
    (hunit : IsUnit (X.submatrix e e).det) (hlift : (X + Complex.I • Y).rank ≤ 4) :
    Y.submatrix e e * (X.submatrix e e)⁻¹ * Y.submatrix e e = -(X.submatrix e e) := by
  have hXS : (X.submatrix e e).IsHermitian := by
    change (X.submatrix e e)ᴴ = X.submatrix e e
    ext i j
    exact congrArg (fun M : Matrix ι ι ℂ => M (e i) (e j)) hX.eq
  have hYS : (Y.submatrix e e).IsHermitian := by
    change (Y.submatrix e e)ᴴ = Y.submatrix e e
    ext i j
    exact congrArg (fun M : Matrix ι ι ℂ => M (e i) (e j)) hY.eq
  have hZS : (X.submatrix e e + Complex.I • Y.submatrix e e).rank ≤ 4 :=
    (rank_submatrix_le (X + Complex.I • Y) e e).trans hlift
  exact rank_eight_lift_inverse_identity _ _ hXS hYS (Fintype.card_fin 8) hunit hZS

end

end SpectralProfile
end MOC
