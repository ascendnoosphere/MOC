import MOC.SchurPlaneSandwich
import MOC.TwoOutlierZeroSupport

/-! Block determinant certificate in the plane of two imaginary outliers.
The lower and upper comparison planes are the two perpendicular line
projections weighted by the spectral endpoint values. -/

open Matrix
open scoped ComplexOrder Matrix

namespace MOC
noncomputable section

/-- The reference real part of the outlier plane, at two constant
spectator spectral values. -/
def outlierReferencePlane (a b c s : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![((b * s^2 : ℝ) : ℂ), ((-b * c * s : ℝ) : ℂ);
     ((-b * c * s : ℝ) : ℂ), ((a + b * c^2 : ℝ) : ℂ)]

/-- The imaginary perturbation of two line projections in outlier-plane
coordinates. -/
def outlierImaginaryPlane (u v c s : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![Complex.I * (u + v * c^2), Complex.I * (v * c * s);
     Complex.I * (v * c * s), Complex.I * (v * s^2)]

theorem outlierReferencePlane_det_re (a b c s : ℝ) :
    (outlierReferencePlane a b c s).det.re = a * b * s^2 := by
  simp [outlierReferencePlane, Matrix.det_fin_two, ← Complex.ofReal_mul,
    ← Complex.ofReal_sub]
  ring

theorem outlierReferencePlane_posDef (a b c s : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hs : s ≠ 0) : (outlierReferencePlane a b c s).PosDef := by
  let L : Matrix (Fin 2) (Fin 2) ℂ := !![0, (s : ℂ); 1, -(c : ℂ)]
  have hl : L.det = -(s : ℂ) := by simp [L, Matrix.det_fin_two]
  have hunit : IsUnit L := Matrix.isUnit_iff_isUnit_det _ |>.mpr
    ((hl.trans_ne (neg_ne_zero.mpr (Complex.ofReal_ne_zero.mpr hs))).isUnit)
  let v : Fin 2 → ℝ := ![a, b]
  have hdiag : (diagonal (fun i => (v i : ℂ))).PosDef := by
    apply Matrix.PosDef.diagonal
    intro i
    simp only [Complex.pos_iff, Complex.ofReal_re, Complex.ofReal_im, and_true]
    exact (show ∀ j : Fin 2, 0 < v j from by simp [Fin.forall_fin_two, v, ha, hb]) i
  have hfac : L * diagonal (fun i => (v i : ℂ)) * Lᴴ = outlierReferencePlane a b c s := by
    apply Matrix.ext
    simp only [Fin.forall_fin_two]
    simp [L, v, outlierReferencePlane, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.conjTranspose_apply, Matrix.vecMul_diagonal]
    constructor <;> constructor <;> ring_nf
    simp
  rw [← hfac]
  exact hdiag.mul_mul_conjTranspose_same (Matrix.vecMul_injective_iff_isUnit.mpr hunit)

private theorem outlier_perturbation_det_re (S : Matrix (Fin 2) (Fin 2) ℂ)
    (hS : S.IsHermitian) (u v c s : ℝ) :
    (S + outlierImaginaryPlane u v c s).det.re = S.det.re - u * v * s^2 := by
  have h₀ : ((S 0 0).re : ℂ) = S 0 0 := hS.coe_re_apply_self 0
  have h₁ : ((S 1 1).re : ℂ) = S 1 1 := hS.coe_re_apply_self 1
  have h₀₁ : star (S 0 1) = S 1 0 := hS.apply 1 0
  have he := re_det_two_outlier_plane (S 0 0).re (S 1 1).re c s u v (S 0 1)
  simp only [Matrix.det_fin_two, Matrix.of_apply, Matrix.vecCons, Fin.cons_zero, Fin.cons_one,
    h₀, h₁, h₀₁] at he
  have hs : S.det.re = (S 0 0).re * (S 1 1).re - Complex.normSq (S 0 1) := by
    rw [Matrix.det_fin_two, ← h₀, ← h₁, ← h₀₁, Complex.sub_re, Complex.mul_re,
      Complex.ofReal_im, Complex.ofReal_re, zero_mul, sub_zero, Complex.star_def, Complex.mul_conj,
      Complex.ofReal_re]
    simp only [Complex.ofReal_re]
  rw [hs, Matrix.det_fin_two]
  simpa only [outlierImaginaryPlane, Matrix.add_apply, Matrix.of_apply, Matrix.vecCons,
    Fin.cons_zero, Fin.cons_one] using he

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- Exact real-part bounds in the outlier-plane block chart. If the product
of the imaginary heights lies outside the reference interval, the sign
certifies the associated height-zero supporting inequality. -/
theorem re_det_two_outliers_block_sandwich
    (A : Matrix (Fin 2) (Fin 2) ℂ) (B : Matrix (Fin 2) κ ℂ) (D : Matrix κ κ ℂ)
    (alo blo ahi bhi u v c s : ℝ) (ha : 0 < alo) (hb : 0 < blo) (hs : s ≠ 0)
    (hD : D.PosDef)
    (hL : (fromBlocks (A - outlierReferencePlane alo blo c s) B Bᴴ D).PosSemidef)
    (hU : (outlierReferencePlane ahi bhi c s - A).PosSemidef) :
    D.det.re * ((alo * blo - u * v) * s^2) ≤
      (fromBlocks (A + outlierImaginaryPlane u v c s) B Bᴴ D).det.re ∧
    (fromBlocks (A + outlierImaginaryPlane u v c s) B Bᴴ D).det.re ≤
      D.det.re * ((ahi * bhi - u * v) * s^2) := by
  let S := A - B * D⁻¹ * Bᴴ
  let L := outlierReferencePlane alo blo c s
  let R := outlierReferencePlane ahi bhi c s
  obtain ⟨hlo, hhi⟩ := schurPlane_posSemidef_sandwich A L R B D hD hL hU
  have hLpos : L.PosDef := outlierReferencePlane_posDef alo blo c s ha hb hs
  have hS : S.PosDef := by
    have h := hLpos.add_posSemidef hlo
    convert h using 1
    dsimp only [S]
    abel
  have ha₀ := det_re_mono_of_posDef hLpos hlo
  have hb₀ := det_re_mono_of_posDef hS hhi
  change L.det.re ≤ S.det.re at ha₀
  change S.det.re ≤ R.det.re at hb₀
  rw [show L.det.re = alo * blo * s^2 from outlierReferencePlane_det_re ..] at ha₀
  rw [show R.det.re = ahi * bhi * s^2 from outlierReferencePlane_det_re ..] at hb₀
  letI := hD.isUnit.invertible
  have hformula :
      (fromBlocks (A + outlierImaginaryPlane u v c s) B Bᴴ D).det.re =
        D.det.re * (S.det.re - u * v * s^2) := by
    rw [Matrix.det_fromBlocks₂₂, Matrix.invOf_eq_nonsing_inv]
    have he : A + outlierImaginaryPlane u v c s - B * D⁻¹ * Bᴴ =
        S + outlierImaginaryPlane u v c s := by dsimp only [S]; abel
    rw [he, Complex.mul_re, outlier_perturbation_det_re _ hS.1]
    have him : D.det.im = 0 := (Complex.nonneg_iff.mp (le_of_lt hD.det_pos)).2.symm
    rw [him, zero_mul, sub_zero]
  have hpos : 0 ≤ D.det.re := (Complex.nonneg_iff.mp (le_of_lt hD.det_pos)).1
  rw [hformula]
  constructor
  · apply mul_le_mul_of_nonneg_left _ hpos
    nlinarith only [ha₀]
  · apply mul_le_mul_of_nonneg_left _ hpos
    nlinarith only [hb₀]

end
end MOC
