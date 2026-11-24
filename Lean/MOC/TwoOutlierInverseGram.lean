import MOC.SchurPlaneSandwich

/-! A determinant sign certificate for two imaginary rank-one perturbations.
The two columns remain in the original ambient basis. -/
open Matrix
open scoped ComplexOrder Matrix

namespace MOC
noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem inverse_sub_posSemidef {A B : Matrix ι ι ℂ}
    (hA : A.PosDef) (hB : B.PosDef) (hab : (B - A).PosSemidef) :
    (A⁻¹ - B⁻¹).PosSemidef := by
  letI := hB.isUnit.invertible
  letI := hA.inv.isUnit.invertible
  have hu := (Matrix.isUnit_iff_isUnit_det A).mp hA.isUnit
  have hblock : (fromBlocks B (1 : Matrix ι ι ℂ) (1 : Matrix ι ι ℂ) A⁻¹).PosSemidef := by
    have h := (Matrix.PosSemidef.fromBlocks₂₂ B (1 : Matrix ι ι ℂ) hA.inv).mpr
      (by simpa only [conjTranspose_one, one_mul, mul_one, Matrix.nonsing_inv_nonsing_inv _ hu] using hab)
    simpa only [conjTranspose_one] using h
  have h := (Matrix.PosSemidef.fromBlocks₁₁ (1 : Matrix ι ι ℂ) A⁻¹ hB).mp (by simpa using hblock)
  simpa only [conjTranspose_one, one_mul, mul_one] using h

private theorem gram_reference_det (V : Matrix ι (Fin 2) ℂ) (a b : ℝ)
    (h00 : (Vᴴ * V) 0 0 = 1) (h11 : (Vᴴ * V) 1 1 = 1)
    (hg : (Vᴴ * V).det ≠ 0) (hab : (a : ℂ) * b ≠ 0)
    (R : Matrix ι ι ℂ)
    (hr : R = (a + b : ℂ) • (1 : Matrix ι ι ℂ) -
      V * diagonal ![(a : ℂ), (b : ℂ)] * Vᴴ) (hR : R.PosDef) :
    (Vᴴ * R⁻¹ * V).det = ((a : ℂ) * b)⁻¹ := by
  let D : Matrix (Fin 2) (Fin 2) ℂ := diagonal ![(a : ℂ), (b : ℂ)]
  let G := Vᴴ * V
  let T := (a + b : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) - D * G
  have hTV : R * V = V * T := by
    rw [hr]
    change (((a + b : ℂ) • (1 : Matrix ι ι ℂ)) - V * D * Vᴴ) * V = _
    simp only [T, G, Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
      Matrix.mul_one, Matrix.mul_assoc]
  have hT : T.det = ((a : ℂ) * b) * G.det := by
    simp [T, D, Matrix.det_fin_two, Matrix.sub_apply, Matrix.smul_apply,
      Matrix.diagonal_mul, Matrix.one_apply, h00, h11, G]
    ring
  have he : (Vᴴ * R⁻¹ * V) * T = G := by
    have hu := (Matrix.isUnit_iff_isUnit_det R).mp hR.isUnit
    rw [Matrix.mul_assoc (Vᴴ * R⁻¹) V T, ← hTV, ← Matrix.mul_assoc,
      Matrix.mul_assoc Vᴴ, Matrix.nonsing_inv_mul _ hu, Matrix.mul_one]
  have hd := congrArg Matrix.det he
  rw [Matrix.det_mul, hT] at hd
  apply mul_right_cancel₀ hg
  calc
    (Vᴴ * R⁻¹ * V).det * G.det = ((a : ℂ) * b)⁻¹ * G.det := by
      apply mul_left_cancel₀ hab
      rw [← mul_assoc, mul_comm ((a : ℂ) * b), mul_assoc, hd, ← mul_assoc,
        mul_inv_cancel₀ hab, one_mul]

private theorem real_det_two_rank_one (H : Matrix ι ι ℂ)
    (hH : H.PosDef) (V : Matrix ι (Fin 2) ℂ) (u v : ℝ) :
    (H + V * diagonal ![Complex.I * u, Complex.I * v] * Vᴴ).det.re =
      H.det.re * (1 - u * v * (Vᴴ * H⁻¹ * V).det.re) := by
  let D : Matrix (Fin 2) (Fin 2) ℂ := diagonal ![Complex.I * u, Complex.I * v]
  let G := Vᴴ * H⁻¹ * V
  have hh : G.IsHermitian := by
    have he := hH.inv.1
    change (Vᴴ * H⁻¹ * V)ᴴ = _
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      he.eq]; simp only [G, Matrix.mul_assoc]
  have hzero (j : Fin 2) : (G j j).im = 0 := by
    have hx : star (G j j) = G j j := congrFun (congrFun hh.eq j) j
    have hi := congrArg Complex.im hx
    simp only [Complex.star_def, Complex.conj_im] at hi
    linarith
  have hHim : H.det.im = 0 := by
    have hx : star H.det = H.det := by rw [← Matrix.det_conjTranspose, hH.1.eq]
    have hi := congrArg Complex.im hx
    simp only [Complex.star_def, Complex.conj_im] at hi
    linarith
  change (H + V * D * Vᴴ).det.re = _
  rw [Matrix.mul_assoc, Matrix.det_add_mul V (D * Vᴴ)
    ((Matrix.isUnit_iff_isUnit_det H).mp hH.isUnit)]
  have he : D * Vᴴ * H⁻¹ * V = D * G := by simp only [G, Matrix.mul_assoc]
  rw [he, Complex.mul_re, hHim, zero_mul, sub_zero]
  have hdet : (1 + D * G).det = 1 + Complex.I * u * G 0 0 +
      Complex.I * v * G 1 1 - ((u * v : ℝ) : ℂ) * G.det := by
    rw [Matrix.det_fin_two, Matrix.det_fin_two]
    simp [D, Matrix.add_apply, Matrix.one_apply, Matrix.diagonal_mul, Complex.ofReal_mul]
    linear_combination (u : ℂ) * v * (G 0 0 * G 1 1 - G 0 1 * G 1 0) * Complex.I_mul_I
  rw [hdet]
  change H.det.re * _ = H.det.re * (1 - u * v * G.det.re)
  simp [ Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.mul_im,
    hzero, Complex.I_re, Complex.I_im]


/-- Two unit, independent outlier columns are enough to certify the
height-zero supporting inequalities by ambient order comparisons.
The proof uses no adapted basis and works in any finite ambient order. -/
theorem re_det_two_outliers_of_ambient_comparison
    (H : Matrix ι ι ℂ) (hH : H.PosDef) (V : Matrix ι (Fin 2) ℂ)
    (hV : Function.Injective V.mulVec)
    (h00 : (Vᴴ * V) 0 0 = 1) (h11 : (Vᴴ * V) 1 1 = 1)
    (u v : ℝ) (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (R : Matrix ι ι ℂ)
    (hr : R = (a + b : ℂ) • (1 : Matrix ι ι ℂ) -
       V * diagonal ![(a : ℂ), (b : ℂ)] * Vᴴ) (hR : R.PosDef) :
    ((R - H).PosSemidef → a * b ≤ u * v →
      (H + V * diagonal ![Complex.I * u, Complex.I * v] * Vᴴ).det.re ≤ 0) ∧
    ((H - R).PosSemidef → u * v ≤ a * b →
      0 ≤ (H + V * diagonal ![Complex.I * u, Complex.I * v] * Vᴴ).det.re) := by
  let G := Vᴴ * V
  have hGp : G.PosDef := by
    simpa only [G, Matrix.mul_one] using
      (Matrix.PosDef.one : (1 : Matrix ι ι ℂ).PosDef).conjTranspose_mul_mul_same hV
  have hg : G.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det G).mp hGp.isUnit).ne_zero
  have hab : 0 < a * b := mul_pos ha hb
  have habc : (a : ℂ) * b ≠ 0 := by exact_mod_cast hab.ne'
  have hrd := gram_reference_det V a b h00 h11 hg habc R hr hR
  have hrd' : (Vᴴ * R⁻¹ * V).det.re = (a * b)⁻¹ := by
    rw [hrd, ← Complex.ofReal_mul, ← Complex.ofReal_inv, Complex.ofReal_re]
  have hdet := real_det_two_rank_one H hH V u v
  have hHp : (Vᴴ * H⁻¹ * V).PosDef := hH.inv.conjTranspose_mul_mul_same hV
  have hRp : (Vᴴ * R⁻¹ * V).PosDef := hR.inv.conjTranspose_mul_mul_same hV
  have hh : 0 < H.det.re := (Complex.pos_iff.mp hH.det_pos).1
  constructor
  · intro hbound huv
    have hm := (inverse_sub_posSemidef hH hR hbound).conjTranspose_mul_mul_same V
    rw [Matrix.mul_sub, Matrix.sub_mul] at hm
    have hgd := det_re_mono_of_posDef hRp hm
    rw [hrd'] at hgd
    have h1 : 1 ≤ u * v * (Vᴴ * H⁻¹ * V).det.re := calc
      1 = (a * b) * (a * b)⁻¹ := (mul_inv_cancel₀ hab.ne').symm
      _ ≤ (u * v) * (Vᴴ * H⁻¹ * V).det.re :=
        mul_le_mul huv hgd (inv_nonneg.mpr hab.le) (hab.le.trans huv)
    rw [hdet]
    exact mul_nonpos_of_nonneg_of_nonpos hh.le (sub_nonpos.mpr h1)
  · intro hbound huv
    have hm := (inverse_sub_posSemidef hR hH hbound).conjTranspose_mul_mul_same V
    rw [Matrix.mul_sub, Matrix.sub_mul] at hm
    have hgd := det_re_mono_of_posDef hHp hm
    rw [hrd'] at hgd
    have hpos : 0 < (Vᴴ * H⁻¹ * V).det.re := (Complex.pos_iff.mp hHp.det_pos).1
    have h1 : u * v * (Vᴴ * H⁻¹ * V).det.re ≤ 1 := calc
      _ ≤ (a * b) * (a * b)⁻¹ := mul_le_mul huv hgd hpos.le hab.le
      _ = 1 := mul_inv_cancel₀ hab.ne'
    rw [hdet]
    exact mul_nonneg hh.le (sub_nonneg.mpr h1)

end
end MOC
