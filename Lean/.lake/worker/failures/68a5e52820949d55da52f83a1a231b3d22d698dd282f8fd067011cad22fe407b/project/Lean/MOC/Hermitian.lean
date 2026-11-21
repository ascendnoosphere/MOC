import MOC.Geometry
import MOC.Normal
import MOC.Singular
import MOC.Support
import MOC.Variational

/-! The determinant support bound for two Hermitian summands, following Fiedler's
variational argument, and its transport to a common affine spectral line. -/

open BigOperators Matrix

namespace MOC

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem det_im_zero_of_hermitian {A : Matrix ι ι ℂ} (hA : A.IsHermitian) :
    A.det.im = 0 := by
  have h := (Matrix.det_conjTranspose A).symm.trans (congrArg Matrix.det hA.eq)
  have h' := congrArg Complex.im h
  simp only [Complex.star_def, Complex.conj_im] at h'
  linarith only [h']

/-- When both summands are Hermitian, a nonsingular support maximum in a direction
with nonzero real part has commuting summands. -/
theorem commute_of_hermitian_support_maximum (A B : Matrix ι ι ℂ) (η : ℂ)
    (hA : A.IsHermitian) (hB : B.IsHermitian) (hη : η.re ≠ 0) (hdet : (A + B).det ≠ 0)
    (hmax : ∀ V : Matrix ι ι ℂ, IsUnitary V →
      (η * (A + V * B * Vᴴ).det).re ≤ (η * (A + B).det).re) : Commute A B := by
  let C := A + B
  let κ := η * C.det
  let E := B * C⁻¹ - C⁻¹ * B
  have hC := hA.add hB
  have hdetim : C.det.im = 0 := det_im_zero_of_hermitian hC
  have hdetre : C.det.re ≠ 0 := fun hz => hdet (Complex.ext hz hdetim)
  have hκre : κ.re ≠ 0 := by
    change (η * C.det).re ≠ 0
    rw [Complex.mul_re, hdetim, mul_zero, sub_zero]
    exact mul_ne_zero hη hdetre
  have hκ : κ + star κ ≠ 0 := by
    intro he
    have he' := congrArg Complex.re he
    simp only [Complex.add_re, Complex.star_def, Complex.conj_re, Complex.zero_re] at he'
    exact hκre (by linarith only [he'])
  have hE : Eᴴ = -E := by
    simp only [E, Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, hB.eq,
      (show (C⁻¹)ᴴ = C⁻¹ from hC.inv), neg_sub]
  have hstat := support_maximum_inverse_commutator A B η hdet hmax
  change (κ • E)ᴴ = κ • E at hstat
  rw [Matrix.conjTranspose_smul, hE, smul_neg] at hstat
  have hzero : (κ + star κ) • E = 0 := by
    rw [add_smul, ← hstat, neg_add_cancel]
  have hc : B * C⁻¹ = C⁻¹ * B := sub_eq_zero.mp ((smul_eq_zero.mp hzero).resolve_left hκ)
  have hunit : IsUnit C.det := isUnit_iff_ne_zero.mpr hdet
  have hCB : C * B = B * C := by
    calc
      C * B = C * ((B * C⁻¹) * C) := by
        rw [Matrix.mul_assoc B, C.nonsing_inv_mul hunit, Matrix.mul_one]
      _ = C * ((C⁻¹ * B) * C) := by rw [hc]
      _ = B * C := by
        rw [← Matrix.mul_assoc C, ← Matrix.mul_assoc C C⁻¹, C.mul_nonsing_inv hunit, Matrix.one_mul]
  change (A + B) * B = B * (A + B) at hCB
  rw [Matrix.add_mul, Matrix.mul_add] at hCB
  exact add_right_cancel hCB

private theorem real_diagonal_hermitian (a : ι → ℝ) :
    (diagonal fun i => (a i : ℂ)).IsHermitian := by
  apply Matrix.isHermitian_diagonal_iff.mpr
  intro i
  simp [isSelfAdjoint_iff, Complex.star_def]

/-- The full determinant hull inclusion when both spectra are real, in every finite order. -/
theorem holds_of_real_spectra (a b : ι → ℝ) (U : Matrix ι ι ℂ) (hU : IsUnitary U) :
    Holds (fun i => (a i : ℂ)) (fun i => (b i : ℂ)) U := by
  let a' (i : ι) : ℂ := a i
  let b' (i : ι) : ℂ := b i
  have ha : (diagonal a').IsHermitian := real_diagonal_hermitian a
  have hb (V : Matrix ι ι ℂ) : (V * diagonal b' * Vᴴ).IsHermitian :=
    Matrix.isHermitian_mul_mul_conjTranspose V (real_diagonal_hermitian b)
  apply (holds_iff_directional a' b' U).mpr
  intro η
  by_cases hη : η.re = 0
  · refine ⟨1, ?_⟩
    have hd : (determinantValue a' b' U).im = 0 := det_im_zero_of_hermitian (ha.add (hb U))
    have hp : (matchingProduct a' b' 1).im = 0 := by
      unfold matchingProduct a' b'
      simp only [← Complex.ofReal_add, ← Complex.ofReal_prod, Complex.ofReal_im]
    simp only [Complex.mul_re, hη, hd, hp, zero_mul, mul_zero, sub_zero, le_refl]
  obtain ⟨V, hV, hmax⟩ := exists_support_maximizer a' b' η
  have hholds : Holds a' b' V := by
    by_cases hdet : determinantValue a' b' V = 0
    · exact holds_of_singular a' b' hV hdet
    apply holds_of_commuting_hermitian a' b' hV ha (hb V)
    apply commute_of_hermitian_support_maximum _ _ η ha (hb V) hη hdet
    intro W hW
    have hWt : IsUnitary Wᴴ := ⟨by simpa using hW.2, by simpa using hW.1⟩
    have hWV : IsUnitary (W * V) := by simpa using relative_unitary Wᴴ V hWt hV
    simpa only [determinantValue, Matrix.conjTranspose_mul, Matrix.mul_assoc] using hmax (W * V) hWV
  obtain ⟨σ, hσ⟩ := (holds_iff_directional a' b' V).mp hholds η
  exact ⟨σ, (hmax U hU).trans hσ⟩

/-- In the difference convention the two spectra lie on the same affine line.
Opposite shifts and common complex scaling transport the real-spectra result. -/
theorem holds_of_common_affine_line (a b : ι → ℝ) (c t : ℂ)
    (U : Matrix ι ι ℂ) (hU : IsUnitary U) :
    Holds (fun i => c * a i + t) (fun i => c * b i - t) U := by
  apply (holds_shift_iff (fun i => c * a i) (fun i => c * b i) hU t).mpr
  unfold Holds
  apply hull_of_common_factor (determinantValue_scale _ _ U c)
    (matchingProduct_scale _ _ c)
  exact holds_of_real_spectra a b U hU

end

end MOC
