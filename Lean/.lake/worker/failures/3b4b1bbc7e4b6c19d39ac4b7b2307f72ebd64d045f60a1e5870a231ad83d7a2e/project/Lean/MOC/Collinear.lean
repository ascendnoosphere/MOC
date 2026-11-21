import MOC.Geometry
import MOC.NormalOrbit
import MOC.Support

/-! Determinant hull inclusion for spectra on parallel affine lines. -/

open BigOperators Matrix

namespace MOC

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem real_diagonal_isHermitian (a : ι → ℝ) :
    (diagonal fun i => (a i : ℂ)).IsHermitian := by
  apply Matrix.isHermitian_diagonal_iff.mpr
  intro i
  simp [isSelfAdjoint_iff, Complex.star_def]

private theorem isStarNormal_add_scalar (H : Matrix ι ι ℂ) (hH : H.IsHermitian) (z : ℂ) :
    IsStarNormal (H + Matrix.scalar ι z) := by
  have hs : (Matrix.scalar ι z)ᴴ = Matrix.scalar ι (star z) := by
    simp only [Matrix.scalar_apply, Matrix.diagonal_conjTranspose, Pi.star_apply]
  have hc (q : ℂ) (M : Matrix ι ι ℂ) : Commute (Matrix.scalar ι q) M :=
    Matrix.scalar_commute q (Commute.all q) M
  constructor
  change Commute (H + Matrix.scalar ι z)ᴴ (H + Matrix.scalar ι z)
  rw [Matrix.conjTranspose_add, hH.eq, hs]
  exact ((Commute.refl H).add_right (hc z H).symm).add_left
    ((hc (star z) H).add_right (hc (star z) (Matrix.scalar ι z)))

/-- An arbitrary constant offset may separate the two real spectral lines. -/
theorem holds_of_real_spectra_with_offset (a b : ι → ℝ) (z : ℂ)
    (U : Matrix ι ι ℂ) (hU : IsUnitary U) :
    Holds (fun i => (a i : ℂ)) (fun i => (b i : ℂ) + z) U := by
  let x (i : ι) : ℂ := a i
  let y (i : ι) : ℂ := (b i : ℂ) + z
  let y₀ (i : ι) : ℂ := b i
  apply (holds_iff_directional x y U).mpr
  intro η
  obtain ⟨V, hV, hmax, htie⟩ := exists_support_frobenius_maximizer x y η
  have hd : diagonal y = diagonal y₀ + Matrix.scalar ι z :=
    (Matrix.diagonal_add y₀ (fun _ => z)).symm
  have hz : Matrix.scalar ι z = z • (1 : Matrix ι ι ℂ) := (Matrix.smul_one_eq_diagonal z).symm
  have hB : V * diagonal y * Vᴴ = V * diagonal y₀ * Vᴴ + Matrix.scalar ι z := by
    rw [hd, Matrix.mul_add, Matrix.add_mul, hz, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_one, hV.1]
  have hH : (diagonal x + V * diagonal y₀ * Vᴴ).IsHermitian :=
    (real_diagonal_isHermitian a).add
      (Matrix.isHermitian_mul_mul_conjTranspose V (real_diagonal_isHermitian b))
  have hC : IsStarNormal (diagonal x + V * diagonal y * Vᴴ) := by
    rw [hB, ← add_assoc]
    exact isStarNormal_add_scalar _ hH z
  have hholds := holds_of_normal_support_frobenius_maximum x y hV η hC hmax htie
  obtain ⟨σ, hσ⟩ := (holds_iff_directional x y V).mp hholds η
  exact ⟨σ, (hmax U hU).trans hσ⟩

/-- Two spectra with independent complex offsets and a common line direction
satisfy the determinant hull inclusion in every finite order. -/
theorem holds_of_parallel_affine_lines (a b : ι → ℝ) (c s t : ℂ)
    (U : Matrix ι ι ℂ) (hU : IsUnitary U) :
    Holds (fun i => c * (a i : ℂ) + s) (fun i => c * (b i : ℂ) + t) U := by
  by_cases hc : c = 0
  · simp only [hc, zero_mul, zero_add]
    exact holds_of_commute _ _ hU (Matrix.scalar_commute t (Commute.all t) U).symm
  · let z := (s + t) / c
    let x (i : ι) : ℂ := a i
    let y (i : ι) : ℂ := (b i : ℂ) + z
    have hz : c * z = s + t := by rw [mul_comm, div_mul_cancel₀ _ hc]
    have hscaled : Holds (fun i => c * x i) (fun i => c * y i) U :=
      hull_of_common_factor (determinantValue_scale x y U c) (matchingProduct_scale x y c)
        (holds_of_real_spectra_with_offset a b z U hU)
    have hy : (fun i => c * y i - s) = fun i => c * (b i : ℂ) + t := by
      funext i
      dsimp only [y]
      rw [mul_add, hz]
      ring
    simpa only [x, hy] using (holds_shift_iff (fun i => c * x i) (fun i => c * y i) hU s).mpr hscaled

end

end MOC
