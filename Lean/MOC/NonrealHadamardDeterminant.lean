import MOC.RankTwoKernelInclusion
import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Mathlib.Tactic.FinCases

/-! A rank-three identity kernel has only zero-one products but its
normalized Hadamard determinant has positive imaginary part. -/

open BigOperators Matrix

namespace MOC.NonrealHadamardDeterminant

noncomputable section

private def numerator : Matrix (Fin 3) (Fin 3) GaussianInt :=
  !![⟨45,64⟩, 60, ⟨48,60⟩; ⟨-60,48⟩, 45, ⟨36,-80⟩; ⟨0,60⟩, -100, 45]

def complexMixer : Matrix (Fin 3) (Fin 3) ℂ :=
  (1 / 125 : ℂ) • numerator.map GaussianInt.toComplex

theorem isUnitary_complexMixer : IsUnitary complexMixer := by
  let g := GaussianInt.toComplex
  have hInt : numerator * numeratorᴴ =
      (15625 : GaussianInt) • (1 : Matrix (Fin 3) (Fin 3) GaussianInt) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  have hG := congrArg (fun M : Matrix (Fin 3) (Fin 3) GaussianInt => M.map g) hInt
  have hstar := Matrix.conjTranspose_map (A := numerator) g GaussianInt.toComplex_star
  simp only [Matrix.map_mul, hstar, Matrix.map_smul' g _ _ (map_mul g), map_ofNat,
    Matrix.map_one g (map_zero g) (map_one g)] at hG
  have hU : complexMixer * complexMixerᴴ = 1 := by
    unfold complexMixer
    change ((1 / 125 : ℂ) • numerator.map g) *
      ((1 / 125 : ℂ) • numerator.map g)ᴴ = 1
    simp only [Matrix.conjTranspose_smul, star_div₀, star_one, star_ofNat, Matrix.smul_mul,
      Matrix.mul_smul, smul_smul, hG]
    norm_num [smul_smul]
  exact ⟨hU, Matrix.mul_eq_one_comm.mp hU⟩

theorem complexMixer_det : complexMixer.det = 1 := by
  have h : numerator.det = (125 : GaussianInt)^3 := by
    rw [Matrix.det_fin_three]
    decide +kernel
  have hm := congrArg GaussianInt.toComplex h
  simp only [RingHom.map_det, RingHom.mapMatrix_apply, map_pow, map_ofNat] at hm
  rw [complexMixer, Matrix.det_smul, Fintype.card_fin, hm]
  norm_num

theorem identity_kernel_value :
    kernelDeterminantValue (1 : Matrix (Fin 3) (Fin 3) ℂ) complexMixer =
      729/15625 + (5184/78125) * Complex.I := by
  have h : (Matrix.of fun i j : Fin 3 =>
      (1 : Matrix (Fin 3) (Fin 3) ℂ) i j * complexMixer i j) =
      diagonal (fun i => complexMixer i i) := by
    ext i j
    by_cases h : i = j <;> simp [h, Matrix.one_apply, Matrix.diagonal_apply]
  rw [kernelDeterminantValue, h, Matrix.det_diagonal, complexMixer_det, div_one]
  norm_num [Fin.prod_univ_three, complexMixer, numerator, GaussianInt.toComplex_def',
    Complex.ext_iff, Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im,
    Complex.normSq_apply]

/-- The separation takes place already at the identity matrix of rank three. -/
theorem identity_kernel_outside_hull :
    kernelDeterminantValue (1 : Matrix (Fin 3) (Fin 3) ℂ) complexMixer ∉
      convexHull ℝ (Set.range (fun σ : Equiv.Perm (Fin 3) =>
        ∏ i, (1 : Matrix (Fin 3) (Fin 3) ℂ) i (σ i))) := by
  intro h
  have hsub : Set.range (fun σ : Equiv.Perm (Fin 3) =>
      ∏ i, (1 : Matrix (Fin 3) (Fin 3) ℂ) i (σ i)) ⊆ {z : ℂ | z.im ≤ 0} := by
    rintro _ ⟨σ, rfl⟩
    change (∏ i, (1 : Matrix (Fin 3) (Fin 3) ℂ) i (σ i)).im ≤ 0
    by_cases hfix : ∀ i, i = σ i
    · have hone : (∏ i, (1 : Matrix (Fin 3) (Fin 3) ℂ) i (σ i)) = 1 :=
        Finset.prod_eq_one (fun i _ => by simp [Matrix.one_apply, hfix i])
      rw [hone]
      norm_num
    · obtain ⟨i, hi⟩ := not_forall.mp hfix
      rw [Finset.prod_eq_zero (Finset.mem_univ i) (by simp [Matrix.one_apply, hi])]
      norm_num
  have hi := convexHull_min hsub (convex_halfSpace_le Complex.imLm.isLinear 0) h
  change (kernelDeterminantValue _ complexMixer).im ≤ 0 at hi
  rw [identity_kernel_value] at hi
  norm_num [Complex.mul_im] at hi

end

end MOC.NonrealHadamardDeterminant
