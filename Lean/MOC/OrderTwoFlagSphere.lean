import MOC.CompleteFlagOrbit
import MOC.FlagSuperlevelFiltration
import MOC.HomologicalRange
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Topology.Category.TopCat.Sphere

/-! The complete flag space in complex dimension two is a sphere.
Odd integral homology vanishing then needs the singular homology calculation of the sphere. -/

open CategoryTheory Matrix Polynomial

namespace MOC

noncomputable section

private def sphereSpectrum : Fin 2 → ℂ := ![1, -1]

private theorem sphereSpectrum_injective : Function.Injective sphereSpectrum := by
  intro i j h
  fin_cases i <;> fin_cases j <;> norm_num [sphereSpectrum] at h ⊢

private theorem mem_sphereSpectralOrbit_iff (A : Matrix (Fin 2) (Fin 2) ℂ) :
    A ∈ spectralFlagOrbit sphereSpectrum ↔ A.IsHermitian ∧ A.trace = 0 ∧ A.det = -1 := by
  constructor
  · rintro ⟨U, hU, rfl⟩
    have hD : (diagonal sphereSpectrum).IsHermitian := by
      rw [Matrix.IsHermitian, Matrix.diagonal_conjTranspose]
      apply congrArg diagonal
      funext i
      fin_cases i <;> simp [sphereSpectrum]
    have htrace : (diagonal sphereSpectrum).trace = 0 := by
      norm_num [Matrix.trace_diagonal, Fin.sum_univ_two, sphereSpectrum]
    have hdet : (diagonal sphereSpectrum).det = -1 := by
      norm_num [Matrix.det_diagonal, Fin.prod_univ_two, sphereSpectrum]
    refine ⟨?_, ?_, ?_⟩
    · rw [Matrix.IsHermitian, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
        Matrix.conjTranspose_conjTranspose, hD.eq, Matrix.mul_assoc]
    · rw [Matrix.trace_mul_cycle, hU.2, Matrix.one_mul, htrace]
    · rw [Matrix.det_mul, Matrix.det_mul, mul_right_comm, ← Matrix.det_mul, hU.1,
        Matrix.det_one, one_mul, hdet]
  · rintro ⟨hHermitian, htrace, hdet⟩
    apply (mem_spectralFlagOrbit_iff_normal_charpoly sphereSpectrum A).mpr
    refine ⟨hHermitian.isSelfAdjoint.isStarNormal, ?_⟩
    have hpoly : A.charpoly = Polynomial.X ^ 2 - Polynomial.X * C A.trace + C A.det := by
      simp only [Matrix.charpoly, Matrix.det_fin_two, Matrix.charmatrix_apply_eq,
        Matrix.charmatrix_apply_ne _ 0 1 (by decide),
        Matrix.charmatrix_apply_ne _ 1 0 (by decide), Matrix.trace_fin_two, map_add, map_sub,
        map_mul]
      ring
    rw [hpoly, htrace, hdet, Fin.prod_univ_two]
    simp only [sphereSpectrum, Matrix.cons_val_zero, Matrix.cons_val_one, map_zero, map_one,
      map_neg, mul_zero, sub_zero]
    ring

private def sphereMatrix (x : EuclideanSpace ℝ (Fin 3)) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(x 0 : ℂ), ⟨x 1, x 2⟩; star (⟨x 1, x 2⟩ : ℂ), -(x 0 : ℂ)]

private theorem sphereMatrix_hermitian (x : EuclideanSpace ℝ (Fin 3)) :
    (sphereMatrix x).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [sphereMatrix]

private theorem sphereMatrix_det (x : EuclideanSpace ℝ (Fin 3)) :
    (sphereMatrix x).det = ((-(x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2) : ℝ) : ℂ) := by
  rw [sphereMatrix, Matrix.det_fin_two_of, Complex.star_def, Complex.mul_conj]
  apply Complex.ext <;>
    simp only [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
      Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im, Complex.normSq_apply] <;> ring

private theorem norm_sq_sphereCoordinates (x : EuclideanSpace ℝ (Fin 3)) :
    ‖x‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_three]
  simp only [Real.norm_eq_abs, Real.sq_abs]

private theorem continuous_sphereMatrix : Continuous sphereMatrix := by
  have hc (i : Fin 3) : Continuous (fun x : EuclideanSpace ℝ (Fin 3) => x i) :=
    (EuclideanSpace.proj i).continuous
  have hd : Continuous (fun x : EuclideanSpace ℝ (Fin 3) => (x 0 : ℂ)) :=
    Complex.continuous_ofReal.comp (hc 0)
  have hz : Continuous (fun x : EuclideanSpace ℝ (Fin 3) => (⟨x 1, x 2⟩ : ℂ)) :=
    Complex.equivRealProdCLM.symm.continuous.comp ((hc 1).prodMk (hc 2))
  apply continuous_matrix
  intro i j
  fin_cases i <;> fin_cases j
  · exact hd
  · exact hz
  · exact hz.star
  · exact hd.neg

private def sphereToSpectralOrbit (x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    spectralFlagOrbit sphereSpectrum := by
  refine ⟨sphereMatrix x.val, (mem_sphereSpectralOrbit_iff _).mpr
    ⟨sphereMatrix_hermitian x.val, ?_, ?_⟩⟩
  · rw [sphereMatrix, Matrix.trace_fin_two_of, add_neg_cancel]
  · have hx := Metric.mem_sphere_zero_iff_norm.mp x.property
    rw [sphereMatrix_det, ← norm_sq_sphereCoordinates x.val, hx]
    norm_num

private theorem sphereToSpectralOrbit_bijective : Function.Bijective sphereToSpectralOrbit := by
  constructor
  · intro x y h
    apply Subtype.ext
    apply (EuclideanSpace.equiv (Fin 3) ℝ).injective
    funext i
    fin_cases i
    · exact congrArg (fun A : spectralFlagOrbit sphereSpectrum => (A.val 0 0).re) h
    · exact congrArg (fun A : spectralFlagOrbit sphereSpectrum => (A.val 0 1).re) h
    · exact congrArg (fun A : spectralFlagOrbit sphereSpectrum => (A.val 0 1).im) h
  · intro A
    obtain ⟨hHermitian, htrace, hdet⟩ := (mem_sphereSpectralOrbit_iff A.val).mp A.property
    let x : EuclideanSpace ℝ (Fin 3) :=
      (EuclideanSpace.equiv (Fin 3) ℝ).symm ![(A.val 0 0).re, (A.val 0 1).re, (A.val 0 1).im]
    have h00 : (x 0 : ℂ) = A.val 0 0 := by
      exact Complex.conj_eq_iff_re.mp (hHermitian.apply 0 0)
    have h01 : (⟨x 1, x 2⟩ : ℂ) = A.val 0 1 := Complex.ext rfl rfl
    have hxA : sphereMatrix x = A.val := by
      ext i j : 1
      fin_cases i <;> fin_cases j
      · exact h00
      · exact h01
      · change star (⟨x 1, x 2⟩ : ℂ) = A.val 1 0
        rw [h01, hHermitian.apply 1 0]
      · change -(x 0 : ℂ) = A.val 1 1
        rw [h00]
        rw [Matrix.trace_fin_two] at htrace
        linear_combination -htrace
    have hsq : ‖x‖ ^ 2 = 1 := by
      rw [← hxA, sphereMatrix_det, ← norm_sq_sphereCoordinates x] at hdet
      simpa only [Complex.neg_re, Complex.ofReal_re, Complex.one_re, neg_inj] using
        congrArg Complex.re hdet
    have hx : x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 := by
      rw [Metric.mem_sphere_zero_iff_norm]
      exact (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp (by simpa only [one_pow] using hsq)
    exact ⟨⟨x, hx⟩, Subtype.ext hxA⟩

/-- The complete flag space of complex dimension two is homeomorphic to the
unit sphere in real dimension three. -/
def orderTwoFlagSphereHomeomorph :
    (Matrix.unitaryGroup (Fin 2) ℂ ⧸ unitaryCoordinateTorus (Fin 2)) ≃ₜ
      Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 := by
  let e := Equiv.ofBijective sphereToSpectralOrbit sphereToSpectralOrbit_bijective
  have he : Continuous e := (continuous_sphereMatrix.comp continuous_subtype_val).subtype_mk _
  exact (completeFlagOrbitHomeomorph sphereSpectrum sphereSpectrum_injective).trans
    he.homeoOfEquivCompactToT2.symm

/-- The order-two complete flag space and the two-sphere have isomorphic integral
singular homology in every degree. -/
def orderTwoFlagSphereHomologyIso (k : ℕ) :
    (integralSingularHomology k).obj
      (TopCat.of (Matrix.unitaryGroup (Fin 2) ℂ ⧸ unitaryCoordinateTorus (Fin 2))) ≅
    (integralSingularHomology k).obj (TopCat.sphere 2) :=
  (integralSingularHomology k).mapIso
    (TopCat.isoOfHomeo (orderTwoFlagSphereHomeomorph.trans Homeomorph.ulift.symm))

end

end MOC
