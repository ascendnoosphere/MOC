import MOC.NormalOrbit
import MOC.SpectralStationarity
import Mathlib.Data.Matrix.Notation

/-! A balanced nonnormal maximum of determinant support and Frobenius norm. -/

open BigOperators Matrix

namespace MOC

noncomputable section

private theorem skew_adjoint_conjugate {ι : Type*} [Fintype ι]
    (D V : Matrix ι ι ℂ) (hD : Dᴴ = -D) : (V * D * Vᴴ)ᴴ = -(V * D * Vᴴ) := by
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hD,
    Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]

/-- Squared Frobenius norm is constant on this relative orbit because its
cross term vanishes for a Hermitian and a skew-Hermitian summand. -/
theorem frobeniusSq_hermitian_add_unitary_skew {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A D V : Matrix ι ι ℂ) (hA : A.IsHermitian) (hD : Dᴴ = -D) (hV : IsUnitary V) :
    frobeniusSq (A + V * D * Vᴴ) = frobeniusSq (A + D) := by
  have hf (B : Matrix ι ι ℂ) (hB : Bᴴ = -B) :
      frobeniusSq (A + B) = ((A * A).trace - (B * B).trace).re := by
    have he (M : Matrix ι ι ℂ) : frobeniusSq M = (M * Mᴴ).trace.re := by
      simp only [frobeniusSq, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
        Matrix.conjTranspose_apply, Complex.re_sum, Complex.star_def, Complex.mul_conj,
        Complex.ofReal_re]
    rw [he, Matrix.conjTranspose_add, hA.eq, hB]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_neg, Matrix.trace_add, Matrix.trace_neg,
      Matrix.trace_mul_comm B A, Complex.add_re, Complex.neg_re, Complex.sub_re]
    ring
  rw [hf _ (skew_adjoint_conjugate D V hD), hf D hD]
  have hs : (V * D * Vᴴ) * (V * D * Vᴴ) = V * (D * D) * Vᴴ := by
    calc
      _ = ((V * D) * (Vᴴ * V)) * D * Vᴴ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hV.2, Matrix.mul_one, Matrix.mul_assoc V D D]
  rw [hs, Matrix.trace_mul_comm (V * (D * D)) Vᴴ, ← Matrix.mul_assoc, hV.2, Matrix.one_mul]

private def balancedLeft : Fin 2 → ℂ :=
  ![((1 / 2 : ℝ) : ℂ), -((1 / 2 : ℝ) : ℂ)]

private def balancedRight : Fin 2 → ℂ :=
  ![((1 / 2 : ℝ) : ℂ) * Complex.I, -(((1 / 2 : ℝ) : ℂ) * Complex.I)]

private def balancedMixer : Matrix (Fin 2) (Fin 2) ℂ :=
  !![((3 / 5 : ℝ) : ℂ), ((-4 / 5 : ℝ) : ℂ);
     ((4 / 5 : ℝ) : ℂ), ((3 / 5 : ℝ) : ℂ)]

private theorem balancedLeft_hermitian : (diagonal balancedLeft).IsHermitian := by
  apply Matrix.isHermitian_diagonal_iff.mpr
  intro i
  fin_cases i <;> simp [balancedLeft, isSelfAdjoint_iff, Complex.star_def]

private theorem balancedRight_skew : (diagonal balancedRight)ᴴ = -diagonal balancedRight := by
  rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_neg]
  apply congrArg (fun d : Fin 2 → ℂ => diagonal d)
  funext i
  change star (balancedRight i) = -balancedRight i
  fin_cases i <;> simp [balancedRight, Complex.star_def, map_mul]

private theorem balancedMixer_star (i j : Fin 2) :
    star (balancedMixer i j) = balancedMixer i j := by
  fin_cases i <;> fin_cases j <;>
    simp only [balancedMixer, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Complex.star_def, Complex.conj_ofReal]

private theorem balancedMixer_unitary : IsUnitary balancedMixer := by
  constructor <;> apply Matrix.ext <;> intro i j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply, balancedMixer_star] <;>
    fin_cases i <;> fin_cases j <;>
    apply Complex.ext <;>
    norm_num [balancedMixer, Matrix.one_apply, Complex.add_re, Complex.add_im, Complex.mul_re,
      Complex.mul_im]

private theorem balanced_support_zero (V : Matrix (Fin 2) (Fin 2) ℂ) (hV : IsUnitary V) :
    (determinantValue balancedLeft balancedRight V).re = 0 := by
  let A := diagonal balancedLeft
  let D := diagonal balancedRight
  let B := V * D * Vᴴ
  have hA : Aᴴ = A := balancedLeft_hermitian.eq
  have hB : Bᴴ = -B := skew_adjoint_conjugate D V balancedRight_skew
  have hd : A.det + D.det = 0 := by
    simp only [A, D, Matrix.det_diagonal, Fin.prod_univ_two, balancedLeft, balancedRight,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [show (((1 / 2 : ℝ) : ℂ) * Complex.I) * -(((1 / 2 : ℝ) : ℂ) * Complex.I) =
      -(((1 / 2 : ℝ) : ℂ) * ((1 / 2 : ℝ) : ℂ)) * (Complex.I * Complex.I) by ring,
      Complex.I_mul_I]
    ring
  have he : (A + B).det + (A - B).det = 2 * (A.det + B.det) := by
    simp only [Matrix.det_fin_two, Matrix.add_apply, Matrix.sub_apply]
    ring
  have hs : (A - B).det = star ((A + B).det) := by
    rw [← Matrix.det_conjTranspose, Matrix.conjTranspose_add, hA, hB, sub_eq_add_neg]
  rw [hs, show B.det = D.det from det_unitary_conjugation V D hV, hd, mul_zero] at he
  have hre := congrArg Complex.re he
  simp only [Complex.add_re, Complex.star_def, Complex.conj_re, Complex.zero_re] at hre
  change (A + B).det.re = 0
  linarith only [hre]

private theorem balanced_sum_explicit :
    diagonal balancedLeft + balancedMixer * diagonal balancedRight * balancedMixerᴴ =
    !![⟨1 / 2, -7 / 50⟩, ⟨0, 12 / 25⟩; ⟨0, 12 / 25⟩, ⟨-1 / 2, 7 / 50⟩] := by
  have hmul (i j : Fin 2) :
      (balancedMixer * diagonal balancedRight * balancedMixerᴴ) i j =
        balancedMixer i 0 * balancedRight 0 * balancedMixer j 0 +
          balancedMixer i 1 * balancedRight 1 * balancedMixer j 1 := by
    rw [Matrix.mul_apply, Fin.sum_univ_two]
    simp only [Matrix.mul_diagonal, Matrix.conjTranspose_apply, balancedMixer_star]
  apply Matrix.ext
  intro i j
  simp only [Matrix.add_apply, hmul]
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    norm_num [balancedLeft, balancedRight, balancedMixer, Matrix.diagonal_apply,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]

/-- Equal traces, equal cubic moments, unit spectral energy, and both orbit
maximality conditions allow a nonsingular nonnormal sum in order two.
The determinant is in the matching hull and the real support gap is zero. -/
theorem exists_balanced_nonnormal_orbit_maximum :
    ∃ (a b : Fin 2 → ℂ) (U : Matrix (Fin 2) (Fin 2) ℂ),
      IsUnitary U ∧ spectralEnergy a b = 1 ∧
      (∑ i, a i) = (∑ i, b i) ∧
      (∑ i, (Complex.normSq (a i) : ℂ) * a i) =
        (∑ i, (Complex.normSq (b i) : ℂ) * b i) ∧
      determinantValue a b U ≠ 0 ∧ ¬ IsStarNormal (diagonal a + U * diagonal b * Uᴴ) ∧
      Holds a b U ∧
      (∀ V : Matrix (Fin 2) (Fin 2) ℂ, IsUnitary V →
        (determinantValue a b V).re = 0 ∧
        frobeniusSq (diagonal a + V * diagonal b * Vᴴ) =
          frobeniusSq (diagonal a + U * diagonal b * Uᴴ)) := by
  refine ⟨balancedLeft, balancedRight, balancedMixer, balancedMixer_unitary, ?_, ?_, ?_,
    ?_, ?_, conjecture_two _ _ _ balancedMixer_unitary, ?_⟩
  · norm_num [spectralEnergy, Fin.sum_univ_two, balancedLeft, balancedRight, Complex.normSq_apply,
      Complex.mul_re, Complex.mul_im]
  · simp [Fin.sum_univ_two, balancedLeft, balancedRight]
  · simp [Fin.sum_univ_two, balancedLeft, balancedRight]
  · intro hn
    have hi := congrArg Complex.im hn
    norm_num [determinantValue, balanced_sum_explicit, Matrix.det_fin_two, Complex.sub_im,
      Complex.mul_im] at hi
  · intro hn
    have hc := hn.star_comm_self.eq
    rw [Matrix.star_eq_conjTranspose, balanced_sum_explicit] at hc
    have hi := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => (M 0 1).im) hc
    norm_num [Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply, Complex.star_def,
      Complex.add_im, Complex.mul_im] at hi
  · intro V hV
    refine ⟨balanced_support_zero V hV, ?_⟩
    rw [frobeniusSq_hermitian_add_unitary_skew _ _ V balancedLeft_hermitian balancedRight_skew hV,
      frobeniusSq_hermitian_add_unitary_skew _ _ balancedMixer balancedLeft_hermitian
        balancedRight_skew balancedMixer_unitary]

end

end MOC
