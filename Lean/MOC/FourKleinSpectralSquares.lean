import MOC.FourKleinInversePencil
import MOC.SpectralProfileDeterminant
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Topology.Instances.Real.Lemmas

/-! Actual spectral costs on the normal Klein-four face. -/

open BigOperators Matrix

namespace MOC

noncomputable section

private abbrev KleinSplitIndex := Fin 1 ⊕ Fin 3

private def kleinIndexEquiv : KleinSplitIndex ≃ Fin 4 := finSumFinEquiv

private def kleinSourcePerm : Fin 24 ≃ Equiv.Perm KleinSplitIndex :=
  (fourPermEquiv.trans (Equiv.inv FourPerm)).trans (kleinIndexEquiv.symm.permCongr)

private theorem kleinSourcePerm_apply (j : Fin 24) (i : KleinSplitIndex) :
    kleinIndexEquiv (kleinSourcePerm j i) = (fourPerm j).symm (kleinIndexEquiv i) := by
  change kleinIndexEquiv ((kleinIndexEquiv.symm.permCongr (fourPerm j).symm) i) = _
  simp only [Equiv.permCongr_apply, Equiv.symm_symm, Equiv.apply_symm_apply]

private theorem kleinSourcePerm_sign (j : Fin 24) :
    (Equiv.Perm.sign (kleinSourcePerm j) : ℤ) = kleinPermutationSign j := by
  change (Equiv.Perm.sign (kleinIndexEquiv.symm.permCongr (fourPerm j).symm) : ℤ) = _
  rw [Equiv.Perm.sign_permCongr, Equiv.Perm.sign_symm, kleinPermutationSign_eq]

def kleinComplexification : Matrix (Fin 3) (Fin 3) ℝ →ₗ[ℝ] Matrix (Fin 3) (Fin 3) ℂ where
  toFun H := Complex.ofRealHom.mapMatrix H
  map_add' H K := map_add Complex.ofRealHom.mapMatrix H K
  map_smul' r H := by
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.smul_apply,
      Complex.ofRealHom_eq_coe, Complex.real_smul, smul_eq_mul, Complex.ofReal_mul] <;> rfl

private theorem klein_tetrahedral_entry (i : KleinSplitIndex) (j : Fin 3) :
    SpectralProfile.tetrahedralFrame i (.inr j) =
      ((kleinTetrahedralColumns (kleinIndexEquiv i) j : ℝ) : ℂ) := by
  let E : Matrix (Fin 4) (Fin 4) ℂ :=
    (1 / 2 : ℂ) • !![1, 1, 1, 1; 1, 1, -1, -1; 1, -1, 1, -1; 1, -1, -1, 1]
  change E (kleinIndexEquiv i) (kleinIndexEquiv (.inr j)) = _
  obtain ⟨k, rfl⟩ := kleinIndexEquiv.symm.surjective i
  rw [kleinIndexEquiv.apply_symm_apply]
  change E k (Fin.natAdd 1 j) = _
  fin_cases k <;> fin_cases j <;>
    norm_num [E, kleinTetrahedralColumns, Matrix.smul_apply, Matrix.of_apply,
      Matrix.cons_val, smul_eq_mul]

private theorem klein_centered_entry (K : Matrix (Fin 3) (Fin 3) ℝ)
    (i j : KleinSplitIndex) :
    SpectralProfile.centeredEmbed SpectralProfile.tetrahedralFrame
      SpectralProfile.tetrahedralFrameᵀ (kleinComplexification K) i j =
        ((kleinCenteredMatrix K (kleinIndexEquiv i) (kleinIndexEquiv j) : ℝ) : ℂ) := by
  simp only [SpectralProfile.centeredEmbed, kleinCenteredMatrix, Matrix.mul_apply,
    Matrix.transpose_apply, Fintype.sum_sum_type, Matrix.fromBlocks_apply₁₁,
    Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
    Matrix.zero_apply, mul_zero, Finset.sum_const_zero, zero_mul, zero_add,
    klein_tetrahedral_entry, kleinComplexification, LinearMap.coe_mk, AddHom.coe_mk,
    RingHom.mapMatrix_apply, Matrix.map_apply, Complex.ofRealHom_eq_coe, Complex.ofReal_sum,
    Complex.ofReal_mul]

private theorem klein_matching_reindex (a b : Fin 4 → ℂ) (j : Fin 24) :
    matchingProduct (a ∘ kleinIndexEquiv) (b ∘ kleinIndexEquiv) (kleinSourcePerm j) =
      matchingProduct a b (fourPerm j).symm := by
  unfold matchingProduct
  exact Fintype.prod_equiv kleinIndexEquiv _ _
    (fun i => by simp only [Function.comp_apply, kleinSourcePerm_apply])

private theorem klein_signed_reindex (g : Fin 24 → ℂ) (K : Matrix (Fin 3) (Fin 3) ℝ) :
    SpectralProfile.signedEvaluation (g ∘ kleinSourcePerm.symm)
      (SpectralProfile.centeredEmbed SpectralProfile.tetrahedralFrame
        SpectralProfile.tetrahedralFrameᵀ (kleinComplexification K)) =
      ∑ j, (kleinPermutationSign j : ℂ) * g j *
        ((∏ i : Fin 4, kleinCenteredMatrix K i (fourPerm j i) : ℝ) : ℂ) := by
  unfold SpectralProfile.signedEvaluation
  rw [← Equiv.sum_comp kleinSourcePerm]
  apply Finset.sum_congr rfl
  intro j _
  rw [kleinSourcePerm_sign]
  simp only [Function.comp_apply, Equiv.symm_apply_apply, klein_centered_entry, kleinSourcePerm_apply]
  congr 2
  rw [Complex.ofReal_prod]
  calc
    _ = ∏ k : Fin 4, ((kleinCenteredMatrix K ((fourPerm j).symm k) k : ℝ) : ℂ) :=
      Fintype.prod_equiv kleinIndexEquiv _ _ (fun _ => rfl)
    _ = _ := by
      rw [← Equiv.prod_comp (fourPerm j)]
      simp only [Equiv.symm_apply_apply]

def kleinRealCost (a b : Fin 4 → ℂ) (η : ℂ) (h : ℝ) : Fin 24 → ℝ :=
  fun j => h - (η * matchingProduct a b (fourPerm j).symm).re

theorem kleinSignedCost_spectral (a b : Fin 4 → ℂ) (η : ℂ) (h : ℝ)
    (K H : Matrix (Fin 3) (Fin 3) ℝ) (hHK : Hᵀ * K = 1) (hKH : K * Hᵀ = 1) :
    kleinSignedCost (kleinRealCost a b η h) (kleinCenteredMatrix K) =
      -(K.det ^ 2 * (η * SpectralProfile.tetrahedralInverseProfile a b
        (kleinComplexification H)).re) := by
  let g (j : Fin 24) : ℂ := (h : ℂ) - η * matchingProduct a b (fourPerm j).symm
  have hre (j : Fin 24) : (g j).re = kleinRealCost a b η h j := by
    simp only [g, Complex.sub_re, Complex.ofReal_re, kleinRealCost]
  have heval := congrArg Complex.re (klein_signed_reindex g K)
  simp only [Complex.re_sum, Complex.mul_re, Complex.mul_im, Complex.intCast_re,
    Complex.intCast_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero,
    sub_zero, zero_add, hre] at heval
  change (SpectralProfile.signedEvaluation (g ∘ kleinSourcePerm.symm)
      (SpectralProfile.centeredEmbed SpectralProfile.tetrahedralFrame
        SpectralProfile.tetrahedralFrameᵀ (kleinComplexification K))).re =
      kleinSignedCost (kleinRealCost a b η h) (kleinCenteredMatrix K) at heval
  have htranspose : (Complex.ofRealHom.mapMatrix H)ᵀ = Complex.ofRealHom.mapMatrix Hᵀ := by
    ext i j
    rfl
  have hmap1 : (kleinComplexification H)ᵀ * kleinComplexification K = 1 := by
    change (Complex.ofRealHom.mapMatrix H)ᵀ * Complex.ofRealHom.mapMatrix K = 1
    rw [htranspose, ← map_mul, hHK, map_one]
  have hmap2 : kleinComplexification K * (kleinComplexification H)ᵀ = 1 := by
    change Complex.ofRealHom.mapMatrix K * (Complex.ofRealHom.mapMatrix H)ᵀ = 1
    rw [htranspose, ← map_mul, hKH, map_one]
  have hs := SpectralProfile.signedEvaluation_inverseCoordinates
    (a ∘ kleinIndexEquiv) (b ∘ kleinIndexEquiv)
    SpectralProfile.tetrahedralFrame SpectralProfile.tetrahedralFrameᵀ
    SpectralProfile.tetrahedralFrame_mul_transpose SpectralProfile.tetrahedralFrame_transpose_mul
    (kleinComplexification K) (kleinComplexification H) hmap1 hmap2
  let S := SpectralProfile.centeredEmbed SpectralProfile.tetrahedralFrame
    SpectralProfile.tetrahedralFrameᵀ (kleinComplexification K)
  change SpectralProfile.signedEvaluation (matchingProduct (a ∘ kleinIndexEquiv)
    (b ∘ kleinIndexEquiv)) S =
      (kleinComplexification K).det ^ 2 *
        SpectralProfile.tetrahedralInverseProfile a b (kleinComplexification H) at hs
  have hg : g ∘ kleinSourcePerm.symm = fun σ => (h : ℂ) -
      η * matchingProduct (a ∘ kleinIndexEquiv) (b ∘ kleinIndexEquiv) σ := by
    funext σ
    obtain ⟨j, rfl⟩ := kleinSourcePerm.surjective σ
    simp only [Function.comp_apply, Equiv.symm_apply_apply, g, klein_matching_reindex]
  have hsum : SpectralProfile.signedEvaluation (g ∘ kleinSourcePerm.symm) S =
      SpectralProfile.signedEvaluation (fun _ => (h : ℂ)) S -
        η * SpectralProfile.signedEvaluation (matchingProduct (a ∘ kleinIndexEquiv)
          (b ∘ kleinIndexEquiv)) S := by
    rw [hg]
    unfold SpectralProfile.signedEvaluation
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [show SpectralProfile.signedEvaluation (fun _ => (h : ℂ)) S = 0 from
    SpectralProfile.signedEvaluation_const_centeredEmbed h _ _ _, zero_sub, hs] at hsum
  have hdet : (kleinComplexification K).det = (K.det : ℂ) :=
    (RingHom.map_det Complex.ofRealHom K).symm
  rw [← heval, hsum, hdet, ← Complex.ofReal_pow, mul_left_comm η,
    Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

private theorem klein_spectral_prism_of_invertible (a b : Fin 4 → ℂ) (η : ℂ) (h : ℝ)
    (β p q : Fin 3 → ℝ) (c : ℝ) (hcost : kleinRealCost a b η h = kleinMatchingCost β p q c)
    (H : Matrix (Fin 3) (Fin 3) ℝ) (hn : H.det ≠ 0) :
    kleinPrismForm β p q c (kleinPrismInput H) =
      ((-8 * η) * SpectralProfile.tetrahedralInverseProfile a b (kleinComplexification H)).re := by
  let K := (Hᵀ)⁻¹
  have hunit : IsUnit (Hᵀ).det := isUnit_iff_ne_zero.mpr (by rwa [Matrix.det_transpose])
  have hKH : K * Hᵀ = 1 := Matrix.nonsing_inv_mul _ hunit
  have hHK : Hᵀ * K = 1 := Matrix.mul_nonsing_inv _ hunit
  have hK : K.det ≠ 0 := by
    have hm := congrArg Matrix.det hKH
    rw [Matrix.det_mul, Matrix.det_one] at hm
    intro he
    rw [he, zero_mul] at hm
    exact zero_ne_one hm
  have hv := klein_signedCost_eq_inversePrism β p q c K H hKH
  rw [← hcost, kleinSignedCost_spectral a b η h K H hHK hKH] at hv
  have hphase (z : ℂ) : ((-8 * η) * z).re = -(8 * (η * z).re) := by
    rw [show (-8 * η) * z = ((-8 : ℝ) : ℂ) * (η * z) by push_cast; ring]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
      neg_mul]
  rw [hphase]
  apply mul_left_cancel₀ (pow_ne_zero 2 hK)
  linear_combination -hv

/-- A continuous formula for the real part of the tetrahedral spectral
profile extends through singular inverse coordinates. -/
theorem klein_tetrahedral_continuous_eq_of_invertible (a b : Fin 4 → ℂ) (η : ℂ)
    (Q : Matrix (Fin 3) (Fin 3) ℝ → ℝ) (hQ : Continuous Q)
    (h : ∀ H : Matrix (Fin 3) (Fin 3) ℝ, H.det ≠ 0 →
      Q H = (η * SpectralProfile.tetrahedralInverseProfile a b (kleinComplexification H)).re)
    (H : Matrix (Fin 3) (Fin 3) ℝ) :
    Q H = (η * SpectralProfile.tetrahedralInverseProfile a b (kleinComplexification H)).re := by
  let M (t : ℝ) : Matrix (Fin 3) (Fin 3) ℝ := t • 1 - (-H)
  let bad : Set ℝ := ((-H).charpoly.roots.toFinset : Set ℝ)
  have hdense : Dense badᶜ := (Finset.finite_toSet _).countable.dense_compl ℝ
  have hinvert (t : ℝ) (ht : t ∈ badᶜ) : (M t).det ≠ 0 := by
    intro hz
    apply ht
    change t ∈ (-H).charpoly.roots.toFinset
    rw [Multiset.mem_toFinset, Polynomial.mem_roots (Matrix.charpoly_monic (-H)).ne_zero]
    change (-H).charpoly.eval t = 0
    rw [Matrix.charpoly, Matrix.eval_det, Matrix.matPolyEquiv_charmatrix,
      Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    simpa only [M, Matrix.smul_one_eq_diagonal] using hz
  obtain ⟨l, hl⟩ := SpectralProfile.tetrahedralInverseProfile_four_squares a b η
  let f (t : ℝ) := Q (M t)
  let g (t : ℝ) := (η * SpectralProfile.tetrahedralInverseProfile a b (kleinComplexification (M t))).re
  have hf : Continuous f := by
    apply hQ.comp
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    dsimp only [M]
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.neg_apply, smul_eq_mul]
    fun_prop
  have hC : Continuous (fun t => kleinComplexification (M t)) := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    change Continuous (fun t => (((M t) i j : ℝ) : ℂ))
    simp only [M, Matrix.sub_apply, Matrix.smul_apply, Matrix.neg_apply, smul_eq_mul]
    fun_prop
  have hcont (i : Fin 4) : Continuous (fun t => l i (kleinComplexification (M t))) :=
    (l i).continuous_of_finiteDimensional.comp hC
  have hg : Continuous g := by
    simp only [g, hl, Complex.re_sum]
    fun_prop
  have heq : badᶜ ⊆ {t : ℝ | f t = g t} :=
    fun t ht => h (M t) (hinvert t ht)
  have h0 := closure_minimal heq (isClosed_eq hf hg) (hdense 0)
  have hM : M 0 = H := by simp only [M, zero_smul, zero_sub, neg_neg]
  simpa only [Set.mem_setOf_eq, f, g, hM] using h0

private theorem klein_spectral_prism (a b : Fin 4 → ℂ) (η : ℂ) (h : ℝ)
    (β p q : Fin 3 → ℝ) (c : ℝ) (hcost : kleinRealCost a b η h = kleinMatchingCost β p q c)
    (H : Matrix (Fin 3) (Fin 3) ℝ) :
    kleinPrismForm β p q c (kleinPrismInput H) =
      ((-8 * η) * SpectralProfile.tetrahedralInverseProfile a b (kleinComplexification H)).re := by
  apply klein_tetrahedral_continuous_eq_of_invertible a b (-8 * η)
    (fun X => kleinPrismForm β p q c (kleinPrismInput X)) _
    (klein_spectral_prism_of_invertible a b η h β p q c hcost) H
  simp only [kleinPrismForm, kleinPrismInput, kleinPrismOff, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
  fun_prop

private theorem klein_cost_eval (a b : Fin 4 → ℂ) (η : ℂ) (h : ℝ) :
    ∃ m : Fin 14 → ℝ, fourMatchingEvaluation m = kleinRealCost a b η h := by
  let d : Fin 14 → ℝ := Pi.single (13 : Fin 14) 1
  have hd (j : Fin 24) : fourMatchingEvaluation d j = 1 := by
    fin_cases j <;> norm_num [d, fourMatchingEvaluation, Pi.single_apply]
  let v (j : Fin 14) :=
    (η * fourNoncrossingCoordinates (fourSpectralPoints a b) j).re
  refine ⟨h • d - v, ?_⟩
  funext j
  change (kleinMatchingEvaluationLinear (h • d - v)) j = _
  rw [map_sub, map_smul]
  change h * fourMatchingEvaluation d j - fourMatchingEvaluation v j = _
  rw [hd, mul_one, fourMatchingEvaluation_spectral_real_part] <;> rfl

/-- All actual spectral support costs with the normal Klein-four contacts
have real matching sum-of-squares certificates. Repeated spectra and
additional contacts are allowed. -/
theorem normalKleinFour_spectral_matching_sos (a b : Fin 4 → ℂ) (η : ℂ) (h : ℝ)
    (hn : ∀ j : Fin 24, (η * matchingProduct a b (fourPerm j).symm).re ≤ h)
    (hc : ∀ j ∈ normalKleinFourContacts, (η * matchingProduct a b (fourPerm j).symm).re = h) :
    IsRealMatchingSOS (fun j => h - (η * matchingProduct a b (fourPerm j).symm).re) := by
  obtain ⟨m, hm⟩ := klein_cost_eval a b η h
  have hz (j : Fin 24) (hj : j ∈ normalKleinFourContacts) :
      fourMatchingEvaluation m j = 0 := by
    rw [hm, kleinRealCost, hc j hj, sub_self]
  obtain ⟨β, p, q, c, hcoord⟩ := exists_kleinMatchingCost m hz
  have hcost : kleinRealCost a b η h = kleinMatchingCost β p q c := hm.symm.trans hcoord
  change IsRealMatchingSOS (kleinRealCost a b η h)
  rw [hcost]
  apply klein_matching_sos_of_prism_bound β p q c
  · intro j
    rw [← hcost]
    exact sub_nonneg.mpr (hn j)
  · intro L
    obtain ⟨l, hl⟩ := SpectralProfile.tetrahedralInverseProfile_four_squares a b (-8 * η)
    let C := kleinComplexification.comp kleinPrismOutputLinear
    let f (i : Fin 4) := ((l i).restrictScalars ℝ).comp C
    obtain ⟨x, hx, hval⟩ := no_negative_five_of_complex_squares f L
    refine ⟨x, hx, ?_⟩
    have hv := klein_spectral_prism a b η h β p q c hcost (kleinPrismOutputLinear (L x))
    rw [kleinPrismInput_output, hl, Complex.re_sum] at hv
    rw [hv]
    exact hval

end
end MOC
