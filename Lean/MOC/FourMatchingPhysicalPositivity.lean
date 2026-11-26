import MOC.FourMinorTransport
import MOC.FourMixedRayCancellation
import MOC.FourOrthogonalMatchingMomentTransport
import MOC.RealMatchingSquares

/-! Alternating correction of the order-four matching moment and transport
from orthogonal to unitary mixers. -/

open BigOperators Matrix

namespace MOC

noncomputable section

private theorem realMatchingMoment_apply_sum (c : Fin 24 → ℝ)
    (i j : MatchingJetIndex) :
    realMatchingMoment c i j =
      ∑ p, c p * realMatchingJet p i * realMatchingJet p j := by
  unfold realMatchingMoment
  rw [Matrix.mul_assoc, Matrix.mul_apply]
  simp only [Matrix.transpose_apply, Matrix.diagonal_mul]
  apply Finset.sum_congr rfl
  intro p _
  ring

private theorem realMatchingMoment_sign :
    realMatchingMoment matchingSign =
      realMatchingExceptionalEmbedding * matchingCornerKernel *
        realMatchingExceptionalEmbeddingᵀ := by
  classical
  ext i j
  let E := realMatchingExceptionalEmbedding
  let T : Matrix MatchingJetIndex MatchingJetIndex ℝ :=
    Matrix.of fun a b => if a = i then if b = j then 1 else 0 else 0
  have hgram (p : Fin 24) :
      realMatchingGramValue T p = realMatchingJet p i * realMatchingJet p j := by
    have hvec (a : MatchingJetIndex) :
        (T *ᵥ realMatchingJet p) a = if a = i then realMatchingJet p j else 0 := by
      by_cases ha : a = i <;>
        simp [T, Matrix.mulVec, dotProduct, ha, ite_mul, Finset.sum_ite_eq']
    simp [realMatchingGramValue, dotProduct, hvec, mul_ite, Finset.sum_ite_eq']
  have hleft (a : MatchingCornerIndex) (l : MatchingJetIndex) :
      (Eᵀ * T) a l = if l = j then E i a else 0 := by
    by_cases hl : l = j <;>
      simp [T, Matrix.mul_apply, Matrix.transpose_apply, hl, mul_ite, Finset.sum_ite_eq']
  have hcorner (a b : MatchingCornerIndex) : realMatchingCorner T a b = E i a * E j b := by
    change (Eᵀ * T * E) a b = _
    rw [Matrix.mul_apply]
    simp [hleft, ite_mul, Finset.sum_ite_eq']
  have hpair := realMatchingGram_alternating_pairing T
  simp only [hgram, hcorner] at hpair
  change realMatchingMoment matchingSign i j =
    (E * matchingCornerKernel (R := ℝ) * Eᵀ : Matrix MatchingJetIndex MatchingJetIndex ℝ) i j
  rw [realMatchingMoment_apply_sum, Matrix.mul_assoc, Matrix.mul_apply]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.mul_sum]
  calc
    _ = ∑ p : Fin 24, matchingSign p * (realMatchingJet p i * realMatchingJet p j) := by
      simp only [mul_assoc]
    _ = _ := hpair
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      ring

private theorem realMatchingMoment_add_scaled (c d : Fin 24 → ℝ) (t : ℝ) :
    realMatchingMoment (fun p => c p + t * d p) =
      realMatchingMoment c + t • realMatchingMoment d := by
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    realMatchingMoment_apply_sum, add_mul, Finset.sum_add_distrib, mul_assoc, Finset.mul_sum]

/-- The determinant of the exceptional two by two factor supplies the
alternating correction when the stated Clifford decomposition holds. -/
theorem realMatchingMoment_alternating_correction
    (c : Fin 24 → ℝ) (P : Matrix MatchingJetIndex MatchingJetIndex ℝ)
    (hP : P.PosSemidef) (u : MatchingCornerIndex → ℝ)
    (hdecomposition : realMatchingMoment c = P +
      realMatchingExceptionalEmbedding *
        matchingCornerPartialTranspose (Matrix.of fun a b => u a * u b) *
        realMatchingExceptionalEmbeddingᵀ) :
    (realMatchingMoment (fun p => c p +
      (Matrix.of (fun i j : Fin 2 => u (i, j))).det * matchingSign p)).PosSemidef := by
  let E := realMatchingExceptionalEmbedding
  let A : Matrix MatchingCornerIndex MatchingCornerIndex ℝ :=
    Matrix.of fun a b => u a * u b
  let δ := (Matrix.of (fun i j : Fin 2 => u (i, j))).det
  have hdefect : matchingCornerPartialTranspose A - A = -δ • matchingCornerKernel :=
    matchingCorner_rank_one_PT_defect u
  have hcorner : matchingCornerPartialTranspose A + δ • matchingCornerKernel = A := by
    rw [sub_eq_iff_eq_add.mp hdefect, neg_smul, add_comm (-(δ • matchingCornerKernel)),
      add_assoc, neg_add_cancel, add_zero]
  have hlift : E * matchingCornerPartialTranspose A * Eᵀ +
      δ • (E * matchingCornerKernel * Eᵀ) = E * A * Eᵀ := by
    calc
      _ = E * (matchingCornerPartialTranspose A + δ • matchingCornerKernel) * Eᵀ := by
        rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]
      _ = _ := by rw [hcorner]
  let B : Matrix (Fin 1) MatchingCornerIndex ℝ := Matrix.of fun _ a => u a
  have hgram : Bᴴ * B = A := by
    ext a b
    simp [B, A, Matrix.mul_apply, Matrix.conjTranspose_apply]
  have hA : A.PosSemidef := hgram ▸ Matrix.posSemidef_conjTranspose_mul_self B
  have hEA : (E * A * Eᵀ).PosSemidef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      hA.mul_mul_conjTranspose_same E
  change (realMatchingMoment (fun p => c p + δ * matchingSign p)).PosSemidef
  rw [realMatchingMoment_add_scaled, hdecomposition, realMatchingMoment_sign,
    add_assoc, hlift]
  exact hP.add hEA

private abbrev indicatorMask (m : Fin 16) : Finset (Fin 4) :=
  Finset.univ.filter fun i => m.val.testBit i.val

private theorem fourSupportCostValue_realMatchingIndicator (U : Matrix (Fin 4) (Fin 4) ℂ)
    (hU : IsUnitary U) (a b : Fin 16) :
    fourSupportCostValue U (realMatchingIndicator a b) =
      subsetMinorSq U (indicatorMask a) (indicatorMask b) := by
  classical
  let I := indicatorMask a
  let J := indicatorMask b
  have hmap (σ : FourPerm) : I.map σ.toEmbedding = J ↔ J.map σ.symm.toEmbedding = I := by
    constructor
    · intro h
      ext i
      rw [← h]
      simp only [Finset.mem_map_equiv, Equiv.symm_symm, Equiv.symm_apply_apply]
    · intro h
      ext i
      rw [← h]
      simp only [Finset.mem_map_equiv, Equiv.symm_symm, Equiv.apply_symm_apply]
  have hind (p : Fin 24) : realMatchingIndicator a b p =
      if J.map (fourPerm p).symm.toEmbedding = I then 1 else 0 := by
    change (Int.cast : ℤ → ℝ) (if I.map (fourPerm p).toEmbedding = J then 1 else 0) = _
    by_cases h : I.map (fourPerm p).toEmbedding = J
    · rw [if_pos h, if_pos ((hmap (fourPerm p)).mp h), Int.cast_one]
    · rw [if_neg h, if_neg (fun he => h ((hmap (fourPerm p)).mpr he)), Int.cast_zero]
  let e : Fin 24 ≃ FourPerm := fourPermEquiv.trans (Equiv.inv FourPerm)
  let f (σ : FourPerm) := if J.map σ.toEmbedding = I then realSignedWeight U σ else 0
  change (∑ p, realSignedWeight U (fourPerm p).symm * realMatchingIndicator a b p) = _
  simp only [hind, mul_ite, mul_one, mul_zero]
  change (∑ p, f (e p)) = _
  rw [Equiv.sum_comp e f]
  have hs := congrArg Complex.re (sum_signedWeight_image_eq_subsetMinorSq U hU I J)
  simpa only [f, realSignedWeight, Finset.sum_filter, Complex.re_sum, apply_ite,
    Complex.ofReal_re, Complex.zero_re] using hs

/-- The common squared-minor mixture transports the pairing of every
cost in the matching space with the same orthogonal weights. -/
theorem fourSupportCostValue_minor_mixture (U : Matrix (Fin 4) (Fin 4) ℂ)
    (hU : IsUnitary U) :
    ∃ (κ : Type) (_ : Fintype κ) (w : κ → ℝ) (O : κ → Matrix.orthogonalGroup (Fin 4) ℝ),
      (∀ k, 0 ≤ w k) ∧ (∑ k, w k) = 1 ∧
      ∀ g ∈ realMatchingFunctionSpace,
        fourSupportCostValue U g =
          ∑ k, w k * fourSupportCostValue (Complex.ofRealHom.mapMatrix (O k).val) g := by
  obtain ⟨κ, inst, w, O, hw, hs, hm⟩ := four_minor_mixture U hU
  letI : Fintype κ := inst
  let V (k : κ) := Complex.ofRealHom.mapMatrix (O k).val
  have hV (k : κ) : IsUnitary (V k) := isUnitary_ofReal_orthogonal (O k)
  refine ⟨κ, inst, w, O, hw, hs, ?_⟩
  intro g hg
  rw [realMatchingFunctionSpace_eq_indicator_span] at hg
  change fourSupportCostValue U g = ∑ k, w k * fourSupportCostValue (V k) g
  induction hg using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨⟨a, b⟩, rfl⟩ := hg
    rw [fourSupportCostValue_realMatchingIndicator U hU]
    simp only [fourSupportCostValue_realMatchingIndicator (V _) (hV _)]
    exact hm (indicatorMask a) (indicatorMask b)
  | zero => simp
  | add a b _ _ ha hb =>
    simp only [map_add, ha, hb, mul_add, Finset.sum_add_distrib]
  | smul a g _ hg =>
    simp only [map_smul, smul_eq_mul, hg, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring

/-- An orthogonal alternating correction for each mixer suffices for
nonnegative unitary evaluation of every matching sum of squares. -/
theorem fourSupportCostValue_nonneg_of_orthogonal_corrected_moment
    (horth : ∀ O : Matrix.orthogonalGroup (Fin 4) ℝ, ∃ t : ℝ,
      (realMatchingMoment (fun p =>
        realSignedWeight (Complex.ofRealHom.mapMatrix O.val) (fourPerm p).symm +
          t * matchingSign p)).PosSemidef)
    (U : Matrix (Fin 4) (Fin 4) ℂ) (hU : IsUnitary U) {g : Fin 24 → ℝ}
    (hg : g ∈ realMatchingFunctionSpace) (hsos : IsRealMatchingSOS g) :
    0 ≤ fourSupportCostValue U g := by
  obtain ⟨κ, inst, w, O, hw, _, hm⟩ := fourSupportCostValue_minor_mixture U hU
  letI : Fintype κ := inst
  rw [hm g hg]
  apply Finset.sum_nonneg
  intro k _
  obtain ⟨t, ht⟩ := horth (O k)
  exact mul_nonneg (hw k) (realMatchingSOS_pairing_nonneg_of_positiveMoment _ t hg hsos ht)

/-- At every complex unitary mixer of order four, a matching sum of
squares that belongs to the matching space evaluates nonnegatively. -/
theorem fourSupportCostValue_nonneg_matchingSOS (U : Matrix (Fin 4) (Fin 4) ℂ)
    (hU : IsUnitary U) {g : Fin 24 → ℝ}
    (hg : g ∈ realMatchingFunctionSpace) (hsos : IsRealMatchingSOS g) :
    0 ≤ fourSupportCostValue U g :=
  fourSupportCostValue_nonneg_of_orthogonal_corrected_moment
    fourOrthogonalMatchingMoment_exists_correction U hU hg hsos

/-- Signed evaluation of a spectral support cost gives the difference
between its height and the determinant projection. -/
theorem fourSupportCostValue_spectral_eq (a b : Fin 4 → ℂ) (η : ℂ) (height : ℝ)
    (U : Matrix (Fin 4) (Fin 4) ℂ) (hU : IsUnitary U) :
    fourSupportCostValue U (fun p => height - (η * matchingProduct a b (fourPerm p).symm).re) =
      height - (η * determinantValue a b U).re := by
  let e : Fin 24 ≃ FourPerm := fourPermEquiv.trans (Equiv.inv FourPerm)
  let f (σ : FourPerm) := realSignedWeight U σ * (height - (η * matchingProduct a b σ).re)
  change (∑ p, f (e p)) = _
  rw [Equiv.sum_comp e f]
  have hscore : (∑ σ, realSignedWeight U σ * (η * matchingProduct a b σ).re) =
      (η * determinantValue a b U).re := by
    have h := congrArg (fun z : ℂ => (η * z).re) (real_signed_determinant a b U hU)
    simpa only [Finset.mul_sum, Complex.re_sum, mul_left_comm η, Complex.re_ofReal_mul] using h
  simp only [f, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, sum_realSignedWeight U hU,
    one_mul, hscore]

/-- A matching sum of squares for a spectral support cost proves the
directional determinant bound at every unitary mixer of order four. -/
theorem four_support_of_spectral_matchingSOS (a b : Fin 4 → ℂ) (η : ℂ) (height : ℝ)
    (U : Matrix (Fin 4) (Fin 4) ℂ) (hU : IsUnitary U)
    (hg : (fun p : Fin 24 => height - (η * matchingProduct a b (fourPerm p).symm).re) ∈
      realMatchingFunctionSpace)
    (hsos : IsRealMatchingSOS (fun p => height - (η * matchingProduct a b (fourPerm p).symm).re)) :
    (η * determinantValue a b U).re ≤ height := by
  have h := fourSupportCostValue_nonneg_matchingSOS U hU hg hsos
  rw [fourSupportCostValue_spectral_eq a b η height U hU] at h
  exact sub_nonneg.mp h

end

end MOC
