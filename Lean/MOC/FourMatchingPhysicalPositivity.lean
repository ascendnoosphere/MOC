import MOC.FourMinorTransport
import MOC.FourMixedRayCancellation
import MOC.FourSupportConeClassification
import MOC.RealMatchingSquares

/-! Alternating correction of the order-four matching moment and transport
from orthogonal to unitary mixers. The Clifford decomposition remains an
explicit hypothesis. -/

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
  change realMatchingMoment matchingSign i j = (E * matchingCornerKernel * Eᵀ) i j
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
  change g ∈ Set.range (fourMatchingEvaluation : (Fin 14 → ℝ) → (Fin 24 → ℝ)) at hg
  rw [four_matching_space_eq_ordinary_span] at hg
  change fourSupportCostValue U g = ∑ k, w k * fourSupportCostValue (V k) g
  induction hg using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨r, rfl⟩ := hg
    rw [fourSupportCostValue_ordinaryRay U hU]
    simp only [fourSupportCostValue_ordinaryRay (V _) (hV _)]
    exact hm (ordinaryCostRows r) (ordinaryCostColumns r)
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

end

end MOC
