import MOC.FourHodgeSurjectivity
import MOC.FourExteriorPairCost
import MOC.FourOrientedBlockAssignments
import MOC.StrongSupport
import Mathlib.Analysis.Complex.Polynomial.Basic

/-! In order four, the real exterior-square representation gives
the support objective and its signed block assignment values. -/

open BigOperators Finset Matrix

namespace MOC

noncomputable section

local notation "FourMatrix" => Matrix (Fin 4) (Fin 4) ℂ
local notation "FourPair" => SubsetLayer (Fin 4) 2
local notation "HodgeMatrix" => Matrix HodgeIndex HodgeIndex ℝ

private theorem hodge_pair_sets (p : HodgeIndex) :
    (fourBlockPair p).val = {fourHodgePair p 0, fourHodgePair p 1} := by
  have h : ∀ q : HodgeIndex, (fourBlockPair q).val = {fourHodgePair q 0, fourHodgePair q 1} := by
    decide +kernel
  exact h p

private theorem hodge_pair_distinct (p : HodgeIndex) : fourHodgePair p 0 ≠ fourHodgePair p 1 := by
  have h : ∀ q : HodgeIndex, fourHodgePair q 0 ≠ fourHodgePair q 1 := by decide +kernel
  exact h p

private theorem fourPairDoubleSum_reindex (f : FourPair → FourPair → ℝ) :
    (∑ J : FourPair, ∑ I : FourPair, f I J) =
      ∑ j : Fin 3, ∑ i : Fin 3, ∑ b : Fin 2, ∑ a : Fin 2,
        f (fourBlockPair (i, a)) (fourBlockPair (j, b)) := by
  calc
    _ = ∑ q : HodgeIndex, ∑ p : HodgeIndex, f (fourBlockPair p) (fourBlockPair q) := by
      rw [← Equiv.sum_comp fourBlockPairEquiv (fun J : FourPair => ∑ I : FourPair, f I J)]
      apply Finset.sum_congr rfl
      intro q _
      exact (Equiv.sum_comp fourBlockPairEquiv (fun I : FourPair => f I (fourBlockPair q))).symm
    _ = _ := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro j _
      simp_rw [Fintype.sum_prod_type]
      exact Finset.sum_comm

private theorem normSq_real_plus_imaginary_half (x y : ℝ) :
    Complex.normSq ((x : ℂ) / 2 + Complex.I * (y : ℂ) / 2) = (x^2 + y^2) / 4 := by
  have he : (x : ℂ) / 2 + Complex.I * (y : ℂ) / 2 =
      ((x / 2 : ℝ) : ℂ) + Complex.I * ((y / 2 : ℝ) : ℂ) := by
    push_cast <;> ring
  rw [he, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.I_re, Complex.I_im, Complex.ofReal_im, Complex.ofReal_re, zero_mul,
    one_mul, mul_zero, sub_zero, add_zero, zero_add]
  ring

private theorem fourHodgeCompound_normSq_entry (U : FourMatrix)
    (hU : IsUnitary U) (hd : U.det = 1) (i j : Fin 3) (a b : Fin 2) :
    Complex.normSq (fourHodgeCompound U (i, a) (j, b)) =
      orientedPlaneAmplitude (a == b) (fourHodgeRealBlock (fourHodgeRealRepresentation U) i j) ^ 2 := by
  let R := fourHodgeRealRepresentation U
  let A := fourHodgeRealBlock R i j
  have he := fourHodgeCompound_block_entry U hU hd i j
  have h₀ : Complex.normSq (fourHodgeCompound U (i, 0) (j, 0)) =
      orientedPlaneAmplitude true A ^ 2 := by
    rw [he.1, normSq_real_plus_imaginary_half, orientedPlaneAmplitude]
    dsimp only [A, fourHodgeRealBlock, Matrix.of_apply, R]
    rw [div_pow, Real.sq_sqrt (by positivity)]
    simp only [if_true]
    ring
  have h₁ : Complex.normSq (fourHodgeCompound U (i, 0) (j, 1)) =
      orientedPlaneAmplitude false A ^ 2 := by
    rw [he.2, normSq_real_plus_imaginary_half, orientedPlaneAmplitude]
    dsimp only [A, fourHodgeRealBlock, Matrix.of_apply, R]
    rw [div_pow, Real.sq_sqrt (by positivity)]
    simp only [Bool.false_eq_true, if_false]
    ring
  have hm (s : Fin 2) : Complex.normSq (fourHodgeCompound U (i, 1) (j, s)) =
      Complex.normSq (fourHodgeCompound U (i, 0) (fourHodgeFlip (j, s))) := by
    fin_cases s
    · have h := fourHodgeCompound_complement U hU hd (i, 0) (j, 1)
      simpa only [fourHodgeFlip_zero, fourHodgeFlip_one, Complex.star_def, Complex.normSq_conj] using
        congrArg Complex.normSq h
    · have h := fourHodgeCompound_complement U hU hd (i, 0) (j, 0)
      simpa only [fourHodgeFlip_zero, fourHodgeFlip_one, Complex.star_def, Complex.normSq_conj] using
        congrArg Complex.normSq h
  fin_cases a
  · fin_cases b
    · exact h₀
    · exact h₁
  · fin_cases b
    · rw [hm, fourHodgeFlip_zero]
      exact h₁
    · rw [hm, fourHodgeFlip_one]
      exact h₀

private theorem hodge_pair_minor (U : FourMatrix) (hU : IsUnitary U) (p q : HodgeIndex) :
    subsetMinorSq U (fourBlockPair p).val (fourBlockPair q).val =
      Complex.normSq (fourHodgeCompound U p q) := by
  rw [hodge_pair_sets p, hodge_pair_sets q]
  exact subsetMinorSq_pair U hU (hodge_pair_distinct p) (hodge_pair_distinct q)

/-- A common phase gives determinant one and preserves the squared
minors and the spectral determinant for every pair of lists. -/
theorem exists_special_unitary_with_same_minor_table
    (U : FourMatrix) (hU : IsUnitary U) :
    ∃ V : FourMatrix, IsUnitary V ∧ V.det = 1 ∧
      subsetMinorSq V = subsetMinorSq U ∧
      (∀ a b : Fin 4 → ℂ, determinantValue a b V = determinantValue a b U) := by
  have hs : Complex.normSq U.det = 1 := by
    have h := congrArg Matrix.det hU.1
    rw [Matrix.det_mul, Matrix.det_conjTranspose, Matrix.det_one, Complex.star_def,
      Complex.mul_conj] at h
    exact Complex.ofReal_injective (h.trans Complex.ofReal_one.symm)
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (U.det)⁻¹ (n := 4) (by decide)
  have hzn : Complex.normSq z = 1 := by
    have h := congrArg Complex.normSq hz
    rw [map_pow, Complex.normSq_inv, hs, inv_one] at h
    exact (pow_left_inj₀ (Complex.normSq_nonneg z) zero_le_one (by decide : 4 ≠ 0)).mp
      (by simpa only [one_pow] using h)
  have h₁ : z * star z = 1 := by
    rw [Complex.star_def, Complex.mul_conj, hzn, Complex.ofReal_one]
  have h₂ : star z * z = 1 := by simpa only [mul_comm] using h₁
  refine ⟨z • U, ⟨?_, ?_⟩, ?_, ?_, fun a b => ?_⟩
  · rw [Matrix.conjTranspose_smul, Matrix.mul_smul, Matrix.smul_mul, smul_smul,
      h₁, one_smul, hU.1]
  · rw [Matrix.conjTranspose_smul, Matrix.mul_smul, Matrix.smul_mul, smul_smul,
      h₂, one_smul, hU.2]
  · rw [Matrix.det_smul, Fintype.card_fin, hz, inv_mul_cancel₀ (det_ne_zero_of_unitary hU)]
  · funext I J
    exact subsetMinorSq_smul_of_normSq_eq_one U z hzn I J
  · have hc : (z • U) * diagonal b * (z • U)ᴴ = U * diagonal b * Uᴴ := by
      rw [Matrix.conjTranspose_smul, Matrix.mul_smul, Matrix.smul_mul,
        Matrix.smul_mul, smul_smul, h₁, one_smul]
    simp only [determinantValue, hc]

/-- The real (SO(6)) objective evaluates the order-four determinant
projection on the image of the exterior-square representation. -/
theorem orderFour_determinant_support_eq_hodge_quadratic (a b : Fin 4 → ℂ) (η : ℂ)
    (U : FourMatrix) (hU : IsUnitary U) (hd : U.det = 1) :
    (η * determinantValue a b U).re = orderFourPairOffset a b η +
      fourHodgeQuadraticCost (orderFourPairCost a b η) (fourHodgeRealRepresentation U) := by
  rw [orderFour_determinant_support_eq_pair_cost a b η U hU,
    fourHodgeQuadraticCost_eq_amplitudes]
  congr 1
  rw [fourPairDoubleSum_reindex]
  simp only [hodge_pair_minor U hU, fourHodgeCompound_normSq_entry U hU hd]

/-- An assignment coming from a permutation has that permutation's
support value. -/
theorem orderFour_matching_support_eq_oriented_assignment (a b : Fin 4 → ℂ) (η : ℂ)
    (σ : Equiv.Perm (Fin 4)) (π : Equiv.Perm (Fin 3)) (flip : Fin 3 → Bool)
    (h : fourBlockRepresents σ π flip) :
    (η * matchingProduct a b σ).re = orderFourPairOffset a b η +
      fourOrientedAssignmentCost (orderFourPairCost a b η) π flip := by
  rw [orderFour_score_eq_pair_cost a b η σ]
  congr 1
  classical
  rw [← fourPairPermutationCost_eq_oriented_assignment (orderFourPairCost a b η) σ π flip h]
  apply Finset.sum_congr rfl
  intro J _
  symm
  let I₀ := subsetLayerPerm 2 σ J
  have hmap : J.val.map σ.toEmbedding = I₀.val := rfl
  rw [hmap, Finset.sum_eq_single_of_mem I₀ (Finset.mem_univ I₀)]
  · simp
  · intro I _ hne
    have hv : I₀.val ≠ I.val := fun he => hne (Subtype.ext he.symm)
    simp only [hv, if_false, mul_zero]

/-- The order-four quadratic support inequality for real exterior-square
coordinates, with the comparison over the 24 even signed assignments. -/
def OrderFourHodgeQuadraticSupport : Prop :=
  ∀ (a b : Fin 4 → ℂ) (η : ℂ) (R : HodgeMatrix), Rᵀ * R = 1 → R.det = 1 →
    ∃ (π : Equiv.Perm (Fin 3)) (flip : Fin 3 → Bool),
      (∏ j, fourBlockSign (flip j)) = 1 ∧
      fourHodgeQuadraticCost (orderFourPairCost a b η) R ≤
        fourOrientedAssignmentCost (orderFourPairCost a b η) π flip

/-- If the quadratic bound holds on the real coordinates, then the
Marcus–de Oliveira inclusion holds in order four. -/
theorem conjecture_four_of_hodge_quadratic_support
    (h : OrderFourHodgeQuadraticSupport) : Conjecture (Fin 4) := by
  intro a b U hU
  obtain ⟨V, hV, hd, _, hval⟩ := exists_special_unitary_with_same_minor_table U hU
  apply (holds_iff_directional a b U).mpr
  intro η
  let R := fourHodgeRealRepresentation V
  have hR : Rᵀ * R = 1 :=
    Matrix.mul_eq_one_comm.mp (fourHodgeRealRepresentation_orthogonal V hV hd)
  obtain ⟨π, flip, hflip, hcost⟩ := h a b η R hR (fourHodgeRealRepresentation_det V hV hd)
  obtain ⟨σ, hσ⟩ := exists_fourPerm_of_oriented_assignment π flip hflip
  refine ⟨σ, ?_⟩
  rw [← hval a b, orderFour_determinant_support_eq_hodge_quadratic a b η V hV hd,
    orderFour_matching_support_eq_oriented_assignment a b η σ π flip hσ]
  exact add_le_add_left hcost _

/-- The Marcus–de Oliveira conjecture in order four is equivalent to
the quadratic support problem over all real special orthogonal
matrices of order six. The spectral lists are arbitrary. -/
theorem conjecture_four_iff_hodge_quadratic_support :
    Conjecture (Fin 4) ↔ OrderFourHodgeQuadraticSupport := by
  refine ⟨?_, conjecture_four_of_hodge_quadratic_support⟩
  intro h a b η R hR hd
  obtain ⟨U, hU, hdet, he⟩ := fourHodgeRealRepresentation_surjective R hR hd
  obtain ⟨σ, hs⟩ := (holds_iff_directional a b U).mp (h a b U hU) η
  obtain ⟨π, flip, hflip, hσ⟩ := exists_oriented_assignment_of_fourPerm σ
  rw [orderFour_determinant_support_eq_hodge_quadratic a b η U hU hdet, he,
    orderFour_matching_support_eq_oriented_assignment a b η σ π flip hσ] at hs
  exact ⟨π, flip, hflip, le_of_add_le_add_left hs⟩

/-- Every admissible assignment attains its cost on a real orthogonal
matrix of determinant one. -/
theorem orderFour_oriented_assignment_cost_attained (a b : Fin 4 → ℂ) (η : ℂ)
    (π : Equiv.Perm (Fin 3)) (flip : Fin 3 → Bool)
    (hflip : (∏ j, fourBlockSign (flip j)) = 1) :
    ∃ R : HodgeMatrix, Rᵀ * R = 1 ∧ R.det = 1 ∧
      fourHodgeQuadraticCost (orderFourPairCost a b η) R =
        fourOrientedAssignmentCost (orderFourPairCost a b η) π flip := by
  obtain ⟨σ, hσ⟩ := exists_fourPerm_of_oriented_assignment π flip hflip
  obtain ⟨U, hU, hUval⟩ := matchingProduct_mem_determinantRange a b σ
  obtain ⟨V, hV, hd, _, hVval⟩ := exists_special_unitary_with_same_minor_table U hU
  refine ⟨fourHodgeRealRepresentation V,
    Matrix.mul_eq_one_comm.mp (fourHodgeRealRepresentation_orthogonal V hV hd),
    fourHodgeRealRepresentation_det V hV hd, ?_⟩
  exact add_left_cancel (show orderFourPairOffset a b η +
      fourHodgeQuadraticCost (orderFourPairCost a b η) (fourHodgeRealRepresentation V) =
      orderFourPairOffset a b η + fourOrientedAssignmentCost (orderFourPairCost a b η) π flip by
    rw [← orderFour_determinant_support_eq_hodge_quadratic a b η V hV hd,
      ← orderFour_matching_support_eq_oriented_assignment a b η σ π flip hσ,
      hVval a b, hUval])

end

end MOC
