import MOC.CommonLawTransport
import MOC.HermitianByNormalFourProof
import MOC.ThreeValues
import MOC.TwoFreeEntries
import Mathlib.NumberTheory.Zsqrtd.GaussianInt

/-! Common permutation weights with a fixed spectrum in order four. -/

open BigOperators Finset Matrix
open scoped ComplexConjugate

namespace MOC

noncomputable section

private theorem weightedDiamondSupport_four_interval (t : ℝ) (ht : 1 < t) (ht₂ : t ≤ 2)
    (U : Matrix (Fin 4) (Fin 4) ℂ) (hU : IsUnitary U) : WeightedDiamondSupportAt t U := by
  have hs : Set.Ioo (1 : ℝ) 2 ⊆ {q : ℝ | WeightedDiamondSupportAt q U} := by
    intro s hs
    have h₁ : 0 < s - 1 := sub_pos.mpr hs.1
    have h₂ : 0 < 2 - s := sub_pos.mpr hs.2
    let u := (s - 1) / (2 - s)
    have hu : 0 < u := div_pos h₁ h₂
    have he : u / (1 + u) = s - 1 := by
      dsimp only [u]
      field_simp [h₂.ne'] <;> ring
    have hc := RayCoefficients.weightedDiamondFacetCompleteness_lower u hu
    rw [he] at hc
    have h := weightedDiamondSupport_of_facetCompleteness (s - 1) h₁.le hc U hU
    rwa [show 1 + (s - 1) = s by ring] at h
  apply closure_minimal hs (isClosed_weightedDiamondSupportAt U)
  rw [closure_Ioo (by norm_num : (1 : ℝ) ≠ 2)]
  exact ⟨ht.le, ht₂⟩

private theorem commonWeights_of_swapped_right {a : Fin 4 → ℂ}
    {U : Matrix (Fin 4) (Fin 4) ℂ} (hU : IsUnitary U)
    (w : Equiv.Perm (Fin 4) → ℝ) (hw : ∀ σ, 0 ≤ w σ) (hs : ∑ σ, w σ = 1)
    (he : ∀ b, weightedMatchingValue b a w = determinantValue b a Uᴴ) :
    HasCommonWeights a U := by
  let rev : Equiv.Perm (Equiv.Perm (Fin 4)) :=
    ⟨fun σ => σ.symm, fun σ => σ.symm, fun _ => rfl, fun _ => rfl⟩
  refine ⟨fun σ => w σ.symm, fun σ => hw σ.symm, (Equiv.sum_comp rev w).trans hs, ?_⟩
  intro b
  rw [weightedMatchingValue_swap, he]
  rw [← determinantValue_left_conjugation a b U hU, determinantValue, add_comm]

/-- Four real eigenvalues admit one law for every complex diagonal partner.
For repeated eigenvalues an adjacent two-minor coupling gives the law directly. -/
theorem commonWeights_four_real_spectrum (a : Fin 4 → ℝ) (U : Matrix (Fin 4) (Fin 4) ℂ)
    (hU : IsUnitary U) : HasCommonWeights (fun i => (a i : ℂ)) U := by
  classical
  have hUadj : IsUnitary Uᴴ :=
    ⟨by simpa only [Matrix.conjTranspose_conjTranspose] using hU.2,
      by simpa only [Matrix.conjTranspose_conjTranspose] using hU.1⟩
  by_cases hinj : Function.Injective a
  · obtain ⟨w, hw, hs, he⟩ := exists_right_weights_four_of_weightedDiamond_support_le_two
      weightedDiamondSupport_four_interval a hinj Uᴴ hUadj
    exact commonWeights_of_swapped_right hU w hw hs he
  · have h : ¬ ∀ i k, a i = a k → i = k := hinj
    push_neg at h
    obtain ⟨i, k, hik, hne⟩ := h
    have hcover : ∀ i k : Fin 4, i ≠ k → ∃ j l : Fin 4,
        ∀ m, m ≠ j → m = i ∨ m = k ∨ m = l := by decide +kernel
    obtain ⟨j, l, hjl⟩ := hcover i k hne
    let J := (Finset.univ : Finset (Fin 4)).filter (fun m => m ≠ j ∧ a m = a i)
    have hj : j ∉ J := by simp [J]
    obtain ⟨w, hw, hs, he⟩ := exists_commonWeights_three_values_one_singleton Uᴴ hUadj J j hj
    have ha : Function.update (fun m => if m ∈ J then (a i : ℂ) else (a l : ℂ)) j (a j) =
        fun m => (a m : ℂ) := by
      funext m
      by_cases hm : m = j
      · subst m
        rw [Function.update_self]
      · rw [Function.update_of_ne hm]
        by_cases hmi : a m = a i
        · simp [J, hm, hmi]
        · rcases hjl m hm with rfl | rfl | rfl
          · exact (hmi rfl).elim
          · exact (hmi hik.symm).elim
          · simp [J, hm, hmi]
    apply commonWeights_of_swapped_right hU w hw hs
    intro b
    simpa only [ha] using he b (a i) (a l) (a j)

/-- A circle or straight line containing the fixed spectrum is sufficient for
one probability law for all diagonal partners in order four. -/
theorem commonWeights_four_of_circle_or_line (a : Fin 4 → ℂ) (U : Matrix (Fin 4) (Fin 4) ℂ)
    (hU : IsUnitary U) (ha : SpectrumOnGeneralizedCircle a) : HasCommonWeights a U :=
  commonWeights_on_circle_of_real U hU (fun b => commonWeights_four_real_spectrum b U hU) a ha

private def obstructionSpectrumInt : Fin 4 → GaussianInt :=
  ![1, ⟨0, -1⟩, -2, ⟨0, -2⟩]

private def obstructionMatrixInt : Matrix (Fin 4) (Fin 4) GaussianInt :=
  !![-5, -11, 1, -7; -1, -5, -11, 7; 7, -7, 7, 7; -11, 1, 5, 7]

/-- The fixed spectrum `(1,-i,-2,-2i)` of the two-free-entry example. -/
def fourCircleLineObstructionSpectrum : Fin 4 → ℂ := GaussianInt.toComplex ∘ obstructionSpectrumInt

/-- The orthogonal mixer of the example, in the eigenbasis of the diagonal partner. -/
def fourCircleLineObstructionMixer : Matrix (Fin 4) (Fin 4) ℂ :=
  (1 / 14 : ℂ) • obstructionMatrixInt.map GaussianInt.toComplex

/-- The two free entries are the first two coordinates. -/
def fourCircleLineObstructionPartner (x y : ℂ) : Fin 4 → ℂ := ![x, y, 0, 1 + Complex.I]

theorem isUnitary_fourCircleLineObstructionMixer : IsUnitary fourCircleLineObstructionMixer := by
  let g := GaussianInt.toComplex
  have hInt : obstructionMatrixInt * obstructionMatrixIntᴴ =
      (196 : GaussianInt) • (1 : Matrix (Fin 4) (Fin 4) GaussianInt) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  have hG := congrArg (fun M : Matrix (Fin 4) (Fin 4) GaussianInt => M.map g) hInt
  have hstar := Matrix.conjTranspose_map (A := obstructionMatrixInt) g GaussianInt.toComplex_star
  simp only [Matrix.map_mul, hstar, Matrix.map_smul' g _ _ (map_mul g), map_ofNat,
    Matrix.map_one g (map_zero g) (map_one g)] at hG
  have hU : fourCircleLineObstructionMixer * fourCircleLineObstructionMixerᴴ = 1 := by
    unfold fourCircleLineObstructionMixer
    change ((1 / 14 : ℂ) • obstructionMatrixInt.map g) *
      ((1 / 14 : ℂ) • obstructionMatrixInt.map g)ᴴ = 1
    simp only [Matrix.conjTranspose_smul, star_div₀, star_one, star_ofNat, Matrix.smul_mul,
      Matrix.mul_smul, smul_smul, hG]
    norm_num [smul_smul]
  exact ⟨hU, Matrix.mul_eq_one_comm.mp hU⟩

private def obstructionCornerInt : Fin 3 → Fin 4 → GaussianInt :=
  ![![0, 0, 0, ⟨1, 1⟩], ![1, 0, 0, ⟨1, 1⟩], ![1, 1, 0, ⟨1, 1⟩]]

private def obstructionCorner (q : Fin 3) : Fin 4 → ℂ :=
  GaussianInt.toComplex ∘ obstructionCornerInt q

private theorem obstructionCorner_eq (q : Fin 3) :
    obstructionCorner q =
      fourCircleLineObstructionPartner (if q = 0 then 0 else 1) (if q = 2 then 1 else 0) := by
  funext j
  fin_cases q <;> fin_cases j <;>
    norm_num [obstructionCorner, obstructionCornerInt, fourCircleLineObstructionPartner,
      GaussianInt.toComplex_def']

private def obstructionScaledSum (q : Fin 3) : Matrix (Fin 4) (Fin 4) GaussianInt :=
  (196 : GaussianInt) • diagonal (obstructionCornerInt q) +
    obstructionMatrixInt * diagonal obstructionSpectrumInt * obstructionMatrixIntᴴ

private def obstructionValueInt : Fin 3 → GaussianInt :=
  ![⟨1116, 536⟩, ⟨751, 1477⟩, ⟨223, 1182⟩]

private def obstructionDirection : Fin 3 → GaussianInt :=
  ![⟨1, 3⟩, ⟨2, -1⟩, ⟨-4, 2⟩]

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 4000 in
private theorem obstructionScaledDet (q : Fin 3) :
    (obstructionScaledSum q).det = (196 : GaussianInt)^3 * obstructionValueInt q := by
  rw [Matrix.det_succ_column_zero]
  simp only [Matrix.det_fin_three, Fin.sum_univ_four]
  fin_cases q <;> decide +kernel

private theorem obstructionCorner_determinant (q : Fin 3) :
    determinantValue fourCircleLineObstructionSpectrum (obstructionCorner q)
      fourCircleLineObstructionMixerᴴ = GaussianInt.toComplex (obstructionValueInt q) / 196 := by
  let g := GaussianInt.toComplex
  let U := fourCircleLineObstructionMixer
  let D := diagonal (obstructionCorner q) + U * diagonal fourCircleLineObstructionSpectrum * Uᴴ
  have hU : IsUnitary U := isUnitary_fourCircleLineObstructionMixer
  have hmap : obstructionMatrixInt.map g = (14 : ℂ) • U := by
    simp [U, fourCircleLineObstructionMixer, smul_smul] <;> norm_num
  have hstar := Matrix.conjTranspose_map (A := obstructionMatrixInt) g GaussianInt.toComplex_star
  have hsum : (obstructionScaledSum q).map g = (196 : ℂ) • D := by
    change (obstructionScaledSum q).map g = (196 : ℂ) •
      (diagonal (fun i => g (obstructionCornerInt q i)) +
        U * diagonal (fun i => g (obstructionSpectrumInt i)) * Uᴴ)
    simp only [obstructionScaledSum, Matrix.map_add g (map_add g),
      Matrix.map_smul' g _ _ (map_mul g), map_ofNat, Matrix.map_mul,
      Matrix.diagonal_map (map_zero g), hstar, hmap, Matrix.conjTranspose_smul,
      star_ofNat, Matrix.smul_mul, Matrix.mul_smul, smul_smul, smul_add]
    norm_num
  have he := congrArg g (obstructionScaledDet q)
  simp only [RingHom.map_det, RingHom.mapMatrix_apply, hsum, Matrix.det_smul,
    Fintype.card_fin, map_mul, map_pow, map_ofNat] at he
  have hd : (196 : ℂ) ≠ 0 := by norm_num
  have hdet : D.det = g (obstructionValueInt q) / 196 := by
    apply (eq_div_iff hd).mpr
    apply mul_left_cancel₀ (pow_ne_zero 3 hd)
    linear_combination he
  rw [← determinantValue_left_conjugation fourCircleLineObstructionSpectrum (obstructionCorner q) U hU,
    add_comm]
  exact hdet

private def obstructionVertex (σ : Equiv.Perm (Fin 4)) (q : Fin 3) : GaussianInt :=
  ∏ j, (obstructionSpectrumInt (σ j) + obstructionCornerInt q j)

private theorem obstructionVertex_bound (σ : Equiv.Perm (Fin 4)) :
    (∑ q, (obstructionDirection q * obstructionVertex σ q).re) ≤ -4 := by
  obtain ⟨i, rfl⟩ := fourPerm_surjective σ
  have h : ∀ i : Fin 24, (∑ q, (obstructionDirection q * obstructionVertex (fourPerm i) q).re)
      ≤ -4 := by decide +kernel
  exact h i

private theorem obstructionNumerator_score :
    (∑ q, (obstructionDirection q * obstructionValueInt q).re) = -769 := by
  decide +kernel

/-- The three corner evaluations rule out common weights for the two
arbitrary complex diagonal entries. This does not refute scalar inclusion. -/
theorem no_fourCircleLine_weights_two_free_entries :
    ¬ ∃ w : Equiv.Perm (Fin 4) → ℝ, (∀ σ, 0 ≤ w σ) ∧ (∑ σ, w σ = 1) ∧
      ∀ x y : ℂ,
        weightedMatchingValue fourCircleLineObstructionSpectrum
          (fourCircleLineObstructionPartner x y) w =
        determinantValue fourCircleLineObstructionSpectrum
          (fourCircleLineObstructionPartner x y) fourCircleLineObstructionMixerᴴ := by
  classical
  rintro ⟨w, hw, hs, he⟩
  let g := GaussianInt.toComplex
  have hc (q : Fin 3) :
      (∑ σ, w σ * ((obstructionDirection q * obstructionVertex σ q).re : ℝ)) =
        ((obstructionDirection q * obstructionValueInt q).re : ℝ) / 196 := by
    have heq : weightedMatchingValue fourCircleLineObstructionSpectrum (obstructionCorner q) w =
        g (obstructionValueInt q) / 196 :=
      ((obstructionCorner_eq q).symm ▸ he (if q = 0 then 0 else 1) (if q = 2 then 1 else 0)).trans
        (obstructionCorner_determinant q)
    have hp (σ : Equiv.Perm (Fin 4)) :
        matchingProduct fourCircleLineObstructionSpectrum (obstructionCorner q) σ =
          g (obstructionVertex σ q) := by
      simp only [g, obstructionVertex, matchingProduct, fourCircleLineObstructionSpectrum,
        obstructionCorner, Function.comp_apply, map_prod, map_add]
    simp only [weightedMatchingValue, hp] at heq
    have h := congrArg (fun z : ℂ => (g (obstructionDirection q) * z).re) heq
    change (g (obstructionDirection q) * (∑ σ, (w σ : ℂ) * g (obstructionVertex σ q))).re =
      (g (obstructionDirection q) * (g (obstructionValueInt q) / 196)).re at h
    rw [Finset.mul_sum, Complex.re_sum, ← mul_div_assoc, ← map_mul] at h
    have hterm (σ : Equiv.Perm (Fin 4)) :
        (g (obstructionDirection q) * ((w σ : ℂ) * g (obstructionVertex σ q))).re =
          w σ * ((obstructionDirection q * obstructionVertex σ q).re : ℝ) := by
      rw [mul_left_comm, Complex.re_ofReal_mul, ← map_mul, ← GaussianInt.to_real_re]
    simp_rw [hterm] at h
    rw [show (196 : ℂ) = ((196 : ℝ) : ℂ) by norm_num, Complex.div_ofReal_re,
      ← GaussianInt.to_real_re] at h
    exact h
  have hbound : (∑ σ, w σ * ∑ q, ((obstructionDirection q * obstructionVertex σ q).re : ℝ))
      ≤ (-4 : ℝ) := calc
    _ ≤ ∑ σ, w σ * (-4 : ℝ) := Finset.sum_le_sum fun σ _ =>
      mul_le_mul_of_nonneg_left (by exact_mod_cast obstructionVertex_bound σ) (hw σ)
    _ = _ := by rw [← Finset.sum_mul, hs, one_mul]
  simp_rw [Finset.mul_sum] at hbound
  rw [Finset.sum_comm] at hbound
  simp_rw [hc, ← Finset.sum_div, ← Int.cast_sum, obstructionNumerator_score] at hbound
  norm_num at hbound

end

end MOC
