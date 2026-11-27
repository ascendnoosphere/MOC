import MOC.CommonLawTransport
import MOC.ContactCensus
import MOC.FiniteMinorLaw
import MOC.HermitianByNormalFourProof
import MOC.Realification
import MOC.StrongSupport
import MOC.ThreeValues
import MOC.TwoFreeEntries
import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Mathlib.Topology.Instances.Matrix

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
  rw [← determinantValue_left_conjugation b a U hU, determinantValue, add_comm]

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
    ext i j : 1
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
      GaussianInt.toComplex_def', Fin.ext_iff]

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
    dsimp only [g, U, fourCircleLineObstructionMixer]
    rw [smul_smul, mul_one_div_cancel (by norm_num : (14 : ℂ) ≠ 0), one_smul]
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

/-- A fixed set of partner positions gives the spectral product on those positions. -/
def commonSpectralMoment {ι : Type*} [Fintype ι] [DecidableEq ι] (a : ι → ℂ)
    (w : Equiv.Perm ι → ℝ) (S : Finset ι) : ℂ :=
  ∑ σ, (w σ : ℂ) * ∏ j ∈ S, a (σ j)

private theorem weightedMatchingValue_expand_moments {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a b : ι → ℂ) (w : Equiv.Perm ι → ℝ) :
    weightedMatchingValue a b w =
      ∑ S : Finset ι, commonSpectralMoment a w S * ∏ j ∈ Sᶜ, b j := by
  unfold weightedMatchingValue matchingProduct commonSpectralMoment
  simp_rw [Fintype.prod_add, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro S _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro σ _
  exact (mul_assoc _ _ _).symm

/-- Agreement on all partner lists implies equality of every product moment.
Zero-one partner lists suffice for coefficient extraction. -/
theorem commonSpectralMoment_eq_of_partner_agreement {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ℂ) (w v : Equiv.Perm ι → ℝ)
    (h : ∀ b, weightedMatchingValue a b w = weightedMatchingValue a b v) (S : Finset ι) :
    commonSpectralMoment a w S = commonSpectralMoment a v S := by
  classical
  let d (J : Finset ι) := commonSpectralMoment a w J - commonSpectralMoment a v J
  have hz (K : Finset ι) : (∑ J : Finset ι, if K ⊆ J then d J else 0) = 0 := by
    let b (j : ι) : ℂ := if j ∈ K then 0 else 1
    have hprod (J : Finset ι) : (∏ j ∈ Jᶜ, b j) = if K ⊆ J then 1 else 0 := by
      by_cases hK : K ⊆ J
      · rw [if_pos hK]
        apply Finset.prod_eq_one
        intro j hj
        exact if_neg (fun hmem => (Finset.mem_compl.mp hj) (hK hmem))
      · rw [if_neg hK]
        obtain ⟨j, hj, hj'⟩ := Finset.not_subset.mp hK
        exact Finset.prod_eq_zero (Finset.mem_compl.mpr hj') (if_pos hj)
    have he := h b
    rw [weightedMatchingValue_expand_moments, weightedMatchingValue_expand_moments] at he
    have hsub := sub_eq_zero.mpr he
    rw [← Finset.sum_sub_distrib] at hsub
    have hterm (J : Finset ι) :
        commonSpectralMoment a w J * (∏ j ∈ Jᶜ, b j) -
          commonSpectralMoment a v J * (∏ j ∈ Jᶜ, b j) =
            if K ⊆ J then d J else 0 := by
      rw [← sub_mul, hprod]
      by_cases hK : K ⊆ J
      · simp only [hK, if_true, mul_one, d]
      · simp only [hK, if_false, mul_zero]
    simpa only [hterm] using hsub
  let Reach (n : ℕ) := ∀ K : Finset ι, Fintype.card ι - K.card = n → d K = 0
  have hReach (n : ℕ) : Reach n := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro K hn
      have he := hz K
      rw [Finset.sum_eq_single K] at he
      · simpa only [if_pos (Finset.Subset.refl K)] using he
      · intro J _ hJK
        by_cases hKJ : K ⊆ J
        · rw [if_pos hKJ]
          have hlt := Finset.card_lt_card (show K ⊂ J from lt_of_le_of_ne hKJ (Ne.symm hJK))
          have hJ := Finset.card_le_univ J
          exact ih (Fintype.card ι - J.card) (by omega) J rfl
        · exact if_neg hKJ
      · intro hK
        exact (hK (Finset.mem_univ K)).elim
  exact sub_eq_zero.mp (hReach _ S rfl)

private theorem commonWeights_singletons_of_distinct
    (a : Fin 4 → ℂ) (ha : Function.Injective a)
    (w v : Equiv.Perm (Fin 4) → ℝ)
    (h : ∀ b, weightedMatchingValue a b w = weightedMatchingValue a b v)
    (i j : Fin 4) :
    (∑ σ, if σ j = i then w σ else 0) = ∑ σ, if σ j = i then v σ else 0 := by
  classical
  let c (k : Fin 4) := a k - a i
  have hc : ∀ b, weightedMatchingValue c b w = weightedMatchingValue c b v := by
    intro b
    have hb (σ : Equiv.Perm (Fin 4)) : matchingProduct c b σ =
        matchingProduct a (fun k => b k - a i) σ := by
      unfold matchingProduct
      apply Finset.prod_congr rfl
      intro k _
      dsimp only [c]
      ring
    simpa only [weightedMatchingValue, hb] using h (fun k => b k - a i)
  let p := ∏ k ∈ (Finset.univ : Finset (Fin 4)).erase i, c k
  have hp : p ≠ 0 := Finset.prod_ne_zero_iff.mpr
    (fun k hk => sub_ne_zero.mpr fun he => (Finset.mem_erase.mp hk).1 (ha he))
  have hprod (σ : Equiv.Perm (Fin 4)) :
      (∏ k ∈ (Finset.univ : Finset (Fin 4)).erase j, c (σ k)) =
        if σ j = i then p else 0 := by
    have hmap : ((Finset.univ : Finset (Fin 4)).erase j).map σ.toEmbedding =
        Finset.univ.erase (σ j) := by
      ext k
      simp only [Finset.mem_map_equiv, Finset.mem_erase, Finset.mem_univ, and_true, ne_eq,
        Equiv.symm_apply_eq]
    have hm := Finset.prod_map ((Finset.univ : Finset (Fin 4)).erase j) σ.toEmbedding c
    simp only [hmap, Equiv.toEmbedding_apply] at hm
    rw [← hm]
    by_cases hσ : σ j = i
    · rw [hσ, if_pos rfl]
    · rw [if_neg hσ]
      exact Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨Ne.symm hσ, Finset.mem_univ _⟩)
        (sub_self (a i))
  have he := commonSpectralMoment_eq_of_partner_agreement c w v hc (Finset.univ.erase j)
  have hm (u : Equiv.Perm (Fin 4) → ℝ) :
      commonSpectralMoment c u (Finset.univ.erase j) =
        ((∑ σ, if σ j = i then u σ else 0 : ℝ) : ℂ) * p := by
    rw [commonSpectralMoment, Complex.ofReal_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro σ _
    rw [hprod]
    split <;> simp only [Complex.ofReal_zero, mul_zero, zero_mul]
  rw [hm w, hm v] at he
  exact Complex.ofReal_injective (mul_right_cancel₀ hp he)

private def circleLinePair (k : Fin 6) : Finset (Fin 4) :=
  ![{0, 1}, {0, 2}, {0, 3}, {1, 2}, {1, 3}, {2, 3}] k

private theorem circleLinePair_injective : Function.Injective circleLinePair := by
  decide +kernel

private theorem circleLinePair_complete (I : Finset (Fin 4)) (hI : I.card = 2) :
    ∃ k, circleLinePair k = I := by
  have h : ∀ I : Finset (Fin 4), I.card = 2 → ∃ k, circleLinePair k = I := by
    decide +kernel
  exact h I hI

set_option maxHeartbeats 1000000 in
private theorem circleLinePair_incident_count (i : Fin 4) (J : Finset (Fin 4)) (hJ : J.card = 2)
    (σ : Equiv.Perm (Fin 4)) :
    (∑ k, if i ∈ circleLinePair k ∧ J.map σ.toEmbedding = circleLinePair k then (1 : ℝ) else 0) =
      ∑ j ∈ J, if σ j = i then (1 : ℝ) else 0 := by
  have h : ∀ (s : Fin 24) (i : Fin 4) (J : Finset (Fin 4)), J.card = 2 →
      (∑ k, if i ∈ circleLinePair k ∧ J.map (fourPerm s).toEmbedding = circleLinePair k
        then (1 : ℤ) else 0) =
        ∑ j ∈ J, if fourPerm s j = i then (1 : ℤ) else 0 := by
    decide +kernel
  obtain ⟨s, rfl⟩ := fourPerm_surjective σ
  have he := congrArg (fun z : ℤ => (z : ℝ)) (h s i J hJ)
  simpa only [Int.cast_sum, apply_ite, Int.cast_one, Int.cast_zero] using he

private theorem dividing_real_coordinates_independent (A B : ℂ)
    (hB : B ≠ 0) (h : (A / B).im ≠ 0) (x y : ℝ)
    (he : (x : ℂ) * A + (y : ℂ) * B = 0) : x = 0 ∧ y = 0 := by
  have hdiv : (x : ℂ) * (A / B) + (y : ℂ) = 0 := by
    apply (mul_right_cancel₀ hB)
    rw [add_mul, mul_assoc, div_mul_cancel₀ _ hB, he, zero_mul]
  have him := congrArg Complex.im hdiv
  simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, add_zero, Complex.zero_im] at him
  have hx := (mul_eq_zero.mp him).resolve_right h
  have hy := congrArg Complex.re hdiv
  simp only [hx, Complex.ofReal_zero, zero_mul, zero_add, Complex.ofReal_re, Complex.zero_re] at hy
  exact ⟨hx, hy⟩

private theorem commonWeights_pair_images_of_independence
    (a : Fin 4 → ℂ) (ha : Function.Injective a)
    (w v : Equiv.Perm (Fin 4) → ℝ)
    (h : ∀ b, weightedMatchingValue a b w = weightedMatchingValue a b v)
    (hB : (a 0 * a 1 + a 2 * a 3) - (a 0 * a 3 + a 1 * a 2) ≠ 0)
    (hInd : (((a 0 * a 1 + a 2 * a 3) - (a 0 * a 2 + a 1 * a 3)) /
      ((a 0 * a 1 + a 2 * a 3) - (a 0 * a 3 + a 1 * a 2))).im ≠ 0)
    (I J : Finset (Fin 4)) (hI : I.card = 2) (hJ : J.card = 2) :
    (∑ σ ∈ Finset.univ.filter (fun σ : Equiv.Perm (Fin 4) => J.map σ.toEmbedding = I), w σ) =
      ∑ σ ∈ Finset.univ.filter (fun σ : Equiv.Perm (Fin 4) => J.map σ.toEmbedding = I), v σ := by
  classical
  let d (S : Finset (Fin 4)) : ℝ := ∑ σ,
    (if J.map σ.toEmbedding = S then (1 : ℝ) else 0) * (w σ - v σ)
  have hsingle (i j : Fin 4) :
      (∑ σ, (if σ j = i then (1 : ℝ) else 0) * (w σ - v σ)) = 0 := by
    have hs := commonWeights_singletons_of_distinct a ha w v h i j
    have hterm (σ : Equiv.Perm (Fin 4)) :
        (if σ j = i then (1 : ℝ) else 0) * (w σ - v σ) =
          (if σ j = i then w σ else 0) - (if σ j = i then v σ else 0) := by
      by_cases hσ : σ j = i <;> simp [hσ]
    simp_rw [hterm, Finset.sum_sub_distrib, hs, sub_self]
  have hInc (i : Fin 4) :
      (∑ k, (if i ∈ circleLinePair k then (1 : ℝ) else 0) * d (circleLinePair k)) = 0 := by
    have hb (k : Fin 6) (σ : Equiv.Perm (Fin 4)) :
        (if i ∈ circleLinePair k then (1 : ℝ) else 0) *
            (if J.map σ.toEmbedding = circleLinePair k then (1 : ℝ) else 0) =
          if i ∈ circleLinePair k ∧ J.map σ.toEmbedding = circleLinePair k then 1 else 0 := by
      by_cases hi : i ∈ circleLinePair k <;>
        by_cases hσ : J.map σ.toEmbedding = circleLinePair k <;> simp [hi, hσ]
    unfold d
    simp_rw [Finset.mul_sum, ← mul_assoc, hb]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul]
    simp_rw [circleLinePair_incident_count i J hJ, Finset.sum_mul]
    rw [Finset.sum_comm]
    simp_rw [hsingle, Finset.sum_const_zero]
  have h₀ : d {0,1} + d {0,2} + d {0,3} = 0 := by
    simpa [Fin.sum_univ_succ, circleLinePair, add_assoc] using hInc 0
  have h₁ : d {0,1} + d {1,2} + d {1,3} = 0 := by
    simpa [Fin.sum_univ_succ, circleLinePair, add_assoc] using hInc 1
  have h₂ : d {0,2} + d {1,2} + d {2,3} = 0 := by
    simpa [Fin.sum_univ_succ, circleLinePair, add_assoc] using hInc 2
  have h₃ : d {0,3} + d {1,3} + d {2,3} = 0 := by
    simpa [Fin.sum_univ_succ, circleLinePair, add_assoc] using hInc 3
  have h01 : d {2,3} = d {0,1} := by linarith only [h₀,h₁,h₂,h₃]
  have h02 : d {1,3} = d {0,2} := by linarith only [h₀,h₁,h₂,h₃]
  have h03 : d {1,2} = d {0,3} := by linarith only [h₀,h₁,h₂,h₃]
  have hm (σ : Equiv.Perm (Fin 4)) :
      (∏ j ∈ J, a (σ j)) =
        ∑ k, (if J.map σ.toEmbedding = circleLinePair k then (1 : ℂ) else 0) *
          ∏ i ∈ circleLinePair k, a i := by
    obtain ⟨k, hk⟩ := circleLinePair_complete (J.map σ.toEmbedding) (by simpa only [Finset.card_map] using hJ)
    rw [Finset.sum_eq_single k, hk, if_pos rfl, one_mul]
    · simpa only [hk, Equiv.toEmbedding_apply] using (Finset.prod_map J σ.toEmbedding a).symm
    · intro l _ hl
      rw [if_neg (fun he => hl ((circleLinePair_injective (hk.trans he)).symm)), zero_mul]
    · intro hn
      exact (hn (Finset.mem_univ k)).elim
  have hmoment := commonSpectralMoment_eq_of_partner_agreement a w v h J
  have hz : (∑ σ, ((w σ - v σ : ℝ) : ℂ) * ∏ j ∈ J, a (σ j)) = 0 := by
    simpa only [commonSpectralMoment, ← Finset.sum_sub_distrib, ← sub_mul, Complex.ofReal_sub]
      using sub_eq_zero.mpr hmoment
  have hsum : (∑ k, (d (circleLinePair k) : ℂ) * ∏ i ∈ circleLinePair k, a i) = 0 := by
    rw [← hz]
    simp_rw [hm, Finset.mul_sum, ← mul_assoc]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    unfold d
    rw [Complex.ofReal_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro σ _
    split <;> simp only [Complex.ofReal_mul, Complex.ofReal_one, Complex.ofReal_zero, one_mul,
      zero_mul, mul_one, mul_zero]
  have hm' : (d {0,1} : ℂ) * (a 0 * a 1 + a 2 * a 3) +
      (d {0,2} : ℂ) * (a 0 * a 2 + a 1 * a 3) +
      (d {0,3} : ℂ) * (a 0 * a 3 + a 1 * a 2) = 0 := by
    have h := hsum
    have hp (i j : Fin 4) (hij : i ≠ j) : (∏ k ∈ ({i,j} : Finset (Fin 4)), a k) = a i * a j :=
      Finset.prod_pair hij
    norm_num [Fin.sum_univ_succ, circleLinePair, h01, h02, h03] at h
    simp only [hp 0 1 (by decide), hp 0 2 (by decide), hp 0 3 (by decide),
      hp 1 2 (by decide), hp 1 3 (by decide), hp 2 3 (by decide)] at h
    linear_combination h
  have hmass : ((d {0,1} : ℝ) : ℂ) + (d {0,2} : ℂ) + (d {0,3} : ℂ) = 0 := by
    exact_mod_cast h₀
  have he : (d {0,2} : ℂ) * ((a 0 * a 1 + a 2 * a 3) - (a 0 * a 2 + a 1 * a 3)) +
      (d {0,3} : ℂ) * ((a 0 * a 1 + a 2 * a 3) - (a 0 * a 3 + a 1 * a 2)) = 0 := by
    linear_combination (a 0 * a 1 + a 2 * a 3) * hmass - hm'
  obtain ⟨hzero₂, hzero₃⟩ := dividing_real_coordinates_independent _ _ hB hInd
    (d {0,2}) (d {0,3}) he
  have hzero₁ : d {0,1} = 0 := by linarith only [h₀,hzero₂,hzero₃]
  have hd : d I = 0 := by
    obtain ⟨k, rfl⟩ := circleLinePair_complete I hI
    fin_cases k <;> simp [circleLinePair, hzero₁,hzero₂,hzero₃,h01,h02,h03]
  apply sub_eq_zero.mp
  rw [← Finset.sum_sub_distrib]
  rw [Finset.sum_filter]
  unfold d at hd
  have hpoint (σ : Equiv.Perm (Fin 4)) :
      (if J.map σ.toEmbedding = I then (1 : ℝ) else 0) * (w σ - v σ) =
        if J.map σ.toEmbedding = I then w σ - v σ else 0 := by
    by_cases hσ : J.map σ.toEmbedding = I <;> simp [hσ]
  simpa only [hpoint] using hd

private def circleLinePairCrossRatio (a : Fin 4 → ℂ) : ℂ :=
  ((a 0 * a 1 + a 2 * a 3) - (a 0 * a 2 + a 1 * a 3)) /
    ((a 0 * a 1 + a 2 * a 3) - (a 0 * a 3 + a 1 * a 2))

private theorem circleLinePairCrossRatio_den (a : Fin 4 → ℂ) :
    (a 0 * a 1 + a 2 * a 3) - (a 0 * a 3 + a 1 * a 2) =
      (a 0 - a 2) * (a 1 - a 3) := by ring

private theorem generalizedCircle_of_real_pair_cross_ratio (a : Fin 4 → ℂ)
    (ha : Function.Injective a) (h : (circleLinePairCrossRatio a).im = 0) :
    SpectrumOnGeneralizedCircle a := by
  let x := a 0
  let y := a 1
  let z := a 2
  let t := a 3
  have hxy : x ≠ y := fun he => (by decide : (0 : Fin 4) ≠ 1) (ha he)
  have hxz : x - z ≠ 0 := sub_ne_zero.mpr fun he => (by decide : (0 : Fin 4) ≠ 2) (ha he)
  have hyz : y - z ≠ 0 := sub_ne_zero.mpr fun he => (by decide : (1 : Fin 4) ≠ 2) (ha he)
  have hty : t - y ≠ 0 := sub_ne_zero.mpr fun he => (by decide : (3 : Fin 4) ≠ 1) (ha he)
  let K := (y - z) / (x - z)
  have hK : K ≠ 0 := div_ne_zero hyz hxz
  let u := (K * (conj y + x)).im / 2
  let v := -(K * (x - conj y)).re / 2
  let c := (K * x * conj y).im
  have hformula (r : ℂ) : (K * (r - x) * conj (r - y)).im =
      K.im * Complex.normSq r - 2 * (u * r.re + v * r.im) + c := by
    dsimp only [u, v, c]
    simp only [Complex.normSq_apply, map_sub, Complex.mul_im, Complex.mul_re, Complex.sub_re,
      Complex.sub_im, Complex.conj_re, Complex.conj_im, Complex.add_re, Complex.add_im]
    ring
  refine ⟨K.im, u, v, c, ?_, ?_⟩
  · by_contra! hfalse
    obtain ⟨hq, hu, hv⟩ := hfalse
    have hk : K.re ≠ 0 := fun hr => hK (Complex.ext hr hq)
    have hr : K.re * (x.re - y.re) = 0 := by
      dsimp only [v] at hv
      simp only [Complex.mul_re, Complex.sub_re, Complex.conj_re, hq, zero_mul, sub_zero] at hv
      linear_combination -2 * hv
    have hi : K.re * (x.im - y.im) = 0 := by
      dsimp only [u] at hu
      simp only [Complex.mul_im, Complex.add_im, Complex.conj_im, hq, zero_mul, add_zero] at hu
      linear_combination 2 * hu
    exact hxy (Complex.ext (sub_eq_zero.mp ((mul_eq_zero.mp hr).resolve_left hk))
      (sub_eq_zero.mp ((mul_eq_zero.mp hi).resolve_left hk)))
  · intro i
    change K.im * Complex.normSq (a i) - 2 * (u * (a i).re + v * (a i).im) + c = 0
    rw [← hformula]
    fin_cases i
    · change (K * (x - x) * conj (x - y)).im = 0
      simp
    · change (K * (y - x) * conj (y - y)).im = 0
      simp
    · change (K * (z - x) * conj (z - y)).im = 0
      have he : K * (z - x) = z - y := by
        dsimp only [K]
        field_simp [hxz]
        ring
      rw [he, mul_comm, ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_im]
    · change (K * (t - x) * conj (t - y)).im = 0
      have he : K * (t - x) / (t - y) = circleLinePairCrossRatio a := by
        unfold circleLinePairCrossRatio
        rw [circleLinePairCrossRatio_den a,
          show a 0 * a 1 + a 2 * a 3 - (a 0 * a 2 + a 1 * a 3) = (x - t) * (y - z) by
            dsimp only [x,y,z,t]; ring]
        change (y - z) / (x - z) * (t - x) / (t - y) = (x - t) * (y - z) / ((x - z) * (y - t))
        have hyt : y - t ≠ 0 := sub_ne_zero.mpr (sub_ne_zero.mp hty).symm
        field_simp [hxz, hty, hyt] <;> ring
      rw [← div_mul_cancel₀ (K * (t - x)) hty, he, mul_assoc,
        mul_comm (t - y) (conj (t - y)), ← Complex.normSq_eq_conj_mul_self]
      simp only [Complex.mul_im, Complex.ofReal_im, h, mul_zero, zero_mul, add_zero]

private theorem injective_of_no_generalized_circle_four {a : Fin 4 → ℂ}
    (ha : ¬ SpectrumOnGeneralizedCircle a) : Function.Injective a := by
  classical
  intro i j hij
  by_contra hn
  apply ha
  apply spectrumOnGeneralizedCircle_of_card_range_le_three
  let S := (Finset.univ : Finset (Fin 4)).erase i
  letI : Fintype (Set.range a) := Fintype.ofFinite _
  let f (k : S) : Set.range a := ⟨a k.val, ⟨k.val, rfl⟩⟩
  have hf : Function.Surjective f := by
    rintro ⟨z, k, rfl⟩
    by_cases hk : k = i
    · subst k
      exact ⟨⟨j, Finset.mem_erase.mpr ⟨Ne.symm hn, Finset.mem_univ _⟩⟩, Subtype.ext hij.symm⟩
    · exact ⟨⟨k, Finset.mem_erase.mpr ⟨hk, Finset.mem_univ _⟩⟩, rfl⟩
  rw [Nat.card_eq_fintype_card]
  apply (Fintype.card_le_of_surjective f hf).trans
  simp [S, Fintype.card_coe]

/-- For a fixed spectrum off every circle and line, agreement for all
diagonal partners forces agreement on every squared minor of the mixer. -/
theorem commonWeights_four_minor_law_of_no_circle_or_line
    (a : Fin 4 → ℂ) (U : Matrix (Fin 4) (Fin 4) ℂ) (hU : IsUnitary U)
    (ha : ¬ SpectrumOnGeneralizedCircle a) (w : Equiv.Perm (Fin 4) → ℝ) (hs : ∑ σ, w σ = 1)
    (he : ∀ b, weightedMatchingValue a b w = determinantValue a b U) :
    ∀ I J : Finset (Fin 4), subsetMinorSq U I J =
      ∑ σ ∈ Finset.univ.filter (fun σ : Equiv.Perm (Fin 4) => J.map σ.toEmbedding = I), w σ := by
  classical
  let v := realSignedWeight U
  have hAgree : ∀ b, weightedMatchingValue a b w = weightedMatchingValue a b v := by
    intro b
    exact (he b).trans (real_signed_determinant a b U hU).symm
  have hInj := injective_of_no_generalized_circle_four ha
  have hV (I J : Finset (Fin 4)) :
      (∑ σ ∈ Finset.univ.filter (fun σ : Equiv.Perm (Fin 4) => J.map σ.toEmbedding = I), v σ) =
        subsetMinorSq U I J := by
    simpa only [v, realSignedWeight, Complex.re_sum, Complex.ofReal_re] using
      congrArg Complex.re (sum_signedWeight_image_eq_subsetMinorSq U hU I J)
  have hB : (a 0 * a 1 + a 2 * a 3) - (a 0 * a 3 + a 1 * a 2) ≠ 0 := by
    rw [circleLinePairCrossRatio_den]
    exact mul_ne_zero (sub_ne_zero.mpr fun h => (by decide : (0 : Fin 4) ≠ 2) (hInj h))
      (sub_ne_zero.mpr fun h => (by decide : (1 : Fin 4) ≠ 3) (hInj h))
  have hInd : (circleLinePairCrossRatio a).im ≠ 0 :=
    fun he => ha (generalizedCircle_of_real_pair_cross_ratio a hInj he)
  apply indexed_minor_law_of_small U hU id w
  intro I J hc hsmall
  simp only [id_eq]
  rw [← hV I J]
  rw [Fintype.card_fin] at hsmall
  have hcases : I.card = 0 ∨ I.card = 1 ∨ I.card = 2 := by omega
  rcases hcases with h₀ | h₁ | h₂
  · have hj : J.card = 0 := hc.symm.trans h₀
    rw [Finset.card_eq_zero.mp h₀, Finset.card_eq_zero.mp hj]
    simp [hs, v, sum_realSignedWeight U hU]
  · obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp h₁
    obtain ⟨j, rfl⟩ := Finset.card_eq_one.mp (hc.symm.trans h₁)
    simpa only [Finset.sum_filter, Finset.map_singleton, Equiv.toEmbedding_apply, Finset.singleton_inj]
      using (commonWeights_singletons_of_distinct a hInj w v hAgree i j).symm
  · exact (commonWeights_pair_images_of_independence a hInj w v hAgree hB hInd
      I J h₂ (hc.symm.trans h₂)).symm

/-- Order-four criterion for a fixed spectrum and every unitary mixer. -/
theorem commonWeights_four_iff_circle_or_line (a : Fin 4 → ℂ) :
    (∀ U : Matrix (Fin 4) (Fin 4) ℂ, IsUnitary U → HasCommonWeights a U) ↔
      SpectrumOnGeneralizedCircle a := by
  constructor
  · intro h
    by_contra ha
    have hU : IsUnitary fourCircleLineObstructionMixerᴴ :=
      ⟨by simpa only [Matrix.conjTranspose_conjTranspose] using isUnitary_fourCircleLineObstructionMixer.2,
        by simpa only [Matrix.conjTranspose_conjTranspose] using isUnitary_fourCircleLineObstructionMixer.1⟩
    obtain ⟨w, hw, hs, he⟩ := h _ hU
    have hm := commonWeights_four_minor_law_of_no_circle_or_line a _ hU ha w hs he
    apply no_fourCircleLine_weights_two_free_entries
    refine ⟨w, hw, hs, fun x y => ?_⟩
    exact determinantValue_eq_sum_of_indexed_minor_law _ _ _ hU id w hm
  · exact fun h U hU => commonWeights_four_of_circle_or_line a U hU h

/-- The same weights for every diagonal shift give the principal minors
of the fixed matrix. -/
theorem principalMinor_eq_commonSpectralMoment {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (a : ι → ℂ) (w : Equiv.Perm ι → ℝ)
    (h : ∀ b, weightedMatchingValue a b w = (A + diagonal b).det) (S : Finset ι) :
    (A.submatrix (fun i : S => (i : ι)) (fun i : S => (i : ι))).det =
      commonSpectralMoment a w S := by
  classical
  let r (t : ℂ) (j : ι) : ℂ := if j ∈ S then 1 else t
  let p (t : ℂ) (j : ι) : ℂ := if j ∈ S then 0 else t⁻¹
  let d (j : ι) : ℂ := if j ∈ S then 0 else 1
  let X (t : ℂ) : Matrix ι ι ℂ := Matrix.of fun i j => r t j * A i j + diagonal d i j
  let f (t : ℂ) (σ : Equiv.Perm ι) (j : ι) : ℂ := r t j * a (σ j) + d j
  let W (t : ℂ) : ℂ := ∑ σ, (w σ : ℂ) * ∏ j, f t σ j
  have hfactor (t : ℂ) (ht : t ≠ 0) (j : ι) : r t j * p t j = d j := by
    by_cases hj : j ∈ S
    · simp only [r, p, d, if_pos hj, mul_zero]
    · simp only [r, p, d, if_neg hj, mul_inv_cancel₀ ht]
  have hX (t : ℂ) (ht : t ≠ 0) :
      X t = Matrix.of (fun i j => r t j * (A + diagonal (p t)) i j) := by
    ext i j : 1
    change r t j * A i j + diagonal d i j = r t j * (A + diagonal (p t)) i j
    rw [Matrix.add_apply, mul_add]
    by_cases hij : i = j
    · subst i
      rw [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq, hfactor t ht j]
    · simp only [Matrix.diagonal_apply, if_neg hij, mul_zero]
  have hW (t : ℂ) (ht : t ≠ 0) :
      W t = (∏ j, r t j) * weightedMatchingValue a (p t) w := by
    unfold W weightedMatchingValue matchingProduct
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro σ _
    rw [mul_left_comm (∏ j, r t j) (w σ : ℂ), ← Finset.prod_mul_distrib]
    congr 1
    apply Finset.prod_congr rfl
    intro j _
    change r t j * a (σ j) + d j = r t j * (a (σ j) + p t j)
    rw [mul_add, hfactor t ht j]
  have hgen : Set.EqOn (fun t => (X t).det) W ({0} : Set ℂ)ᶜ := by
    intro t ht
    have ht' : t ≠ 0 := by simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using ht
    change (X t).det = W t
    rw [hX t ht', Matrix.det_mul_row, hW t ht', h (p t)]
  have hr (j : ι) : Continuous (fun t => r t j) := by
    by_cases hj : j ∈ S
    · simpa only [r, if_pos hj] using (continuous_const : Continuous (fun _ : ℂ => (1 : ℂ)))
    · simpa only [r, if_neg hj] using (continuous_id : Continuous (fun t : ℂ => t))
  have hcontX : Continuous (fun t => (X t).det) := by
    apply Continuous.matrix_det
    apply continuous_matrix
    intro i j
    exact ((hr j).mul continuous_const).add continuous_const
  have hcontW : Continuous W :=
    continuous_finset_sum _ fun σ _ => continuous_const.mul
      (continuous_finset_prod _ fun j _ => ((hr j).mul continuous_const).add continuous_const)
  have heq : (X 0).det = W 0 :=
    hgen.closure hcontX hcontW (dense_compl_singleton (0 : ℂ) 0)
  let K := {j : ι // j ∉ S}
  let e : S ⊕ K ≃ ι := Equiv.sumCompl (fun j => j ∈ S)
  let N := A.submatrix (fun i : S => (i : ι)) (fun i : S => (i : ι))
  let Q := A.submatrix (fun i : K => (i : ι)) (fun i : S => (i : ι))
  have hBlock : (X 0).submatrix e e = Matrix.fromBlocks N 0 Q 1 := by
    ext (i | i) (j | j) : 1
    · change r 0 j * A i j + diagonal d i j = N i j
      by_cases hij : (i : ι) = j <;>
        simp [r, d, N, i.property, j.property, Matrix.diagonal_apply, hij]
    · change r 0 j * A i j + diagonal d i j = 0
      have hij : (i : ι) ≠ j := fun he => j.property (he ▸ i.property)
      simp only [r, if_neg j.property, zero_mul, Matrix.diagonal_apply, if_neg hij, add_zero]
    · change r 0 j * A i j + diagonal d i j = Q i j
      have hij : (i : ι) ≠ j := fun he => i.property (he.symm ▸ j.property)
      simp only [r, if_pos j.property, one_mul, Matrix.diagonal_apply, if_neg hij, add_zero,
        Q, Matrix.submatrix_apply]
    · change r 0 j * A i j + diagonal d i j = (1 : Matrix K K ℂ) i j
      by_cases hij : i = j
      · subst j
        simp only [r, d, if_neg i.property, zero_mul, Matrix.diagonal_apply_eq, zero_add,
          Matrix.one_apply_eq]
      · have hv : (i : ι) ≠ j := fun he => hij (Subtype.ext he)
        simp only [r, if_neg j.property, zero_mul, Matrix.diagonal_apply, if_neg hv,
          zero_add, Matrix.one_apply, if_neg hij]
  have hdet : (X 0).det = N.det := by
    rw [← Matrix.det_submatrix_equiv_self e (X 0), hBlock, Matrix.det_fromBlocks_zero₁₂,
      Matrix.det_one, mul_one]
  have hprod (σ : Equiv.Perm ι) : (∏ j, f 0 σ j) = ∏ j ∈ S, a (σ j) := calc
    _ = ∏ j ∈ S, f 0 σ j := by
      symm
      apply Finset.prod_subset (Finset.subset_univ S)
      intro j _ hj
      simp only [f, r, d, if_neg hj, zero_mul, zero_add]
    _ = _ := Finset.prod_congr rfl fun j hj => by
      simp only [f, r, d, if_pos hj, one_mul, add_zero]
  simpa only [hdet, N, W, hprod, commonSpectralMoment] using heq

/-- One law represents every principal minor of a unitary conjugate of
a real diagonal matrix in order four. -/
theorem commonPrincipalMinorWeights_four (a : Fin 4 → ℝ) (U : Matrix (Fin 4) (Fin 4) ℂ)
    (hU : IsUnitary U) :
    ∃ w : Equiv.Perm (Fin 4) → ℝ, (∀ σ, 0 ≤ w σ) ∧ (∑ σ, w σ = 1) ∧
      ∀ S : Finset (Fin 4),
        ((U * diagonal (fun i => (a i : ℂ)) * Uᴴ).submatrix
          (fun i : S => (i : Fin 4)) (fun i : S => (i : Fin 4))).det =
            commonSpectralMoment (fun i => (a i : ℂ)) w S := by
  let b (i : Fin 4) : ℂ := a i
  have hU' : IsUnitary Uᴴ :=
    ⟨by simpa only [Matrix.conjTranspose_conjTranspose] using hU.2,
      by simpa only [Matrix.conjTranspose_conjTranspose] using hU.1⟩
  obtain ⟨w, hw, hsum, h⟩ := commonWeights_four_real_spectrum a Uᴴ hU'
  refine ⟨w, hw, hsum, fun S => principalMinor_eq_commonSpectralMoment
    (U * diagonal b * Uᴴ) b w (fun q => ?_) S⟩
  exact (h q).trans (determinantValue_left_conjugation b q U hU).symm

/-- A real linear objective on the principal minors of a complex matrix. -/
def fourPrincipalMinorScore (c : Finset (Fin 4) → ℝ) (A : Matrix (Fin 4) (Fin 4) ℂ) : ℝ :=
  ∑ S : Finset (Fin 4), c S *
    (A.submatrix (fun i : S => (i : Fin 4)) (fun i : S => (i : Fin 4))).det.re

private theorem fourPrincipalMinorScore_diagonal (c : Finset (Fin 4) → ℝ) (a : Fin 4 → ℝ) :
    fourPrincipalMinorScore c (diagonal (fun i => (a i : ℂ))) =
      ∑ S : Finset (Fin 4), c S * ∏ i ∈ S, a i := by
  unfold fourPrincipalMinorScore
  apply Finset.sum_congr rfl
  intro S _
  congr 1
  have hd : (diagonal (fun i => (a i : ℂ))).submatrix
      (fun i : S => (i : Fin 4)) (fun i : S => (i : Fin 4)) =
        diagonal (fun i : S => (a i : ℂ)) := by
    ext i j : 1
    by_cases he : i = j
    · subst j
      simp
    · have hv : (i : Fin 4) ≠ j := fun h => he (Subtype.ext h)
      simp [Matrix.diagonal_apply, he, hv]
  rw [hd, Matrix.det_diagonal, ← Complex.ofReal_prod, Complex.ofReal_re, Finset.prod_coe_sort]

private theorem fourPrincipalMinorScore_convex (c : Finset (Fin 4) → ℝ) (a : Fin 4 → ℝ)
    (U : Matrix (Fin 4) (Fin 4) ℂ) (hU : IsUnitary U) :
    ∃ w : Equiv.Perm (Fin 4) → ℝ, (∀ σ, 0 ≤ w σ) ∧ (∑ σ, w σ = 1) ∧
      fourPrincipalMinorScore c (U * diagonal (fun i => (a i : ℂ)) * Uᴴ) =
        ∑ σ, w σ * fourPrincipalMinorScore c (diagonal (fun i => (a (σ i) : ℂ))) := by
  obtain ⟨w, hw, hsum, h⟩ := commonPrincipalMinorWeights_four a U hU
  refine ⟨w, hw, hsum, ?_⟩
  have hm (S : Finset (Fin 4)) :
      (commonSpectralMoment (fun i => (a i : ℂ)) w S).re =
        ∑ σ, w σ * ∏ i ∈ S, a (σ i) := by
    simp only [commonSpectralMoment, Complex.re_sum, ← Complex.ofReal_prod,
      ← Complex.ofReal_mul, Complex.ofReal_re]
  conv_lhs =>
    rw [fourPrincipalMinorScore]
    simp only [h, hm]
  have hd (σ : Equiv.Perm (Fin 4)) :
      fourPrincipalMinorScore c (diagonal (fun i => (a (σ i) : ℂ))) =
        ∑ S : Finset (Fin 4), c S * ∏ i ∈ S, a (σ i) :=
    fourPrincipalMinorScore_diagonal c (a ∘ σ)
  simp_rw [hd, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro σ _
  apply Finset.sum_congr rfl
  intro S _
  ring

/-- A diagonal permutation maximizes every real linear objective on the
principal minors of the order-four Hermitian orbit. -/
theorem exists_diagonal_maximizer_four_principal_minors
    (a : Fin 4 → ℝ) (c : Finset (Fin 4) → ℝ) :
    ∃ σ : Equiv.Perm (Fin 4),
      (∃ U : Matrix (Fin 4) (Fin 4) ℂ, IsUnitary U ∧
        U * diagonal (fun i => (a i : ℂ)) * Uᴴ = diagonal (fun i => (a (σ i) : ℂ))) ∧
      ∀ U : Matrix (Fin 4) (Fin 4) ℂ, IsUnitary U →
        fourPrincipalMinorScore c (U * diagonal (fun i => (a i : ℂ)) * Uᴴ) ≤
          fourPrincipalMinorScore c (diagonal (fun i => (a (σ i) : ℂ))) := by
  classical
  let F (σ : Equiv.Perm (Fin 4)) :=
    fourPrincipalMinorScore c (diagonal (fun i => (a (σ i) : ℂ)))
  obtain ⟨σ, _, hσ⟩ := Finset.exists_max_image Finset.univ F Finset.univ_nonempty
  refine ⟨σ, ⟨σ.permMatrix ℂ, isUnitary_permMatrix σ, ?_⟩, fun U hU => ?_⟩
  · rw [permMatrix_conjugates, Matrix.submatrix_diagonal_equiv] <;> rfl
  · obtain ⟨w, hw, hsum, h⟩ := fourPrincipalMinorScore_convex c a U hU
    rw [h]
    change (∑ τ, w τ * F τ) ≤ F σ
    calc
      _ ≤ ∑ τ, w τ * F σ := Finset.sum_le_sum fun τ _ =>
        mul_le_mul_of_nonneg_left (hσ τ (Finset.mem_univ τ)) (hw τ)
      _ = F σ := by rw [← Finset.sum_mul, hsum, one_mul]

/-- A real linear objective on the principal minors of a real matrix. -/
def fourRealPrincipalMinorScore (c : Finset (Fin 4) → ℝ) (A : Matrix (Fin 4) (Fin 4) ℝ) : ℝ :=
  ∑ S : Finset (Fin 4), c S *
    (A.submatrix (fun i : S => (i : Fin 4)) (fun i : S => (i : Fin 4))).det

private theorem fourPrincipalMinorScore_ofReal (c : Finset (Fin 4) → ℝ)
    (A : Matrix (Fin 4) (Fin 4) ℝ) :
    fourPrincipalMinorScore c (Complex.ofRealHom.mapMatrix A) = fourRealPrincipalMinorScore c A := by
  unfold fourPrincipalMinorScore fourRealPrincipalMinorScore
  apply Finset.sum_congr rfl
  intro S _
  congr 1
  rw [RingHom.mapMatrix_apply, Matrix.submatrix_map]
  exact congrArg Complex.re (Complex.ofRealHom.map_det _).symm

/-- A diagonal permutation also attains the maximum on the real symmetric orbit. -/
theorem exists_diagonal_maximizer_four_real_principal_minors
    (a : Fin 4 → ℝ) (c : Finset (Fin 4) → ℝ) :
    ∃ σ : Equiv.Perm (Fin 4),
      (∃ O : Matrix.orthogonalGroup (Fin 4) ℝ,
        O.val * diagonal a * O.valᵀ = diagonal (a ∘ σ)) ∧
      ∀ O : Matrix.orthogonalGroup (Fin 4) ℝ,
        fourRealPrincipalMinorScore c (O.val * diagonal a * O.valᵀ) ≤
          fourRealPrincipalMinorScore c (diagonal (a ∘ σ)) := by
  classical
  let f : Matrix (Fin 4) (Fin 4) ℝ →+* Matrix (Fin 4) (Fin 4) ℂ :=
    Complex.ofRealHom.mapMatrix
  have hf : Function.Injective f := by
    intro A B h
    ext i j : 1
    exact Complex.ofReal_injective (congrArg (fun C : Matrix (Fin 4) (Fin 4) ℂ => C i j) h)
  have hd (b : Fin 4 → ℝ) : f (diagonal b) = diagonal (fun i => (b i : ℂ)) := by
    ext i j : 1
    by_cases h : i = j <;> simp [f, Matrix.diagonal_apply, h]
  have hstar (M : Matrix (Fin 4) (Fin 4) ℝ) : f Mᵀ = (f M)ᴴ := by
    ext i j : 1
    exact (Complex.conj_ofReal (M j i)).symm
  have hp (τ : Equiv.Perm (Fin 4)) : f (τ.permMatrix ℝ) = τ.permMatrix ℂ := by
    ext i j : 1
    by_cases h : τ i = j <;>
      simp [f, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, h, eq_comm]
  obtain ⟨σ, _, hσ⟩ := exists_diagonal_maximizer_four_principal_minors a c
  let P := σ.permMatrix ℝ
  have hP : P ∈ Matrix.orthogonalGroup (Fin 4) ℝ := by
    apply (Matrix.mem_orthogonalGroup_iff _ _).mpr
    apply hf
    change f (P * Pᵀ) = f 1
    rw [f.map_mul, hstar, f.map_one, show f P = σ.permMatrix ℂ from hp σ]
    exact (isUnitary_permMatrix σ).1
  refine ⟨σ, ⟨⟨P, hP⟩, ?_⟩, fun O => ?_⟩
  · change P * diagonal a * Pᵀ = diagonal (a ∘ σ)
    apply hf
    rw [f.map_mul, f.map_mul, hd, hd, hstar, show f P = σ.permMatrix ℂ from hp σ,
      permMatrix_conjugates, Matrix.submatrix_diagonal_equiv] <;> rfl
  · have hv := hσ (f O.val) (isUnitary_ofReal_orthogonal O)
    have he : diagonal (fun i => (a (σ i) : ℂ)) = f (diagonal (a ∘ σ)) := (hd (a ∘ σ)).symm
    rw [← hstar O.val, ← hd a, ← f.map_mul, ← f.map_mul,
      he] at hv
    simpa only [f, fourPrincipalMinorScore_ofReal] using hv

end

end MOC
