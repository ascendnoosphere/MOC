import MOC.FourSupportConeClassification
import MOC.FourMixedRayCancellation
import MOC.Support

/-! Holden's fourteen-term expansion for order-four matching costs and the
effect of a contact on the mixed-ray obstruction.
The coefficient table is Theorem 2.1 of
https://raw.githubusercontent.com/ajt60gaibb/OpenProblemsInNLA/eb7c9d64f91757a82fbe9167e80ab9c1b7f36c22/references/holden-mi05-2026-09-13/report.pdf .
-/

open BigOperators

namespace MOC

noncomputable section

/-- The fourteen matchings in Holden's expansion, in the row-to-column
lexicographic coordinates of the support cone. -/
def holdenFourteenTermIndex (i : Fin 14) : Fin 24 :=
  ![0, 4, 15, 19, 8, 7, 16, 23, 13, 10, 22, 17, 9, 18] i

private def holdenFourteenTermFeature (i : Fin 14) : Fin 34 :=
  ![0, 0, 5, 10, 15, 16, 23, 30, 17, 20, 24, 25, 28, 33] i

private def holdenBalanceInt (p : Fin 24) : ℤ :=
  ordinaryCostRayInt 0 p + ordinaryCostRayInt 5 p + ordinaryCostRayInt 10 p +
  ordinaryCostRayInt 15 p + ordinaryCostRayInt 17 p + ordinaryCostRayInt 20 p -
  ordinaryCostRayInt 22 p - ordinaryCostRayInt 27 p

private def holdenFourteenTermNumerator (i : Fin 14) (p : Fin 24) : ℤ :=
  if i = 0 then holdenBalanceInt p
  else if i.val ≤ 7 then
    4 * ordinaryCostRayInt (holdenFourteenTermFeature i) p - holdenBalanceInt p
  else 4 * ordinaryCostRayInt (holdenFourteenTermFeature i) p

set_option maxRecDepth 4096 in
set_option maxHeartbeats 3000000 in
private theorem holdenFourteenTermGenerator (r : Fin 34) (p : Fin 24) :
    4 * ordinaryCostRayInt r p = ∑ i : Fin 14,
      ordinaryCostRayInt r (holdenFourteenTermIndex i) * holdenFourteenTermNumerator i p := by
  have h : ∀ (r : Fin 34) (p : Fin 24),
      4 * ordinaryCostRayInt r p = ∑ i : Fin 14,
        ordinaryCostRayInt r (holdenFourteenTermIndex i) * holdenFourteenTermNumerator i p := by
    intro r
    fin_cases r <;> decide +kernel
  exact h r p

private theorem holdenFourteenTermProfile (g : Fin 24 → ℝ)
    (hg : g ∈ Submodule.span ℝ (Set.range ordinaryCostRay)) :
    (4 : ℝ) • g = ∑ i : Fin 14, g (holdenFourteenTermIndex i) •
      (fun p => (holdenFourteenTermNumerator i p : ℝ)) := by
  induction hg using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨r, rfl⟩ := hg
    funext p
    have h := congrArg (Int.cast : ℤ → ℝ) (holdenFourteenTermGenerator r p)
    simpa only [Int.cast_mul, Int.cast_ofNat, Int.cast_sum, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul, ordinaryCostRay] using h
  | zero => simp
  | add f g _ _ hf hg =>
    rw [smul_add, hf, hg, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [Pi.add_apply, add_smul]
  | smul c g _ hg =>
    rw [smul_smul, mul_comm (4 : ℝ) c, ← smul_smul, hg, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Pi.smul_apply, smul_eq_mul, mul_smul]

/-- Holden's signed coefficient at the given matching. The numerator uses
ordinary minor profiles, whose mixer evaluations are squared minors. -/
def holdenFourteenTermWeight (U : Matrix (Fin 4) (Fin 4) ℂ) (i : Fin 14) : ℝ :=
  fourSupportCostValue U (fun p => (holdenFourteenTermNumerator i p : ℝ)) / 4

/-- The fourteen-term expansion on the entire span of ordinary minor
indicators. In particular it applies to actual matching-product costs. -/
theorem holdenFourteenTerm_evaluation (U : Matrix (Fin 4) (Fin 4) ℂ)
    (g : Fin 24 → ℝ) (hg : g ∈ Submodule.span ℝ (Set.range ordinaryCostRay)) :
    fourSupportCostValue U g =
      ∑ i : Fin 14, holdenFourteenTermWeight U i * g (holdenFourteenTermIndex i) := by
  have h := congrArg (fourSupportCostValue U) (holdenFourteenTermProfile g hg)
  simp only [map_smul, map_sum, smul_eq_mul] at h
  have hsum :
      (∑ i : Fin 14, holdenFourteenTermWeight U i * g (holdenFourteenTermIndex i)) =
        (∑ i : Fin 14, g (holdenFourteenTermIndex i) *
          fourSupportCostValue U (fun p => (holdenFourteenTermNumerator i p : ℝ))) / 4 := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    unfold holdenFourteenTermWeight
    ring
  rw [hsum, ← h]
  ring

/-- At a negative anchor weight, all thirteen other weights are
nonnegative. The first seven add the opposite of the anchor weight to an
ordinary squared minor, and the other six consist of an ordinary minor. -/
theorem holdenFourteenTerm_nonneg_away_from_anchor (U : Matrix (Fin 4) (Fin 4) ℂ)
    (hU : IsUnitary U) (hanchor : holdenFourteenTermWeight U 0 ≤ 0)
    (i : Fin 14) (hi : i ≠ 0) : 0 ≤ holdenFourteenTermWeight U i := by
  let c : Fin 24 → ℝ := fun p => (holdenBalanceInt p : ℝ)
  let r := holdenFourteenTermFeature i
  have h0 : holdenFourteenTermWeight U 0 = fourSupportCostValue U c / 4 := by
    simp only [holdenFourteenTermWeight, holdenFourteenTermNumerator, if_pos rfl, if_true, c]
  have hc : fourSupportCostValue U c ≤ 0 := by
    rw [h0] at hanchor
    linarith only [hanchor]
  have hr : 0 ≤ fourSupportCostValue U (ordinaryCostRay r) := by
    rw [fourSupportCostValue_ordinaryRay U hU]
    exact subsetMinorSq_nonneg U _ _
  by_cases hseven : i.val ≤ 7
  · have he : (fun p => (holdenFourteenTermNumerator i p : ℝ)) =
        (4 : ℝ) • ordinaryCostRay r - c := by
      funext p
      simp only [holdenFourteenTermNumerator, if_neg hi, if_pos hseven, c, r,
        ordinaryCostRay, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Int.cast_sub,
        Int.cast_mul, Int.cast_ofNat]
    rw [holdenFourteenTermWeight, he, map_sub, map_smul, smul_eq_mul]
    exact div_nonneg (sub_nonneg.mpr (hc.trans (mul_nonneg (by norm_num) hr))) (by norm_num)
  · have he : (fun p => (holdenFourteenTermNumerator i p : ℝ)) =
        (4 : ℝ) • ordinaryCostRay r := by
      funext p
      simp only [holdenFourteenTermNumerator, if_neg hi, if_neg hseven, r,
        ordinaryCostRay, Pi.smul_apply, smul_eq_mul, Int.cast_mul, Int.cast_ofNat]
    rw [holdenFourteenTermWeight, he, map_smul, smul_eq_mul]
    exact div_nonneg (mul_nonneg (by norm_num) hr) (by norm_num)

private def canonicalHoldenTermIndex (i : Fin 14) : Fin 24 :=
  ![5, 1, 22, 17, 6, 9, 18, 14, 23, 7, 12, 20, 8, 15] i

private theorem canonicalHoldenTermIndex_relabel (i : Fin 14) :
    fourCostRelabelIndex 1 4 (canonicalHoldenTermIndex i) = holdenFourteenTermIndex i := by
  exact (by decide +kernel : ∀ j : Fin 14,
    fourCostRelabelIndex 1 4 (canonicalHoldenTermIndex j) = holdenFourteenTermIndex j) i

private def holdenAddedTermIndex (i : Fin 7) : Fin 14 :=
  Fin.succ (Fin.castLE (by decide : 7 ≤ 13) i)

/-- The seven-gap sum in the positive part of the signed expansion,
minus the anchor gap, in the canonical mixed-ray coordinates. -/
def canonicalHoldenSevenGap : (Fin 24 → ℝ) →ₗ[ℝ] ℝ :=
  (∑ i : Fin 7, LinearMap.proj (canonicalHoldenTermIndex (holdenAddedTermIndex i))) -
    LinearMap.proj (canonicalHoldenTermIndex 0)

private theorem canonicalHoldenSevenGap_apply (g : Fin 24 → ℝ) :
    canonicalHoldenSevenGap g =
      (∑ i : Fin 7, g (canonicalHoldenTermIndex (holdenAddedTermIndex i))) -
        g (canonicalHoldenTermIndex 0) := by
  simp only [canonicalHoldenSevenGap, LinearMap.sub_apply, LinearMap.sum_apply,
    LinearMap.proj_apply]

/-- The seven-gap sum alone leaves a shortfall of twice the mixed
coefficient. The other squared-minor contributions are needed in this
branch of the expansion. -/
theorem canonicalHoldenSevenGap_mixed (t : ℝ) {o : Fin 24 → ℝ}
    (ho : fourOrdinaryCostCone fourCanonicalCapOrdinaryRays o) :
    canonicalHoldenSevenGap (o + t • mixedCostRay 0) = -2 * t := by
  have hmixInt :
      (∑ i : Fin 7, mixedCostRayInt 0 (canonicalHoldenTermIndex (holdenAddedTermIndex i))) -
        mixedCostRayInt 0 (canonicalHoldenTermIndex 0) = -2 := by
    decide +kernel
  have hmix : canonicalHoldenSevenGap (mixedCostRay 0) = -2 := by
    rw [canonicalHoldenSevenGap_apply]
    simpa only [Int.cast_sub, Int.cast_sum, Int.cast_neg, Int.cast_ofNat, mixedCostRay] using
      congrArg (Int.cast : ℤ → ℝ) hmixInt
  have hordInt : ∀ k : Fin 34, k ∈ fourCanonicalCapOrdinaryRays →
      (∑ i : Fin 7, ordinaryCostRayInt k (canonicalHoldenTermIndex (holdenAddedTermIndex i))) -
        ordinaryCostRayInt k (canonicalHoldenTermIndex 0) = 0 := by
    intro k
    fin_cases k <;> decide +kernel
  obtain ⟨c, _, hsupp, rfl⟩ := ho
  have hterm (k : Fin 34) : c k * canonicalHoldenSevenGap (ordinaryCostRay k) = 0 := by
    by_cases hk : k ∈ fourCanonicalCapOrdinaryRays
    · have hzero : canonicalHoldenSevenGap (ordinaryCostRay k) = 0 := by
        rw [canonicalHoldenSevenGap_apply]
        simpa only [Int.cast_sub, Int.cast_sum, Int.cast_zero, ordinaryCostRay] using
          congrArg (Int.cast : ℤ → ℝ) (hordInt k hk)
      rw [hzero, mul_zero]
    · rw [hsupp k hk, zero_mul]
  simp only [map_add, map_smul, map_sum, smul_eq_mul, hterm, Finset.sum_const_zero,
    hmix, zero_add]
  ring

/-- Two distinct mixed rays cannot both have negative value at a unitary. -/
theorem four_negativeMixedRay_unique (U : Matrix (Fin 4) (Fin 4) ℂ) (hU : IsUnitary U)
    (r s : Fin 48) (hr : fourSupportCostValue U (mixedCostRay r) < 0)
    (hs : fourSupportCostValue U (mixedCostRay s) < 0) :
    r = s := by
  by_contra hrs
  have h := fourSupportCostValue_ordinaryNonnegative U hU (fourMixedPair_cancels r s hrs)
  rw [map_add] at h
  linarith only [h, hr, hs]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 3000000 in
private theorem mixedCostRay_nonnegative (r : Fin 48) (p : Fin 24) :
    0 ≤ mixedCostRay r p := by
  have h : ∀ (r : Fin 48) (p : Fin 24), 0 ≤ mixedCostRayInt r p := by
    intro r
    fin_cases r <;> decide +kernel
  change 0 ≤ (mixedCostRayInt r p : ℝ)
  exact Int.cast_nonneg.mpr (h r p)

/-- A contact at a positive coordinate of every negatively evaluated mixed
ray suffices for a nonnegative support value. There is at most one such ray. -/
theorem fourSupportCostValue_nonneg_of_contacts (U : Matrix (Fin 4) (Fin 4) ℂ)
    (hU : IsUnitary U) {g : Fin 24 → ℝ} (hg : FourSupportCost g)
    (hcontact : ∀ r : Fin 48, fourSupportCostValue U (mixedCostRay r) < 0 →
      ∃ p : Fin 24, g p = 0 ∧ 0 < mixedCostRay r p) :
    0 ≤ fourSupportCostValue U g := by
  obtain ⟨⟨m, rfl⟩, hn⟩ := hg
  obtain ⟨a, b, ha, hb, hdecomp⟩ := four_cost_cone_decomposition m hn
  rw [hdecomp, map_add, map_sum, map_sum]
  simp only [map_smul, smul_eq_mul]
  apply add_nonneg
  · apply Finset.sum_nonneg
    intro i _
    rw [fourSupportCostValue_ordinaryRay U hU]
    exact mul_nonneg (ha i) (subsetMinorSq_nonneg U _ _)
  · apply Finset.sum_nonneg
    intro r _
    by_cases hr : 0 ≤ fourSupportCostValue U (mixedCostRay r)
    · exact mul_nonneg (hb r) hr
    · obtain ⟨p, hp, hrp⟩ := hcontact r (lt_of_not_ge hr)
      have hsingle : b r * mixedCostRay r p ≤ ∑ i, b i * mixedCostRay i p :=
        Finset.single_le_sum (fun i _ => mul_nonneg (hb i) (mixedCostRay_nonnegative i p))
          (Finset.mem_univ r)
      have hord : 0 ≤ ∑ i, a i * ordinaryCostRay i p := by
        apply Finset.sum_nonneg
        intro i _
        apply mul_nonneg (ha i)
        rw [ordinaryCostRay, ordinaryCostRayInt_indicator]
        split <;> norm_num
      have hsum : (∑ i, a i * ordinaryCostRay i p) + ∑ i, b i * mixedCostRay i p = 0 := by
        simpa only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using
          (congrFun hdecomp p).symm.trans hp
      have hzero : b r = 0 := by
        have hterm : b r * mixedCostRay r p ≤ 0 := by
          linarith only [hsingle, hord, hsum]
        exact le_antisymm (nonpos_of_mul_nonpos_left hterm hrp) (hb r)
      rw [hzero, zero_mul]

/-- A nonnegative spectral gap at a maximizing matching lies in the
order-four support cone. -/
theorem fourSpectralGap_mem_supportCost (a b : Fin 4 → ℂ) (η : ℂ) (r : Equiv.Perm (Fin 4))
    (hmax : ∀ s : Equiv.Perm (Fin 4), 0 ≤ matchingGap a b η r s) :
    FourSupportCost (fun p : Fin 24 => matchingGap a b η r (fourPerm p).symm) := by
  refine ⟨?_, fun p => hmax (fourPerm p).symm⟩
  let H : ℝ := (η * matchingProduct a b r).re
  let c (i : Fin 14) := ((H : ℂ) * fourNoncrossingCoordinates
    (fourSpectralPoints (fun _ => 1) (fun _ => 0)) i).re
  let m (i : Fin 14) := (η * fourNoncrossingCoordinates (fourSpectralPoints a b) i).re
  have hc (p : Fin 24) : fourMatchingEvaluation c p = H := by
    simpa only [c, matchingProduct, add_zero, Finset.prod_const_one, mul_one, Complex.ofReal_re] using
      fourMatchingEvaluation_spectral_real_part (fun _ => 1) (fun _ => 0) (H : ℂ) p
  have hconst : (fun _ : Fin 24 => H) ∈ realMatchingFunctionSpace := ⟨c, funext hc⟩
  have hscore : (fun p : Fin 24 => (η * matchingProduct a b (fourPerm p).symm).re) ∈
      realMatchingFunctionSpace :=
    ⟨m, funext (fourMatchingEvaluation_spectral_real_part a b η)⟩
  exact realMatchingFunctionSpace.sub_mem hconst hscore

/-- The directional order-four determinant bound when each negatively
evaluated mixed ray has a positive coordinate at a maximizing matching. -/
theorem four_support_bound_of_mixedRay_contacts (a b : Fin 4 → ℂ)
    (U : Matrix (Fin 4) (Fin 4) ℂ) (hU : IsUnitary U) (η : ℂ) (r : Equiv.Perm (Fin 4))
    (hmax : ∀ s : Equiv.Perm (Fin 4), 0 ≤ matchingGap a b η r s)
    (hcontact : ∀ i : Fin 48, fourSupportCostValue U (mixedCostRay i) < 0 →
      ∃ p : Fin 24, matchingGap a b η r (fourPerm p).symm = 0 ∧ 0 < mixedCostRay i p) :
    (η * determinantValue a b U).re ≤ (η * matchingProduct a b r).re := by
  apply sub_nonneg.mp
  rw [support_gap_eq a b U hU η r]
  let e : Fin 24 ≃ Equiv.Perm (Fin 4) := fourPermEquiv.trans (Equiv.inv (Equiv.Perm (Fin 4)))
  rw [← Equiv.sum_comp e (fun s => realSignedWeight U s * matchingGap a b η r s)]
  exact fourSupportCostValue_nonneg_of_contacts U hU
    (fourSpectralGap_mem_supportCost a b η r hmax) hcontact

/-- A unitary with nonnegative evaluation on all mixed rays satisfies
the order-four inclusion for all pairs of spectra. -/
theorem four_holds_of_nonnegative_mixed_rays (a b : Fin 4 → ℂ)
    (U : Matrix (Fin 4) (Fin 4) ℂ) (hU : IsUnitary U)
    (hmixed : ∀ i : Fin 48, 0 ≤ fourSupportCostValue U (mixedCostRay i)) :
    Holds a b U := by
  classical
  apply (holds_iff_directional a b U).mpr
  intro η
  obtain ⟨r, _, hr⟩ := Finset.exists_max_image Finset.univ
    (fun s : Equiv.Perm (Fin 4) => (η * matchingProduct a b s).re)
    ⟨Equiv.refl (Fin 4), Finset.mem_univ _⟩
  refine ⟨r, four_support_bound_of_mixedRay_contacts a b U hU η r ?_ ?_⟩
  · intro s
    exact sub_nonneg.mpr (hr s (Finset.mem_univ s))
  · intro i hi
    exact (not_lt_of_ge (hmixed i) hi).elim

end

end MOC
