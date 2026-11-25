import MOC.FourFourteenTermSupport
import MOC.FourMinorTransport
import MOC.FourQuaternionMinor

/-! A bound on the order-four determinant outside the matching hull. The
bound uses the actual gaps on the support of the negative mixed ray. -/

open BigOperators Matrix

namespace MOC

noncomputable section

private def mixedBoundRows : Fin 4 → Finset (Fin 4) :=
  ![{1}, {2}, {2, 3}, {1, 3}]

private def mixedBoundColumns : Fin 4 → Finset (Fin 4) :=
  ![{2}, {1}, {2, 3}, {0, 2}]

-- Permutation 3 sends rows 1, 2, and 3 to 2, 3, and 1 in the seed.
private def mixedBoundRowPerm (r : Fin 48) : FourPerm :=
  fourPerm ⟨r.val % 24, Nat.mod_lt _ (by decide)⟩ * fourPerm 3

private def mixedBoundColumnPerm (r : Fin 48) : FourPerm :=
  (fourPerm (if r.val < 24 then 0 else 1)).symm

private def mixedBoundCoefficient (k : Fin 4) : ℤ :=
  ![1, 1, 1, -1] k

private def mixedBoundRowSet (r : Fin 48) (k : Fin 4) : Finset (Fin 4) :=
  (mixedBoundRows k).map (mixedBoundRowPerm r).toEmbedding

private def mixedBoundColumnSet (r : Fin 48) (k : Fin 4) : Finset (Fin 4) :=
  (mixedBoundColumns k).map (mixedBoundColumnPerm r).toEmbedding

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
private theorem mixedBound_certificate (r : Fin 48) (p : Fin 24) :
    mixedCostRayInt r p = ∑ k : Fin 4,
      if (mixedBoundColumnSet r k).map (fourPerm p).symm.toEmbedding = mixedBoundRowSet r k
      then mixedBoundCoefficient k else 0 := by
  have h : ∀ (i : Fin 48) (j : Fin 24), mixedCostRayInt i j = ∑ k : Fin 4,
      if (mixedBoundColumnSet i k).map (fourPerm j).symm.toEmbedding = mixedBoundRowSet i k
      then mixedBoundCoefficient k else 0 := by
    intro i
    fin_cases i <;> decide +kernel
  exact h r p

private def mixedBoundMinorForm (U : Matrix (Fin 4) (Fin 4) ℂ) : ℝ :=
  subsetMinorSq U {1} {2} + subsetMinorSq U {2} {1} +
    subsetMinorSq U {2, 3} {2, 3} - subsetMinorSq U {1, 3} {0, 2}

private theorem mixedBoundMinorForm_orthogonal (O : Matrix.orthogonalGroup (Fin 4) ℝ) :
    -(2 / 27 : ℝ) ≤ mixedBoundMinorForm (Complex.ofRealHom.mapMatrix O.val) := by
  obtain ⟨q, r, hq, hr, hs, hd⟩ := exists_quaternionRotation_same_squaredMinors O
  have h := mixed_quaternion_rotation_lower q r
    (by simpa only [Fin.sum_univ_four] using hq) (by simpa only [Fin.sum_univ_four] using hr)
  dsimp only at h
  rw [← hs 1 2, ← hs 2 1, ← hd 2 3 2 3 (by decide) (by decide),
    ← hd 1 3 0 2 (by decide) (by decide)] at h
  exact h

private theorem mixedBoundMinorForm_unitary (U : Matrix (Fin 4) (Fin 4) ℂ)
    (hU : IsUnitary U) : -(2 / 27 : ℝ) ≤ mixedBoundMinorForm U := by
  obtain ⟨κ, inst, w, O, hw, hsum, hm⟩ := four_minor_mixture U hU
  letI : Fintype κ := inst
  let V (k : κ) := Complex.ofRealHom.mapMatrix (O k).val
  have heq : mixedBoundMinorForm U = ∑ k, w k * mixedBoundMinorForm (V k) := by
    unfold mixedBoundMinorForm
    simp only [hm, V, mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  calc
    -(2 / 27 : ℝ) = ∑ k, w k * -(2 / 27 : ℝ) := by
      rw [← Finset.sum_mul, hsum, one_mul]
    _ ≤ ∑ k, w k * mixedBoundMinorForm (V k) :=
      Finset.sum_le_sum fun k _ =>
        mul_le_mul_of_nonneg_left (mixedBoundMinorForm_orthogonal (O k)) (hw k)
    _ = mixedBoundMinorForm U := heq.symm

private theorem mixedBound_eval (U : Matrix (Fin 4) (Fin 4) ℂ) (hU : IsUnitary U)
    (r : Fin 48) :
    fourSupportCostValue U (mixedCostRay r) =
      mixedBoundMinorForm (U.submatrix (mixedBoundRowPerm r) (mixedBoundColumnPerm r)) := by
  let V := U.submatrix (mixedBoundRowPerm r) (mixedBoundColumnPerm r)
  let I := mixedBoundRowSet r
  let J := mixedBoundColumnSet r
  let c (k : Fin 4) := (mixedBoundCoefficient k : ℝ)
  let indicator (k : Fin 4) (p : Fin 24) : ℝ :=
    if (J k).map (fourPerm p).symm.toEmbedding = I k then 1 else 0
  have hprofile : mixedCostRay r = ∑ k : Fin 4, c k • indicator k := by
    funext p
    have h := congrArg (Int.cast : ℤ → ℝ) (mixedBound_certificate r p)
    simpa only [mixedCostRay, I, J, c, indicator, Int.cast_sum, apply_ite, Int.cast_zero,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_ite, mul_one, mul_zero] using h
  have hind (k : Fin 4) : fourSupportCostValue U (indicator k) =
      subsetMinorSq V (mixedBoundRows k) (mixedBoundColumns k) := by
    change fourSupportCostValue U (indicator k) =
      subsetMinorSq (U.submatrix (mixedBoundRowPerm r) (mixedBoundColumnPerm r))
        (mixedBoundRows k) (mixedBoundColumns k)
    rw [squared_minor_reindex _ _ U hU]
    let e : Fin 24 ≃ FourPerm := fourPermEquiv.trans (Equiv.inv FourPerm)
    have he (p : Fin 24) : e p = (fourPerm p).symm := rfl
    have hperm := Equiv.sum_comp e (fun σ =>
      if (J k).map σ.toEmbedding = I k then realSignedWeight U σ else 0)
    simp only [he] at hperm
    have hminor := congrArg Complex.re (sum_signedWeight_image_eq_subsetMinorSq U hU (I k) (J k))
    simp only [Finset.sum_filter, Complex.re_sum, apply_ite, Complex.zero_re,
      Complex.ofReal_re] at hminor
    change (∑ p, realSignedWeight U (fourPerm p).symm * indicator k p) =
      subsetMinorSq U (I k) (J k)
    simp only [indicator, mul_ite, mul_one, mul_zero]
    exact hperm.trans hminor
  rw [hprofile, map_sum]
  simp only [map_smul, smul_eq_mul, hind, Fin.sum_univ_four]
  change ((1 : ℤ) : ℝ) * subsetMinorSq V {1} {2} + ((1 : ℤ) : ℝ) * subsetMinorSq V {2} {1} +
    ((1 : ℤ) : ℝ) * subsetMinorSq V {2, 3} {2, 3} + ((-1 : ℤ) : ℝ) * subsetMinorSq V {1, 3} {0, 2} =
    mixedBoundMinorForm V
  simp only [mixedBoundMinorForm, Int.cast_one, Int.cast_neg, one_mul, neg_one_mul, sub_eq_add_neg]

/-- Each mixed ray has value at least `-2/27` at every complex unitary
matrix of order four. -/
theorem four_mixedRay_value_lower (U : Matrix (Fin 4) (Fin 4) ℂ) (hU : IsUnitary U)
    (r : Fin 48) :
    -(2 / 27 : ℝ) ≤ fourSupportCostValue U (mixedCostRay r) := by
  rw [mixedBound_eval U hU r]
  exact mixedBoundMinorForm_unitary _ (unitary_reindex _ _ hU)

private theorem ordinaryBound_nonneg (r : Fin 34) (p : Fin 24) :
    0 ≤ ordinaryCostRay r p := by
  unfold ordinaryCostRay
  rw [ordinaryCostRayInt_indicator]
  split <;> norm_num

private theorem mixedBound_nonneg (r : Fin 48) (p : Fin 24) :
    0 ≤ mixedCostRay r p := by
  let q := fourCostRelabelIndex (if r.val < 24 then 0 else 1)
    ⟨r.val % 24, Nat.mod_lt _ (by decide)⟩ p
  have h : ∀ q : Fin 24, 0 ≤ mixedCostSeedInt q := by decide +kernel
  change 0 ≤ (mixedCostSeedInt q : ℝ)
  exact_mod_cast h q

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem mixedBound_has_double (r : Fin 48) : ∃ p : Fin 24, mixedCostRay r p = 2 := by
  have h : ∀ i : Fin 48, ∃ p : Fin 24, mixedCostRayInt i p = 2 := by
    intro i
    fin_cases i <;> decide +kernel
  obtain ⟨p, hp⟩ := h r
  exact ⟨p, by simpa only [mixedCostRay, Int.cast_ofNat] using congrArg (Int.cast : ℤ → ℝ) hp⟩

/-- At any positive coordinate of the negative mixed ray, the cost
limits the largest possible coefficient of that ray. The resulting
bound uses the actual value of the ray at the given unitary. -/
theorem four_supportCostValue_ge_of_negative_mixed_coordinate
    (U : Matrix (Fin 4) (Fin 4) ℂ) (hU : IsUnitary U)
    {g : Fin 24 → ℝ} (hg : FourSupportCost g) (r : Fin 48)
    (hr : fourSupportCostValue U (mixedCostRay r) < 0) (p : Fin 24)
    (hp : 0 < mixedCostRay r p) :
    fourSupportCostValue U (mixedCostRay r) * (g p / mixedCostRay r p) ≤
      fourSupportCostValue U g := by
  obtain ⟨⟨m, rfl⟩, hn⟩ := hg
  obtain ⟨a, b, ha, hb, hdecomp⟩ := four_cost_cone_decomposition m hn
  let F := fourSupportCostValue U
  have hordinary (i : Fin 34) : 0 ≤ F (ordinaryCostRay i) := by
    rw [fourSupportCostValue_ordinaryRay U hU]
    exact subsetMinorSq_nonneg U _ _
  have hpoint : b r * mixedCostRay r p ≤ fourMatchingEvaluation m p := by
    have h := congrFun hdecomp p
    simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h
    rw [h]
    have ha' : 0 ≤ ∑ i, a i * ordinaryCostRay i p :=
      Finset.sum_nonneg fun i _ => mul_nonneg (ha i) (ordinaryBound_nonneg i p)
    have hb' : b r * mixedCostRay r p ≤ ∑ i, b i * mixedCostRay i p :=
      Finset.single_le_sum (fun i _ => mul_nonneg (hb i) (mixedBound_nonneg i p))
        (Finset.mem_univ r)
    linarith only [ha', hb']
  have hratio : b r ≤ fourMatchingEvaluation m p / mixedCostRay r p :=
    (le_div_iff₀ hp).2 hpoint
  have hmixed : b r * F (mixedCostRay r) ≤ ∑ j, b j * F (mixedCostRay j) := by
    rw [← Finset.sum_erase_add Finset.univ (fun j => b j * F (mixedCostRay j))
      (Finset.mem_univ r)]
    have he : 0 ≤ ∑ j ∈ Finset.univ.erase r, b j * F (mixedCostRay j) := by
      apply Finset.sum_nonneg
      intro j hj
      have hne := (Finset.mem_erase.mp hj).1
      exact mul_nonneg (hb j)
        (le_of_not_gt fun hj' => hne (four_negativeMixedRay_unique U hU j r hj' hr))
    linarith only [he]
  have heval : b r * F (mixedCostRay r) ≤ fourSupportCostValue U (fourMatchingEvaluation m) := by
    rw [hdecomp, map_add, map_sum, map_sum]
    simp only [map_smul, smul_eq_mul]
    have ha' : 0 ≤ ∑ i, a i * F (ordinaryCostRay i) :=
      Finset.sum_nonneg fun i _ => mul_nonneg (ha i) (hordinary i)
    linarith only [ha', hmixed]
  have hweighted : F (mixedCostRay r) * (fourMatchingEvaluation m p / mixedCostRay r p) ≤
      b r * F (mixedCostRay r) := by
    rw [mul_comm (F (mixedCostRay r))]
    exact mul_le_mul_of_nonpos_right hratio hr.le
  exact hweighted.trans heval

/-- A maximizing matching and a positive coordinate of the negative mixed
ray bound the possible directional excess of the determinant. -/
theorem four_support_bound_of_negative_mixed_coordinate (a b : Fin 4 → ℂ)
    (U : Matrix (Fin 4) (Fin 4) ℂ) (hU : IsUnitary U) (η : ℂ) (s : FourPerm)
    (hmax : ∀ t : FourPerm, 0 ≤ matchingGap a b η s t) (r : Fin 48)
    (hr : fourSupportCostValue U (mixedCostRay r) < 0) (p : Fin 24)
    (hp : 0 < mixedCostRay r p) :
    (η * determinantValue a b U).re ≤ (η * matchingProduct a b s).re -
      fourSupportCostValue U (mixedCostRay r) *
        (matchingGap a b η s (fourPerm p).symm / mixedCostRay r p) := by
  have h := four_supportCostValue_ge_of_negative_mixed_coordinate U hU
    (fourSpectralGap_mem_supportCost a b η s hmax) r hr p hp
  let e : Fin 24 ≃ FourPerm := fourPermEquiv.trans (Equiv.inv FourPerm)
  have he (q : Fin 24) : e q = (fourPerm q).symm := rfl
  have hsum := Equiv.sum_comp e (fun t => realSignedWeight U t * matchingGap a b η s t)
  simp only [he] at hsum
  change _ ≤ ∑ q, realSignedWeight U (fourPerm q).symm * matchingGap a b η s (fourPerm q).symm at h
  rw [hsum, ← support_gap_eq a b U hU η s] at h
  linarith only [h]

/-- The directional excess of an order-four determinant is at most one
twenty-seventh of the directional width of the matching hull. -/
theorem four_support_bound_with_width (a b : Fin 4 → ℂ)
    (U : Matrix (Fin 4) (Fin 4) ℂ) (hU : IsUnitary U) (η : ℂ)
    (s t : FourPerm) (hmax : ∀ q, (η * matchingProduct a b q).re ≤ (η * matchingProduct a b s).re)
    (hmin : ∀ q, (η * matchingProduct a b t).re ≤ (η * matchingProduct a b q).re) :
    (η * determinantValue a b U).re ≤ (η * matchingProduct a b s).re +
      ((η * matchingProduct a b s).re - (η * matchingProduct a b t).re) / 27 := by
  have hgap (q : FourPerm) : 0 ≤ matchingGap a b η s q := sub_nonneg.mpr (hmax q)
  have hwidth : 0 ≤ (η * matchingProduct a b s).re - (η * matchingProduct a b t).re :=
    sub_nonneg.mpr (hmin s)
  by_cases hneg : ∃ r : Fin 48, fourSupportCostValue U (mixedCostRay r) < 0
  · obtain ⟨r, hr⟩ := hneg
    obtain ⟨p, hp⟩ := mixedBound_has_double r
    have hp' : 0 < mixedCostRay r p := by rw [hp]; norm_num
    have h := four_support_bound_of_negative_mixed_coordinate a b U hU η s hgap r hr p hp'
    rw [hp] at h
    have hfloor := mul_le_mul_of_nonneg_right (four_mixedRay_value_lower U hU r)
      (div_nonneg (hgap (fourPerm p).symm) (by norm_num : (0 : ℝ) ≤ 2))
    have hle := hmin (fourPerm p).symm
    unfold matchingGap at h hfloor
    linarith only [h, hfloor, hle]
  · have h := four_support_bound_of_mixedRay_contacts a b U hU η s hgap
      (fun r hr => (hneg ⟨r, hr⟩).elim)
    linarith only [h, hwidth]

/-- Every order-four determinant belongs to the matching hull plus one
twenty-seventh of its difference body. The listed vertices use all ordered
pairs of matching products. -/
theorem four_determinant_mem_enlarged_matching_hull (a b : Fin 4 → ℂ)
    (U : Matrix (Fin 4) (Fin 4) ℂ) (hU : IsUnitary U) :
    determinantValue a b U ∈ convexHull ℝ (Set.range fun p : FourPerm × FourPerm =>
      matchingProduct a b p.1 + (matchingProduct a b p.1 - matchingProduct a b p.2) / 27) := by
  classical
  apply mem_hull_of_directional_bound
  intro η
  obtain ⟨s, _, hs⟩ := Finset.exists_max_image Finset.univ
    (fun p : FourPerm => (η * matchingProduct a b p).re) ⟨1, Finset.mem_univ _⟩
  obtain ⟨t, _, ht⟩ := Finset.exists_min_image Finset.univ
    (fun p : FourPerm => (η * matchingProduct a b p).re) ⟨1, Finset.mem_univ _⟩
  refine ⟨(s, t), ?_⟩
  have h := four_support_bound_with_width a b U hU η s t
    (fun p => hs p (Finset.mem_univ p)) (fun p => ht p (Finset.mem_univ p))
  change (η * determinantValue a b U).re ≤
    (η * (matchingProduct a b s + (matchingProduct a b s - matchingProduct a b t) / 27)).re
  rw [mul_add, Complex.add_re, ← mul_div_assoc, mul_sub, Complex.div_ofNat_re, Complex.sub_re]
  exact h

end

end MOC
