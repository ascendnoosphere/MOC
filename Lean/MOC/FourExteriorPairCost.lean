import MOC.OrderFivePairMarkers
import MOC.SubsetAssignmentSupport

/-! In order four the determinant is an affine evaluation of the squared
pair minors. Fold the empty and singleton layers with their complements.
Each ordered pair of doubletons occurs once. -/

open BigOperators Matrix Finset

namespace MOC

noncomputable section

local notation "Pair₄" => SubsetLayer (Fin 4) 2

private def subsetMonomial₄ (a b : Fin 4 → ℂ) (I J : Finset (Fin 4)) : ℂ :=
  (∏ i ∈ Iᶜ, a i) * ∏ j ∈ J, b j

private def singletonCoefficient₄ (a b : Fin 4 → ℂ) (i j : Fin 4) : ℂ :=
  subsetMonomial₄ a b {i} {j} + subsetMonomial₄ a b ({i}ᶜ) ({j}ᶜ)

/-- The coefficient of the squared pair minor in the determinant. -/
def orderFourPairCoefficient (a b : Fin 4 → ℂ) (I J : Pair₄) : ℂ :=
  subsetMonomial₄ a b I.val J.val +
    (∑ i ∈ I.val, ∑ j ∈ J.val, singletonCoefficient₄ a b i j) / 2

/-- The constant term of the affine evaluation of the pair minors. -/
def orderFourDeterminantOffset (a b : Fin 4 → ℂ) : ℂ :=
  subsetMonomial₄ a b ∅ ∅ + subsetMonomial₄ a b univ univ -
    (∑ i, ∑ j, singletonCoefficient₄ a b i j) / 2

/-- The coefficient of one squared pair minor in a real support direction. -/
def orderFourPairCost (a b : Fin 4 → ℂ) (η : ℂ) (I J : Pair₄) : ℝ :=
  (η * orderFourPairCoefficient a b I J).re

/-- The constant term in a real support direction. -/
def orderFourPairOffset (a b : Fin 4 → ℂ) (η : ℂ) : ℝ :=
  (η * orderFourDeterminantOffset a b).re

private def subsetComplement₄ : Equiv.Perm (Finset (Fin 4)) :=
  ⟨(·ᶜ), (·ᶜ), compl_compl, compl_compl⟩

private theorem sum_singletons₄ (f : Finset (Fin 4) → ℂ) :
    (∑ J : Finset (Fin 4), if J.card = 1 then f J else 0) = ∑ j : Fin 4, f {j} := by
  classical
  rw [← Finset.sum_filter]
  symm
  apply Finset.sum_bij (fun j (_ : j ∈ (univ : Finset (Fin 4))) => ({j} : Finset (Fin 4)))
  · intro j _
    simp
  · intro x _ y _ h
    simpa using h
  · intro J hJ
    obtain ⟨j, hj⟩ := Finset.card_eq_one.mp (Finset.mem_filter.mp hJ).2
    exact ⟨j, Finset.mem_univ _, hj.symm⟩
  · intros
    rfl

private theorem sum_folded_layers₄ (f : Finset (Fin 4) → ℂ) :
    (∑ J, f J) = (f ∅ + f univ) + (∑ j : Fin 4, (f {j} + f ({j}ᶜ))) +
      ∑ J : Pair₄, f J.val := by
  classical
  let g (J : Finset (Fin 4)) := f J + f Jᶜ
  have hpart : (∑ J, f J) =
      (∑ J, if J.card ≤ 1 then f J else 0) +
      (∑ J, if 2 < J.card then f J else 0) +
      ∑ J, if J.card = 2 then f J else 0 := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro J _
    rcases lt_trichotomy J.card 2 with h | h | h
    · simp [show J.card ≤ 1 by omega, show ¬ 2 < J.card by omega, h.ne]
    · simp [h]
    · simp [show ¬ J.card ≤ 1 by omega, h, h.ne']
  have hhigh : (∑ J, if 2 < J.card then f J else 0) =
      ∑ J, if J.card ≤ 1 then f Jᶜ else 0 := by
    rw [← Equiv.sum_comp subsetComplement₄ (fun J => if 2 < J.card then f J else 0)]
    apply Finset.sum_congr rfl
    intro J _
    change (if 2 < Jᶜ.card then f Jᶜ else 0) = _
    have hcard := Finset.card_add_card_compl J
    have he : 2 < Jᶜ.card ↔ J.card ≤ 1 := by
      simp only [Fintype.card_fin] at hcard
      omega
    rw [he]
  have hfold :
      (∑ J, if J.card ≤ 1 then f J else 0) + (∑ J, if J.card ≤ 1 then f Jᶜ else 0) =
        ∑ J, if J.card ≤ 1 then g J else 0 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro J _
    by_cases h : J.card ≤ 1 <;> simp only [g, h, if_true, if_false, add_zero]
  have hzero : (∑ J : Finset (Fin 4), if J.card = 0 then g J else 0) = g ∅ := by
    simp only [Finset.card_eq_zero]
    rw [Finset.sum_ite_eq', if_pos (Finset.mem_univ _)]
  have hlow : (∑ J, if J.card ≤ 1 then g J else 0) = g ∅ + ∑ j : Fin 4, g {j} := by
    rw [← hzero, ← sum_singletons₄ g, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro J _
    by_cases h : J.card ≤ 1
    · rcases (show J.card = 0 ∨ J.card = 1 by omega) with h₀ | h₁ <;> simp [h₀, h₁]
    · simp [h, show J.card ≠ 0 by omega, show J.card ≠ 1 by omega]
  have htwo : (∑ J : Finset (Fin 4), if J.card = 2 then f J else 0) =
      ∑ J : Pair₄, f J.val := by
    rw [← Finset.sum_filter]
    exact Finset.sum_subtype _ (by simp) f
  rw [hpart, hhigh, hfold, hlow, htwo]
  simp only [g, compl_empty]

private theorem map_complement₄ (J : Finset (Fin 4)) (σ : Equiv.Perm (Fin 4)) :
    Jᶜ.map σ.toEmbedding = (J.map σ.toEmbedding)ᶜ := by
  ext i
  simp [Finset.mem_map_equiv]

private theorem matching_folded_layers₄ (a b : Fin 4 → ℂ) (σ : Equiv.Perm (Fin 4)) :
    matchingProduct a b σ = (subsetMonomial₄ a b ∅ ∅ + subsetMonomial₄ a b univ univ) +
      (∑ j, singletonCoefficient₄ a b (σ j) j) +
      ∑ J : Pair₄, subsetMonomial₄ a b (subsetLayerPerm 2 σ J).val J.val := by
  rw [matchingProduct_expand_subsets]
  change (∑ J, subsetMonomial₄ a b (J.map σ.toEmbedding) J) = _
  rw [sum_folded_layers₄]
  simp only [map_complement₄, Finset.map_empty, Finset.map_univ_equiv, Finset.map_singleton,
    singletonCoefficient₄, subsetLayerPerm, Equiv.coe_fn_mk]

private theorem sum_incident_pairs₄ (f : Finset (Fin 4) → ℝ) (j : Fin 4) :
    (∑ J : Pair₄, if j ∈ J.val then f J.val else 0) =
      ∑ l ∈ (univ : Finset (Fin 4)).erase j, f {j,l} := by
  classical
  symm
  let S := (univ : Finset (Fin 4)).erase j
  let T := (univ : Finset (Finset (Fin 4))).filter (fun J => J.card = 2)
  have he : (S.image fun l => ({j,l} : Finset (Fin 4))) = T.filter (fun J => j ∈ J) := by
    ext J
    simp only [S, T, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, Finset.mem_erase]
    constructor
    · rintro ⟨l, ⟨hl, _⟩, rfl⟩
      exact ⟨Finset.card_pair hl.symm, Finset.mem_insert_self _ _⟩
    · rintro ⟨hcard, hj⟩
      obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp hcard
      rcases Finset.mem_insert.mp hj with h | h
      · subst x
        exact ⟨y, ⟨hxy.symm, trivial⟩, rfl⟩
      · have h' := Finset.mem_singleton.mp h
        subst y
        exact ⟨x, ⟨hxy, trivial⟩, Finset.pair_comm _ _⟩
  have hinj : Set.InjOn (fun l => ({j,l} : Finset (Fin 4))) S := by
    intro l hl m _ h
    have hlj := (Finset.mem_erase.mp hl).1
    change ({j,l} : Finset (Fin 4)) = {j,m} at h
    have hL : l ∈ ({j,m} : Finset (Fin 4)) := by rw [← h]; simp
    exact Finset.mem_singleton.mp ((Finset.mem_insert.mp hL).resolve_left hlj)
  calc
    (∑ l ∈ S, f {j,l}) = ∑ J ∈ S.image (fun l => ({j,l} : Finset (Fin 4))), f J :=
      (Finset.sum_image (fun x hx y hy => hinj hx hy)).symm
    _ = ∑ J ∈ T, if j ∈ J then f J else 0 := by rw [he, Finset.sum_filter]
    _ = ∑ J : Pair₄, if j ∈ J.val then f J.val else 0 :=
      Finset.sum_subtype T (by simp [T]) _

/-- Sum the squared pair minors incident to a row and a column. -/
theorem orderFour_incident_pair_minorSq (U : Matrix (Fin 4) (Fin 4) ℂ)
    (hU : IsUnitary U) (i j : Fin 4) :
    (∑ J : Pair₄, ∑ I : Pair₄,
      if i ∈ I.val ∧ j ∈ J.val then subsetMinorSq U I.val J.val else 0) =
      1 + 2 * Complex.normSq (U i j) := by
  classical
  let T := (univ : Finset (Finset (Fin 4))).filter (fun I => I.card = 2)
  let S := (univ : Finset (Finset (Fin 4))).filter (fun I => I.card = 2 ∧ i ∈ I)
  have hT (I : Finset (Fin 4)) : I ∈ T ↔ I.card = 2 := by simp [T]
  have hS : T.filter (fun I => i ∈ I) = S := by
    ext I
    simp [T, S, and_assoc]
  have hinner (J : Finset (Fin 4)) :
      (∑ I : Pair₄, if i ∈ I.val then subsetMinorSq U I.val J else 0) =
        ∑ I ∈ S, subsetMinorSq U I J := by
    rw [← Finset.sum_subtype T hT
      (fun I => if i ∈ I then subsetMinorSq U I J else 0),
      ← Finset.sum_filter, hS]
  have hsplit (J : Pair₄) :
      (∑ I : Pair₄, if i ∈ I.val ∧ j ∈ J.val then subsetMinorSq U I.val J.val else 0) =
        if j ∈ J.val then ∑ I ∈ S, subsetMinorSq U I J.val else 0 := by
    by_cases h : j ∈ J.val
    · simpa only [h, and_true, if_true] using hinner J.val
    · simp only [h, and_false, if_false, Finset.sum_const_zero]
  simp_rw [hsplit]
  rw [sum_incident_pairs₄ (fun J => ∑ I ∈ S, subsetMinorSq U I J) j]
  have h := sum_incident_pair_minorSq (ι := Fin 4) (by simp) U hU i j
  norm_num [S] at h ⊢
  exact h

private theorem permutation_incident_count₄ (σ : Equiv.Perm (Fin 4)) (i j : Fin 4) :
    (∑ J : Pair₄, if j ∈ J.val ∧ i ∈ (subsetLayerPerm 2 σ J).val then (1 : ℝ) else 0) =
      1 + 2 * (if σ j = i then 1 else 0) := by
  classical
  have he (J : Pair₄) :
      (if j ∈ J.val ∧ i ∈ (subsetLayerPerm 2 σ J).val then (1 : ℝ) else 0) =
        if j ∈ J.val then (if i ∈ J.val.map σ.toEmbedding then 1 else 0) else 0 := by
    by_cases h : j ∈ J.val <;> simp [h, subsetLayerPerm]
  simp_rw [he]
  rw [sum_incident_pairs₄ (fun J => if i ∈ J.map σ.toEmbedding then 1 else 0) j]
  have hinner (l : Fin 4) (hl : l ∈ (univ : Finset (Fin 4)).erase j) :
      (∑ I ∈ (univ : Finset (Finset (Fin 4))).filter (fun I => I.card = 2 ∧ i ∈ I),
        (if ({j,l} : Finset (Fin 4)).map σ.toEmbedding = I then (1 : ℝ) else 0)) =
        if i ∈ ({j,l} : Finset (Fin 4)).map σ.toEmbedding then 1 else 0 := by
    let T := ({j,l} : Finset (Fin 4)).map σ.toEmbedding
    have hcardT : T.card = 2 := by
      dsimp [T]
      rw [card_map]
      exact card_pair (Finset.mem_erase.mp hl).1.symm
    change (∑ I ∈ (univ : Finset (Finset (Fin 4))).filter
      (fun I => I.card = 2 ∧ i ∈ I), if T = I then (1 : ℝ) else 0) =
      if i ∈ T then 1 else 0
    simp_rw [eq_comm (a := T)]
    simp [Finset.sum_ite_eq', hcardT]
  have hc := count_incident_pair_images (ι := Fin 4) (by simp) i j σ
  rw [Finset.sum_congr rfl hinner] at hc
  norm_num at hc ⊢
  exact hc

private theorem sum_pair_singleton_coefficients₄ (H : Fin 4 → Fin 4 → ℂ)
    (σ : Equiv.Perm (Fin 4)) :
    (∑ J : Pair₄, ∑ i ∈ (subsetLayerPerm 2 σ J).val, ∑ j ∈ J.val, H i j) =
      (∑ i, ∑ j, H i j) + 2 * ∑ j, H (σ j) j := by
  classical
  let e (J : Pair₄) (i j : Fin 4) : ℂ :=
    if j ∈ J.val ∧ i ∈ (subsetLayerPerm 2 σ J).val then 1 else 0
  have he (J : Pair₄) : (∑ i, ∑ j, H i j * e J i j) =
      ∑ i ∈ (subsetLayerPerm 2 σ J).val, ∑ j ∈ J.val, H i j := by
    have hi (i : Fin 4) : (∑ j, H i j * e J i j) =
        if i ∈ (subsetLayerPerm 2 σ J).val then (∑ j ∈ J.val, H i j) else 0 := by
      by_cases h : i ∈ (subsetLayerPerm 2 σ J).val
      · simp only [e, h, and_true, if_true, mul_ite, mul_one, mul_zero,
          ← Finset.sum_filter, Finset.filter_univ_mem]
      · simp [e, h]
    simp_rw [hi, ← Finset.sum_filter, Finset.filter_univ_mem]
  have hcount (i j : Fin 4) : ∑ J, e J i j = 1 + 2 * (if σ j = i then 1 else 0) := by
    have h := congrArg Complex.ofReal (permutation_incident_count₄ σ i j)
    simpa only [e, Complex.ofReal_sum, Complex.ofReal_add, Complex.ofReal_mul,
      Complex.ofReal_ofNat, Complex.ofReal_one, Complex.ofReal_zero, apply_ite] using h
  calc
    _ = ∑ J : Pair₄, ∑ i, ∑ j, H i j * e J i j := by simp only [he]
    _ = ∑ i, ∑ j, H i j * ∑ J, e J i j := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum]
    _ = _ := by
      simp_rw [hcount, mul_add, mul_one, mul_left_comm (H _ _) (2 : ℂ),
        Finset.sum_add_distrib, ← Finset.mul_sum]
      congr 1
      rw [Finset.sum_comm]
      apply congrArg (fun x : ℂ => 2 * x)
      apply Finset.sum_congr rfl
      intro j _
      simp [mul_ite, Finset.sum_ite_eq', eq_comm]

/-- The affine pair table evaluates to the matching product at every
permutation. -/
theorem orderFour_matchingProduct_eq_pair_coefficients (a b : Fin 4 → ℂ)
    (σ : Equiv.Perm (Fin 4)) :
    matchingProduct a b σ = orderFourDeterminantOffset a b +
      ∑ J : Pair₄, orderFourPairCoefficient a b (subsetLayerPerm 2 σ J) J := by
  rw [matching_folded_layers₄]
  simp only [orderFourDeterminantOffset, orderFourPairCoefficient, Finset.sum_add_distrib,
    ← Finset.sum_div, sum_pair_singleton_coefficients₄]
  ring

/-- The spectral determinant is the affine evaluation of its squared
pair minors for arbitrary complex spectra. -/
theorem orderFour_determinantValue_eq_pair_coefficients (a b : Fin 4 → ℂ)
    (U : Matrix (Fin 4) (Fin 4) ℂ) (hU : IsUnitary U) :
    determinantValue a b U = orderFourDeterminantOffset a b +
      ∑ J : Pair₄, ∑ I : Pair₄,
        orderFourPairCoefficient a b I J * (subsetMinorSq U I.val J.val : ℂ) := by
  classical
  let K := orderFourPairCoefficient a b
  rw [← signed_determinant a b U hU]
  simp_rw [orderFour_matchingProduct_eq_pair_coefficients a b, mul_add, Finset.sum_add_distrib]
  rw [← Finset.sum_mul, sum_signedWeight U (det_ne_zero_of_unitary hU), one_mul]
  congr 1
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro J _
  rw [← Finset.sum_fiberwise univ (fun σ : Equiv.Perm (Fin 4) => subsetLayerPerm 2 σ J)]
  apply Finset.sum_congr rfl
  intro I _
  have hfilter :
      (univ : Finset (Equiv.Perm (Fin 4))).filter (fun σ => subsetLayerPerm 2 σ J = I) =
        univ.filter (fun σ => J.val.map σ.toEmbedding = I.val) := by
    ext σ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  change (∑ σ ∈ univ.filter (fun σ => subsetLayerPerm 2 σ J = I),
    signedWeight U σ * K (subsetLayerPerm 2 σ J) J) = K I J * (subsetMinorSq U I.val J.val : ℂ)
  calc
    _ = (∑ σ ∈ univ.filter (fun σ => subsetLayerPerm 2 σ J = I), signedWeight U σ) * K I J := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro σ hσ
      rw [(Finset.mem_filter.mp hσ).2]
    _ = _ := by
      rw [hfilter, sum_signedWeight_image_eq_subsetMinorSq U hU]
      exact mul_comm _ _

/-- The real support score at a permutation uses the same pair costs. -/
theorem orderFour_score_eq_pair_cost (a b : Fin 4 → ℂ) (η : ℂ)
    (σ : Equiv.Perm (Fin 4)) :
    (η * matchingProduct a b σ).re = orderFourPairOffset a b η +
      ∑ J : Pair₄, orderFourPairCost a b η (subsetLayerPerm 2 σ J) J := by
  rw [orderFour_matchingProduct_eq_pair_coefficients]
  simp only [orderFourPairOffset, orderFourPairCost, mul_add, Finset.mul_sum,
    Complex.add_re, Complex.re_sum]

/-- The real support score of the determinant is the affine evaluation
of the pair costs on the squared pair minors. -/
theorem orderFour_determinant_support_eq_pair_cost (a b : Fin 4 → ℂ) (η : ℂ)
    (U : Matrix (Fin 4) (Fin 4) ℂ) (hU : IsUnitary U) :
    (η * determinantValue a b U).re = orderFourPairOffset a b η +
      ∑ J : Pair₄, ∑ I : Pair₄, orderFourPairCost a b η I J * subsetMinorSq U I.val J.val := by
  rw [orderFour_determinantValue_eq_pair_coefficients a b U hU]
  simp only [orderFourPairOffset, orderFourPairCost, mul_add, Finset.mul_sum, Complex.add_re,
    Complex.re_sum, ← mul_assoc, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero]

end

end MOC
