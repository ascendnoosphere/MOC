import MOC.OrderFivePairMarkers
import MOC.SubsetAssignmentSupport

/-! In order five every actual spectral support objective factors through the
doubleton layer. The coefficients below are explicit and may have either sign.
Assignment dual feasible potentials can certify one objective without a common
positive minor law. -/

open BigOperators Matrix Finset

namespace MOC

noncomputable section

local notation "Pair₅" => SubsetLayer (Fin 5) 2

/-- One real cost in the usual subset expansion. -/
def orderFiveSubsetCost (a b : Fin 5 → ℂ) (η : ℂ) (I J : Finset (Fin 5)) : ℝ :=
  (η * ((∏ i ∈ Iᶜ, a i) * ∏ j ∈ J, b j)).re

def orderFiveFoldedCost (a b : Fin 5 → ℂ) (η : ℂ) (I J : Finset (Fin 5)) : ℝ :=
  orderFiveSubsetCost a b η I J + orderFiveSubsetCost a b η Iᶜ Jᶜ

def orderFiveSingletonCost (a b : Fin 5 → ℂ) (η : ℂ) (i j : Fin 5) : ℝ :=
  orderFiveFoldedCost a b η {i} {j}

def orderFivePairCost (a b : Fin 5 → ℂ) (η : ℂ) (I J : Pair₅) : ℝ :=
  orderFiveFoldedCost a b η I.val J.val +
    (∑ i ∈ I.val, ∑ j ∈ J.val, orderFiveSingletonCost a b η i j) / 3

def orderFivePairOffset (a b : Fin 5 → ℂ) (η : ℂ) : ℝ :=
  orderFiveFoldedCost a b η ∅ ∅ - (∑ i, ∑ j, orderFiveSingletonCost a b η i j) / 3

private def complementPerm₅ : Equiv.Perm (Finset (Fin 5)) where
  toFun J := Jᶜ
  invFun J := Jᶜ
  left_inv := compl_compl
  right_inv := compl_compl

private theorem complement_low_iff_high (J : Finset (Fin 5)) :
    ¬ Jᶜ.card ≤ 2 ↔ J.card ≤ 2 := by
  have h := J.card_le_univ
  simp only [Fintype.card_fin] at h
  simp only [Finset.card_compl, Fintype.card_fin]
  omega

private theorem orderFive_sum_fold (f : Finset (Fin 5) → ℝ) :
    (∑ J, f J) = ∑ J ∈ univ.filter (fun J : Finset (Fin 5) => J.card ≤ 2), (f J + f Jᶜ) := by
  classical
  rw [← Finset.sum_filter_add_sum_filter_not univ (fun J : Finset (Fin 5) => J.card ≤ 2) f,
    Finset.sum_add_distrib]
  congr 1
  simp only [Finset.sum_filter]
  rw [← Equiv.sum_comp complementPerm₅ (fun J => if ¬ J.card ≤ 2 then f J else 0)]
  simp only [complementPerm₅, Equiv.coe_fn_mk]
  apply Finset.sum_congr rfl
  intro J _
  have he : 2 < Jᶜ.card ↔ J.card ≤ 2 := (lt_iff_not_ge _ _).trans (complement_low_iff_high J)
  simp [he]

private theorem sum_low_layer₅ (f : Finset (Fin 5) → ℝ) :
    (∑ J ∈ univ.filter (fun J : Finset (Fin 5) => J.card ≤ 2), f J) =
      f ∅ + (∑ j : Fin 5, f {j}) + ∑ J : Pair₅, f J.val := by
  classical
  have h₀ : (∑ J : Finset (Fin 5), if J.card = 0 then f J else 0) = f ∅ := by
    simp only [Finset.card_eq_zero]
    rw [Finset.sum_ite_eq', if_pos (Finset.mem_univ _)]
  have h₁ : (∑ J : Finset (Fin 5), if J.card = 1 then f J else 0) =
      ∑ j : Fin 5, f {j} := by
    rw [← Finset.sum_filter]
    symm
    apply Finset.sum_bij (fun j (_ : j ∈ (univ : Finset (Fin 5))) => ({j} : Finset (Fin 5)))
    · intro j _
      simp
    · intro x _ y _ h
      simpa using h
    · intro J hJ
      obtain ⟨j, hj⟩ := Finset.card_eq_one.mp (Finset.mem_filter.mp hJ).2
      exact ⟨j, Finset.mem_univ _, hj.symm⟩
    · intros; rfl
  have h₂ : (∑ J : Finset (Fin 5), if J.card = 2 then f J else 0) =
      ∑ J : Pair₅, f J.val := by
    rw [← Finset.sum_filter]
    exact Finset.sum_subtype _ (by simp) f
  rw [← h₀, ← h₁, ← h₂, Finset.sum_filter, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro J _
  by_cases hJ : J.card ≤ 2
  · rcases (show J.card = 0 ∨ J.card = 1 ∨ J.card = 2 by omega) with h | h | h <;> simp [h]
  · have hzero : J.card ≠ 0 := by omega
    have hone : J.card ≠ 1 := by omega
    have htwo : J.card ≠ 2 := by omega
    simp [hJ, hzero, hone, htwo]

private theorem map_complement₅ (J : Finset (Fin 5)) (σ : Equiv.Perm (Fin 5)) :
    Jᶜ.map σ.toEmbedding = (J.map σ.toEmbedding)ᶜ := by
  ext i
  simp [Finset.mem_map_equiv]

private theorem orderFive_folded_score (a b : Fin 5 → ℂ) (η : ℂ)
    (σ : Equiv.Perm (Fin 5)) :
    (η * matchingProduct a b σ).re =
      orderFiveFoldedCost a b η ∅ ∅ +
        (∑ j, orderFiveSingletonCost a b η (σ j) j) +
        ∑ J : Pair₅, orderFiveFoldedCost a b η (subsetLayerPerm 2 σ J).val J.val := by
  classical
  rw [matchingProduct_expand_subsets, Finset.mul_sum, Complex.re_sum]
  change (∑ J, orderFiveSubsetCost a b η (J.map σ.toEmbedding) J) = _
  rw [orderFive_sum_fold]
  simp_rw [map_complement₅]
  change (∑ J ∈ univ.filter (fun J : Finset (Fin 5) => J.card ≤ 2),
    orderFiveFoldedCost a b η (J.map σ.toEmbedding) J) = _
  rw [sum_low_layer₅]
  simp [orderFiveSingletonCost, subsetLayerPerm]

private theorem incidentPairSum₅ (f : Finset (Fin 5) → ℝ) (j : Fin 5) :
    (∑ J : Pair₅, if j ∈ J.val then f J.val else 0) =
      ∑ l ∈ (univ : Finset (Fin 5)).erase j, f {j,l} := by
  classical
  symm
  let S := (univ : Finset (Fin 5)).erase j
  let T := (univ : Finset (Finset (Fin 5))).filter (fun J => J.card = 2)
  have he : (S.image fun l => ({j,l} : Finset (Fin 5))) = T.filter (fun J => j ∈ J) := by
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
  have hinj : Set.InjOn (fun l => ({j,l} : Finset (Fin 5))) S := by
    intro l hl m hm h
    have hlj := (Finset.mem_erase.mp hl).1
    change ({j,l} : Finset (Fin 5)) = {j,m} at h
    have hL : l ∈ ({j,m} : Finset (Fin 5)) := by rw [← h]; simp
    exact Finset.mem_singleton.mp ((Finset.mem_insert.mp hL).resolve_left hlj)
  calc
    (∑ l ∈ S, f {j,l}) = ∑ J ∈ S.image (fun l => ({j,l} : Finset (Fin 5))), f J :=
      (Finset.sum_image (fun x hx y hy => hinj hx hy)).symm
    _ = ∑ J ∈ T, if j ∈ J then f J else 0 := by rw [he, Finset.sum_filter]
    _ = ∑ J : Pair₅, if j ∈ J.val then f J.val else 0 :=
      Finset.sum_subtype T (by simp [T]) _

private theorem orderFive_count_pair_containment (σ : Equiv.Perm (Fin 5)) (i j : Fin 5) :
    (∑ J : Pair₅, if j ∈ J.val ∧ i ∈ (subsetLayerPerm 2 σ J).val then (1 : ℝ) else 0) =
      1 + 3 * (if σ j = i then 1 else 0) := by
  classical
  have he (J : Pair₅) :
      (if j ∈ J.val ∧ i ∈ (subsetLayerPerm 2 σ J).val then (1 : ℝ) else 0) =
        if j ∈ J.val then (if i ∈ J.val.map σ.toEmbedding then 1 else 0) else 0 := by
    by_cases h : j ∈ J.val <;> simp [h, subsetLayerPerm]
  simp_rw [he]
  rw [incidentPairSum₅ (fun J => if i ∈ J.map σ.toEmbedding then 1 else 0) j]
  have hinner (l : Fin 5) (hl : l ∈ (univ : Finset (Fin 5)).erase j) :
      (∑ I ∈ (univ : Finset (Finset (Fin 5))).filter (fun I => I.card = 2 ∧ i ∈ I),
        (if ({j,l} : Finset (Fin 5)).map σ.toEmbedding = I then (1 : ℝ) else 0)) =
        if i ∈ ({j,l} : Finset (Fin 5)).map σ.toEmbedding then 1 else 0 := by
    let T := ({j,l} : Finset (Fin 5)).map σ.toEmbedding
    have hcardT : T.card = 2 := by
      dsimp [T]
      rw [card_map]
      exact card_pair (Finset.mem_erase.mp hl).1.symm
    change (∑ I ∈ (univ : Finset (Finset (Fin 5))).filter
      (fun I => I.card = 2 ∧ i ∈ I), if T = I then (1 : ℝ) else 0) =
      if i ∈ T then 1 else 0
    simp_rw [eq_comm (a := T)]
    simp [Finset.sum_ite_eq', hcardT]
  have hc := count_incident_pair_images (ι := Fin 5) (by simp) i j σ
  rw [Finset.sum_congr rfl hinner] at hc
  norm_num at hc ⊢
  exact hc

private theorem orderFive_sum_pair_singleton (H : Fin 5 → Fin 5 → ℝ)
    (σ : Equiv.Perm (Fin 5)) :
    (∑ J : Pair₅, ∑ i ∈ (subsetLayerPerm 2 σ J).val, ∑ j ∈ J.val, H i j) =
      (∑ i, ∑ j, H i j) + 3 * ∑ j, H (σ j) j := by
  classical
  let e (J : Pair₅) (i j : Fin 5) : ℝ :=
    if j ∈ J.val ∧ i ∈ (subsetLayerPerm 2 σ J).val then 1 else 0
  have he (J : Pair₅) : (∑ i, ∑ j, H i j * e J i j) =
      ∑ i ∈ (subsetLayerPerm 2 σ J).val, ∑ j ∈ J.val, H i j := by
    have hi (i : Fin 5) : (∑ j, H i j * e J i j) =
        if i ∈ (subsetLayerPerm 2 σ J).val then (∑ j ∈ J.val, H i j) else 0 := by
      by_cases h : i ∈ (subsetLayerPerm 2 σ J).val
      · simp only [e, h, and_true, if_true, mul_ite, mul_one, mul_zero,
          ← Finset.sum_filter, Finset.filter_univ_mem]
      · simp [e, h]
    simp_rw [hi, ← Finset.sum_filter, Finset.filter_univ_mem]
  have hcount (i j : Fin 5) : ∑ J, e J i j = 1 + 3 * (if σ j = i then 1 else 0) :=
    orderFive_count_pair_containment σ i j
  calc
    _ = ∑ J : Pair₅, ∑ i, ∑ j, H i j * e J i j := by simp only [he]
    _ = ∑ i, ∑ j, H i j * ∑ J, e J i j := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum]
    _ = _ := by
      simp_rw [hcount, mul_add, mul_one, mul_left_comm (H _ _) (3 : ℝ),
        Finset.sum_add_distrib, ← Finset.mul_sum]
      congr 1
      rw [Finset.sum_comm]
      apply congrArg (fun x : ℝ => 3 * x)
      apply Finset.sum_congr rfl
      intro j _
      simp [mul_ite, Finset.sum_ite_eq', eq_comm]

/-- The explicit order-five doubleton cost formula holds for every complex
spectral pair, every support direction, and every vertex. -/
theorem orderFive_score_eq_pair_cost (a b : Fin 5 → ℂ) (η : ℂ)
    (σ : Equiv.Perm (Fin 5)) :
    (η * matchingProduct a b σ).re = orderFivePairOffset a b η +
      ∑ J : Pair₅, orderFivePairCost a b η (subsetLayerPerm 2 σ J) J := by
  rw [orderFive_folded_score]
  simp only [orderFivePairOffset, orderFivePairCost, Finset.sum_add_distrib,
    ← Finset.sum_div, orderFive_sum_pair_singleton]
  ring

private theorem orderFive_sum_pair_cost_as_events (C : Pair₅ → Pair₅ → ℝ)
    (σ : Equiv.Perm (Fin 5)) :
    (∑ J : Pair₅, C (subsetLayerPerm 2 σ J) J) =
      ∑ e : Pair₅ × Pair₅, C e.2 e.1 * subsetImageEvent e.2.val e.1.val σ := by
  classical
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro J _
  symm
  let I₀ := subsetLayerPerm 2 σ J
  have he (I : Pair₅) (hI : I ≠ I₀) : J.val.map σ.toEmbedding ≠ I.val := by
    intro h
    exact hI (Subtype.ext h.symm)
  rw [Finset.sum_eq_single I₀]
  · simp [subsetImageEvent, I₀, subsetLayerPerm]
  · intro I _ hI
    simp [subsetImageEvent, he I hI]
  · simp

/-- The support of the determinant is an explicit affine evaluation of its
doubleton squared minors, via the exact signed determinant law. -/
theorem orderFive_determinant_support_eq_pair_cost (a b : Fin 5 → ℂ) (η : ℂ)
    (U : Matrix (Fin 5) (Fin 5) ℂ) (hU : IsUnitary U) :
    (η * determinantValue a b U).re =
      orderFivePairOffset a b η +
        ∑ J : Pair₅, ∑ I : Pair₅, orderFivePairCost a b η I J * subsetMinorSq U I.val J.val := by
  classical
  let C := orderFivePairCost a b η
  let z := orderFivePairOffset a b η
  have he := congrArg (fun d : ℂ => (η * d).re) (real_signed_determinant a b U hU)
  have hdet : (∑ σ : Equiv.Perm (Fin 5), realSignedWeight U σ * (η * matchingProduct a b σ).re) =
      (η * determinantValue a b U).re := by
    simp only [Finset.mul_sum, Complex.re_sum] at he
    calc
      _ = ∑ σ : Equiv.Perm (Fin 5), (η * ((realSignedWeight U σ : ℂ) * matchingProduct a b σ)).re := by
        apply Finset.sum_congr rfl
        intro σ _
        rw [mul_left_comm, Complex.mul_re]
        simp
      _ = _ := he
  rw [← hdet]
  simp_rw [orderFive_score_eq_pair_cost a b η, orderFive_sum_pair_cost_as_events,
    mul_add, Finset.sum_add_distrib]
  rw [← Finset.sum_mul, sum_realSignedWeight U hU, one_mul]
  rw [signed_expectation_subsetImageCombo U hU (fun e : Pair₅ × Pair₅ => e.2.val)
    (fun e => e.1.val) (fun e => C e.2 e.1), Fintype.sum_prod_type]

/-- A bound in an individual support direction follows from a feasible dual
on the explicit doubleton costs, without a universal common law. -/
theorem orderFive_spectral_support_le_pair_dual (a b : Fin 5 → ℂ) (η : ℂ)
    (U : Matrix (Fin 5) (Fin 5) ℂ) (hU : IsUnitary U) (r q : Pair₅ → ℝ)
    (hdual : ∀ I J, orderFivePairCost a b η I J ≤ r I + q J) :
    (η * determinantValue a b U).re ≤ orderFivePairOffset a b η + (∑ I, r I) + ∑ J, q J :=
  spectral_support_le_subset_assignment_dual a b U hU η 2 _ _ r q
    (orderFive_score_eq_pair_cost a b η) hdual

/-- Tightness on an assignment induced by an actual label permutation
certifies the desired MOC support inequality in the tested direction. -/
theorem orderFive_spectral_support_of_tight_pair_dual (a b : Fin 5 → ℂ) (η : ℂ)
    (U : Matrix (Fin 5) (Fin 5) ℂ) (hU : IsUnitary U) (r q : Pair₅ → ℝ)
    (σ₀ : Equiv.Perm (Fin 5))
    (hdual : ∀ I J, orderFivePairCost a b η I J ≤ r I + q J)
    (htight : ∀ J, orderFivePairCost a b η (subsetLayerPerm 2 σ₀ J) J =
      r (subsetLayerPerm 2 σ₀ J) + q J) :
    (η * determinantValue a b U).re ≤ (η * matchingProduct a b σ₀).re :=
  spectral_support_of_tight_induced_subset_assignment a b U hU η 2 _ _ r q σ₀
    (orderFive_score_eq_pair_cost a b η) hdual htight

end

end MOC
