import MOC.OrderFiveDisjointPairSupport

/-! A doubly stochastic table of doubletons admits disjoint transports in both
orientations but exceeds every matching on a translated pair of real spectra. -/

open BigOperators Finset Matrix

namespace MOC.OrderFiveDisjointPairObstruction

private abbrev Pair := SubsetLayer (Fin 5) 2

private def contrast (I : Pair) : ℤ :=
  if I.val = {0,1} then 1 else if I.val = {0,2} then -1 else 0

private def weight (I J : Pair) : ℤ := 3 - contrast I * contrast J

private def flow (J K I L : Pair) : ℤ :=
  (if Disjoint I.val L.val then 1 else 0) -
    (if L.val = {3,4} then contrast I * contrast J else 0) -
    (if I.val = {3,4} then contrast L * contrast K else 0)

private theorem weight_nonneg : ∀ I J, 0 ≤ weight I J := by decide +kernel
private theorem weight_sum : ∀ J, ∑ I, weight I J = 30 := by decide +kernel
private theorem weight_symm (I J : Pair) : weight I J = weight J I := by
  simp only [weight, mul_comm]

private theorem disjoint_count : ∀ I : Pair,
    ∑ L : Pair, (if Disjoint I.val L.val then (1 : ℤ) else 0) = 3 := by decide +kernel
private theorem contrast_sum : ∑ L : Pair, contrast L = 0 := by decide +kernel
private theorem bridge_sum : ∀ z : ℤ,
    (∑ L : Pair, if L.val = {3,4} then z else 0) = z := by
  intro z
  let H : Pair := ⟨{3,4}, by decide⟩
  have he (L : Pair) : L.val = {3,4} ↔ L = H := by
    change L.val = H.val ↔ L = H
    exact Subtype.ext_iff.symm
  simp only [he, sum_ite_eq', mem_univ, if_true]

private theorem flow_left (J K I : Pair) : ∑ L, flow J K I L = weight I J := by
  simp only [flow, weight, sum_sub_distrib, disjoint_count, bridge_sum]
  split_ifs <;> simp only [← sum_mul, contrast_sum, zero_mul, sum_const_zero, sub_zero]

private theorem flow_symm (J K I L : Pair) : flow J K I L = flow K J L I := by
  unfold flow
  by_cases h : Disjoint I.val L.val
  · simp only [h, h.symm, if_true]; ring
  · have h' : ¬ Disjoint L.val I.val := fun hd => h hd.symm
    simp only [h, h', if_false]; ring

private theorem flow_entry : ∀ I L : Pair, ∀ x y : Fin 3,
    let z : ℤ := (if Disjoint I.val L.val then 1 else 0) -
      (if L.val = {3,4} then contrast I * ((x.val : ℤ)-1) else 0) -
      (if I.val = {3,4} then contrast L * ((y.val : ℤ)-1) else 0)
    0 ≤ z ∧ (z ≠ 0 → Disjoint I.val L.val) := by decide +kernel

private theorem contrast_range : ∀ I : Pair, ∃ x : Fin 3, (x.val : ℤ)-1 = contrast I := by
  decide +kernel

private theorem cut_nonneg (t : OrderFiveDisjointPairCut) :
    0 ≤ ∑ J : Pair, ∑ I : Pair, t.adjustment I J * (weight I J : ℝ) := by
  have hf (I L : Pair) : 0 ≤ flow t.first t.second I L ∧
      (flow t.first t.second I L ≠ 0 → Disjoint I.val L.val) := by
    obtain ⟨x,hx⟩ := contrast_range t.first
    obtain ⟨y,hy⟩ := contrast_range t.second
    simpa only [hx, hy, flow] using flow_entry I L x y
  have h := (transportReducedCost_nonneg_and_zero
    (fun I L : Pair => Disjoint I.val L.val)
    (fun I => (weight I t.first : ℝ)) (fun L => (weight L t.second : ℝ))
    (fun I => t.leftCost I.val) (fun L => t.rightCost L.val)
    (fun I L => (flow t.first t.second I L : ℝ))
    (fun I L => by dsimp only; exact_mod_cast (hf I L).1)
    (fun I L h => (hf I L).2 (by dsimp only at h; exact_mod_cast h))
    (fun I => by dsimp only; exact_mod_cast flow_left t.first t.second I)
    (fun L => by simp only [flow_symm t.first t.second]; exact_mod_cast flow_left t.second t.first L)
    t.nonneg).1
  simp only [OrderFiveDisjointPairCut.adjustment, add_mul, sum_add_distrib, ite_mul, zero_mul]
  rw [sum_comm (f := fun J I => if J = t.first then t.leftCost I.val * (weight I J : ℝ) else 0),
    sum_comm (f := fun J I => if J = t.second then t.rightCost I.val * (weight I J : ℝ) else 0)]
  simpa only [sum_ite_eq', mem_univ, if_true, mul_comm] using h

private def first : Fin 5 → ℤ := ![2,2,1,1,1]
private def second : Fin 5 → ℤ := ![0,0,-1,-1,-1]
private def folded (I J : Finset (Fin 5)) : ℤ :=
  (∏ i ∈ Iᶜ, first i) * (∏ j ∈ J, second j) +
  (∏ i ∈ I, first i) * (∏ j ∈ Jᶜ, second j)
private def tripleCost (I J : Pair) : ℤ :=
  3 * folded I.val J.val + ∑ i ∈ I.val, ∑ j ∈ J.val, folded {i} {j}
private def tripleOffset : ℤ :=
  3 * folded ∅ ∅ - ∑ i, ∑ j, folded {i} {j}

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 16000 in
private theorem fixture_score :
    30 * tripleOffset + ∑ J : Pair, ∑ I : Pair, tripleCost I J * weight I J = 8 := by
  decide +kernel

set_option maxRecDepth 8000 in
private theorem fixture_matching : ∀ σ : Equiv.Perm (Fin 5),
    ∏ j, (first (σ j) + second j) = 0 := by decide +kernel

private abbrev a (i : Fin 5) : ℂ := first i
private abbrev b (i : Fin 5) : ℂ := second i

private theorem folded_cast (I J : Finset (Fin 5)) :
    orderFiveFoldedCost a b 1 I J = (folded I J : ℝ) := by
  simp only [orderFiveFoldedCost, orderFiveSubsetCost, one_mul, compl_compl, folded,
    a, b, ← Int.cast_prod, ← Int.cast_mul, Complex.intCast_re, Int.cast_add]

private theorem cost_cast (I J : Pair) :
    3 * orderFivePairCost a b 1 I J = (tripleCost I J : ℝ) := by
  simp only [orderFivePairCost, orderFiveSingletonCost, folded_cast, tripleCost,
    Int.cast_add, Int.cast_mul, Int.cast_ofNat, Int.cast_sum]
  ring

private theorem offset_cast : 3 * orderFivePairOffset a b 1 = (tripleOffset : ℝ) := by
  simp only [orderFivePairOffset, orderFiveSingletonCost, folded_cast, tripleOffset,
    Int.cast_sub, Int.cast_mul, Int.cast_ofNat, Int.cast_sum]
  ring

/-- Even when every matching vanishes, the order-five disjoint-pair dual need
not certify its support height. -/
theorem not_disjoint_pair_dual_test : ¬ OrderFiveDisjointPairDualTest := by
  intro H
  obtain ⟨m,t,r,q,σ,hdual,hmatch⟩ := H a b 1
  have hm : (1 * matchingProduct a b σ).re = 0 := by
    simp only [matchingProduct, a, b, ← Int.cast_add, ← Int.cast_prod, fixture_matching,
      Int.cast_zero, mul_zero, Complex.zero_re]
  rw [hm] at hmatch
  have hsum (J : Pair) : (∑ I, (weight I J : ℝ)) = 30 := by exact_mod_cast weight_sum J
  have hrow (I : Pair) : (∑ J, (weight I J : ℝ)) = 30 := by
    simpa only [weight_symm I] using hsum I
  have hd := sum_le_sum (s := (univ : Finset Pair)) (fun J _ =>
    sum_le_sum (s := (univ : Finset Pair)) (fun I _ =>
      mul_le_mul_of_nonneg_right (hdual I J) (show 0 ≤ (weight I J : ℝ) by
        exact_mod_cast weight_nonneg I J)))
  simp only [add_mul, sum_add_distrib, sum_mul] at hd
  rw [sum_comm (f := fun J I => r I * (weight I J : ℝ))] at hd
  simp only [← mul_sum, hsum, hrow, ← sum_mul] at hd
  have hcuts : 0 ≤ ∑ J : Pair, ∑ I : Pair, ∑ k, (t k).adjustment I J * (weight I J : ℝ) := by
    simp_rw [sum_comm (f := fun I k => (t k).adjustment I _ * (weight I _ : ℝ))]
    rw [sum_comm]
    exact sum_nonneg fun k _ => cut_nonneg (t k)
  have hscore := congrArg (fun z : ℤ => (z : ℝ)) fixture_score
  push_cast at hscore
  simp only [← cost_cast, ← offset_cast, mul_assoc, ← mul_sum] at hscore
  simp only [← sum_mul] at hcuts
  linarith only [hscore, hmatch, hd, hcuts]

end MOC.OrderFiveDisjointPairObstruction
