import MOC.FourSupportCostProfiles
import MOC.TwoValues
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Cancellation and the canonical thirteen-ordinary-ray section of the
order-four support-cost cone. All certificate equalities use integer
permutation profiles before scalar extension to the reals. -/

open BigOperators

namespace MOC

noncomputable section

/-- Nonnegative combinations of the specified ordinary rays. -/
def fourOrdinaryCostCone (S : Finset (Fin 34)) (x : Fin 24 → ℝ) : Prop :=
  ∃ c : Fin 34 → ℝ, (∀ k, 0 ≤ c k) ∧ (∀ k, k ∉ S → c k = 0) ∧
    x = ∑ k, c k • ordinaryCostRay k

/-- The ordinary generators in the canonical mixed section. -/
def fourCanonicalCapOrdinaryRays : Finset (Fin 34) :=
  {0, 7, 10, 13, 17, 18, 20, 22, 23, 27, 28, 30, 31}

theorem fourCanonicalCapOrdinaryRays_card : fourCanonicalCapOrdinaryRays.card = 13 := by
  decide +kernel

private theorem ordinary_zero (S : Finset (Fin 34)) :
    fourOrdinaryCostCone S 0 := by
  refine ⟨fun _ => 0, fun _ => le_rfl, fun _ _ => rfl, ?_⟩
  simp only [zero_smul, Finset.sum_const_zero]

private theorem ordinary_mono {S T : Finset (Fin 34)} (h : S ⊆ T)
    {x : Fin 24 → ℝ} (hx : fourOrdinaryCostCone S x) :
    fourOrdinaryCostCone T x := by
  obtain ⟨c, hnonneg, hsupp, heq⟩ := hx
  exact ⟨c, hnonneg, fun k hk => hsupp k (fun hs => hk (h hs)), heq⟩

private theorem ordinary_add {S : Finset (Fin 34)} {x y : Fin 24 → ℝ}
    (hx : fourOrdinaryCostCone S x) (hy : fourOrdinaryCostCone S y) :
    fourOrdinaryCostCone S (x + y) := by
  obtain ⟨a, hapos, hasupp, rfl⟩ := hx
  obtain ⟨b, hbpos, hbsupp, rfl⟩ := hy
  refine ⟨fun k => a k + b k, fun k => add_nonneg (hapos k) (hbpos k), ?_, ?_⟩
  · exact fun k hk => by rw [hasupp k hk, hbsupp k hk, add_zero]
  · simp only [add_smul, Finset.sum_add_distrib]

private theorem ordinary_smul {S : Finset (Fin 34)} {x : Fin 24 → ℝ}
    (hx : fourOrdinaryCostCone S x) {t : ℝ} (ht : 0 ≤ t) :
    fourOrdinaryCostCone S (t • x) := by
  obtain ⟨c, hpos, hsupp, rfl⟩ := hx
  refine ⟨fun k => t * c k, fun k => mul_nonneg ht (hpos k), ?_, ?_⟩
  · exact fun k hk => by rw [hsupp k hk, mul_zero]
  · simp only [Finset.smul_sum, mul_smul]

private theorem ordinary_ray {S : Finset (Fin 34)} {r : Fin 34} (hr : r ∈ S) :
    fourOrdinaryCostCone S (ordinaryCostRay r) := by
  let c : Fin 34 → ℝ := fun k => if k = r then 1 else 0
  refine ⟨c, ?_, ?_, ?_⟩
  · intro k
    by_cases hk : k = r
    · simp only [c, if_pos hk, zero_le_one]
    · simp only [c, if_neg hk, le_refl]
  · intro k hk
    have hn : k ≠ r := fun he => hk (he ▸ hr)
    simp only [c, if_neg hn]
  · rw [Finset.sum_eq_single r]
    · simp only [c, if_pos rfl, one_smul]
    · intro k _ hk
      simp only [c, if_neg hk, zero_smul]
    · intro h
      exact (h (Finset.mem_univ r)).elim

private theorem ordinary_sum {ι : Type*} {S : Finset (Fin 34)}
    (s : Finset ι) (x : ι → Fin 24 → ℝ)
    (hx : ∀ k ∈ s, fourOrdinaryCostCone S (x k)) :
    fourOrdinaryCostCone S (∑ k ∈ s, x k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using ordinary_zero S
  | insert k s hk ih =>
    rw [Finset.sum_insert hk]
    exact ordinary_add (hx k (Finset.mem_insert_self k s))
      (ih (fun j hj => hx j (Finset.mem_insert_of_mem hj)))

private theorem ordinary_list_sum {S : Finset (Fin 34)} (l : List (Fin 34))
    (hl : ∀ k ∈ l, k ∈ S) :
    fourOrdinaryCostCone S (l.map ordinaryCostRay).sum := by
  induction l with
  | nil => exact ordinary_zero S
  | cons k l ih =>
    simp only [List.map_cons, List.sum_cons]
    exact ordinary_add (ordinary_ray (hl k (List.mem_cons_self)))
      (ih (fun j hj => hl j (List.mem_cons_of_mem _ hj)))

private theorem ordinary_list_sum_cast (l : List (Fin 34)) (p : Fin 24) :
    ((l.map (fun k => ordinaryCostRayInt k p)).sum : ℝ) =
      (l.map ordinaryCostRay).sum p := by
  induction l with
  | nil => simp only [List.map_nil, List.sum_nil, Int.cast_zero, Pi.zero_apply]
  | cons k l ih =>
    simp only [List.map_cons, List.sum_cons, Int.cast_add, Pi.add_apply, ih, ordinaryCostRay]

/-- An ordinary decomposition of the sum of the seed and each other mixed ray.
The empty entry for the seed is excluded from the cancellation theorem. -/
private def seedPairOrdinaryRays : Fin 48 → List (Fin 34) :=
  ![
[], [0, 7, 17, 18, 20], [0, 13, 30, 28, 31],
    [0, 14, 23, 27, 28], [0, 13, 22, 25, 30], [0, 10, 22, 23, 27],
    [13, 10, 17, 18, 20], [17, 18, 18, 20, 30, 31], [13, 0, 27, 25, 31],
    [16, 18, 22, 27, 28, 31], [25, 23, 31, 30, 18, 17], [10, 1, 18, 17, 23],
    [13, 3, 23, 22, 28], [24, 23, 30, 31, 18, 20], [7, 13, 22, 23, 27],
    [7, 0, 31, 32, 20], [22, 23, 23, 27, 17, 20], [32, 28, 20, 17, 23, 22],
    [21, 18, 27, 22, 28, 30], [10, 0, 20, 21, 27], [7, 2, 28, 30, 18],
    [10, 7, 30, 28, 31], [29, 28, 17, 20, 23, 27], [30, 28, 28, 31, 22, 27],
    [0, 13, 22, 27, 28], [17, 18, 22, 23, 28, 30], [0, 7, 10, 13],
    [0, 10, 17, 20, 23], [0, 7, 30, 31, 18], [0, 0, 20, 27, 31],
    [17, 18, 27, 23, 28, 31], [17, 18, 22, 23, 25, 27], [13, 10, 31, 30, 18],
    [10, 10, 31, 17, 22], [0, 3, 4, 7], [31, 28, 20, 18, 16, 17],
    [7, 13, 20, 17, 23], [0, 2, 8, 10], [13, 13, 20, 22, 30],
    [22, 23, 30, 28, 32, 31], [20, 18, 27, 23, 24, 22], [22, 23, 31, 28, 18, 20],
    [7, 7, 27, 30, 17], [27, 23, 31, 28, 29, 30], [30, 28, 17, 18, 21, 20],
    [0, 1, 12, 13], [30, 28, 20, 18, 23, 27], [10, 7, 27, 22, 28]
  ]

/-- The seed absorbs each ordinary ray outside the canonical section. -/
private def seedOrdinaryAbsorptionRays : Fin 34 → List (Fin 34) :=
  ![
[], [10, 22, 28, 31], [7, 17, 23, 27],
    [13, 18, 20, 30], [10, 17, 18, 31], [0, 20, 23, 27],
    [13, 22, 28, 30], [], [13, 20, 22, 23],
    [7, 17, 18, 30], [], [0, 27, 28, 31],
    [7, 27, 28, 30], [], [0, 18, 20, 31],
    [10, 17, 22, 23], [0, 10, 31], [],
    [], [22, 23, 27, 28], [],
    [7, 13, 30], [], [],
    [0, 13, 20], [7, 10, 17], [18, 28, 30, 31],
    [], [], [0, 7, 27],
    [], [], [10, 13, 22],
    [17, 18, 20, 23]
  ]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
private theorem seed_pair_certificate (r : Fin 48) (hr : r ≠ 0) (p : Fin 24) :
    mixedCostRayInt 0 p + mixedCostRayInt r p =
      ((seedPairOrdinaryRays r).map (fun k => ordinaryCostRayInt k p)).sum := by
  have h : ∀ s : Fin 48, s ≠ 0 → ∀ q : Fin 24,
      mixedCostRayInt 0 q + mixedCostRayInt s q =
        ((seedPairOrdinaryRays s).map (fun k => ordinaryCostRayInt k q)).sum := by
    intro s
    fin_cases s <;> decide +kernel
  exact h r hr p

private theorem seed_pair_ordinary (r : Fin 48) (hr : r ≠ 0) :
    fourOrdinaryCostCone Finset.univ (mixedCostRay 0 + mixedCostRay r) := by
  have h : mixedCostRay 0 + mixedCostRay r = ((seedPairOrdinaryRays r).map ordinaryCostRay).sum := by
    funext p
    have he := congrArg (Int.cast : ℤ → ℝ) (seed_pair_certificate r hr p)
    simpa only [Int.cast_add, ordinary_list_sum_cast, Pi.add_apply, mixedCostRay] using he
  rw [h]
  exact ordinary_list_sum (seedPairOrdinaryRays r) (fun k _ => Finset.mem_univ k)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
private theorem seed_absorption_certificate (r : Fin 34) (hr : r ∉ fourCanonicalCapOrdinaryRays)
    (p : Fin 24) :
    mixedCostRayInt 0 p + ordinaryCostRayInt r p =
      ((seedOrdinaryAbsorptionRays r).map (fun k => ordinaryCostRayInt k p)).sum := by
  have h : ∀ s : Fin 34, s ∉ fourCanonicalCapOrdinaryRays → ∀ q : Fin 24,
      mixedCostRayInt 0 q + ordinaryCostRayInt s q =
        ((seedOrdinaryAbsorptionRays s).map (fun k => ordinaryCostRayInt k q)).sum := by
    intro s
    fin_cases s <;> decide +kernel
  exact h r hr p

/-- The sum of the canonical mixed ray and any ordinary ray outside the
specified thirteen-ray face is a nonnegative sum of rays in that face. -/
theorem fourCanonicalMixed_absorbsOrdinary (r : Fin 34) (hr : r ∉ fourCanonicalCapOrdinaryRays) :
    fourOrdinaryCostCone fourCanonicalCapOrdinaryRays (mixedCostRay 0 + ordinaryCostRay r) := by
  have hs : ∀ s : Fin 34, ∀ k : Fin 34,
      k ∈ seedOrdinaryAbsorptionRays s → k ∈ fourCanonicalCapOrdinaryRays := by
    intro s
    fin_cases s <;> decide +kernel
  have h : mixedCostRay 0 + ordinaryCostRay r =
      ((seedOrdinaryAbsorptionRays r).map ordinaryCostRay).sum := by
    funext p
    have he := congrArg (Int.cast : ℤ → ℝ) (seed_absorption_certificate r hr p)
    simpa only [Int.cast_add, ordinary_list_sum_cast, Pi.add_apply, mixedCostRay,
      ordinaryCostRay] using he
  rw [h]
  exact ordinary_list_sum (seedOrdinaryAbsorptionRays r) (hs r)

private def costRelabelRow (swap : Bool) : FourPerm :=
  fourPerm (if swap then 1 else 0)

private def composeCostFlips (a b : Bool) : Bool :=
  if a then !b else b

/-- Independent relabeling of the permutation slots. The two permitted row
maps and all column maps already cover the orbit of the seed. -/
def fourCostRelabel (swap : Bool) (b : FourPerm) : (Fin 24 → ℝ) →ₗ[ℝ] (Fin 24 → ℝ) where
  toFun x p := x (fourPermIndex (costRelabelRow swap * fourPerm p * b))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem fourPerm_index_right (p : FourPerm) : fourPerm (fourPermIndex p) = p :=
  fourPermEquiv.apply_symm_apply p

private theorem costRelabelRow_square (swap : Bool) : costRelabelRow swap * costRelabelRow swap = 1 := by
  cases swap <;> decide +kernel

private theorem costRelabelRow_product (a b : Bool) :
    costRelabelRow a * costRelabelRow b = costRelabelRow (composeCostFlips a b) := by
  cases a <;> cases b <;> decide +kernel

private theorem costRelabel_comp (a c : Bool) (b d : FourPerm) (x : Fin 24 → ℝ) :
    fourCostRelabel a b (fourCostRelabel c d x) =
      fourCostRelabel (composeCostFlips c a) (b * d) x := by
  funext p
  change x (fourPermIndex (costRelabelRow c *
    fourPerm (fourPermIndex (costRelabelRow a * fourPerm p * b)) * d)) =
    x (fourPermIndex (costRelabelRow (composeCostFlips c a) * fourPerm p * (b * d)))
  rw [fourPerm_index_right, ← costRelabelRow_product]
  simp only [mul_assoc]

private theorem costRelabel_inverse (swap : Bool) (b : FourPerm) (x : Fin 24 → ℝ) :
    fourCostRelabel swap b (fourCostRelabel swap b⁻¹ x) = x := by
  funext p
  change x (fourPermIndex (costRelabelRow swap *
    fourPerm (fourPermIndex (costRelabelRow swap * fourPerm p * b)) * b⁻¹)) = x p
  rw [fourPerm_index_right]
  have h : costRelabelRow swap * (costRelabelRow swap * fourPerm p * b) * b⁻¹ = fourPerm p := by
    calc
      _ = (costRelabelRow swap * costRelabelRow swap) * fourPerm p * (b * b⁻¹) := by
        simp only [mul_assoc]
      _ = fourPerm p := by rw [costRelabelRow_square, one_mul, mul_inv_cancel, mul_one]
  rw [h, fourPermIndex_fourPerm]

private def mixedRayIndex (swap : Bool) (b : Fin 24) : Fin 48 :=
  ⟨b.val + (if swap then 24 else 0), by
    have hb := b.isLt
    cases swap <;> simp <;> omega⟩

private theorem mixed_seed_profile (p : Fin 24) :
    mixedCostRayInt 0 p = mixedCostSeedInt p := by
  change mixedCostSeedInt (fourPermIndex (1 * fourPerm p * 1)) = mixedCostSeedInt p
  rw [one_mul, mul_one, fourPermIndex_fourPerm]

private theorem mixedRay_encoded (swap : Bool) (b : FourPerm) :
    fourCostRelabel swap b (mixedCostRay 0) =
      mixedCostRay (mixedRayIndex swap (fourPermIndex b)) := by
  let j := fourPermIndex b
  let r := mixedRayIndex swap j
  have hj : j.val < 24 := j.isLt
  have hrow : (if r.val < 24 then (0 : Fin 24) else 1) = (if swap then 1 else 0) := by
    cases swap with
    | false =>
      have hr : r.val < 24 := by simpa [r, mixedRayIndex] using hj
      simp [hr]
    | true =>
      have hr : ¬ r.val < 24 := by
        change ¬ j.val + 24 < 24
        omega
      simp [hr]
  have hmod : (⟨r.val % 24, Nat.mod_lt _ (by decide)⟩ : Fin 24) = j := by
    apply Fin.ext
    change (j.val + (if swap then 24 else 0)) % 24 = j.val
    cases swap with
    | false => exact Nat.mod_eq_of_lt hj
    | true =>
      change (j.val + 24) % 24 = j.val
      omega
  funext p
  change (mixedCostRayInt 0 (fourPermIndex (costRelabelRow swap * fourPerm p * b)) : ℝ) =
    (mixedCostRayInt r p : ℝ)
  rw [mixed_seed_profile, mixedCostRayInt, fourCostRelabelIndex, hrow, hmod]
  rw [show fourPerm j = b from fourPerm_index_right b]
  rfl

private theorem mixedRay_preimage (r : Fin 48) :
    ∃ (swap : Bool) (b : FourPerm), mixedCostRay r = fourCostRelabel swap b (mixedCostRay 0) := by
  let swap : Bool := if r.val < 24 then false else true
  let j : Fin 24 := ⟨r.val % 24, Nat.mod_lt _ (by decide)⟩
  refine ⟨swap, fourPerm j, ?_⟩
  rw [mixedRay_encoded, fourPermIndex_fourPerm]
  have hr : r = mixedRayIndex swap j := by
    apply Fin.ext
    have hlt := r.isLt
    by_cases h : r.val < 24
    · simp [swap, j, mixedRayIndex, h, Nat.mod_eq_of_lt h]
    · simp [swap, j, mixedRayIndex, h] <;> omega
  rw [← hr]

private theorem costRelabel_mixed (swap : Bool) (b : FourPerm) (r : Fin 48) :
    ∃ s : Fin 48, fourCostRelabel swap b (mixedCostRay r) = mixedCostRay s := by
  obtain ⟨c, d, he⟩ := mixedRay_preimage r
  rw [he, costRelabel_comp]
  exact ⟨mixedRayIndex (composeCostFlips c swap) (fourPermIndex (b * d)), mixedRay_encoded _ _⟩

private def pairBitMask (p : Fin 4 × Fin 4) : ℕ :=
  2 ^ p.1.val + 2 ^ p.2.val

private def pairIndexOfMask : ℕ → ℕ
  | 3 => 0
  | 5 => 1
  | 9 => 2
  | 6 => 3
  | 10 => 4
  | 12 => 5
  | _ => 0

/-- Reindex a singleton or pair indicator. A pair that loses label zero
is replaced by its complement, in both the source and the target. -/
private def ordinaryRelabelIndex (swap : Bool) (b : Fin 24) (r : Fin 34) : Fin 34 :=
  let row := costRelabelRow swap
  let col := fourPerm b
  let code :=
    if r.val < 16 then
      4 * (col ⟨r.val / 4 % 4, Nat.mod_lt _ (by decide)⟩).val +
        (row ⟨r.val % 4, Nat.mod_lt _ (by decide)⟩).val
    else
      let I := fourCostPair ⟨(r.val - 16) / 6 % 6, Nat.mod_lt _ (by decide)⟩
      let J := fourCostPair ⟨(r.val - 16) % 6, Nat.mod_lt _ (by decide)⟩
      let I' := pairBitMask (col I.1, col I.2)
      let J' := pairBitMask (row J.1, row J.2)
      if I' % 2 = 1 then 16 + 6 * pairIndexOfMask I' + pairIndexOfMask J'
      else 16 + 6 * pairIndexOfMask (15 - I') + pairIndexOfMask (15 - J')
  ⟨code % 34, Nat.mod_lt _ (by decide)⟩

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
private theorem ordinaryRelabel_certificate
    (swap : Bool) (b : Fin 24) (r : Fin 34) (p : Fin 24) :
    ordinaryCostRayInt r (fourPermIndex (costRelabelRow swap * fourPerm p * fourPerm b)) =
      ordinaryCostRayInt (ordinaryRelabelIndex swap b r) p := by
  have h : ∀ (c : Fin 24) (t : Bool) (k : Fin 34) (q : Fin 24),
      ordinaryCostRayInt k (fourPermIndex (costRelabelRow t * fourPerm q * fourPerm c)) =
        ordinaryCostRayInt (ordinaryRelabelIndex t c k) q := by
    intro c t
    fin_cases c <;> cases t <;> decide +kernel
  exact h b swap r p

private theorem costRelabel_ordinaryRay (swap : Bool) (b : FourPerm) (r : Fin 34) :
    fourCostRelabel swap b (ordinaryCostRay r) =
      ordinaryCostRay (ordinaryRelabelIndex swap (fourPermIndex b) r) := by
  funext p
  have he := ordinaryRelabel_certificate swap (fourPermIndex b) r p
  rw [fourPerm_index_right] at he
  exact congrArg (Int.cast : ℤ → ℝ) he

private theorem costRelabel_ordinary (swap : Bool) (b : FourPerm) {x : Fin 24 → ℝ}
    (hx : fourOrdinaryCostCone Finset.univ x) :
    fourOrdinaryCostCone Finset.univ (fourCostRelabel swap b x) := by
  obtain ⟨c, hc, _, rfl⟩ := hx
  rw [map_sum]
  apply ordinary_sum
  intro k _
  rw [map_smul, costRelabel_ordinaryRay]
  exact ordinary_smul (ordinary_ray (Finset.mem_univ _)) (hc k)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
private theorem mixed_ray_injective : Function.Injective mixedCostRay := by
  have he : ∀ r s : Fin 48, (∀ p : Fin 24, mixedCostRayInt r p = mixedCostRayInt s p) → r = s := by
    intro r
    fin_cases r <;> decide +kernel
  intro r s hrs
  apply he r s
  intro p
  exact Int.cast_injective (R := ℝ) (congrFun hrs p)

/-- Every pair of distinct mixed rays cancels into a nonnegative sum of
ordinary rays with equal coefficients on the two mixed rays. -/
theorem fourMixedPair_cancels (i j : Fin 48) (hij : i ≠ j) :
    fourOrdinaryCostCone Finset.univ (mixedCostRay i + mixedCostRay j) := by
  obtain ⟨swap, b, hi⟩ := mixedRay_preimage i
  obtain ⟨k, hj⟩ := costRelabel_mixed swap b⁻¹ j
  have hi' : fourCostRelabel swap b⁻¹ (mixedCostRay i) = mixedCostRay 0 := by
    rw [hi]
    simpa only [inv_inv] using costRelabel_inverse swap b⁻¹ (mixedCostRay 0)
  have hk : k ≠ 0 := by
    intro hk0
    rw [hk0, ← hi'] at hj
    have he := congrArg (fourCostRelabel swap b) hj
    simp only [costRelabel_inverse] at he
    exact hij (mixed_ray_injective he.symm)
  have hc : fourOrdinaryCostCone Finset.univ
      (fourCostRelabel swap b⁻¹ (mixedCostRay i + mixedCostRay j)) := by
    rw [map_add, hi', hj]
    exact seed_pair_ordinary k hk
  exact costRelabel_inverse swap b (mixedCostRay i + mixedCostRay j) ▸
    costRelabel_ordinary swap b hc

private theorem scaled_pair_split (x y : Fin 24 → ℝ) (a b : ℝ) :
    a • x + b • y = b • (x + y) + (a - b) • x := by
  funext p
  change a * x p + b * y p = b * (x p + y p) + (a - b) * x p
  ring

private theorem two_mixed_weights_reduce (i j : Fin 48) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ∃ (O : Fin 24 → ℝ) (k : Fin 48) (t : ℝ),
      fourOrdinaryCostCone Finset.univ O ∧ 0 ≤ t ∧
        a • mixedCostRay i + b • mixedCostRay j = O + t • mixedCostRay k := by
  by_cases h : i = j
  · subst j
    refine ⟨0, i, a + b, ordinary_zero _, add_nonneg ha hb, ?_⟩
    rw [zero_add, add_smul]
  have hp := fourMixedPair_cancels i j h
  by_cases hba : b ≤ a
  · exact ⟨b • (mixedCostRay i + mixedCostRay j), i, a - b, ordinary_smul hp hb,
      sub_nonneg.mpr hba, scaled_pair_split _ _ a b⟩
  · refine ⟨a • (mixedCostRay i + mixedCostRay j), j, b - a, ordinary_smul hp ha,
      sub_nonneg.mpr (le_of_not_ge hba), ?_⟩
    rw [add_comm (a • mixedCostRay i), scaled_pair_split, add_comm (mixedCostRay j) (mixedCostRay i)]

/-- A sum of nonnegatively weighted mixed rays is ordinary apart from at most
one mixed term. This is an identity of the whole cost profile. -/
theorem fourMixedCostSum_reduce (w : Fin 48 → ℝ) (hw : ∀ i, 0 ≤ w i) :
    ∃ (O : Fin 24 → ℝ) (k : Fin 48) (t : ℝ),
      fourOrdinaryCostCone Finset.univ O ∧ 0 ≤ t ∧
        (∑ i, w i • mixedCostRay i) = O + t • mixedCostRay k := by
  have H (S : Finset (Fin 48)) :
      ∃ (O : Fin 24 → ℝ) (k : Fin 48) (t : ℝ),
        fourOrdinaryCostCone Finset.univ O ∧ 0 ≤ t ∧
          (∑ i ∈ S, w i • mixedCostRay i) = O + t • mixedCostRay k := by
    induction S using Finset.induction_on with
    | empty =>
      exact ⟨0, 0, 0, ordinary_zero _, le_rfl,
        by simp only [Finset.sum_empty, zero_smul, add_zero]⟩
    | insert j S h ih =>
      obtain ⟨O, k, t, hO, ht, hrep⟩ := ih
      obtain ⟨P, l, u, hP, hu, hpair⟩ := two_mixed_weights_reduce k j ht (hw j)
      refine ⟨O + P, l, u, ordinary_add hO hP, hu, ?_⟩
      rw [Finset.sum_insert h, hrep]
      calc
        _ = O + (t • mixedCostRay k + w j • mixedCostRay j) := by ac_rfl
        _ = _ := by rw [hpair, add_assoc]
  exact H Finset.univ

private theorem canonical_face_subset (x : Fin 24 → ℝ)
    (hx : fourOrdinaryCostCone fourCanonicalCapOrdinaryRays x) :
    fourOrdinaryCostCone Finset.univ x :=
  ordinary_mono (fun k _ => Finset.mem_univ k) hx

private theorem canonical_absorb_one (O : Fin 24 → ℝ)
    (hO : fourOrdinaryCostCone fourCanonicalCapOrdinaryRays O)
    (k : Fin 34) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    let x := s • ordinaryCostRay k + (O + t • mixedCostRay 0)
    fourOrdinaryCostCone Finset.univ x ∨
      ∃ (P : Fin 24 → ℝ) (u : ℝ), fourOrdinaryCostCone fourCanonicalCapOrdinaryRays P ∧
        0 ≤ u ∧ x = P + u • mixedCostRay 0 := by
  dsimp only
  by_cases hk : k ∈ fourCanonicalCapOrdinaryRays
  · right
    refine ⟨s • ordinaryCostRay k + O, t,
      ordinary_add (ordinary_smul (ordinary_ray hk) hs) hO, ht, ?_⟩
    rw [add_assoc]
  have hpair := fourCanonicalMixed_absorbsOrdinary k hk
  by_cases hst : s ≤ t
  · right
    refine ⟨O + s • (mixedCostRay 0 + ordinaryCostRay k), t - s,
      ordinary_add hO (ordinary_smul hpair hs), sub_nonneg.mpr hst, ?_⟩
    calc
      _ = O + (t • mixedCostRay 0 + s • ordinaryCostRay k) := by ac_rfl
      _ = _ := by rw [scaled_pair_split, add_assoc]
  · left
    have hrest :=
      ordinary_smul (ordinary_ray (Finset.mem_univ k)) (sub_nonneg.mpr (le_of_not_ge hst))
    have he : s • ordinaryCostRay k + (O + t • mixedCostRay 0) =
        (O + t • (mixedCostRay 0 + ordinaryCostRay k)) + (s - t) • ordinaryCostRay k := by
      calc
        _ = O + (s • ordinaryCostRay k + t • mixedCostRay 0) := by ac_rfl
        _ = _ := by rw [scaled_pair_split, add_comm (ordinaryCostRay k) (mixedCostRay 0), add_assoc]
    rw [he]
    exact ordinary_add (canonical_face_subset _ (ordinary_add hO (ordinary_smul hpair ht))) hrest

/-- Add a nonnegative ordinary combination to the canonical mixed ray.
Either the cost becomes ordinary, or every surviving ordinary coefficient
is supported on the designated thirteen rays. -/
theorem fourCanonicalMixed_normalForm (O : Fin 24 → ℝ)
    (hO : fourOrdinaryCostCone Finset.univ O) (t : ℝ) (ht : 0 ≤ t) :
    fourOrdinaryCostCone Finset.univ (O + t • mixedCostRay 0) ∨
      ∃ (P : Fin 24 → ℝ) (u : ℝ), fourOrdinaryCostCone fourCanonicalCapOrdinaryRays P ∧
        0 ≤ u ∧ O + t • mixedCostRay 0 = P + u • mixedCostRay 0 := by
  obtain ⟨c, hc, _, rfl⟩ := hO
  have H (S : Finset (Fin 34)) :
      let x := (∑ k ∈ S, c k • ordinaryCostRay k) + t • mixedCostRay 0
      fourOrdinaryCostCone Finset.univ x ∨
        ∃ (P : Fin 24 → ℝ) (u : ℝ), fourOrdinaryCostCone fourCanonicalCapOrdinaryRays P ∧
          0 ≤ u ∧ x = P + u • mixedCostRay 0 := by
    induction S using Finset.induction_on with
    | empty =>
      right
      exact ⟨0, t, ordinary_zero _, ht, by rw [Finset.sum_empty]⟩
    | insert k S hk ih =>
      dsimp only at ih ⊢
      rw [Finset.sum_insert hk, add_assoc]
      rcases ih with h | ⟨P, u, hP, hu, hr⟩
      · left
        exact ordinary_add (ordinary_smul (ordinary_ray (Finset.mem_univ k)) (hc k)) h
      · rw [hr]
        exact canonical_absorb_one P hP k (hc k) hu
  exact H Finset.univ

/-- The canonical thirteen-ray section normal form for any nonnegative
expansion in the thirty-four ordinary and forty-eight mixed rays. A
nonordinary cost has strictly positive coefficient on the single mixed ray. -/
theorem fourSupportCost_normalForm_of_nonnegative_expansion
    (x : Fin 24 → ℝ) (a : Fin 34 → ℝ) (b : Fin 48 → ℝ)
    (ha : ∀ k, 0 ≤ a k) (hb : ∀ k, 0 ≤ b k)
    (hx : x = (∑ k, a k • ordinaryCostRay k) + ∑ k, b k • mixedCostRay k) :
    fourOrdinaryCostCone Finset.univ x ∨
      ∃ (swap : Bool) (r : FourPerm) (P : Fin 24 → ℝ) (t : ℝ),
        fourOrdinaryCostCone fourCanonicalCapOrdinaryRays P ∧
          0 < t ∧ x = fourCostRelabel swap r (P + t • mixedCostRay 0) := by
  obtain ⟨O, k, s, hO, hs, hrep⟩ := fourMixedCostSum_reduce b hb
  let A := (∑ j, a j • ordinaryCostRay j) + O
  have hA : fourOrdinaryCostCone Finset.univ A := ordinary_add
    ⟨a, ha, fun j hj => (hj (Finset.mem_univ j)).elim, rfl⟩ hO
  obtain ⟨swap, r, hk⟩ := mixedRay_preimage k
  let A' := fourCostRelabel swap r⁻¹ A
  have hA' : fourOrdinaryCostCone Finset.univ A' := costRelabel_ordinary swap r⁻¹ hA
  have he : x = fourCostRelabel swap r (A' + s • mixedCostRay 0) := by
    rw [hx, hrep, ← add_assoc, hk, map_add, map_smul]
    rw [show fourCostRelabel swap r A' = A from costRelabel_inverse swap r A]
  rcases fourCanonicalMixed_normalForm A' hA' s hs with h | ⟨P, t, hP, ht, h⟩
  · left
    exact he.symm ▸ costRelabel_ordinary swap r h
  · by_cases hp : 0 < t
    · exact Or.inr ⟨swap, r, P, t, hP, hp, by rw [he, h]⟩
    · have hz : t = 0 := le_antisymm (le_of_not_gt hp) ht
      rw [h, hz, zero_smul, add_zero] at he
      exact Or.inl (he.symm ▸ costRelabel_ordinary swap r (canonical_face_subset P hP))

/-- Evaluation of a permutation cost at a mixer by the real signed
determinant coefficients. -/
def fourSupportCostValue (U : Matrix (Fin 4) (Fin 4) ℂ) : (Fin 24 → ℝ) →ₗ[ℝ] ℝ where
  toFun x := ∑ p, realSignedWeight U (fourPerm p).symm * x p
  map_add' x y := by
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' t x := by
    change (∑ p, realSignedWeight U (fourPerm p).symm * (t * x p)) =
      t * ∑ p, realSignedWeight U (fourPerm p).symm * x p
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p _
    ring

/-- The ordinary profiles evaluate to the actual squared minors. -/
theorem fourSupportCostValue_ordinaryRay (U : Matrix (Fin 4) (Fin 4) ℂ)
    (hU : IsUnitary U) (r : Fin 34) :
    fourSupportCostValue U (ordinaryCostRay r) =
      subsetMinorSq U (ordinaryCostRows r) (ordinaryCostColumns r) := by
  let e : Fin 24 ≃ FourPerm := fourPermEquiv.trans (Equiv.inv FourPerm)
  let I := ordinaryCostRows r
  let J := ordinaryCostColumns r
  have he (p : Fin 24) : e p = (fourPerm p).symm := rfl
  have hsum := Equiv.sum_comp e (fun σ =>
    if J.map σ.toEmbedding = I then realSignedWeight U σ else 0)
  simp only [he] at hsum
  have hminor := congrArg Complex.re (sum_signedWeight_image_eq_subsetMinorSq U hU I J)
  simp only [Finset.sum_filter, Complex.re_sum, apply_ite, Complex.zero_re,
    Complex.ofReal_re] at hminor
  have hprofile (p : Fin 24) :
      realSignedWeight U (fourPerm p).symm * ordinaryCostRay r p =
        if J.map (fourPerm p).symm.toEmbedding = I then realSignedWeight U (fourPerm p).symm else 0 := by
    unfold ordinaryCostRay
    rw [ordinaryCostRayInt_indicator]
    by_cases h : J.map (fourPerm p).symm.toEmbedding = I
    · rw [if_pos h, Int.cast_one, mul_one, if_pos h]
    · rw [if_neg h, Int.cast_zero, mul_zero, if_neg h]
  change (∑ p, realSignedWeight U (fourPerm p).symm * ordinaryCostRay r p) =
    subsetMinorSq U I J
  simp_rw [hprofile]
  rw [hsum]
  exact hminor

/-- The ordinary branch of the normal form is nonnegative at every unitary. -/
theorem fourSupportCostValue_ordinaryNonnegative {S : Finset (Fin 34)}
    (U : Matrix (Fin 4) (Fin 4) ℂ) (hU : IsUnitary U)
    {x : Fin 24 → ℝ} (hx : fourOrdinaryCostCone S x) :
    0 ≤ fourSupportCostValue U x := by
  obtain ⟨c, hc, _, rfl⟩ := hx
  rw [map_sum]
  apply Finset.sum_nonneg
  intro r _
  rw [map_smul, smul_eq_mul, fourSupportCostValue_ordinaryRay U hU r]
  exact mul_nonneg (hc r) (subsetMinorSq_nonneg U _ _)

end

end MOC
