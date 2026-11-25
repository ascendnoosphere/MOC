import MOC.FourCoincidence
import MOC.FourMatchingRelations
import MOC.Support
import Mathlib.Data.Real.Sqrt

/-! A constant cost on the matchings that pair the two zero labels has
a nonnegative decomposition into singleton and two-element indicators. -/

open BigOperators Finset Matrix

namespace MOC

noncomputable section

private abbrev Cell := Fin 3 × Fin 3

private def rebalancedCell (w : Fin 3 → Fin 3 → ℝ) (r c : Fin 3 → ℝ)
    (i j : Fin 3) : ℝ :=
  w i j + r i + c j - ((∑ k, r k) + (∑ k, c k)) / 2

private theorem rebalance_one_negative_row (w : Fin 3 → Fin 3 → ℝ) (i j : Fin 3)
    (hij : w i j < 0) (hout : ∀ k l, k ≠ i → 0 ≤ w k l)
    (hpair : ∀ i k j l, i ≠ k → j ≠ l → 0 ≤ w i j + w k l) :
    ∃ r c : Fin 3 → ℝ, (∀ k, 0 ≤ r k) ∧ (∀ k, 0 ≤ c k) ∧
      ∀ k l, 0 ≤ rebalancedCell w r c k l := by
  classical
  obtain ⟨j₀, _, hmax⟩ := Finset.exists_max_image Finset.univ
    (fun t : Fin 3 => -w i t) ⟨0, Finset.mem_univ 0⟩
  have hnonempty : (Finset.univ.erase j₀ : Finset (Fin 3)).Nonempty := by
    fin_cases j₀ <;> decide
  obtain ⟨j₁, hj₁, hnext⟩ := Finset.exists_max_image (Finset.univ.erase j₀)
    (fun t : Fin 3 => -w i t) hnonempty
  let p := -w i j₀
  let q := max 0 (-w i j₁)
  have hp : 0 ≤ p := (neg_pos.mpr hij).le.trans (hmax j (Finset.mem_univ j))
  have hq : 0 ≤ q := le_max_left _ _
  have hqp : q ≤ p := max_le hp (hmax j₁ (Finset.mem_univ j₁))
  have hj₁₀ : j₁ ≠ j₀ := Finset.ne_of_mem_erase hj₁
  let r (k : Fin 3) := if k = i then p + q else 0
  let c (l : Fin 3) := if l = j₀ then p - q else 0
  have hsumr : ∑ k, r k = p + q := by
    simp only [r, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have hsumc : ∑ l, c l = p - q := by
    simp only [c, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  refine ⟨r, c, fun k => ?_, fun l => ?_, fun k l => ?_⟩
  · dsimp only [r]
    split_ifs
    · exact add_nonneg hp hq
    · exact le_rfl
  · dsimp only [c]
    split_ifs
    · exact sub_nonneg.mpr hqp
    · exact le_rfl
  · unfold rebalancedCell
    rw [hsumr, hsumc]
    by_cases hk : k = i
    · subst k
      by_cases hl : l = j₀
      · subst l
        simp only [r, c, if_pos rfl]
        dsimp only [p]
        linarith
      · have hneg : -w i l ≤ q :=
          (hnext l (Finset.mem_erase.mpr ⟨hl, Finset.mem_univ l⟩)).trans (le_max_right _ _)
        simp only [r, c, if_pos rfl, if_neg hl, add_zero]
        linarith only [hneg]
    · by_cases hl : l = j₀
      · subst l
        have hneg : -w i j₁ ≤ w k j₀ := by
          linarith only [hpair i k j₁ j₀ (Ne.symm hk) hj₁₀]
        have hbound : q ≤ w k j₀ := max_le (hout k j₀ hk) hneg
        simp only [r, c, if_neg hk, if_pos rfl, add_zero]
        linarith only [hbound]
      · have hbound : p ≤ w k l := by
          dsimp only [p]
          linarith only [hpair i k j₀ l (Ne.symm hk) (Ne.symm hl)]
        simp only [r, c, if_neg hk, if_neg hl, add_zero]
        linarith only [hbound]

/-- Nonnegative sums on pairs in distinct rows and columns allow nonnegative
row, column, and rebalanced cell coefficients. -/
private theorem rebalance_collision_weights (w : Fin 3 → Fin 3 → ℝ)
    (hpair : ∀ i k j l, i ≠ k → j ≠ l → 0 ≤ w i j + w k l) :
    ∃ r c : Fin 3 → ℝ, (∀ k, 0 ≤ r k) ∧ (∀ k, 0 ≤ c k) ∧
      ∀ k l, 0 ≤ rebalancedCell w r c k l := by
  classical
  by_cases hneg : ∃ i j, w i j < 0
  · obtain ⟨i, j, hij⟩ := hneg
    by_cases hother : ∃ k l, k ≠ i ∧ w k l < 0
    · obtain ⟨k, l, hki, hkl⟩ := hother
      have hlj : l = j := by
        by_contra hne
        linarith only [hpair i k j l (Ne.symm hki) (Ne.symm hne), hij, hkl]
      subst l
      have hcol (s t : Fin 3) (ht : t ≠ j) : 0 ≤ w s t := by
        by_cases hs : s = i
        · subst s
          linarith only [hpair i k t j (Ne.symm hki) ht, hkl]
        · linarith only [hpair s i t j hs ht, hij]
      obtain ⟨c, r, hc, hr, hcr⟩ := rebalance_one_negative_row
        (fun x y => w y x) j i hij (fun t s ht => hcol s t ht)
        (fun x y s t hxy hst => hpair s t x y hst hxy)
      refine ⟨r, c, hr, hc, fun s t => ?_⟩
      simpa only [rebalancedCell, add_comm (∑ k, c k) (∑ k, r k),
        add_right_comm (w s t) (c t) (r s)] using hcr t s
    · exact rebalance_one_negative_row w i j hij
        (fun k l hki => le_of_not_gt fun hkl => hother ⟨k, l, hki, hkl⟩) hpair
  · refine ⟨0, 0, fun _ => le_rfl, fun _ => le_rfl, fun i j => ?_⟩
    simpa only [rebalancedCell, Pi.zero_apply, Finset.sum_const_zero, add_zero,
      zero_div, sub_zero] using (le_of_not_gt fun hij => hneg ⟨i, j, hij⟩)

/-- For a matching outside the fixed-label coset, record the missing row
and column, then the two cells that give its two-element indicators. -/
private def collisionCells (k : Fin 24) : Option (Cell × Cell × Cell) :=
  ![none, none, none, none, none, none,
    some ((0, 0), (1, 2), (2, 1)), some ((0, 0), (1, 1), (2, 2)),
    some ((1, 0), (0, 2), (2, 1)), some ((2, 0), (0, 2), (1, 1)),
    some ((1, 0), (0, 1), (2, 2)), some ((2, 0), (0, 1), (1, 2)),
    some ((0, 1), (1, 2), (2, 0)), some ((0, 1), (1, 0), (2, 2)),
    some ((1, 1), (0, 2), (2, 0)), some ((2, 1), (0, 2), (1, 0)),
    some ((1, 1), (0, 0), (2, 2)), some ((2, 1), (0, 0), (1, 2)),
    some ((0, 2), (1, 1), (2, 0)), some ((0, 2), (1, 0), (2, 1)),
    some ((1, 2), (0, 1), (2, 0)), some ((2, 2), (0, 1), (1, 0)),
    some ((1, 2), (0, 0), (2, 1)), some ((2, 2), (0, 0), (1, 1))] k

private def collisionPairValue (h : ℝ) (w : Fin 3 → Fin 3 → ℝ) (k : Fin 24) : ℝ :=
  match collisionCells k with
  | none => h
  | some (_, x, y) => w x.1 x.2 + w y.1 y.2

/-- Each cell weight is half of the sum of two matching costs minus
the third cost on a triangle of nonattacking cells. -/
private def collisionCellWeights (g : Fin 24 → ℝ) : Fin 3 → Fin 3 → ℝ :=
  ![![(g 23 + g 16 - g 7) / 2, (g 11 + g 20 - g 12) / 2, (g 15 + g 8 - g 19) / 2],
    ![(g 19 + g 15 - g 8) / 2, (g 7 + g 23 - g 16) / 2, (g 12 + g 11 - g 20) / 2],
    ![(g 20 + g 12 - g 11) / 2, (g 8 + g 19 - g 15) / 2, (g 16 + g 7 - g 23) / 2]]

set_option maxHeartbeats 3000000 in
private theorem matchingEvaluation_eq_collisionPair (m : Fin 14 → ℝ) (h : ℝ)
    (hc : ∀ k : Fin 24, k.val < 6 → fourMatchingEvaluation m k = h) (k : Fin 24) :
    fourMatchingEvaluation m k = collisionPairValue h
      (collisionCellWeights (fourMatchingEvaluation m)) k := by
  have h₀ := hc 0 (by decide)
  have h₁ := hc 1 (by decide)
  have h₂ := hc 2 (by decide)
  have h₃ := hc 3 (by decide)
  have h₄ := hc 4 (by decide)
  have h₅ := hc 5 (by decide)
  simp only [fourMatchingEvaluation, Matrix.cons_val] at h₀ h₁ h₂ h₃ h₄ h₅
  fin_cases k <;>
    norm_num [collisionPairValue, collisionCells, collisionCellWeights, fourMatchingEvaluation] <;>
    linarith only [h₀, h₁, h₂, h₃, h₄, h₅]

set_option maxHeartbeats 3000000 in
private theorem collisionCells_cover (i k j l : Fin 3) (hik : i ≠ k) (hjl : j ≠ l) :
    ∃ p : Fin 24, ((collisionCells p).map Prod.snd = some ((i, j), (k, l))) ∨
      ((collisionCells p).map Prod.snd = some ((k, l), (i, j))) := by
  revert i k j l
  decide +kernel

/-- The ordinary generators for a fixed zero-label coset consist of seven
singleton indicators and nine two-element subset-image indicators. -/
def fourOppositePairOrdinaryCost (h : ℝ) (r c : Fin 3 → ℝ)
    (w : Fin 3 → Fin 3 → ℝ) (σ : FourPerm) : ℝ :=
  (if σ 0 = 0 then h else 0) +
    (∑ i, if σ 0 = i.succ then r i else 0) +
    (∑ j, if σ j.succ = 0 then c j else 0) +
    ∑ i, ∑ j,
      if (({0, j.succ} : Finset (Fin 4))ᶜ).map σ.toEmbedding = {0, i.succ}
      then w i j else 0

private theorem collision_fixed_mask (k : Fin 24) :
    (fourPerm k).symm 0 = 0 ↔ collisionCells k = none := by
  revert k
  decide +kernel

private theorem collision_row_mask (k : Fin 24) (i : Fin 3) :
    (fourPerm k).symm 0 = i.succ ↔ (collisionCells k).map (fun x => x.1.1) = some i := by
  revert k i
  decide +kernel

private theorem collision_column_mask (k : Fin 24) (j : Fin 3) :
    (fourPerm k).symm j.succ = 0 ↔ (collisionCells k).map (fun x => x.1.2) = some j := by
  revert k j
  decide +kernel

set_option maxHeartbeats 3000000 in
private theorem collision_minor_mask (k : Fin 24) (i j : Fin 3) :
    (({0, j.succ} : Finset (Fin 4))ᶜ).map (fourPerm k).symm.toEmbedding = {0, i.succ} ↔
      ((collisionCells k).map (fun x => decide ((i, j) = x.2.1 ∨ (i, j) = x.2.2))).getD false = true := by
  revert k i j
  decide +kernel

set_option maxHeartbeats 3000000 in
private theorem oppositePairOrdinaryCost_rebalanced (h : ℝ) (r c : Fin 3 → ℝ)
    (w : Fin 3 → Fin 3 → ℝ) (k : Fin 24) :
    fourOppositePairOrdinaryCost h r c (rebalancedCell w r c) (fourPerm k).symm =
      collisionPairValue h w k := by
  unfold fourOppositePairOrdinaryCost
  simp only [collision_fixed_mask, collision_row_mask, collision_column_mask, collision_minor_mask,
    Fin.sum_univ_three]
  fin_cases k <;>
    norm_num [collisionPairValue, collisionCells, rebalancedCell, Fin.sum_univ_three] <;> ring

/-- A nonnegative matching cost that is constant on the six permutations
that fix label zero is a nonnegative combination of ordinary indicators. -/
theorem fourOppositePair_ordinary_cost (m : Fin 14 → ℝ) (h : ℝ)
    (hn : ∀ k, 0 ≤ fourMatchingEvaluation m k)
    (hc : ∀ k : Fin 24, k.val < 6 → fourMatchingEvaluation m k = h) :
    0 ≤ h ∧ ∃ r c : Fin 3 → ℝ, ∃ w : Fin 3 → Fin 3 → ℝ,
      (∀ i, 0 ≤ r i) ∧ (∀ j, 0 ≤ c j) ∧ (∀ i j, 0 ≤ w i j) ∧
      ∀ k, fourMatchingEvaluation m k = fourOppositePairOrdinaryCost h r c w (fourPerm k).symm := by
  let w := collisionCellWeights (fourMatchingEvaluation m)
  have hval (k : Fin 24) : fourMatchingEvaluation m k = collisionPairValue h w k :=
    matchingEvaluation_eq_collisionPair m h hc k
  have hpairPos (p : Fin 24) (x y : Cell)
      (he : (collisionCells p).map Prod.snd = some (x, y)) :
      0 ≤ w x.1 x.2 + w y.1 y.2 := by
    have hnonneg := hn p
    rw [hval] at hnonneg
    unfold collisionPairValue at hnonneg
    cases hslots : collisionCells p with
    | none => simp only [hslots, Option.map_none, reduceCtorEq] at he
    | some t =>
      obtain ⟨s, u, v⟩ := t
      have huv : (u, v) = (x, y) := Option.some.inj (by
        simpa only [hslots, Option.map_some] using he)
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj huv
      simpa only [hslots] using hnonneg
  have hp (i k j l : Fin 3) (hik : i ≠ k) (hjl : j ≠ l) : 0 ≤ w i j + w k l := by
    obtain ⟨p, he | he⟩ := collisionCells_cover i k j l hik hjl
    · exact hpairPos p (i, j) (k, l) he
    · simpa only [add_comm (w k l) (w i j)] using hpairPos p (k, l) (i, j) he
  obtain ⟨r, c, hr, hc', hw⟩ := rebalance_collision_weights w hp
  refine ⟨(hc 0 (by decide)) ▸ hn 0, r, c, rebalancedCell w r c, hr, hc', hw, fun k => ?_⟩
  rw [hval, oppositePairOrdinaryCost_rebalanced]

private def collisionIndicatorRows : Fin 16 → Finset (Fin 4) :=
  ![{0}, {1}, {2}, {3}, {0}, {0}, {0},
    {0, 1}, {0, 1}, {0, 1}, {0, 2}, {0, 2}, {0, 2}, {0, 3}, {0, 3}, {0, 3}]

private def collisionIndicatorColumns : Fin 16 → Finset (Fin 4) :=
  ![{0}, {0}, {0}, {0}, {1}, {2}, {3},
    {2, 3}, {1, 3}, {1, 2}, {2, 3}, {1, 3}, {1, 2}, {2, 3}, {1, 3}, {1, 2}]

private def collisionIndicatorCoefficients (h : ℝ) (r c : Fin 3 → ℝ)
    (w : Fin 3 → Fin 3 → ℝ) : Fin 16 → ℝ :=
  ![h, r 0, r 1, r 2, c 0, c 1, c 2,
    w 0 0, w 0 1, w 0 2, w 1 0, w 1 1, w 1 2, w 2 0, w 2 1, w 2 2]

private def collisionIndicator {R : Type*} [Zero R] [One R] (p : Fin 16) (σ : FourPerm) : R :=
  if (collisionIndicatorColumns p).map σ.toEmbedding = collisionIndicatorRows p then 1 else 0

set_option maxHeartbeats 3000000 in
private theorem oppositePairOrdinaryCost_eq_sum (h : ℝ) (r c : Fin 3 → ℝ)
    (w : Fin 3 → Fin 3 → ℝ) (σ : FourPerm) :
    fourOppositePairOrdinaryCost h r c w σ =
      ∑ p : Fin 16, collisionIndicatorCoefficients h r c w p * collisionIndicator p σ := by
  have h₁ : ({0, 1} : Finset (Fin 4))ᶜ = {2, 3} := by decide
  have h₂ : ({0, 2} : Finset (Fin 4))ᶜ = {1, 3} := by decide
  have h₃ : ({0, 3} : Finset (Fin 4))ᶜ = {1, 2} := by decide
  norm_num [fourOppositePairOrdinaryCost, collisionIndicatorCoefficients, collisionIndicator,
    collisionIndicatorRows, collisionIndicatorColumns, Fin.sum_univ_succ, h₁, h₂, h₃,
    Finset.map_singleton, mul_ite] <;> ring

private def collisionIndicatorCoordinates (p : Fin 16) : Fin 14 → ℤ :=
  fourMatchingCoordinatesOfValues (fun k => collisionIndicator p (fourPerm k).symm)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem collisionIndicator_realized (p : Fin 16) (k : Fin 24) :
    fourMatchingEvaluation (fun i => (collisionIndicatorCoordinates p i : ℝ)) k =
      collisionIndicator p (fourPerm k).symm := by
  have hint : ∀ (i : Fin 16) (j : Fin 24),
      fourMatchingEvaluation (collisionIndicatorCoordinates i) j =
        (collisionIndicator i (fourPerm j).symm : ℤ) := by
    decide +kernel
  have hcast :
      fourMatchingEvaluation (fun i => (collisionIndicatorCoordinates p i : ℝ)) k =
        (fourMatchingEvaluation (collisionIndicatorCoordinates p) k : ℝ) := by
    fin_cases k <;> simp only [fourMatchingEvaluation, Matrix.cons_val, Int.cast_add,
      Int.cast_mul, Int.cast_ofNat]
  rw [hcast, hint]
  unfold collisionIndicator
  split_ifs <;> simp only [Int.cast_one, Int.cast_zero]

private theorem matchingEvaluation_scale_collision (c : ℝ) (m : Fin 14 → ℝ) (k : Fin 24) :
    fourMatchingEvaluation (fun i => c * m i) k = c * fourMatchingEvaluation m k := by
  fin_cases k <;> simp only [fourMatchingEvaluation, Matrix.cons_val] <;> ring

/-- The constant-coset cost is a sum of sixteen real squares in the same
fourteen-coordinate matching-function space. -/
theorem fourOppositePair_matching_squares (m : Fin 14 → ℝ) (h : ℝ)
    (hn : ∀ k, 0 ≤ fourMatchingEvaluation m k)
    (hc : ∀ k : Fin 24, k.val < 6 → fourMatchingEvaluation m k = h) :
    ∃ v : Fin 16 → Fin 14 → ℝ, ∀ k, fourMatchingEvaluation m k =
      ∑ p, (fourMatchingEvaluation (v p) k) ^ 2 := by
  obtain ⟨hh, r, c, w, hr, hc', hw, hcost⟩ := fourOppositePair_ordinary_cost m h hn hc
  let t := collisionIndicatorCoefficients h r c w
  have ht (p : Fin 16) : 0 ≤ t p := by
    fin_cases p <;> simp only [t, collisionIndicatorCoefficients, Matrix.cons_val] <;>
      first | exact hh | exact hr _ | exact hc' _ | exact hw _ _
  refine ⟨fun p i => Real.sqrt (t p) * (collisionIndicatorCoordinates p i : ℝ), fun k => ?_⟩
  rw [hcost, oppositePairOrdinaryCost_eq_sum]
  apply Finset.sum_congr rfl
  intro p _
  rw [matchingEvaluation_scale_collision, collisionIndicator_realized]
  change t p * collisionIndicator p (fourPerm k).symm = _
  unfold collisionIndicator
  split_ifs <;> simp only [mul_one, mul_zero, zero_pow (by decide : (2 : ℕ) ≠ 0),
    Real.sq_sqrt (ht p)]

private theorem matchingEvaluation_sub_height (m : Fin 14 → ℝ) (h : ℝ) (k : Fin 24) :
    fourMatchingEvaluation (fun i => (if i = 13 then h else 0) - m i) k =
      h - fourMatchingEvaluation m k := by
  fin_cases k <;> norm_num [fourMatchingEvaluation] <;> ring

private theorem collision_label_of_index (k : Fin 24) (hk : k.val < 6) :
    (fourPerm k).symm 0 = 0 := by
  revert k
  decide +kernel

/-- When the two zero labels pair opposite eigenvalues, every nonnegative
directional support cost has the ordinary decomposition. -/
theorem fourOppositePair_spectral_ordinary_cost (a b : Fin 4 → ℂ) (η : ℂ) (H : ℝ)
    (hab : a 0 + b 0 = 0) (hn : ∀ σ : FourPerm, (η * matchingProduct a b σ).re ≤ H) :
    0 ≤ H ∧ ∃ r c : Fin 3 → ℝ, ∃ w : Fin 3 → Fin 3 → ℝ,
      (∀ i, 0 ≤ r i) ∧ (∀ j, 0 ≤ c j) ∧ (∀ i j, 0 ≤ w i j) ∧
      ∀ σ : FourPerm, H - (η * matchingProduct a b σ).re =
        fourOppositePairOrdinaryCost H r c w σ := by
  let m (i : Fin 14) := (η * fourNoncrossingCoordinates (fourSpectralPoints a b) i).re
  let n (i : Fin 14) := (if i = 13 then H else 0) - m i
  have hprofile (k : Fin 24) : fourMatchingEvaluation n k =
      H - (η * matchingProduct a b (fourPerm k).symm).re := by
    change fourMatchingEvaluation (fun i => (if i = 13 then H else 0) - m i) k = _
    rw [matchingEvaluation_sub_height]
    rw [fourMatchingEvaluation_spectral_real_part a b η k]
  have hfixed (k : Fin 24) (hk : k.val < 6) : fourMatchingEvaluation n k = H := by
    have hz : matchingProduct a b (fourPerm k).symm = 0 := by
      unfold matchingProduct
      apply Finset.prod_eq_zero (Finset.mem_univ (0 : Fin 4))
      rw [collision_label_of_index k hk, hab]
    rw [hprofile, hz, mul_zero, Complex.zero_re, sub_zero]
  obtain ⟨hH, r, c, w, hr, hc, hw, hrep⟩ :=
    fourOppositePair_ordinary_cost n H
      (fun k => by rw [hprofile]; exact sub_nonneg.mpr (hn (fourPerm k).symm)) hfixed
  refine ⟨hH, r, c, w, hr, hc, hw, fun σ => ?_⟩
  obtain ⟨k, hk⟩ := fourPerm_surjective σ.symm
  have hs : (fourPerm k).symm = σ := by rw [hk, Equiv.symm_symm]
  rw [← hs, ← hprofile]
  exact hrep k

/-- Any opposite eigenvalue pair, at arbitrary labels, gives the order-four
support bound in every complex direction. -/
theorem four_support_of_opposite_eigenvalue_pair (a b : Fin 4 → ℂ)
    (U : Matrix (Fin 4) (Fin 4) ℂ) (hU : IsUnitary U) {i j : Fin 4}
    (hij : a i + b j = 0) (η : ℂ) :
    ∃ σ : FourPerm, (η * determinantValue a b U).re ≤ (η * matchingProduct a b σ).re :=
  (holds_iff_directional a b U).mp (holds_four_of_opposite_entries a b U hU hij) η

end

end MOC
