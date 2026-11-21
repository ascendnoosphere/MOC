import MOC.Claim

/-! Balanced cuts in the support of a unitary give paired block splits. -/

open BigOperators Matrix

namespace MOC

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- If the rows in `s` are supported in `t`, the excess column capacity of `t`
is exactly the squared mass received from rows outside `s`. -/
theorem unitary_support_cut_balance {U : Matrix ι ι ℂ} (hU : IsUnitary U)
    (s t : Finset ι) (hzero : ∀ i ∈ s, ∀ j ∉ t, U i j = 0) :
    (s.card : ℝ) + ∑ j ∈ t, ∑ i ∈ sᶜ, Complex.normSq (U i j) = (t.card : ℝ) := by
  have hst := normSq_transpose_doublyStochastic U hU
  have hrow (i : ι) : ∑ j, Complex.normSq (U i j) = 1 :=
    sum_col_of_mem_doublyStochastic hst i
  have hcol (j : ι) : ∑ i, Complex.normSq (U i j) = 1 :=
    sum_row_of_mem_doublyStochastic hst j
  have hrect : (∑ i ∈ s, ∑ j ∈ t, Complex.normSq (U i j)) = (s.card : ℝ) := by
    calc
      _ = ∑ i ∈ s, (1 : ℝ) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [← hrow i]
        apply Finset.sum_subset (Finset.subset_univ t)
        intro j _ hj
        rw [hzero i hi j hj, map_zero]
      _ = _ := by simp
  rw [Finset.sum_comm] at hrect
  rw [← hrect, ← Finset.sum_add_distrib]
  simp_rw [Finset.sum_add_sum_compl, hcol]
  simp

theorem card_le_of_unitary_support_cut {U : Matrix ι ι ℂ} (hU : IsUnitary U)
    (s t : Finset ι) (hzero : ∀ i ∈ s, ∀ j ∉ t, U i j = 0) : s.card ≤ t.card := by
  have hnonneg : 0 ≤ ∑ j ∈ t, ∑ i ∈ sᶜ, Complex.normSq (U i j) :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _
  have hle : (s.card : ℝ) ≤ (t.card : ℝ) := by
    rw [← unitary_support_cut_balance hU s t hzero]
    exact le_add_of_nonneg_right hnonneg
  exact_mod_cast hle

/-- A one-sided vanishing cut of equal size exposes two nonempty square blocks. -/
theorem hasProperPairedBlocks_of_unitary_support_cut {n : ℕ}
    {U : Matrix (Fin n) (Fin n) ℂ} (hU : IsUnitary U) (s t : Finset (Fin n))
    (hs : s.Nonempty) (hs' : ∃ i, i ∉ s) (hcard : s.card = t.card)
    (hzero : ∀ i ∈ s, ∀ j ∉ t, U i j = 0) : HasProperPairedBlocks U := by
  classical
  have hbalance := unitary_support_cut_balance hU s t hzero
  have hmass : (∑ j ∈ t, ∑ i ∈ sᶜ, Complex.normSq (U i j)) = 0 := by
    have heq : (s.card : ℝ) + (∑ j ∈ t, ∑ i ∈ sᶜ, Complex.normSq (U i j)) =
        (s.card : ℝ) + 0 := by
      simpa only [hcard, add_zero] using hbalance
    exact add_left_cancel heq
  have hother (i : Fin n) (hi : i ∉ s) (j : Fin n) (hj : j ∈ t) : U i j = 0 := by
    have hcol := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ =>
      Finset.sum_nonneg fun i _ => Complex.normSq_nonneg (U i j))).mp hmass j hj
    exact Complex.normSq_eq_zero.mp
      ((Finset.sum_eq_zero_iff_of_nonneg (fun i _ => Complex.normSq_nonneg (U i j))).mp
        hcol i (Finset.mem_compl.mpr hi))
  let k := Fintype.card {i : Fin n // i ∉ s}
  have hcolcard : Fintype.card {i : Fin n // i ∉ t} = k := by
    apply Fintype.card_compl_eq_card_compl (fun i : Fin n => i ∈ t) (fun i => i ∈ s)
    exact (Fintype.card_coe t).trans (hcard.symm.trans (Fintype.card_coe s).symm)
  have hk : 0 < k := by
    obtain ⟨i, hi⟩ := hs'
    exact Fintype.card_pos_iff.mpr ⟨⟨i, hi⟩⟩
  let r := s.equivFin.symm
  let r' := (Fintype.equivFin {i : Fin n // i ∉ s}).symm
  let c := (Finset.equivFinOfCardEq hcard.symm : t ≃ Fin s.card).symm
  let c' := (Fintype.equivFinOfCardEq hcolcard).symm
  let eRow := (Equiv.sumCongr r r').trans (Equiv.sumCompl (fun i => i ∈ s))
  let eCol := (Equiv.sumCongr c c').trans (Equiv.sumCompl (fun i => i ∈ t))
  refine ⟨s.card, k, eRow, eCol, U.submatrix (fun i => r i) (fun j => c j),
    U.submatrix (fun i => r' i) (fun j => c' j), Finset.card_pos.mpr hs, hk, ?_⟩
  ext i j : 1
  rcases i with i | i <;> rcases j with j | j
  · rfl
  · change U (r i) (c' j) = 0
    exact hzero _ (r i).property _ (c' j).property
  · change U (r' i) (c j) = 0
    exact hother _ (r' i).property _ (c j).property
  · rfl

/-- The column neighbors of a row set in the support of a matrix. -/
def supportColumns (U : Matrix ι ι ℂ) (s : Finset ι) : Finset ι := by
  classical
  exact Finset.univ.filter (fun j => ∃ i ∈ s, U i j ≠ 0)

/-- Without a proper paired block split, every nonempty proper row set
has strictly more column neighbors than rows. -/
theorem card_lt_supportColumns_of_no_paired_blocks {n : ℕ}
    {U : Matrix (Fin n) (Fin n) ℂ} (hU : IsUnitary U) (hblocks : ¬ HasProperPairedBlocks U)
    (s : Finset (Fin n)) (hs : s.Nonempty) (hs' : ∃ i, i ∉ s) :
    s.card < (supportColumns U s).card := by
  classical
  have hzero : ∀ i ∈ s, ∀ j ∉ supportColumns U s, U i j = 0 := by
    intro i hi j hj
    by_contra hn
    apply hj
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, i, hi, hn⟩
  apply lt_of_le_of_ne (card_le_of_unitary_support_cut hU s _ hzero)
  exact fun heq => hblocks (hasProperPairedBlocks_of_unitary_support_cut hU s _ hs hs' heq hzero)

/-- One can restrict the all-order conjecture to relative eigenbases whose
nonempty proper row sets have strict support expansion. -/
theorem mocIsTrue_iff_strict_support_expansion :
    MOCIsTrue ↔ ∀ (n : ℕ), 4 ≤ n → ∀ (a b : Fin n → ℂ)
      (U : Matrix (Fin n) (Fin n) ℂ), IsUnitary U →
      (∀ s : Finset (Fin n), s.Nonempty → (∃ i, i ∉ s) →
        s.card < (supportColumns U s).card) → Holds a b U := by
  constructor
  · intro h n _ a b U hU _
    exact h n a b U hU
  · intro h
    apply mocIsTrue_iff_no_proper_paired_blocks.mpr
    intro n hn a b U hU hblocks
    exact h n hn a b U hU (card_lt_supportColumns_of_no_paired_blocks hU hblocks)

end

end MOC
