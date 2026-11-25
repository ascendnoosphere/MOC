import MOC.SparseRow

/-! The determinant hull inclusion for complex unitary matrices of order
four with zero diagonal. -/

open BigOperators Matrix Finset

namespace MOC

noncomputable section

/-- A reference derangement on four labels. -/
private def fourDerangementBase : Equiv.Perm (Fin 4) :=
  Equiv.swap 0 1 * Equiv.swap 2 3

private theorem fourDerangementBase_deranges (j : Fin 4) : fourDerangementBase j ≠ j := by
  revert j
  decide +kernel

private def fourDerangementLeft := fourDerangementBase * Equiv.swap 0 2
private def fourDerangementRight := fourDerangementBase * Equiv.swap 0 3
private def fourDerangementMid := fourDerangementLeft * Equiv.swap 1 3

private theorem four_derangement_list (σ : Equiv.Perm (Fin 4)) :
    (∀ l, σ l ≠ l) →
    σ = fourDerangementBase ∨
    σ = fourDerangementLeft ∨
    σ = fourDerangementRight ∨
    σ = fourDerangementBase * Equiv.swap 1 2 ∨
    σ = fourDerangementBase * Equiv.swap 1 3 ∨
    σ = fourDerangementMid ∨
    σ = fourDerangementRight * Equiv.swap 1 2 ∨
    σ = fourDerangementMid * Equiv.swap 0 1 ∨
    σ = fourDerangementMid * Equiv.swap 2 3 := by
  revert σ
  decide +kernel

/-- The derangements on four labels are connected by swaps of two columns
that preserve the absence of fixed labels. -/
private theorem four_derangement_induction (P : Equiv.Perm (Fin 4) → Prop)
    (hbase : P fourDerangementBase)
    (hswap : ∀ (σ : Equiv.Perm (Fin 4)) (j k : Fin 4), j ≠ k →
      (∀ l, σ l ≠ l) → (∀ l, (σ * Equiv.swap j k) l ≠ l) → P σ →
      P (σ * Equiv.swap j k))
    (σ : Equiv.Perm (Fin 4)) (hσ : ∀ l, σ l ≠ l) : P σ := by
  have hleft : ∀ l, fourDerangementLeft l ≠ l := by decide +kernel
  have hright : ∀ l, fourDerangementRight l ≠ l := by decide +kernel
  have hmid : ∀ l, fourDerangementMid l ≠ l := by decide +kernel
  have hpLeft : P fourDerangementLeft :=
    hswap _ 0 2 (by decide) fourDerangementBase_deranges hleft hbase
  have hpRight : P fourDerangementRight :=
    hswap _ 0 3 (by decide) fourDerangementBase_deranges hright hbase
  have hpMid : P fourDerangementMid :=
    hswap _ 1 3 (by decide) hleft hmid hpLeft
  rcases four_derangement_list σ hσ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hbase
  · exact hpLeft
  · exact hpRight
  · exact hswap _ 1 2 (by decide) fourDerangementBase_deranges hσ hbase
  · exact hswap _ 1 3 (by decide) fourDerangementBase_deranges hσ hbase
  · exact hpMid
  · exact hswap _ 1 2 (by decide) hright hσ hpRight
  · exact hswap _ 0 1 (by decide) hmid hσ hpMid
  · exact hswap _ 2 3 (by decide) hmid hσ hpMid

private theorem fin4_four_distinct_cover :
    ∀ r s j k : Fin 4, r ≠ s → r ≠ j → r ≠ k → s ≠ j → s ≠ k → j ≠ k →
      ∀ x, x = j ∨ x = k ∨ x = r ∨ x = s := by
  decide +kernel

private theorem pair_swap_positive {a b c d : ℂ} (hc : c ≠ 0) (hd : d ≠ 0)
    (h : a * star c + b * star d = 0) :
    ∃ t : ℝ, 0 < t ∧ -(c * b) = (t : ℂ) * (a * d) := by
  have hcpos : 0 < Complex.normSq c := Complex.normSq_pos.mpr hc
  have hdpos : 0 < Complex.normSq d := Complex.normSq_pos.mpr hd
  refine ⟨Complex.normSq c / Complex.normSq d, div_pos hcpos hdpos, ?_⟩
  rw [Complex.ofReal_div]
  have hdn : (Complex.normSq d : ℂ) ≠ 0 := by exact_mod_cast hdpos.ne'
  field_simp
  rw [Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_conj_mul_self]
  change -(c * b * (star d * d)) = star c * c * (a * d)
  linear_combination -(c * d) * h

/-- A swap of two columns that preserves the absence of fixed points changes
the signed determinant term by a positive real factor. -/
private theorem leibnizTerm_mul_swap_pos {U : Matrix (Fin 4) (Fin 4) ℂ}
    (hU : IsUnitary U) (hz : ∀ i, U i i = 0)
    (hn : ∀ i j, i ≠ j → U i j ≠ 0) (σ : Equiv.Perm (Fin 4)) (j k : Fin 4)
    (hjk : j ≠ k) (hσ : ∀ i, σ i ≠ i) (hτ : ∀ i, (σ * Equiv.swap j k) i ≠ i) :
    ∃ c : ℝ, 0 < c ∧ leibnizTerm U (σ * Equiv.swap j k) = (c : ℂ) * leibnizTerm U σ := by
  classical
  let r := σ j
  let s := σ k
  have hrs : r ≠ s := fun h => hjk (σ.injective h)
  have hrj : r ≠ j := hσ j
  have hsk : s ≠ k := hσ k
  have hrk : r ≠ k := by simpa [r, Equiv.Perm.mul_apply] using hτ k
  have hsj : s ≠ j := by simpa [s, Equiv.Perm.mul_apply] using hτ j
  have horth : (∑ x, U r x * star (U s x)) = 0 := by
    have h := congrArg (fun A : Matrix (Fin 4) (Fin 4) ℂ => A r s) hU.1
    simpa only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply_ne hrs] using h
  have hpair : U r j * star (U s j) + U r k * star (U s k) = 0 := by
    rw [← Finset.sum_pair (f := fun x => U r x * star (U s x)) hjk]
    refine (Finset.sum_subset (Finset.subset_univ _) ?_).trans horth
    intro x _ hx
    rcases fin4_four_distinct_cover r s j k hrs hrj hrk hsj hsk hjk x with h | h | h | h
    · exact (hx (by simp [h])).elim
    · exact (hx (by simp [h])).elim
    · rw [h, hz, zero_mul]
    · rw [h, hz, star_zero, mul_zero]
  obtain ⟨c, hcp, hc⟩ := pair_swap_positive (hn s j hsj) (hn s k hsk) hpair
  refine ⟨c, hcp, ?_⟩
  let S := ((Finset.univ : Finset (Fin 4)).erase j).erase k
  have hfact (f : Fin 4 → ℂ) : (∏ x, f x) = f j * f k * ∏ x ∈ S, f x := by
    rw [← Finset.mul_prod_erase Finset.univ f (Finset.mem_univ j),
      ← Finset.mul_prod_erase (Finset.univ.erase j) f (Finset.mem_erase.mpr ⟨hjk.symm, Finset.mem_univ k⟩)]
    rw [mul_assoc]
  have hrest :
      (∏ x ∈ S, U ((σ * Equiv.swap j k) x) x) = ∏ x ∈ S, U (σ x) x := by
    apply Finset.prod_congr rfl
    intro x hx
    have hk := (Finset.mem_erase.mp hx).1
    have hj := (Finset.mem_erase.mp (Finset.mem_erase.mp hx).2).1
    rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hj hk]
  unfold leibnizTerm
  rw [hfact (fun x => U ((σ * Equiv.swap j k) x) x), hfact (fun x => U (σ x) x), hrest]
  simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_left, Equiv.swap_apply_right,
    Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hjk, Units.val_mul, Units.val_neg, Units.val_one,
    Int.cast_mul, Int.cast_neg, Int.cast_one]
  change (((Equiv.Perm.sign σ : ℤ) : ℂ) * -1) *
      (U s j * U r k * ∏ x ∈ S, U (σ x) x) =
    (c : ℂ) * (((Equiv.Perm.sign σ : ℤ) : ℂ) *
      (U r j * U s k * ∏ x ∈ S, U (σ x) x))
  linear_combination (((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ x ∈ S, U (σ x) x) * hc

private theorem four_supportColumns_card_le_two {U : Matrix (Fin 4) (Fin 4) ℂ}
    (i j : Fin 4) (hij : i ≠ j) (hi : U i i = 0) (hj : U i j = 0) :
    (supportColumns U {i}).card ≤ 2 := by
  classical
  have hs : supportColumns U {i} ⊆ ({i, j} : Finset (Fin 4))ᶜ := by
    intro k hk
    have hU : U i k ≠ 0 := by simpa [supportColumns] using hk
    exact Finset.mem_compl.mpr fun h =>
      (Finset.mem_insert.mp h).elim (fun h => hU (h ▸ hi)) (fun h =>
        hU (Finset.mem_singleton.mp h ▸ hj))
  have hc := Finset.card_le_card hs
  simpa [Finset.card_compl, hij] using hc

private theorem four_realSignedWeight_nonneg_of_zero_diagonal_of_offDiagonal_ne_zero
    {U : Matrix (Fin 4) (Fin 4) ℂ} (hU : IsUnitary U)
    (hz : ∀ i, U i i = 0) (hn : ∀ i j, i ≠ j → U i j ≠ 0) :
    ∀ σ, 0 ≤ realSignedWeight U σ := by
  classical
  let P (σ : Equiv.Perm (Fin 4)) := ∃ c : ℝ, 0 ≤ c ∧
    leibnizTerm U σ = (c : ℂ) * leibnizTerm U fourDerangementBase
  have hbase : P fourDerangementBase := ⟨1, zero_le_one, by simp⟩
  have hswap (σ : Equiv.Perm (Fin 4)) (j k : Fin 4) (hjk : j ≠ k)
      (hσ : ∀ i, σ i ≠ i) (hτ : ∀ i, (σ * Equiv.swap j k) i ≠ i) :
      P σ → P (σ * Equiv.swap j k) := by
    rintro ⟨c, hc, he⟩
    obtain ⟨d, hd, hr⟩ := leibnizTerm_mul_swap_pos hU hz hn σ j k hjk hσ hτ
    refine ⟨d * c, mul_nonneg hd.le hc, ?_⟩
    rw [hr, he, Complex.ofReal_mul, mul_assoc]
  have hall (σ : Equiv.Perm (Fin 4)) : P σ := by
    by_cases hs : ∀ i, σ i ≠ i
    · exact four_derangement_induction P hbase hswap σ hs
    · push_neg at hs
      obtain ⟨i, hi⟩ := hs
      refine ⟨0, le_rfl, ?_⟩
      have hprod : (∏ j, U (σ j) j) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ i) (show U (σ i) i = 0 by rw [hi, hz])
      simp [leibnizTerm, hprod]
  obtain ⟨c, hc⟩ := Classical.axiomOfChoice hall
  have hw (σ : Equiv.Perm (Fin 4)) : realSignedWeight U σ =
      c σ * realSignedWeight U fourDerangementBase := by
    rw [realSignedWeight, realSignedWeight, signedWeight, (hc σ).2, mul_div_assoc]
    simp [signedWeight, Complex.mul_re]
  have hsum : (∑ σ, c σ) * realSignedWeight U fourDerangementBase = 1 := by
    rw [Finset.sum_mul]
    calc
      _ = ∑ σ, realSignedWeight U σ := Finset.sum_congr rfl (fun σ _ => (hw σ).symm)
      _ = 1 := sum_realSignedWeight U hU
  have hs : 0 ≤ ∑ σ, c σ :=
    Finset.sum_nonneg (fun σ _ => (hc σ).1)
  have hpos : 0 ≤ realSignedWeight U fourDerangementBase := by
    by_contra! hn
    have hprod := mul_nonpos_of_nonneg_of_nonpos hs hn.le
    rw [hsum] at hprod
    exact (not_le_of_gt (zero_lt_one : (0 : ℝ) < 1)) hprod
  intro σ
  rw [hw]
  exact mul_nonneg (hc σ).1 hpos

/-- A complex unitary matrix of order four with zero diagonal satisfies the
determinant convex-hull inclusion for all spectral labels. -/
theorem four_holds_zero_diagonal_unitary (a b : Fin 4 → ℂ)
    {U : Matrix (Fin 4) (Fin 4) ℂ} (hU : IsUnitary U) (hz : ∀ i, U i i = 0) :
    Holds a b U := by
  classical
  by_cases hn : ∀ i j, i ≠ j → U i j ≠ 0
  · exact holds_of_nonneg_realSignedWeight a b hU
      (four_realSignedWeight_nonneg_of_zero_diagonal_of_offDiagonal_ne_zero
        hU hz hn)
  · push_neg at hn
    obtain ⟨i, j, hij, hij₀⟩ := hn
    exact holds_of_row_degree_le_two conjecture_three a b hU i
      (four_supportColumns_card_le_two i j hij (hz i) hij₀)

end

end MOC
