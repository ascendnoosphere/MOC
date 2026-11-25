import MOC.DeficitContactTransfer

/-! A regular violation with maximal contact count is isolated in its
fiber of fixed complex active matching gaps. -/

open MvPolynomial Set

namespace MOC

noncomputable section

variable {n : ℕ}

/-- The ideal of the fiber that fixes every active complex gap at `z`. -/
def chartOldGapFiberIdeal (η : ℂ) (r : ContactMatching n)
    (z : MatchingChartVariable n → ℂ) : Ideal (MvPolynomial (MatchingChartVariable n) ℂ) :=
  Ideal.span (range fun i => chartOldGapPolynomial η r z i -
    C (eval z (chartOldGapPolynomial η r z i)))

/-- Any prime in the fiber strictly below the point ideal would yield a
curve on which the contact count can be increased. -/
theorem chart_point_ideal_minimal_of_maximal_contacts
    (hn : 2 ≤ n) (U : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ) (hU : IsUnitary U)
    (η : ℂ) (r : ContactMatching n) (z : MatchingChartVariable n → ℂ)
    (hz : eval z (matchingChartRegularPolynomial n) ≠ 0)
    (hmax : ∀ σ, 0 ≤ (chartMatchingGap η r z σ).re)
    (hpos : 0 < (η * eval z (matchingChartDeficitPolynomial U r)).re)
    (hmaximal : ∀ w : MatchingChartVariable n → ℂ,
      eval w (matchingChartRegularPolynomial n) ≠ 0 →
      (∀ σ, 0 ≤ (chartMatchingGap η r w σ).re) →
      0 < (η * eval w (matchingChartDeficitPolynomial U r)).re →
      (chartContacts η r w).card ≤ (chartContacts η r z).card) :
    vanishingIdeal ({z} : Set (MatchingChartVariable n → ℂ)) ∈
      (chartOldGapFiberIdeal η r z).minimalPrimes := by
  classical
  let I := chartOldGapFiberIdeal η r z
  let M := vanishingIdeal ({z} : Set (MatchingChartVariable n → ℂ))
  let p := chartOldGapPolynomial η r z
  have hIM : I ≤ M := by
    refine Ideal.span_le.mpr ?_
    rintro _ ⟨i, rfl⟩
    exact (mem_vanishingIdeal_singleton_iff z _).mpr (by simp)
  change Minimal (fun P : Ideal (MvPolynomial (MatchingChartVariable n) ℂ) =>
    P.IsPrime ∧ I ≤ P) M
  refine ⟨⟨inferInstance, hIM⟩, ?_⟩
  intro P hP hPM
  apply Classical.byContradiction
  intro hnle
  have hp (i : ↥((chartContacts η r z).erase r)) : p i - C (eval z (p i)) ∈ P :=
    hP.2 (Ideal.subset_span ⟨i, rfl⟩)
  obtain ⟨Q, hQ, hG, hlt, f, hfi, hf⟩ :=
    exists_finite_curve_of_polynomial_fiber_of_prime p z P hP.1 hp
      (lt_of_le_of_ne hPM fun h => hnle h.ge)
  letI : Q.IsPrime := hQ
  obtain ⟨w, hw, hwpos, hwmax, hwmore⟩ :=
    exists_new_contact_on_fixed_old_gap_curve hn U hU η r z hz hmax hpos Q hG hlt f hfi hf
  exact (not_le_of_gt (Finset.card_lt_card hwmore)) (hmaximal w hw hwmax hwpos)

/-- It suffices to prove support in charts whose point ideals are minimal
over the ideal fixing the old active complex gaps. -/
theorem mocIsTrue_iff_terminal_chart_support_minimal_prime :
    MOCIsTrue ↔ ∀ n : ℕ, 2 ≤ n →
      ∀ (U : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ) (_ : IsUnitary U)
        (η : ℂ) (r : ContactMatching n) (z : MatchingChartVariable n → ℂ),
        eval z (matchingChartRegularPolynomial n) ≠ 0 →
        (∀ σ, 0 ≤ (chartMatchingGap η r z σ).re) →
        vanishingIdeal ({z} : Set (MatchingChartVariable n → ℂ)) ∈
          (chartOldGapFiberIdeal η r z).minimalPrimes →
        (η * eval z (matchingChartDeficitPolynomial U r)).re ≤ 0 := by
  classical
  constructor
  · intro h n _ U hU η r z _ hmax _
    obtain ⟨a, b, hab⟩ := exists_spectra_of_matchingChartCoordinate z
    obtain ⟨σ, hσ⟩ := (holds_iff_directional a b U).mp (h (n + 2) a b U hU) η
    have hg := hmax σ
    simp only [chartMatchingGap, ← hab r, ← hab σ, mul_sub, Complex.sub_re] at hg
    rw [eval_matchingChartDeficitPolynomial z a b U hU r hab, mul_sub, Complex.sub_re]
    exact sub_nonpos.mpr (hσ.trans (sub_nonneg.mp hg))
  · intro hterminal
    apply mocIsTrue_iff_terminal_chart_support.mpr
    intro n hn U hU η r z hz hmax _
    by_contra! hpos
    let admissible (w : MatchingChartVariable n → ℂ) : Prop :=
      eval w (matchingChartRegularPolynomial n) ≠ 0 ∧
      (∀ σ, 0 ≤ (chartMatchingGap η r w σ).re) ∧
      0 < (η * eval w (matchingChartDeficitPolynomial U r)).re
    let sizes := (Finset.range (Fintype.card (ContactMatching n) + 1)).filter fun k =>
      ∃ w, admissible w ∧ (chartContacts η r w).card = k
    have hsize (w : MatchingChartVariable n → ℂ) (hw : admissible w) :
        (chartContacts η r w).card ∈ sizes :=
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr
        (Nat.lt_succ_of_le (Finset.card_le_univ _)), w, hw, rfl⟩
    obtain ⟨k, hk, hkmax⟩ := Finset.exists_max_image sizes id
      ⟨_, hsize z ⟨hz, hmax, hpos⟩⟩
    obtain ⟨w, hw, hkw⟩ := (Finset.mem_filter.mp hk).2
    have hminimal := chart_point_ideal_minimal_of_maximal_contacts hn U hU η r w
      hw.1 hw.2.1 hw.2.2 (fun v hv hvmax hvpos =>
        (hkmax _ (hsize v ⟨hv, hvmax, hvpos⟩)).trans_eq hkw.symm)
    exact (not_lt_of_ge (hterminal n hn U hU η r w hw.1 hw.2.1 hminimal)) hw.2.2

end

end MOC
