import MOC.DeficitContactTransfer
import MOC.FourContactRay

/-! The rank condition on a terminal contact chart survives eliminating
matching edges shared by all its contacts. -/

open BigOperators Matrix MvPolynomial

namespace MOC

private theorem chartOldGapRank_mono_of_contacts {n : ℕ} (η : ℂ) (r : ContactMatching n)
    (z w : MatchingChartVariable n → ℂ) (h : chartContacts η r z ⊆ chartContacts η r w) :
    chartOldGapRank η r z ≤ chartOldGapRank η r w := by
  let S := Set.range (chartOldGapPolynomial η r z)
  let T := Set.range (chartOldGapPolynomial η r w)
  have hST : S ⊆ T := by
    rintro _ ⟨⟨σ, hσ⟩, rfl⟩
    obtain ⟨hne, hm⟩ := Finset.mem_erase.mp hσ
    exact ⟨⟨σ, Finset.mem_erase.mpr ⟨hne, h hm⟩⟩, rfl⟩
  letI : FiniteDimensional ℂ (Submodule.span ℂ T) :=
    FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
  change Module.finrank ℂ (Submodule.span ℂ S) ≤ Module.finrank ℂ (Submodule.span ℂ T)
  exact Submodule.finrank_mono (Submodule.span_mono hST)

/-- The unrestricted conjecture reduces to regular terminal charts with
full old-gap rank and no edge shared by all active matchings. -/
theorem mocIsTrue_iff_terminal_chart_support_old_gap_rank_no_common_edge :
    MOCIsTrue ↔ ∀ n : ℕ, 2 ≤ n →
      ∀ (U : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ) (_ : IsUnitary U)
        (η : ℂ) (r : ContactMatching n) (z : MatchingChartVariable n → ℂ),
        eval z (matchingChartRegularPolynomial n) ≠ 0 →
        (∀ σ, 0 ≤ (chartMatchingGap η r z σ).re) →
        2 * (n + 2) - 2 ≤ chartOldGapRank η r z →
        (∀ i j, ∃ σ ∈ chartContacts η r z, σ j ≠ i) →
        (η * eval z (matchingChartDeficitPolynomial U r)).re ≤ 0 := by
  constructor
  · intro h n hn U hU η r z hz hmax hrank _
    exact (mocIsTrue_iff_terminal_chart_support_old_gap_rank.mp h) n hn U hU η r z hz hmax hrank
  · intro hterminal
    apply mocIsTrue_iff_terminal_chart_support_old_gap_rank.mpr
    intro n hn U hU η r z hz hmax hrank
    by_cases hη : η = 0
    · simp [hη]
    obtain ⟨_, hnz, hzinj⟩ := (eval_matchingChartRegularPolynomial_ne_zero z).mp hz
    obtain ⟨a, b, hab⟩ := exists_spectra_of_matchingChartCoordinate z
    have hreg (i j : Fin (n + 2)) : a i + b j ≠ 0 := by
      intro hzero
      let σ := Equiv.swap j i
      have hprod : matchingProduct a b σ = 0 := Finset.prod_eq_zero (Finset.mem_univ j) (by
        simpa only [σ, Equiv.swap_apply_left] using hzero)
      exact hnz σ ((hab σ).symm.trans hprod)
    have hinj : Function.Injective (matchingProduct a b) := by
      intro σ τ he
      exact hzinj (by rw [← hab σ, ← hab τ, he])
    let H := (η * matchingProduct a b r).re
    have hscore (σ : ContactMatching n) :
        (chartMatchingGap η r z σ).re = H - (η * matchingProduct a b σ).re := by
      rw [chartMatchingGap, ← hab r, ← hab σ, mul_sub, Complex.sub_re]
    have hs (σ : ContactMatching n) : (η * matchingProduct a b σ).re ≤ H := by
      apply sub_nonneg.mp
      rw [← hscore]
      exact hmax σ
    obtain ⟨c, d, hdet, hle, hpres, hdist, hcdreg, hnoedge⟩ :=
      exists_no_common_active_edge_of_regular_support a b U hU η hη H hreg hs
    have hcdinj : Function.Injective (matchingProduct c d) := by
      intro σ τ he
      by_contra hne
      exact hdist σ τ (hinj.ne hne) he
    obtain ⟨hc, hd⟩ := injective_spectra_of_matchingProduct_injective hcdinj
    have hp : ((0 : Fin (n + 1)).succ : Fin (n + 2)) ≠ 0 := Fin.succ_ne_zero _
    obtain ⟨w, hpiv, hwnz, hw⟩ :=
      exists_matchingChartCoordinate_of_nonopposite c d hcdreg (hc.ne hp) (hd.ne hp)
    have hwreg : eval w (matchingChartRegularPolynomial n) ≠ 0 :=
      (eval_matchingChartRegularPolynomial_ne_zero w).mpr ⟨hpiv, hwnz, fun σ τ he =>
        hcdinj (by rw [hw σ, hw τ, he])⟩
    have hwscore (σ : ContactMatching n) :
        (chartMatchingGap η r w σ).re = H - (η * matchingProduct c d σ).re := by
      rw [chartMatchingGap, ← hw r, ← hw σ, hpres r rfl, mul_sub, Complex.sub_re]
    have hwmax (σ : ContactMatching n) : 0 ≤ (chartMatchingGap η r w σ).re := by
      rw [hwscore]
      exact sub_nonneg.mpr (hle σ)
    have hsubset : chartContacts η r z ⊆ chartContacts η r w := by
      intro σ hσ
      have he := (mem_chartContacts η r σ z).mp hσ
      rw [hscore, sub_eq_zero] at he
      apply (mem_chartContacts η r σ w).mpr
      rw [hwscore, hpres σ he.symm, he, sub_self]
    have hwedge (i j : Fin (n + 2)) : ∃ σ ∈ chartContacts η r w, σ j ≠ i := by
      obtain ⟨σ, he, hne⟩ := hnoedge i j
      refine ⟨σ, (mem_chartContacts η r σ w).mpr ?_, hne⟩
      rw [hwscore, he, sub_self]
    have hnew := hterminal n hn U hU η r w hwreg hwmax
      (hrank.trans (chartOldGapRank_mono_of_contacts η r z w hsubset)) hwedge
    rw [eval_matchingChartDeficitPolynomial w c d U hU r hw, hpres r rfl,
      mul_sub, Complex.sub_re] at hnew
    rw [eval_matchingChartDeficitPolynomial z a b U hU r hab, mul_sub, Complex.sub_re]
    exact (sub_le_sub_right hdet _).trans hnew

end MOC
