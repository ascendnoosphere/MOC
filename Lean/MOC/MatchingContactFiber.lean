import MOC.HighContact
import MOC.PolynomialFiberDimension

/-! Fewer than (2N-2) active labels leave a varying inactive gap. -/

open Matrix

namespace MOC

/-- In a regular high-contact chart below the terminal count, fixing the old
complex gaps and the complex determinant deficit leaves another regular
point. At least one inactive complex gap changes there. -/
theorem exists_inactive_gap_change_on_matching_fiber
    {n : ℕ} (hn : 2 ≤ n) (U : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ)
    (η : ℂ) (hη : η ≠ 0) (r : ContactMatching n)
    (z : MatchingChartVariable n → ℂ)
    (hz : MvPolynomial.eval z (matchingChartRegularPolynomial n) ≠ 0)
    (hcard : (chartContacts η r z).card < 2 * (n + 2) - 2) :
    ∃ w : MatchingChartVariable n → ℂ,
      MvPolynomial.eval w (matchingChartRegularPolynomial n) ≠ 0 ∧
      (∀ i : Option ↥((chartContacts η r z).erase r),
        MvPolynomial.eval w (matchingChartContactPolynomial U (chartContacts η r z) r i) =
        MvPolynomial.eval z (matchingChartContactPolynomial U (chartContacts η r z) r i)) ∧
      ∃ σ ∉ chartContacts η r z, chartMatchingGap η r z σ ≠ chartMatchingGap η r w σ := by
  classical
  let T := chartContacts η r z
  have hr : r ∈ T := by change r ∈ chartContacts η r z; simp [chartMatchingGap]
  have hc : Fintype.card (Option ↥(T.erase r)) < Fintype.card (MatchingChartVariable n) := by
    rw [card_matchingChartContactConstraints T r hr, card_matchingChartVariable]
    exact hcard
  obtain ⟨w, hne, hw, hfiber⟩ := exists_other_regular_point_of_polynomial_fiber
    (matchingChartContactPolynomial U T r) (matchingChartRegularPolynomial n) z hz hc
  refine ⟨w, hw, hfiber, ?_⟩
  by_contra! hfixed
  let e : Fin 4 ↪ Fin (n + 2) := Fin.castLEEmb (by omega)
  apply hne
  symm
  apply matchingChart_eq_of_differences_eq z w hz r (e 0) (e 1) (e 2) (e 3)
    (e.injective.ne (by decide)) (e.injective.ne (by decide)) (e.injective.ne (by decide))
    (e.injective.ne (by decide)) (e.injective.ne (by decide)) (e.injective.ne (by decide))
  intro σ
  by_cases hσ : σ ∈ T
  · by_cases he : σ = r
    · subst σ
      simp
    · have h := hfiber (some ⟨σ, Finset.mem_erase.mpr ⟨he, hσ⟩⟩)
      change MvPolynomial.eval w (matchingChartPolynomial r - matchingChartPolynomial σ) =
        MvPolynomial.eval z (matchingChartPolynomial r - matchingChartPolynomial σ) at h
      simpa only [map_sub, eval_matchingChartPolynomial] using h.symm
  · exact mul_left_cancel₀ hη (hfixed σ hσ)

end MOC
