import MOC.HighContact
import MOC.PolynomialFiberCurve

/-! A positive-dimensional contact fiber contains a curve on which at least
one inactive matching gap is a nonconstant projection. -/

open MvPolynomial Set

namespace MOC

noncomputable section

variable {n : ℕ}

/-- The polynomial whose value is the complex gap to an inactive matching. -/
def matchingChartGapPolynomial (η : ℂ) (r σ : ContactMatching n) :
    MvPolynomial (MatchingChartVariable n) ℂ :=
  C η * (matchingChartPolynomial r - matchingChartPolynomial σ)

@[simp] theorem eval_matchingChartGapPolynomial (η : ℂ) (r σ : ContactMatching n)
    (z : MatchingChartVariable n → ℂ) :
    eval z (matchingChartGapPolynomial η r σ) = chartMatchingGap η r z σ := by
  simp only [matchingChartGapPolynomial, chartMatchingGap, map_mul, map_sub, eval_C,
    eval_matchingChartPolynomial]

/-- Any prime curve through a regular point of the fixed-contact fiber has
an inactive gap that is nonscalar in its coordinate ring. -/
theorem exists_nonscalar_inactive_gap_on_curve
    (hn : 2 ≤ n) (U : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ)
    (η : ℂ) (hη : η ≠ 0) (r : ContactMatching n)
    (z : MatchingChartVariable n → ℂ)
    (hz : eval z (matchingChartRegularPolynomial n) ≠ 0)
    (Q : Ideal (MvPolynomial (MatchingChartVariable n) ℂ)) [Q.IsPrime]
    (hQ : Q < vanishingIdeal ({z} : Set (MatchingChartVariable n → ℂ)))
    (hfiber : ∀ i : Option ↥((chartContacts η r z).erase r),
      let p := matchingChartContactPolynomial U (chartContacts η r z) r i
      p - C (eval z p) ∈ Q) :
    ∃ σ ∉ chartContacts η r z,
      Ideal.Quotient.mk Q (matchingChartGapPolynomial η r σ) ∉
        range (algebraMap ℂ (MvPolynomial (MatchingChartVariable n) ℂ ⧸ Q)) := by
  classical
  by_contra! hscalar
  have hsubset : zeroLocus Q ⊆ ({z} : Set (MatchingChartVariable n → ℂ)) := by
    intro w hw
    have hvalues (p : MvPolynomial (MatchingChartVariable n) ℂ)
        (hp : p ∈ Q) : eval w p = eval z p :=
      ((mem_zeroLocus_iff.mp hw) p hp).trans
        ((mem_vanishingIdeal_singleton_iff z p).mp (hQ.le hp)).symm
    rw [Set.mem_singleton_iff]
    symm
    let e : Fin 4 ↪ Fin (n + 2) := Fin.castLEEmb (by omega)
    apply matchingChart_eq_of_differences_eq z w hz r (e 0) (e 1) (e 2) (e 3)
      (e.injective.ne (by decide)) (e.injective.ne (by decide)) (e.injective.ne (by decide))
      (e.injective.ne (by decide)) (e.injective.ne (by decide)) (e.injective.ne (by decide))
    intro σ
    by_cases hs : σ ∈ chartContacts η r z
    · by_cases he : σ = r
      · subst σ
        simp only [sub_self]
      · let i : ↥((chartContacts η r z).erase r) := ⟨σ, Finset.mem_erase.mpr ⟨he, hs⟩⟩
        have h := (mem_zeroLocus_iff.mp hw) _ (hfiber (some i))
        change eval w ((matchingChartPolynomial r - matchingChartPolynomial σ) -
          C (eval z (matchingChartPolynomial r - matchingChartPolynomial σ))) = 0 at h
        simp only [map_sub, eval_C, eval_matchingChartPolynomial, sub_eq_zero] at h
        exact h.symm
    · obtain ⟨c, hc⟩ := hscalar σ hs
      let p := matchingChartGapPolynomial η r σ
      change Ideal.Quotient.mk Q (C c) = Ideal.Quotient.mk Q p at hc
      have hp : p - C c ∈ Q := by
        apply Ideal.Quotient.eq_zero_iff_mem.mp
        rw [map_sub, hc, sub_self]
      have h := hvalues (p - C c) hp
      simp only [map_sub, eval_C] at h
      have hg : eval z p = eval w p := sub_right_cancel h.symm
      simp only [p, eval_matchingChartGapPolynomial, chartMatchingGap] at hg
      exact mul_left_cancel₀ hη hg
  have hle := vanishingIdeal_anti_mono hsubset
  rw [MvPolynomial.IsPrime.vanishingIdeal_zeroLocus] at hle
  exact (not_le_of_gt hQ) hle

/-- Below the terminal contact count, an affine curve through the given
point fixes the old gaps and the determinant deficit while varying an
inactive gap. Its coordinate ring is finite over an affine line. -/
theorem exists_matching_contact_curve
    (hn : 2 ≤ n) (U : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ)
    (η : ℂ) (hη : η ≠ 0) (r : ContactMatching n)
    (z : MatchingChartVariable n → ℂ)
    (hz : eval z (matchingChartRegularPolynomial n) ≠ 0)
    (hcard : (chartContacts η r z).card < 2 * (n + 2) - 2) :
    ∃ Q : Ideal (MvPolynomial (MatchingChartVariable n) ℂ), Q.IsPrime ∧
      (∀ i : Option ↥((chartContacts η r z).erase r),
        let p := matchingChartContactPolynomial U (chartContacts η r z) r i
        p - C (eval z p) ∈ Q) ∧
      Q < vanishingIdeal ({z} : Set (MatchingChartVariable n → ℂ)) ∧
      (∃ f : Polynomial ℂ →ₐ[ℂ] (MvPolynomial (MatchingChartVariable n) ℂ ⧸ Q),
        Function.Injective f ∧ f.Finite) ∧
      ∃ σ ∉ chartContacts η r z,
        Ideal.Quotient.mk Q (matchingChartGapPolynomial η r σ) ∉
          range (algebraMap ℂ (MvPolynomial (MatchingChartVariable n) ℂ ⧸ Q)) := by
  classical
  let T := chartContacts η r z
  have hr : r ∈ T := by change r ∈ chartContacts η r z; simp [chartMatchingGap]
  have hc : Fintype.card (Option ↥(T.erase r)) < Fintype.card (MatchingChartVariable n) := by
    rw [card_matchingChartContactConstraints T r hr, card_matchingChartVariable]
    exact hcard
  obtain ⟨Q, hQ, hfiber, hlt, hfinite⟩ := exists_finite_curve_of_polynomial_fiber
    (matchingChartContactPolynomial U T r) z hc
  letI : Q.IsPrime := hQ
  exact ⟨Q, hQ, hfiber, hlt, hfinite,
    exists_nonscalar_inactive_gap_on_curve hn U η hη r z hz Q hlt hfiber⟩

end

end MOC
