import MOC.FiniteCurveLocalAccess
import MOC.FiniteCurvePlaneCover
import MOC.FiniteCurveReprojection
import MOC.MatchingContactCurve

/-! The contact count increases on a regular polynomial fiber by lifting a
path along a nonconstant inactive gap. -/

open MvPolynomial Set

namespace MOC

noncomputable section

variable {n : ℕ}

/-- A curve on which an inactive gap varies admits a regular covering with a
starting point in the positive chamber. -/
theorem matchingChartContactCover_of_curve
    (U : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ) (η : ℂ) (r : ContactMatching n)
    (z : MatchingChartVariable n → ℂ)
    (hz : eval z (matchingChartRegularPolynomial n) ≠ 0)
    (hmax : ∀ σ, 0 ≤ (chartMatchingGap η r z σ).re)
    (Q : Ideal (MvPolynomial (MatchingChartVariable n) ℂ)) [Q.IsPrime]
    (hfiber : ∀ j : Option ↥((chartContacts η r z).erase r),
      let p := matchingChartContactPolynomial U (chartContacts η r z) r j
      p - C (eval z p) ∈ Q)
    (hlt : Q < vanishingIdeal ({z} : Set (MatchingChartVariable n → ℂ)))
    (f : Polynomial ℂ →ₐ[ℂ] (MvPolynomial (MatchingChartVariable n) ℂ ⧸ Q))
    (hfi : Function.Injective f) (hf : f.Finite)
    (i : ContactMatching n) (hi : i ∉ chartContacts η r z)
    (hi' : Ideal.Quotient.mk Q (matchingChartGapPolynomial η r i) ∉
      range (algebraMap ℂ (MvPolynomial (MatchingChartVariable n) ℂ ⧸ Q))) :
    Nonempty (MatchingChartContactCover U η r z) := by
  classical
  let B := MvPolynomial (MatchingChartVariable n) ℂ ⧸ Q
  let u := matchingChartGapPolynomial η r i
  let R := matchingChartRegularPolynomial n
  have hR : Ideal.Quotient.mk Q R ≠ 0 := by
    intro he
    exact hz ((mem_vanishingIdeal_singleton_iff z R).mp
      (hlt.le (Ideal.Quotient.eq_zero_iff_mem.mp he)))
  let T : Set ℂ := {a | ∃ φ : B →ₐ[ℂ] ℂ,
    φ (Ideal.Quotient.mk Q u) = a ∧ φ (Ideal.Quotient.mk Q R) = 0}
  have hT : T.Finite := finite_exceptional_values_of_nonconstant_parameter f hf hfi
    (Ideal.Quotient.mk Q u) hi' (Ideal.Quotient.mk Q R) hR
  obtain ⟨S, hS, hTS, hcover⟩ :=
    exists_isCoveringMap_curve_projection_off_finite Q f hf hfi u hi' hT
  let J := (chartContacts η r z)ᶜ
  let V : Set (MatchingChartVariable n → ℂ) := ⋂ σ : ↥J,
    {w | 0 < (eval w (matchingChartGapPolynomial η r σ.val)).re}
  have hV : IsOpen V := isOpen_iInter_of_finite fun σ =>
    isOpen_lt continuous_const
      (Complex.continuous_re.comp (MvPolynomial.continuous_eval _))
  have hzV : z ∈ V := by
    apply mem_iInter.mpr
    intro σ
    change 0 < (eval z (matchingChartGapPolynomial η r σ.val)).re
    rw [eval_matchingChartGapPolynomial]
    apply lt_of_le_of_ne (hmax σ.val)
    intro he
    exact (Finset.mem_compl.mp σ.property) ((mem_chartContacts η r σ.val z).mpr he.symm)
  have hzQ : z ∈ zeroLocus Q := fun p hp => (mem_vanishingIdeal_singleton_iff z p).mp (hlt.le hp)
  have hu (c : ℂ) : Ideal.Quotient.mk Q (u - C c) ≠ 0 := by
    intro he
    rw [map_sub, sub_eq_zero] at he
    exact hi' ⟨c, he.symm⟩
  obtain ⟨t, ht⟩ := Ideal.Quotient.mk_surjective (I := Q) (f Polynomial.X)
  obtain ⟨w, hwV, hwQ, hwS⟩ :=
    exists_near_curve_point_avoiding_finite_values Q f hf hfi t u ht hu hzQ hV hzV hS
  let carrier := {w : MatchingChartVariable n → ℂ | w ∈ zeroLocus Q ∧ eval w u ∈ Sᶜ}
  have hav (v : carrier) : chartMatchingGap η r v.val i ∈ Sᶜ := by
    simpa only [u, eval_matchingChartGapPolynomial] using v.property.2
  have hc : IsCoveringMap (fun v : carrier =>
      (⟨chartMatchingGap η r v.val i, hav v⟩ : ↥Sᶜ)) := by
    have heq : (fun v : carrier => (⟨eval v.val u, v.property.2⟩ : ↥Sᶜ)) =
        (fun v : carrier => (⟨chartMatchingGap η r v.val i, hav v⟩ : ↥Sᶜ)) := by
      funext v
      exact Subtype.ext (eval_matchingChartGapPolynomial η r i v.val)
    rw [← heq]
    exact hcover
  refine ⟨{
    carrier := carrier
    inactive := i
    notContact := hi
    exceptional := S
    finiteExceptional := hS
    avoids := hav
    covering := hc
    regular := ?_
    sameFiber := ?_
    initial := ⟨w, hwQ, hwS⟩
    positive := ?_
  }⟩
  · intro v hv
    let φ : B →ₐ[ℂ] ℂ := Ideal.Quotient.liftₐ Q (MvPolynomial.aeval v.val)
      (fun p hp => v.property.1 p hp)
    exact v.property.2 (hTS ⟨φ, rfl, hv⟩)
  · intro v j
    have h := v.property.1 _ (hfiber j)
    simpa only [map_sub, eval_C, sub_eq_zero] using h
  · intro σ hσ
    simpa only [eval_matchingChartGapPolynomial] using
      mem_iInter.mp hwV ⟨σ, Finset.mem_compl.mpr hσ⟩

/-- Below the terminal count there is a regular covering suitable for
adding one more contact. -/
theorem exists_matchingChartContactCover
    (hn : 2 ≤ n) (U : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ)
    (η : ℂ) (hη : η ≠ 0) (r : ContactMatching n)
    (z : MatchingChartVariable n → ℂ)
    (hz : eval z (matchingChartRegularPolynomial n) ≠ 0)
    (hmax : ∀ σ, 0 ≤ (chartMatchingGap η r z σ).re)
    (hcard : (chartContacts η r z).card < 2 * (n + 2) - 2) :
    Nonempty (MatchingChartContactCover U η r z) := by
  obtain ⟨Q, hQ, hfiber, hlt, ⟨f, hfi, hf⟩, i, hi, hi'⟩ :=
    exists_matching_contact_curve hn U η hη r z hz hcard
  letI : Q.IsPrime := hQ
  exact matchingChartContactCover_of_curve U η r z hz hmax Q hfiber hlt f hfi hf i hi hi'

/-- In orders at least four, it suffices to establish support for regular
charts having at least twice their order minus two active matchings. -/
theorem mocIsTrue_iff_terminal_chart_support :
    MOCIsTrue ↔ ∀ n : ℕ, 2 ≤ n →
      ∀ (U : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ) (_ : IsUnitary U)
        (η : ℂ) (r : ContactMatching n) (z : MatchingChartVariable n → ℂ),
        eval z (matchingChartRegularPolynomial n) ≠ 0 →
        (∀ σ, 0 ≤ (chartMatchingGap η r z σ).re) →
        2 * (n + 2) - 2 ≤ (chartContacts η r z).card →
        (η * eval z (matchingChartDeficitPolynomial U r)).re ≤ 0 := by
  constructor
  · intro h n _ U hU η r z _ hmax _
    obtain ⟨a, b, hab⟩ := exists_spectra_of_matchingChartCoordinate z
    obtain ⟨σ, hσ⟩ := (holds_iff_directional a b U).mp (h (n + 2) a b U hU) η
    have hg := hmax σ
    simp only [chartMatchingGap, ← hab r, ← hab σ, mul_sub, Complex.sub_re] at hg
    rw [eval_matchingChartDeficitPolynomial z a b U hU r hab, mul_sub, Complex.sub_re]
    exact sub_nonpos.mpr (hσ.trans (sub_nonneg.mp hg))
  · intro hterminal
    apply mocIsTrue_of_regular_contact_covers _ hterminal
    intro n hn U _ η r z hz hmax hpos _ hcard
    have hη : η ≠ 0 := by
      intro he
      simp [he] at hpos
    exact exists_matchingChartContactCover hn U η hη r z hz hmax hcard

end

end MOC
