import MOC.ContactHalfPlaneLift
import MOC.FiniteCurveLocalAccess
import MOC.FiniteCurvePlaneCover
import MOC.HolomorphicContactLimit
import MOC.MatchingContactTransfer
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! On a regular contact curve where the determinant deficit is
nonconstant, the deficit itself can serve as covering projection. -/

open BigOperators Matrix MvPolynomial Set

namespace MOC

variable {n : ℕ}

/-- A curve fixing the old contacts and varying the positive deficit
contains a regular point with a new contact and positive deficit. -/
theorem exists_new_contact_of_nonscalar_deficit
    (U : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ) (hU : IsUnitary U)
    (η : ℂ) (hη : η ≠ 0) (r : ContactMatching n) (z : MatchingChartVariable n → ℂ)
    (hz : eval z (matchingChartRegularPolynomial n) ≠ 0)
    (hmax : ∀ σ, 0 ≤ (chartMatchingGap η r z σ).re)
    (hpos : 0 < (η * eval z (matchingChartDeficitPolynomial U r)).re)
    (Q : Ideal (MvPolynomial (MatchingChartVariable n) ℂ)) [Q.IsPrime]
    (hzQ : z ∈ zeroLocus Q)
    (hold : ∀ v ∈ zeroLocus Q, ∀ σ ∈ chartContacts η r z,
      chartMatchingGap η r v σ = chartMatchingGap η r z σ)
    (f : Polynomial ℂ →ₐ[ℂ] (MvPolynomial (MatchingChartVariable n) ℂ ⧸ Q))
    (hfi : Function.Injective f) (hf : f.Finite)
    (hu : Ideal.Quotient.mk Q (C η * matchingChartDeficitPolynomial U r) ∉
      range (algebraMap ℂ (MvPolynomial (MatchingChartVariable n) ℂ ⧸ Q)))
    (hJne : ((chartContacts η r z)ᶜ).Nonempty) :
    ∃ w : MatchingChartVariable n → ℂ,
      eval w (matchingChartRegularPolynomial n) ≠ 0 ∧
      (0 < (η * eval w (matchingChartDeficitPolynomial U r)).re) ∧
      (∀ σ, 0 ≤ (chartMatchingGap η r w σ).re) ∧
      chartContacts η r z ⊂ chartContacts η r w := by
  classical
  let B := MvPolynomial (MatchingChartVariable n) ℂ ⧸ Q
  let u := C η * matchingChartDeficitPolynomial U r
  let p := matchingChartRegularPolynomial n
  let J := (chartContacts η r z)ᶜ
  have hreg : Ideal.Quotient.mk Q p ≠ 0 := fun he =>
    hz (hzQ p (Ideal.Quotient.eq_zero_iff_mem.mp he))
  let T : Set ℂ := {a | ∃ φ : B →ₐ[ℂ] ℂ,
    φ (Ideal.Quotient.mk Q u) = a ∧ φ (Ideal.Quotient.mk Q p) = 0}
  have hT : T.Finite := finite_exceptional_values_of_nonconstant_parameter f hf hfi
    (Ideal.Quotient.mk Q u) hu (Ideal.Quotient.mk Q p) hreg
  obtain ⟨S, hS, hTS, hcover, hhol⟩ :=
    exists_curve_projection_covering_and_holomorphic_sections Q f hf hfi u hu hT
  let K := CurveProjectionPoints Q u Sᶜ
  have hKreg (v : K) : eval v.val p ≠ 0 := by
    intro hv
    let φ : B →ₐ[ℂ] ℂ := Ideal.Quotient.liftₐ Q (MvPolynomial.aeval v.val)
      (fun g hg => v.property.1 g hg)
    exact v.property.2 (hTS ⟨φ, rfl, hv⟩)
  let V : Set (MatchingChartVariable n → ℂ) :=
    {w | 0 < (eval w u).re} ∩ (⋂ σ : ↥J,
      {w | 0 < (eval w (matchingChartGapPolynomial η r σ.val)).re})
  have hV : IsOpen V :=
    (isOpen_lt continuous_const (Complex.continuous_re.comp (MvPolynomial.continuous_eval u))).inter
      (isOpen_iInter_of_finite fun σ => isOpen_lt continuous_const
        (Complex.continuous_re.comp (MvPolynomial.continuous_eval _)))
  have hzV : z ∈ V := by
    refine ⟨by simpa only [u, map_mul, eval_C] using hpos, mem_iInter.mpr fun σ => ?_⟩
    change 0 < (eval z (matchingChartGapPolynomial η r σ.val)).re
    rw [eval_matchingChartGapPolynomial]
    apply lt_of_le_of_ne (hmax σ.val)
    intro he
    exact (Finset.mem_compl.mp σ.property) ((mem_chartContacts η r σ.val z).mpr he.symm)
  have huu (a : ℂ) : Ideal.Quotient.mk Q (u - C a) ≠ 0 := by
    intro he
    rw [map_sub, sub_eq_zero] at he
    exact hu ⟨a, he.symm⟩
  obtain ⟨t, ht⟩ := Ideal.Quotient.mk_surjective (I := Q) (f Polynomial.X)
  obtain ⟨w, hwV, hwQ, hwS⟩ :=
    exists_near_curve_point_avoiding_finite_values Q f hf hfi t u ht huu hzQ hV hzV hS
  let w₀ : K := ⟨w, hwQ, hwS⟩
  let H (σ : ContactMatching n) (v : K) : ℂ := chartMatchingGap η r v.val σ
  by_contra hnone
  have hno (v : K) (hv : 0 < (eval v.val u).re)
      (hn : ∀ σ ∈ J, 0 ≤ (H σ v).re) (σ : ContactMatching n) (hσ : σ ∈ J) :
      (H σ v).re ≠ 0 := by
    intro hzσ
    have holdzero (τ : ContactMatching n) (hτ : τ ∈ chartContacts η r z) :
        (H τ v).re = 0 := by
      exact (congrArg Complex.re (hold v.val v.property.1 τ hτ)).trans
        ((mem_chartContacts η r τ z).mp hτ)
    apply hnone
    refine ⟨v.val, hKreg v, by simpa only [u, map_mul, eval_C] using hv, fun τ => ?_, ?_⟩
    · by_cases hτ : τ ∈ chartContacts η r z
      · exact (holdzero τ hτ).ge
      · exact hn τ (Finset.mem_compl.mpr hτ)
    · refine Finset.ssubset_iff_subset_ne.mpr
        ⟨fun τ hτ => (mem_chartContacts η r τ v.val).mpr (holdzero τ hτ), ?_⟩
      intro he
      have hnew := (mem_chartContacts η r σ v.val).mpr hzσ
      rw [← he] at hnew
      exact (Finset.mem_compl.mp hσ) hnew
  have hC (σ : ContactMatching n) : Continuous (H σ) := by
    simpa only [H, eval_matchingChartGapPolynomial] using
      (MvPolynomial.continuous_eval (matchingChartGapPolynomial η r σ)).comp continuous_subtype_val
  have hw₀ : ∀ σ ∈ J, 0 < (H σ w₀).re := by
    intro σ hσ
    simpa only [H, w₀, eval_matchingChartGapPolynomial] using mem_iInter.mp hwV.2 ⟨σ, hσ⟩
  obtain ⟨R, hR, hRS, F, hFD, hFpos⟩ := exists_deficit_halfPlane_section_of_no_new_contact
    J hJne H (fun σ _ => hC σ) (fun v : K => eval v.val u) hS (fun v => v.property.2)
    hcover w₀ hwV.1 hw₀ hno
  let W : Set ℂ := {a | R < a.re}
  have hW : IsOpen W := isOpen_lt continuous_const Complex.continuous_re
  let a (w : ℂ) : MatchingChartVariable n → ℂ :=
    if hw : w ∈ W then (F ⟨w, hw⟩).val else 0
  have ha (w : ℂ) (hw : w ∈ W) : a w = (F ⟨w, hw⟩).val := dif_pos hw
  have hac : ContinuousOn a W := by
    apply continuousOn_iff_continuous_restrict.mpr
    change Continuous (a ∘ Subtype.val)
    have he : a ∘ Subtype.val = Subtype.val ∘ F := funext fun v : W => ha v.val v.property
    rw [he]
    exact continuous_subtype_val.comp F.continuous
  have haQ (w : ℂ) (hw : w ∈ W) : a w ∈ zeroLocus Q := by rw [ha w hw]; exact (F ⟨w, hw⟩).property.1
  have haD (w : ℂ) (hw : w ∈ W) : eval (a w) u = w := by rw [ha w hw]; exact hFD ⟨w, hw⟩
  apply no_holomorphic_deficit_halfPlane_section U hU η hη r R hR a
  · intro v hv
    rw [ha v hv]
    exact hKreg (F ⟨v, hv⟩)
  · intro v hv
    simpa only [u, map_mul, eval_C] using haD v hv
  · intro σ
    simpa only [eval_matchingChartGapPolynomial] using
      hhol W hW hRS a hac haQ haD (matchingChartGapPolynomial η r σ)
  · intro σ
    by_cases hs : σ ∈ chartContacts η r z
    · exact Or.inr ⟨_, (mem_chartContacts η r σ z).mp hs, fun v hv => hold _ (haQ v hv) σ hs⟩
    · exact Or.inl (fun v hv => by rw [ha v hv]; exact hFpos ⟨v, hv⟩ σ (Finset.mem_compl.mpr hs))

/-- The complex difference to one active matching other than the reference. -/
noncomputable def chartOldGapPolynomial (η : ℂ) (r : ContactMatching n)
    (z : MatchingChartVariable n → ℂ) (i : ↥((chartContacts η r z).erase r)) :
    MvPolynomial (MatchingChartVariable n) ℂ :=
  matchingChartPolynomial r - matchingChartPolynomial i.val

/-- A prime curve fixing the old complex differences adds a contact while
preserving strict violation in the same support direction. -/
theorem exists_new_contact_on_fixed_old_gap_curve
    (hn : 2 ≤ n) (U : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ) (hU : IsUnitary U)
    (η : ℂ) (r : ContactMatching n) (z : MatchingChartVariable n → ℂ)
    (hz : eval z (matchingChartRegularPolynomial n) ≠ 0)
    (hmax : ∀ σ, 0 ≤ (chartMatchingGap η r z σ).re)
    (hpos : 0 < (η * eval z (matchingChartDeficitPolynomial U r)).re)
    (Q : Ideal (MvPolynomial (MatchingChartVariable n) ℂ)) [Q.IsPrime]
    (hG : ∀ i, chartOldGapPolynomial η r z i - C (eval z (chartOldGapPolynomial η r z i)) ∈ Q)
    (hlt : Q < vanishingIdeal ({z} : Set (MatchingChartVariable n → ℂ)))
    (f : Polynomial ℂ →ₐ[ℂ] (MvPolynomial (MatchingChartVariable n) ℂ ⧸ Q))
    (hfi : Function.Injective f) (hf : f.Finite) :
    ∃ w : MatchingChartVariable n → ℂ,
      eval w (matchingChartRegularPolynomial n) ≠ 0 ∧
      (0 < (η * eval w (matchingChartDeficitPolynomial U r)).re) ∧
      (∀ σ, 0 ≤ (chartMatchingGap η r w σ).re) ∧
      chartContacts η r z ⊂ chartContacts η r w := by
  classical
  have hη : η ≠ 0 := fun h => by simpa [h] using hpos
  let S := chartContacts η r z
  have hzQ : z ∈ zeroLocus Q := fun p hp =>
    (mem_vanishingIdeal_singleton_iff z p).mp (hlt.le hp)
  let p := matchingChartDeficitPolynomial U r
  let B := MvPolynomial (MatchingChartVariable n) ℂ ⧸ Q
  by_cases hp : Ideal.Quotient.mk Q p ∈ range (algebraMap ℂ B)
  · obtain ⟨c, hc⟩ := hp
    have hpc : p - C c ∈ Q := by
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      rw [map_sub]
      change Ideal.Quotient.mk Q p - algebraMap ℂ B c = 0
      rw [hc, sub_self]
    have hval : eval z p = c := by
      have h := hzQ (p - C c) hpc
      simpa only [map_sub, eval_C, sub_eq_zero] using h
    have hfiber (i : Option ↥(S.erase r)) :
        let q := matchingChartContactPolynomial U S r i
        q - C (eval z q) ∈ Q := by
      cases i with
      | none => change p - C (eval z p) ∈ Q; rw [hval]; exact hpc
      | some i => exact hG i
    obtain ⟨i, hi, hi'⟩ := exists_nonscalar_inactive_gap_on_curve hn U η hη r z hz Q hlt hfiber
    obtain ⟨cv⟩ := matchingChartContactCover_of_curve U η r z hz hmax Q hfiber hlt f hfi hf i hi hi'
    obtain ⟨w, hw, hdef, hnneg, hmore⟩ := exists_chart_with_more_contacts cv
    exact ⟨w, hw, by rw [hdef]; exact hpos, hnneg, hmore⟩
  · have hp' : Ideal.Quotient.mk Q (C η * p) ∉ range (algebraMap ℂ B) := by
      rintro ⟨c, hc⟩
      have hprod : algebraMap ℂ B η * Ideal.Quotient.mk Q p = algebraMap ℂ B c := by
        simpa only [map_mul] using hc.symm
      apply hp
      refine ⟨η⁻¹ * c, ?_⟩
      rw [map_mul, ← hprod, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hη, map_one, one_mul]
    have hfixed (w : MatchingChartVariable n → ℂ) (hw : w ∈ zeroLocus Q)
        (σ : ContactMatching n) (hσ : σ ∈ S) :
        chartMatchingGap η r w σ = chartMatchingGap η r z σ := by
      by_cases h : σ = r
      · subst σ; simp [chartMatchingGap]
      have hc := hw _ (hG ⟨σ, Finset.mem_erase.mpr ⟨h, hσ⟩⟩)
      change eval w ((matchingChartPolynomial r - matchingChartPolynomial σ) -
        C (eval z (matchingChartPolynomial r - matchingChartPolynomial σ))) = 0 at hc
      simp only [map_sub, eval_C, eval_matchingChartPolynomial, sub_eq_zero] at hc
      simp only [chartMatchingGap, hc]
    have hJ : (Sᶜ).Nonempty := by
      by_contra hnJ
      have hall (σ : ContactMatching n) : σ ∈ S := by
        by_contra h
        exact hnJ ⟨σ, Finset.mem_compl.mpr h⟩
      obtain ⟨a, b, hab⟩ := exists_spectra_of_matchingChartCoordinate z
      have hzero (σ : ContactMatching n) : matchingGap a b η r σ = 0 := by
        simpa only [matchingGap, chartMatchingGap, ← hab, mul_sub, Complex.sub_re] using
          (mem_chartContacts η r σ z).mp (hall σ)
      have hd := support_gap_eq a b U hU η r
      simp only [hzero, mul_zero, Finset.sum_const_zero, sub_eq_zero] at hd
      rw [eval_matchingChartDeficitPolynomial z a b U hU r hab, mul_sub, Complex.sub_re, hd,
        sub_self] at hpos
      exact (lt_irrefl _ hpos)
    exact exists_new_contact_of_nonscalar_deficit U hU η hη r z hz hmax hpos
      Q hzQ hfixed f hfi hf hp' hJ

/-- Freezing only the old complex matching differences leaves a curve
through a regular violation with at most twice the order minus two contacts. -/
theorem exists_new_contact_at_twice_order_minus_two
    (hn : 2 ≤ n) (U : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ) (hU : IsUnitary U)
    (η : ℂ) (r : ContactMatching n) (z : MatchingChartVariable n → ℂ)
    (hz : eval z (matchingChartRegularPolynomial n) ≠ 0)
    (hmax : ∀ σ, 0 ≤ (chartMatchingGap η r z σ).re)
    (hpos : 0 < (η * eval z (matchingChartDeficitPolynomial U r)).re)
    (hc : (chartContacts η r z).card ≤ 2 * (n + 2) - 2) :
    ∃ w : MatchingChartVariable n → ℂ,
      eval w (matchingChartRegularPolynomial n) ≠ 0 ∧
      (0 < (η * eval w (matchingChartDeficitPolynomial U r)).re) ∧
      (∀ σ, 0 ≤ (chartMatchingGap η r w σ).re) ∧
      chartContacts η r z ⊂ chartContacts η r w := by
  classical
  let S := chartContacts η r z
  have hr : r ∈ S := by simp [S, chartMatchingGap]
  have hdim : Fintype.card ↥(S.erase r) < Fintype.card (MatchingChartVariable n) := by
    rw [Fintype.card_coe, Finset.card_erase_of_mem hr, card_matchingChartVariable]
    have hp : 0 < S.card := Finset.card_pos.mpr ⟨r, hr⟩
    exact lt_of_lt_of_le (Nat.sub_lt hp Nat.zero_lt_one) hc
  obtain ⟨Q, hQ, hG, hlt, f, hfi, hf⟩ :=
    exists_finite_curve_of_polynomial_fiber (chartOldGapPolynomial η r z) z hdim
  letI : Q.IsPrime := hQ
  exact exists_new_contact_on_fixed_old_gap_curve hn U hU η r z hz hmax hpos Q hG hlt f hfi hf

/-- Complex span dimension of the old matching differences, with the
reference matching omitted. -/
noncomputable def chartOldGapRank (η : ℂ) (r : ContactMatching n)
    (z : MatchingChartVariable n → ℂ) : ℕ :=
  (Set.range (chartOldGapPolynomial η r z)).finrank ℂ

/-- A regular strict violation can acquire another contact whenever its
active differences span fewer dimensions than the chart has variables. -/
theorem exists_new_contact_of_low_old_gap_rank
    (hn : 2 ≤ n) (U : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ) (hU : IsUnitary U)
    (η : ℂ) (r : ContactMatching n) (z : MatchingChartVariable n → ℂ)
    (hz : eval z (matchingChartRegularPolynomial n) ≠ 0)
    (hmax : ∀ σ, 0 ≤ (chartMatchingGap η r z σ).re)
    (hpos : 0 < (η * eval z (matchingChartDeficitPolynomial U r)).re)
    (hrank : chartOldGapRank η r z < 2 * (n + 2) - 2) :
    ∃ w : MatchingChartVariable n → ℂ,
      eval w (matchingChartRegularPolynomial n) ≠ 0 ∧
      (0 < (η * eval w (matchingChartDeficitPolynomial U r)).re) ∧
      (∀ σ, 0 ≤ (chartMatchingGap η r w σ).re) ∧
      chartContacts η r z ⊂ chartContacts η r w := by
  classical
  let V := Submodule.span ℂ (Set.range (chartOldGapPolynomial η r z))
  letI : FiniteDimensional ℂ V :=
    FiniteDimensional.span_of_finite ℂ (Set.finite_range (chartOldGapPolynomial η r z))
  let b := Module.finBasis ℂ V
  let p := V.subtype ∘ b
  have hdim : Fintype.card (Fin (Module.finrank ℂ V)) < Fintype.card (MatchingChartVariable n) := by
    rw [Fintype.card_fin, card_matchingChartVariable]
    exact hrank
  have hspan : Submodule.span ℂ (Set.range p) = V := by
    change Submodule.span ℂ (Set.range (V.subtype ∘ b)) = V
    rw [Set.range_comp, ← Submodule.map_span, b.span_eq, Submodule.map_subtype_top]
  obtain ⟨Q, hQ, hp, hlt, f, hfi, hf⟩ := exists_finite_curve_of_polynomial_fiber p z hdim
  letI : Q.IsPrime := hQ
  have hfixed (q : MvPolynomial (MatchingChartVariable n) ℂ)
      (hq : q ∈ Submodule.span ℂ (Set.range p)) : q - C (eval z q) ∈ Q := by
    induction hq using Submodule.span_induction with
    | mem q hmem =>
        obtain ⟨i, rfl⟩ := hmem
        exact hp i
    | zero => simp
    | add a b _ _ ha hb =>
        rw [map_add, map_add, add_sub_add_comm]
        exact Q.add_mem ha hb
    | smul c a _ ha =>
        change C c * a - C (eval z (C c * a)) ∈ Q
        rw [map_mul, eval_C, map_mul, ← mul_sub]
        exact Ideal.mul_mem_left Q _ ha
  refine exists_new_contact_on_fixed_old_gap_curve hn U hU η r z hz hmax hpos Q ?_ hlt f hfi hf
  intro i
  apply hfixed
  rw [hspan]
  exact Submodule.subset_span (Set.mem_range_self i)

/-- The unrestricted conjecture is equivalent to terminal support in regular
charts with at least twice the order minus one active matchings. -/
theorem mocIsTrue_iff_terminal_chart_support_twice_minus_one :
    MOCIsTrue ↔ ∀ n : ℕ, 2 ≤ n →
      ∀ (U : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ) (_ : IsUnitary U)
        (η : ℂ) (r : ContactMatching n) (z : MatchingChartVariable n → ℂ),
        eval z (matchingChartRegularPolynomial n) ≠ 0 →
        (∀ σ, 0 ≤ (chartMatchingGap η r z σ).re) →
        2 * (n + 2) - 1 ≤ (chartContacts η r z).card →
        (η * eval z (matchingChartDeficitPolynomial U r)).re ≤ 0 := by
  constructor
  · intro h n hn U hU η r z hz hmax hc
    exact (mocIsTrue_iff_terminal_chart_support.mp h) n hn U hU η r z hz hmax (by omega)
  · intro ht
    apply mocIsTrue_iff_terminal_chart_support.mpr
    intro n hn U hU η r z hz hmax hc
    by_cases hs : 2 * (n + 2) - 1 ≤ (chartContacts η r z).card
    · exact ht n hn U hU η r z hz hmax hs
    by_contra! hpos
    obtain ⟨w, hw, hwpos, hwmax, hmore⟩ :=
      exists_new_contact_at_twice_order_minus_two hn U hU η r z hz hmax hpos (by omega)
    have hmore' := Finset.card_lt_card hmore
    exact (not_le_of_gt hwpos) (ht n hn U hU η r w hw hwmax (by omega))

/-- The terminal support check can be restricted to charts where the old
matching differences span at least as many dimensions as the chart has variables. -/
theorem mocIsTrue_iff_terminal_chart_support_old_gap_rank :
    MOCIsTrue ↔ ∀ n : ℕ, 2 ≤ n →
      ∀ (U : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ) (_ : IsUnitary U)
        (η : ℂ) (r : ContactMatching n) (z : MatchingChartVariable n → ℂ),
        eval z (matchingChartRegularPolynomial n) ≠ 0 →
        (∀ σ, 0 ≤ (chartMatchingGap η r z σ).re) →
        2 * (n + 2) - 2 ≤ chartOldGapRank η r z →
        (η * eval z (matchingChartDeficitPolynomial U r)).re ≤ 0 := by
  classical
  constructor
  · intro h n hn U hU η r z hz hmax hrank
    have hr : r ∈ chartContacts η r z := by simp [chartMatchingGap]
    have hcard : chartOldGapRank η r z ≤ (chartContacts η r z).card - 1 := by
      rw [← Finset.card_erase_of_mem hr, ← Fintype.card_coe]
      exact finrank_range_le_card (R := ℂ) (chartOldGapPolynomial η r z)
    exact (mocIsTrue_iff_terminal_chart_support_twice_minus_one.mp h)
      n hn U hU η r z hz hmax (by omega)
  · intro hterminal
    apply mocIsTrue_iff_terminal_chart_support_twice_minus_one.mpr
    intro n hn U hU η r z hz hmax _
    by_contra! hpos
    let admissible (w : MatchingChartVariable n → ℂ) : Prop :=
      eval w (matchingChartRegularPolynomial n) ≠ 0 ∧
      0 < (η * eval w (matchingChartDeficitPolynomial U r)).re ∧
      ∀ σ, 0 ≤ (chartMatchingGap η r w σ).re
    let sizes := (Finset.range (Fintype.card (ContactMatching n) + 1)).filter fun k =>
      ∃ w, admissible w ∧ (chartContacts η r w).card = k
    have hsize (w : MatchingChartVariable n → ℂ) (hw : admissible w) :
        (chartContacts η r w).card ∈ sizes :=
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr
        (Nat.lt_succ_of_le (Finset.card_le_univ _)), w, hw, rfl⟩
    obtain ⟨k, hk, hkmax⟩ := Finset.exists_max_image sizes id
      ⟨_, hsize z ⟨hz, hpos, hmax⟩⟩
    obtain ⟨w, hw, hkw⟩ := (Finset.mem_filter.mp hk).2
    have hrank : 2 * (n + 2) - 2 ≤ chartOldGapRank η r w := by
      by_contra! hsmall
      obtain ⟨v, hv, hvpos, hvmax, hmore⟩ :=
        exists_new_contact_of_low_old_gap_rank hn U hU η r w hw.1 hw.2.2 hw.2.1 hsmall
      have hbound := hkmax _ (hsize v ⟨hv, hvpos, hvmax⟩)
      change (chartContacts η r v).card ≤ k at hbound
      exact (not_le_of_gt (Finset.card_lt_card hmore)) (hbound.trans_eq hkw.symm)
    exact (not_lt_of_ge (hterminal n hn U hU η r w hw.1 hw.2.2 hrank)) hw.2.1

end MOC
