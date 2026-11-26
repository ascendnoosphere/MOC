import MOC.DeterminantPolynomialInfeasibility
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Algebra.Ring.Semireal.Defs
import Mathlib.Data.Fintype.Powerset
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! Exact certificate implications for polynomial determinant separation. -/

open BigOperators

namespace MOC

noncomputable section

private theorem map_sumSq {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    {a : R} (ha : IsSumSq a) : IsSumSq (f a) := by
  induction ha with
  | zero =>
      rw [map_zero]
      exact IsSumSq.zero
  | sq_add b _ ih =>
      rw [map_add, map_mul]
      exact IsSumSq.sq_add (f b) ih

private theorem eval_nonneg_of_sumSq_mod_equations {V K : Type*} [Fintype K]
    (f : K → MvPolynomial V ℝ) (x : V → ℝ) (hx : ∀ k, MvPolynomial.eval x (f k) = 0)
    {p s : MvPolynomial V ℝ} (hs : IsSumSq s) (h : K → MvPolynomial V ℝ)
    (he : p = s + ∑ k, h k * f k) : 0 ≤ MvPolynomial.eval x p := by
  have hEval := congrArg (MvPolynomial.eval x) he
  simp only [map_add, map_sum, map_mul, hx, mul_zero, Finset.sum_const_zero, add_zero] at hEval
  rw [hEval]
  exact (map_sumSq (MvPolynomial.eval x) hs).nonneg

private theorem lift_quotient_sumSq {R : Type*} [CommRing R] (I : Ideal R)
    {a : R ⧸ I} (ha : IsSumSq a) : ∃ b : R, IsSumSq b ∧ Ideal.Quotient.mk I b = a := by
  induction ha with
  | zero => exact ⟨0, IsSumSq.zero, map_zero _⟩
  | sq_add c _ ih =>
      obtain ⟨b, hb, hmap⟩ := ih
      obtain ⟨d, hd⟩ := Ideal.Quotient.mk_surjective (I := I) c
      exact ⟨d * d + b, IsSumSq.sq_add d hb, by rw [map_add, map_mul, hd, hmap]⟩

private theorem not_isSemireal_iff_neg_one_sumSq (R : Type*) [CommRing R] :
    ¬ IsSemireal R ↔ IsSumSq (-1 : R) := by
  classical
  constructor
  · intro h
    by_contra hs
    apply h
    constructor
    intro a ha hz
    apply hs
    have he : a = -1 := by
      calc
        a = -1 + (1 + a) := by rw [← add_assoc, neg_add_cancel, zero_add]
        _ = -1 := by rw [hz, add_zero]
    exact he ▸ ha
  · intro hs h
    letI := h
    exact IsSemireal.not_isSumSq_neg_one hs

/-- A sum-of-squares identity modulo finitely many equations is equivalent
to a sum-of-squares representation of minus one in the coordinate ring. -/
theorem polynomial_certificate_iff_quotient_sumSq {R K : Type*} [CommRing R] [Fintype K]
    (f : K → R) :
    (∃ s : R, IsSumSq s ∧ ∃ h : K → R, (-1 : R) = s + ∑ k, h k * f k) ↔
      IsSumSq (-1 : R ⧸ Ideal.span (Set.range f)) := by
  let I := Ideal.span (Set.range f)
  let q := Ideal.Quotient.mk I
  change _ ↔ IsSumSq (-1 : R ⧸ I)
  have hzero (k : K) : q (f k) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_range_self k))
  constructor
  · rintro ⟨s, hs, h, he⟩
    have hq := congrArg q he
    simp only [map_neg, map_one, map_add, map_sum, map_mul, hzero, mul_zero,
      Finset.sum_const_zero, add_zero] at hq
    exact hq.symm ▸ map_sumSq q hs
  · intro hs
    obtain ⟨s, hsq, hmap⟩ := lift_quotient_sumSq I hs
    have hzero' : q (-1 - s) = 0 := by
      change Ideal.Quotient.mk I (-1 - s) = 0
      rw [map_sub, map_neg, map_one, hmap, sub_self]
    obtain ⟨h, he⟩ := Ideal.mem_span_range_iff_exists_fun.mp
      (Ideal.Quotient.eq_zero_iff_mem.mp hzero')
    refine ⟨s, hsq, h, ?_⟩
    calc
      (-1 : R) = (-1 - s) + s := (sub_add_cancel _ _).symm
      _ = s + ∑ k, h k * f k := by rw [he, add_comm]

/-- The absence of a finite sum-of-squares equation certificate is
equivalent to semireality of the coordinate ring. -/
theorem semireal_quotient_iff_no_polynomial_certificate {R K : Type*}
    [CommRing R] [Fintype K] (f : K → R) :
    IsSemireal (R ⧸ Ideal.span (Set.range f)) ↔
      ¬ ∃ s : R, IsSumSq s ∧ ∃ h : K → R, (-1 : R) = s + ∑ k, h k * f k := by
  classical
  rw [polynomial_certificate_iff_quotient_sumSq]
  exact not_not.symm.trans (not_congr (not_isSemireal_iff_neg_one_sumSq _))

/-- Real solutions of a polynomial system are the real-valued algebra
homomorphisms of its coordinate ring. -/
theorem real_zeros_iff_real_algebra_point {V K : Type*} (f : K → MvPolynomial V ℝ) :
    (∃ x : V → ℝ, ∀ k, MvPolynomial.eval x (f k) = 0) ↔
      Nonempty ((MvPolynomial V ℝ ⧸ Ideal.span (Set.range f)) →ₐ[ℝ] ℝ) := by
  let I := Ideal.span (Set.range f)
  constructor
  · rintro ⟨x, hx⟩
    have hker : I ≤ RingHom.ker (MvPolynomial.eval x) := by
      apply Ideal.span_le.mpr
      rintro _ ⟨k, rfl⟩
      exact RingHom.mem_ker.mpr (hx k)
    refine ⟨Ideal.Quotient.liftₐ I (MvPolynomial.aeval x) (fun p hp => ?_)⟩
    change MvPolynomial.eval x p = 0
    exact RingHom.mem_ker.mp (hker hp)
  · rintro ⟨φ⟩
    let ψ : MvPolynomial V ℝ →ₐ[ℝ] ℝ := φ.comp (Ideal.Quotient.mkₐ ℝ I)
    let x : V → ℝ := ψ ∘ MvPolynomial.X
    have he : MvPolynomial.aeval x = ψ := (MvPolynomial.aeval_unique ψ).symm
    refine ⟨x, fun k => ?_⟩
    change MvPolynomial.aeval x (f k) = 0
    rw [he]
    change φ (Ideal.Quotient.mk I (f k)) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_range_self k)), map_zero]

/-- An exact finite equation certificate follows from a sum-of-squares
representation of minus one in the equation quotient. -/
theorem no_real_zeros_of_quotient_sumSq {V K : Type*} [Fintype K]
    (f : K → MvPolynomial V ℝ)
    (h : IsSumSq (-1 : MvPolynomial V ℝ ⧸ Ideal.span (Set.range f))) :
    ¬ ∃ x : V → ℝ, ∀ k, MvPolynomial.eval x (f k) = 0 := by
  rintro ⟨x, hx⟩
  obtain ⟨s, hs, a, he⟩ := (polynomial_certificate_iff_quotient_sumSq f).mpr h
  have hn := eval_nonneg_of_sumSq_mod_equations f x hx hs a he
  rw [map_neg, map_one] at hn
  exact (not_le_of_gt (neg_neg_of_pos zero_lt_one)) hn

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

local notation "P" => MvPolynomial (DeterminantWitnessVariable ι) ℝ

/-- Additive nonnegative margin polynomials for the closed separation test. -/
def determinantUnitMargin (σ : Equiv.Perm ι) : P := determinantGapPolynomial σ - 1

private theorem exists_unit_margin_scale {K : Type*} [Fintype K] [Nonempty K]
    (g : K → ℝ) (hg : ∀ k, 0 < g k) {n : ℕ} (hn : n ≠ 0) :
    ∃ r : ℝ, 0 < r ∧ ∀ k, 1 ≤ r ^ n * g k := by
  obtain ⟨k₀, _, hmin⟩ := Finset.exists_min_image Finset.univ g Finset.univ_nonempty
  let r := max 1 (g k₀)⁻¹
  have hr : 1 ≤ r := le_max_left _ _
  refine ⟨r, zero_lt_one.trans_le hr, fun k => ?_⟩
  calc
    1 = (g k₀)⁻¹ * g k₀ := (inv_mul_cancel₀ (hg k₀).ne').symm
    _ ≤ r * g k₀ := mul_le_mul_of_nonneg_right (le_max_right _ _) (hg k₀).le
    _ ≤ r ^ n * g k₀ := mul_le_mul_of_nonneg_right (le_self_pow₀ hr hn) (hg k₀).le
    _ ≤ r ^ n * g k := mul_le_mul_of_nonneg_left (hmin k (Finset.mem_univ k))
      (pow_nonneg (zero_le_one.trans hr) n)

/-- A strict separator in positive order can be scaled until every
determinant gap is at least one. -/
theorem conjecture_iff_no_unit_margin_witness [Nonempty ι] :
    Conjecture ι ↔ ¬ ∃ x : DeterminantWitnessVariable ι → ℝ,
      (∀ i j c, MvPolynomial.eval x (determinantGramPolynomial i j c) = 0) ∧
      (∀ σ, 0 ≤ MvPolynomial.eval x (determinantUnitMargin σ)) := by
  rw [conjecture_iff_no_polynomial_witness]
  constructor
  · rintro h ⟨x, hU, hgap⟩
    refine h ⟨x, hU, fun σ => zero_lt_one.trans_le (sub_nonneg.mp ?_)⟩
    simpa only [determinantUnitMargin, map_sub, map_one] using hgap σ
  · rintro h ⟨x, hGram, hgap⟩
    obtain ⟨r, _, hnorm⟩ := exists_unit_margin_scale
      (fun σ => MvPolynomial.eval x (determinantGapPolynomial σ)) hgap
      (Fintype.card_ne_zero (α := ι))
    let a := witnessFirstSpectrum x
    let b := witnessSecondSpectrum x
    let U := witnessMixer x
    let y := witnessValuation (fun i => (r : ℂ) * a i) (fun i => (r : ℂ) * b i) U (fun _ => 0)
    obtain ⟨ha, hb, hU⟩ := witnessValuation_values
      (fun i => (r : ℂ) * a i) (fun i => (r : ℂ) * b i) U (fun _ => 0)
    have hUnitary : IsUnitary (witnessMixer y) := by
      rw [hU]
      exact (gramPolynomials_zero_iff x).mp hGram
    refine h ⟨y, (gramPolynomials_zero_iff y).mpr hUnitary, fun σ => ?_⟩
    have he : MvPolynomial.eval y (determinantGapPolynomial σ) =
        r ^ Fintype.card ι * MvPolynomial.eval x (determinantGapPolynomial σ) := by
      rw [eval_determinantGapPolynomial, eval_determinantGapPolynomial, ha, hb, hU,
        determinantValue_scale, matchingProduct_scale, ← mul_sub,
        ← Complex.ofReal_pow, Complex.re_ofReal_mul]
    rw [determinantUnitMargin, map_sub, map_one, he]
    exact sub_nonneg.mpr (hnorm σ)

/-- The nonnegative margins can also be represented by real slack squares. -/
def determinantUnitMarginEquation : DeterminantWitnessEquation ι → P
  | .inl (i, j, c) => determinantGramPolynomial i j c
  | .inr σ => determinantUnitMargin σ - MvPolynomial.X (.inr σ) ^ 2

/-- The closed separation system is equivalent to the slack-square
equation system. -/
theorem conjecture_iff_no_unit_margin_equation_witness [Nonempty ι] :
    Conjecture ι ↔ ¬ ∃ x : DeterminantWitnessVariable ι → ℝ,
      ∀ k, MvPolynomial.eval x (determinantUnitMarginEquation k) = 0 := by
  rw [conjecture_iff_no_unit_margin_witness]
  constructor
  · rintro h ⟨x, hx⟩
    refine h ⟨x, fun i j c => hx (.inl (i, j, c)), fun σ => ?_⟩
    have he : MvPolynomial.eval x (determinantUnitMargin σ) = x (.inr σ) ^ 2 := by
      apply sub_eq_zero.mp
      simpa only [determinantUnitMarginEquation, map_sub, map_pow, MvPolynomial.eval_X]
        using hx (.inr σ)
    rw [he]
    exact sq_nonneg _
  · rintro h ⟨x, hGram, hgap⟩
    let a := witnessFirstSpectrum x
    let b := witnessSecondSpectrum x
    let U := witnessMixer x
    let t (σ : Equiv.Perm ι) := Real.sqrt (MvPolynomial.eval x (determinantUnitMargin σ))
    let y := witnessValuation a b U t
    obtain ⟨ha, hb, hU⟩ := witnessValuation_values a b U t
    have hUnitary : IsUnitary (witnessMixer y) := by
      rw [hU]
      exact (gramPolynomials_zero_iff x).mp hGram
    refine h ⟨y, ?_⟩
    rintro (⟨i, j, c⟩ | σ)
    · exact (gramPolynomials_zero_iff y).mpr hUnitary i j c
    · simp only [determinantUnitMarginEquation, map_sub, map_pow, MvPolynomial.eval_X]
      have he : MvPolynomial.eval y (determinantUnitMargin σ) =
          MvPolynomial.eval x (determinantUnitMargin σ) := by
        simp only [determinantUnitMargin, map_sub, map_one, eval_determinantGapPolynomial,
          ha, hb, hU]
      change MvPolynomial.eval y (determinantUnitMargin σ) - t σ ^ 2 = 0
      rw [he, t, Real.sq_sqrt (hgap σ), sub_self]

/-- The extra variables are a common strict margin and its reciprocal square-root witness. -/
abbrev DeterminantCommonMarginVariable (ι : Type*) := DeterminantWitnessVariable ι ⊕ Bool

/-- The common-margin system has one extra equation to force the margin to be positive. -/
abbrev DeterminantCommonMarginEquation (ι : Type*) := DeterminantWitnessEquation ι ⊕ Unit

/-- Express strict separation by a positive common margin and nonnegative
square slacks for the excess over that margin. -/
def determinantCommonMarginPolynomial : DeterminantCommonMarginEquation ι →
    MvPolynomial (DeterminantCommonMarginVariable ι) ℝ
  | .inl (.inl (i, j, c)) => MvPolynomial.rename Sum.inl (determinantGramPolynomial i j c)
  | .inl (.inr σ) => MvPolynomial.rename Sum.inl (determinantGapPolynomial σ) -
      MvPolynomial.X (.inr false) - MvPolynomial.X (.inl (.inr σ)) ^ 2
  | .inr _ => MvPolynomial.X (.inr false) * MvPolynomial.X (.inr true) ^ 2 - 1

/-- The common-margin polynomial equations characterize strict counterexamples. -/
theorem conjecture_iff_no_common_margin_witness [Nonempty ι] :
    Conjecture ι ↔ ¬ ∃ x : DeterminantCommonMarginVariable ι → ℝ,
      ∀ k, MvPolynomial.eval x (determinantCommonMarginPolynomial k) = 0 := by
  rw [conjecture_iff_no_polynomial_witness]
  constructor
  · rintro h ⟨x, hx⟩
    let z : DeterminantWitnessVariable ι → ℝ := x ∘ Sum.inl
    have hδmul : x (.inr false) * x (.inr true) ^ 2 = 1 := by
      apply sub_eq_zero.mp
      simpa only [determinantCommonMarginPolynomial, map_sub, map_mul, map_pow,
        MvPolynomial.eval_X, map_one] using hx (.inr ())
    have hδprod : 0 < x (.inr false) * x (.inr true) ^ 2 := by
      rw [hδmul]
      exact zero_lt_one
    have hδ : 0 < x (.inr false) := pos_of_mul_pos_left hδprod (sq_nonneg _)
    refine h ⟨z, fun i j c => ?_, fun σ => ?_⟩
    · simpa only [determinantCommonMarginPolynomial, MvPolynomial.eval_rename]
        using hx (.inl (.inl (i, j, c)))
    · have he : MvPolynomial.eval z (determinantGapPolynomial σ) - x (.inr false) =
          x (.inl (.inr σ)) ^ 2 := by
        apply sub_eq_zero.mp
        simpa only [determinantCommonMarginPolynomial, MvPolynomial.eval_rename,
          map_sub, map_pow, MvPolynomial.eval_X] using hx (.inl (.inr σ))
      have hn : 0 ≤ MvPolynomial.eval z (determinantGapPolynomial σ) - x (.inr false) := by
        rw [he]
        exact sq_nonneg _
      exact hδ.trans_le (sub_nonneg.mp hn)
  · rintro h ⟨x, hGram, hgap⟩
    let g (σ : Equiv.Perm ι) := MvPolynomial.eval x (determinantGapPolynomial σ)
    obtain ⟨σ₀, _, hmin⟩ := Finset.exists_min_image Finset.univ g Finset.univ_nonempty
    let δ := g σ₀
    have hδ : 0 < δ := hgap σ₀
    have hδle (σ : Equiv.Perm ι) : δ ≤ g σ := hmin σ (Finset.mem_univ σ)
    let a := witnessFirstSpectrum x
    let b := witnessSecondSpectrum x
    let U := witnessMixer x
    let t (σ : Equiv.Perm ι) := Real.sqrt (g σ - δ)
    let z := witnessValuation a b U t
    let y : DeterminantCommonMarginVariable ι → ℝ :=
      Sum.elim z fun c => if c then (Real.sqrt δ)⁻¹ else δ
    obtain ⟨ha, hb, hU⟩ := witnessValuation_values a b U t
    have hUnitary : IsUnitary (witnessMixer z) := by
      rw [hU]
      exact (gramPolynomials_zero_iff x).mp hGram
    refine h ⟨y, ?_⟩
    rintro ((⟨i, j, c⟩ | σ) | ⟨⟩)
    · rw [determinantCommonMarginPolynomial, MvPolynomial.eval_rename]
      exact (gramPolynomials_zero_iff z).mpr hUnitary i j c
    · simp only [determinantCommonMarginPolynomial, map_sub, map_pow, MvPolynomial.eval_X,
        MvPolynomial.eval_rename]
      change MvPolynomial.eval z (determinantGapPolynomial σ) - δ - t σ ^ 2 = 0
      have he : MvPolynomial.eval z (determinantGapPolynomial σ) = g σ := by
        rw [g, eval_determinantGapPolynomial, eval_determinantGapPolynomial, ha, hb, hU]
      rw [he, t, Real.sq_sqrt (sub_nonneg.mpr (hδle σ)), sub_self]
    · simp only [determinantCommonMarginPolynomial, map_sub, map_mul, map_pow,
        MvPolynomial.eval_X, map_one]
      change δ * (Real.sqrt δ)⁻¹ ^ 2 - 1 = 0
      rw [inv_pow, Real.sq_sqrt hδ.le, mul_inv_cancel₀ hδ.ne', sub_self]

/-- The finite preordering identity uses one product of margins for each
subset of matching permutations. Each product has a sum-of-squares multiplier. -/
def HasDeterminantPreorderingCertificate : Prop :=
  ∃ s : Finset (Equiv.Perm ι) → P, (∀ J, IsSumSq (s J)) ∧
    ∃ h : ι × ι × Bool → P,
      (-1 : P) = (∑ J, s J * ∏ σ ∈ J, determinantUnitMargin σ) +
        ∑ k, h k * determinantGramPolynomial k.1 k.2.1 k.2.2

/-- Evaluating a preordering identity rules out the closed separation system. -/
theorem no_unit_margin_witness_of_preordering_certificate
    (h : HasDeterminantPreorderingCertificate (ι := ι)) :
    ¬ ∃ x : DeterminantWitnessVariable ι → ℝ,
      (∀ i j c, MvPolynomial.eval x (determinantGramPolynomial i j c) = 0) ∧
      (∀ σ, 0 ≤ MvPolynomial.eval x (determinantUnitMargin σ)) := by
  rintro ⟨s, hs, a, he⟩ ⟨x, hGram, hmargin⟩
  have hEval := congrArg (MvPolynomial.eval x) he
  simp only [map_neg, map_one, map_add, map_sum, map_mul, map_prod, hGram,
    mul_zero, Finset.sum_const_zero, add_zero] at hEval
  have hnonneg : 0 ≤ ∑ J : Finset (Equiv.Perm ι), MvPolynomial.eval x (s J) *
      ∏ σ ∈ J, MvPolynomial.eval x (determinantUnitMargin σ) := by
    apply Finset.sum_nonneg
    intro J _
    exact mul_nonneg (map_sumSq (MvPolynomial.eval x) (hs J)).nonneg
      (Finset.prod_nonneg fun σ _ => hmargin σ)
  linarith only [hEval, hnonneg]

/-- A preordering certificate gives the determinant inclusion in positive order. -/
theorem conjecture_of_preordering_certificate [Nonempty ι]
    (h : HasDeterminantPreorderingCertificate (ι := ι)) : Conjecture ι :=
  conjecture_iff_no_unit_margin_witness.mpr (no_unit_margin_witness_of_preordering_certificate h)

/-- At fixed spectra, an exact sum of squares modulo unitarity suffices
for the polynomial that represents the support cost. This includes the
case where the representative and the identity have degree at most four. -/
theorem conjecture_of_fixed_spectral_cost_certificates [Nonempty ι]
    (h : ∀ a b : ι → ℂ, ∃ σ : Equiv.Perm ι,
      ∃ p s : P, IsSumSq s ∧
        (∀ U : Matrix ι ι ℂ, IsUnitary U →
          MvPolynomial.eval (witnessValuation a b U (fun _ => 0)) p =
            (matchingProduct a b σ).re - (determinantValue a b U).re) ∧
        ∃ q : ι × ι × Bool → P,
          p = s + ∑ k, q k * determinantGramPolynomial k.1 k.2.1 k.2.2) :
    Conjecture ι := by
  rw [conjecture_iff_real_bound]
  intro a b U hU
  obtain ⟨σ, p, s, hs, hvalue, q, hcert⟩ := h a b
  let x := witnessValuation a b U (fun _ => 0)
  obtain ⟨_, _, hxU⟩ := witnessValuation_values a b U (fun _ => 0)
  have hUnitary : IsUnitary (witnessMixer x) := by rwa [hxU]
  have hx := (gramPolynomials_zero_iff x).mpr hUnitary
  have hn := eval_nonneg_of_sumSq_mod_equations
    (fun k : ι × ι × Bool => determinantGramPolynomial k.1 k.2.1 k.2.2)
    x (fun k => hx k.1 k.2.1 k.2.2) hs q hcert
  rw [hvalue U hU] at hn
  exact ⟨σ, sub_nonneg.mp hn⟩

/-- Passing to the slack-square quotient converts a preordering certificate
to a sum-of-squares certificate for equations alone. -/
theorem quotient_sumSq_of_determinant_preordering_certificate
    (h : HasDeterminantPreorderingCertificate (ι := ι)) :
    IsSumSq (-1 : P ⧸ Ideal.span (Set.range determinantUnitMarginEquation)) := by
  let I := Ideal.span (Set.range (determinantUnitMarginEquation (ι := ι)))
  let q := Ideal.Quotient.mk I
  have hzero (k : DeterminantWitnessEquation ι) : q (determinantUnitMarginEquation k) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_range_self k))
  have hGram (i j : ι) (c : Bool) : q (determinantGramPolynomial i j c) = 0 :=
    hzero (.inl (i, j, c))
  have hSq (σ : Equiv.Perm ι) : IsSumSq (q (determinantUnitMargin σ)) := by
    have he : q (determinantUnitMargin σ) = q (MvPolynomial.X (.inr σ) : P) ^ 2 := by
      apply sub_eq_zero.mp
      simpa only [determinantUnitMarginEquation, map_sub, map_pow] using hzero (.inr σ)
    rw [he, pow_two]
    exact IsSumSq.mul_self _
  obtain ⟨s, hs, a, he⟩ := h
  have hq := congrArg q he
  simp only [map_neg, map_one, map_add, map_sum, map_mul, map_prod, hGram, mul_zero,
    Finset.sum_const_zero, add_zero] at hq
  change IsSumSq (-1 : P ⧸ I)
  rw [hq]
  exact IsSumSq.sum fun J _ => (map_sumSq q (hs J)).mul (IsSumSq.prod fun σ _ => hSq σ)

/-- A certificate in the strict separation coordinate ring suffices. -/
theorem conjecture_of_polynomial_quotient_sumSq [Nonempty ι]
    (h : IsSumSq (-1 : P ⧸ Ideal.span (Set.range determinantWitnessPolynomial))) :
    Conjecture ι :=
  conjecture_iff_no_polynomial_equation_witness.mpr
    (no_real_zeros_of_quotient_sumSq determinantWitnessPolynomial h)

/-- In positive order, the conjecture holds exactly when the strict
separation coordinate ring has no real point. -/
theorem conjecture_iff_no_polynomial_quotient_real_point [Nonempty ι] :
    Conjecture ι ↔
      ¬ Nonempty ((P ⧸ Ideal.span (Set.range determinantWitnessPolynomial)) →ₐ[ℝ] ℝ) :=
  conjecture_iff_no_polynomial_equation_witness.trans
    (not_congr (real_zeros_iff_real_algebra_point determinantWitnessPolynomial))

/-- The missing direction of certificate completeness is the real-point
theorem for the semireal strict separation coordinate ring. -/
theorem determinant_certificate_completeness_iff_semireal_real_point [Nonempty ι] :
    let A := P ⧸ Ideal.span (Set.range determinantWitnessPolynomial)
    (Conjecture ι → IsSumSq (-1 : A)) ↔ (IsSemireal A → Nonempty (A →ₐ[ℝ] ℝ)) := by
  classical
  dsimp only
  rw [conjecture_iff_no_polynomial_quotient_real_point,
    ← not_isSemireal_iff_neg_one_sumSq]
  constructor
  · intro h hsemi
    by_contra hpoint
    exact h hpoint hsemi
  · intro h hpoint hsemi
    exact hpoint (h hsemi)

end
end MOC
