import MOC.MatchingContactTransfer
import MOC.MatchingTriangle
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! The contact transfer counts independent polynomial constraints. The
alternating identity on a full triangle can leave room for an additional
contact even at the nominal threshold. -/

open MvPolynomial Set

namespace MOC

variable {n : ℕ}

/-- The dimension of the complex span of the active gap polynomials and
the determinant deficit. -/
noncomputable def matchingChartConstraintRank
    (U : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ) (η : ℂ) (r : ContactMatching n)
    (z : MatchingChartVariable n → ℂ) : ℕ :=
  Module.finrank ℂ (Submodule.span ℂ
    (Set.range (matchingChartContactPolynomial U (chartContacts η r z) r)))

/-- A spanning list of fewer than `2N - 2` complex constraints is enough to
construct the fixed-contact curve, even when the number of labels is larger. -/
theorem exists_matching_contact_curve_of_spanning_constraints
    (hn : 2 ≤ n) (U : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ)
    (η : ℂ) (hη : η ≠ 0) (r : ContactMatching n)
    (z : MatchingChartVariable n → ℂ)
    (hz : eval z (matchingChartRegularPolynomial n) ≠ 0)
    {κ : Type*} [Fintype κ] (p : κ → MvPolynomial (MatchingChartVariable n) ℂ)
    (hcard : Fintype.card κ < 2 * (n + 2) - 2)
    (hspan : ∀ i, matchingChartContactPolynomial U (chartContacts η r z) r i ∈
      Submodule.span ℂ (Set.range p)) :
    ∃ Q : Ideal (MvPolynomial (MatchingChartVariable n) ℂ), Q.IsPrime ∧
      (∀ i : Option ↥((chartContacts η r z).erase r),
        let q := matchingChartContactPolynomial U (chartContacts η r z) r i
        q - C (eval z q) ∈ Q) ∧
      Q < vanishingIdeal ({z} : Set (MatchingChartVariable n → ℂ)) ∧
      (∃ f : Polynomial ℂ →ₐ[ℂ] (MvPolynomial (MatchingChartVariable n) ℂ ⧸ Q),
        Function.Injective f ∧ f.Finite) ∧
      ∃ σ ∉ chartContacts η r z,
        Ideal.Quotient.mk Q (matchingChartGapPolynomial η r σ) ∉
          Set.range (algebraMap ℂ (MvPolynomial (MatchingChartVariable n) ℂ ⧸ Q)) := by
  have hc : Fintype.card κ < Fintype.card (MatchingChartVariable n) := by
    rwa [card_matchingChartVariable]
  obtain ⟨Q, hQ, hp, hlt, hf⟩ := exists_finite_curve_of_polynomial_fiber p z hc
  have hspan' (q : MvPolynomial (MatchingChartVariable n) ℂ)
      (hq : q ∈ Submodule.span ℂ (Set.range p)) : q - C (eval z q) ∈ Q := by
    induction hq using Submodule.span_induction with
    | mem q hm =>
        obtain ⟨i, rfl⟩ := hm
        exact hp i
    | zero => simp
    | add a b ha hb iha ihb =>
        rw [map_add, map_add, add_sub_add_comm]
        exact Q.add_mem iha ihb
    | smul c a ha iha =>
        rw [MvPolynomial.smul_eq_C_mul, map_mul, eval_C, map_mul, ← mul_sub]
        exact Ideal.mul_mem_left Q _ iha
  have hcontact i := hspan' _ (hspan i)
  letI : Q.IsPrime := hQ
  exact ⟨Q, hQ, hcontact, hlt, hf,
    exists_nonscalar_inactive_gap_on_curve hn U η hη r z hz Q hlt hcontact⟩

/-- A short spanning list allows the same covering transfer as a small
active set. -/
theorem exists_matchingChartContactCover_of_spanning_constraints
    (hn : 2 ≤ n) (U : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ)
    (η : ℂ) (hη : η ≠ 0) (r : ContactMatching n)
    (z : MatchingChartVariable n → ℂ)
    (hz : eval z (matchingChartRegularPolynomial n) ≠ 0)
    (hmax : ∀ σ, 0 ≤ (chartMatchingGap η r z σ).re)
    {κ : Type*} [Fintype κ] (p : κ → MvPolynomial (MatchingChartVariable n) ℂ)
    (hcard : Fintype.card κ < 2 * (n + 2) - 2)
    (hspan : ∀ i, matchingChartContactPolynomial U (chartContacts η r z) r i ∈
      Submodule.span ℂ (Set.range p)) :
    Nonempty (MatchingChartContactCover U η r z) := by
  obtain ⟨Q, hQ, hfiber, hlt, ⟨f, hfi, hf⟩, i, hi, hi'⟩ :=
    exists_matching_contact_curve_of_spanning_constraints hn U η hη r z hz p hcard hspan
  letI : Q.IsPrime := hQ
  exact matchingChartContactCover_of_curve U η r z hz hmax Q hfiber hlt f hfi hf i hi hi'

/-- Small constraint rank gives a contact cover even when many matching
labels are active. -/
theorem exists_matchingChartContactCover_of_low_constraint_rank
    (hn : 2 ≤ n) (U : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ)
    (η : ℂ) (hη : η ≠ 0) (r : ContactMatching n)
    (z : MatchingChartVariable n → ℂ)
    (hz : eval z (matchingChartRegularPolynomial n) ≠ 0)
    (hmax : ∀ σ, 0 ≤ (chartMatchingGap η r z σ).re)
    (hrank : matchingChartConstraintRank U η r z < 2 * (n + 2) - 2) :
    Nonempty (MatchingChartContactCover U η r z) := by
  let p := matchingChartContactPolynomial U (chartContacts η r z) r
  let V := Submodule.span ℂ (Set.range p)
  letI : FiniteDimensional ℂ V := FiniteDimensional.span_of_finite ℂ (Set.finite_range p)
  let b := Module.finBasis ℂ V
  let q := V.subtype ∘ b
  have hq : Submodule.span ℂ (Set.range q) = V := by
    change Submodule.span ℂ (Set.range (V.subtype ∘ b)) = V
    rw [Set.range_comp, ← Submodule.map_span, b.span_eq, Submodule.map_subtype_top]
  refine exists_matchingChartContactCover_of_spanning_constraints hn U η hη r z hz hmax q ?_ ?_
  · simpa only [Fintype.card_fin] using hrank
  · intro i
    rw [hq]
    exact Submodule.subset_span (Set.mem_range_self i)

/-- It suffices to prove the terminal support inequality at charts where
the constraint span has dimension at least the number of chart variables. -/
theorem mocIsTrue_iff_terminal_chart_support_of_constraint_rank :
    MOCIsTrue ↔ ∀ n : ℕ, 2 ≤ n →
      ∀ (U : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ) (_ : IsUnitary U)
        (η : ℂ) (r : ContactMatching n) (z : MatchingChartVariable n → ℂ),
        eval z (matchingChartRegularPolynomial n) ≠ 0 →
        (∀ σ, 0 ≤ (chartMatchingGap η r z σ).re) →
        2 * (n + 2) - 2 ≤ matchingChartConstraintRank U η r z →
        (η * eval z (matchingChartDeficitPolynomial U r)).re ≤ 0 := by
  constructor
  · intro h n hn U hU η r z hz hmax hrank
    have hr : r ∈ chartContacts η r z := by simp [chartMatchingGap]
    have hcard : matchingChartConstraintRank U η r z ≤ (chartContacts η r z).card := by
      rw [← card_matchingChartContactConstraints (chartContacts η r z) r hr]
      exact finrank_range_le_card (R := ℂ) (matchingChartContactPolynomial U (chartContacts η r z) r)
    exact (mocIsTrue_iff_terminal_chart_support.mp h) n hn U hU η r z hz hmax (hrank.trans hcard)
  · intro hterminal
    apply mocIsTrue_iff_terminal_chart_support.mpr
    intro n hn U hU η r z hz hmax _
    by_contra! hpos
    have hη : η ≠ 0 := by
      intro he
      simp [he] at hpos
    obtain ⟨w, hw, hdef, hnonneg, _, hrank⟩ := exists_chart_with_terminal_contacts_of_covers
      U η r z hz hmax (terminal := fun w => 2 * (n + 2) - 2 ≤ matchingChartConstraintRank U η r w)
      (fun w hw _ hm _ hnot => exists_matchingChartContactCover_of_low_constraint_rank
        hn U η hη r w hw hm (lt_of_not_ge hnot))
    exact (not_lt_of_ge (hterminal n hn U hU η r w hw hnonneg hrank)) (hdef.symm ▸ hpos)

private theorem matchingChartPolynomial_triangle_identity
    (r : ContactMatching n) (i j k : Fin (n + 2))
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    matchingChartPolynomial r +
      matchingChartPolynomial (r * Equiv.swap i j * Equiv.swap j k) +
      matchingChartPolynomial (r * Equiv.swap j k * Equiv.swap i j) =
    matchingChartPolynomial (r * Equiv.swap i j) +
      matchingChartPolynomial (r * Equiv.swap i k) +
      matchingChartPolynomial (r * Equiv.swap j k) := by
  apply MvPolynomial.funext
  intro z
  obtain ⟨a, b, he⟩ := exists_spectra_of_matchingChartCoordinate z
  simp only [map_add, eval_matchingChartPolynomial, ← he]
  exact matchingProduct_triangle_identity a b r i j k hij hik hjk

/-- At the nominal terminal count, all five nonreference permutations of a
three-label triangle allow one constraint to be removed. The transfer then
adds a contact. -/
theorem exists_matchingChartContactCover_of_full_triangle
    (hn : 2 ≤ n) (U : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ)
    (η : ℂ) (hη : η ≠ 0) (r : ContactMatching n) (i j k : Fin (n + 2))
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (z : MatchingChartVariable n → ℂ)
    (hz : eval z (matchingChartRegularPolynomial n) ≠ 0)
    (hmax : ∀ σ, 0 ≤ (chartMatchingGap η r z σ).re)
    (hcard : (chartContacts η r z).card ≤ 2 * (n + 2) - 2)
    (hT : {r * Equiv.swap i j, r * Equiv.swap i k, r * Equiv.swap j k,
      r * Equiv.swap i j * Equiv.swap j k, r * Equiv.swap j k * Equiv.swap i j} ⊆
        chartContacts η r z) : Nonempty (MatchingChartContactCover U η r z) := by
  classical
  let T := chartContacts η r z
  let u := r * Equiv.swap i j
  let v := r * Equiv.swap i k
  let w := r * Equiv.swap j k
  let a := r * Equiv.swap i j * Equiv.swap j k
  let b := r * Equiv.swap j k * Equiv.swap i j
  change ({u, v, w, a, b} : Finset (ContactMatching n)) ⊆ T at hT
  have hbi : b i = r k := by simp only [b, Equiv.Perm.mul_apply, Equiv.swap_apply_left]
  have hbj : b j = r i := by
    simp only [b, Equiv.Perm.mul_apply, Equiv.swap_apply_right,
      Equiv.swap_apply_of_ne_of_ne hij hik]
  have hne {ρ : ContactMatching n} {l : Fin (n + 2)} (hρ : ρ i = r l) (hl : l ≠ k) : ρ ≠ b := by
    intro h
    exact hl (r.injective (hρ.symm.trans ((congrArg (fun e : ContactMatching n => e i) h).trans hbi)))
  have hrb : r ≠ b := hne rfl hik
  have hub : u ≠ b := hne (by simp [u, Equiv.Perm.mul_apply]) hjk
  have hvb : v ≠ b := by
    intro h
    have h' : v j = b j := congrArg (fun e : ContactMatching n => e j) h
    rw [hbj, show v j = r j by simp [v, Equiv.Perm.mul_apply,
      Equiv.swap_apply_of_ne_of_ne hij.symm hjk]] at h'
    exact hij (r.injective h'.symm)
  have hwb : w ≠ b := hne (by simp [w, Equiv.Perm.mul_apply,
    Equiv.swap_apply_of_ne_of_ne hij hik]) hik
  have hab : a ≠ b := hne (by simp [a, Equiv.Perm.mul_apply,
    Equiv.swap_apply_of_ne_of_ne hij hik]) hjk
  let A := (T.erase r).erase b
  have hrT : r ∈ T := by simp [T, chartMatchingGap]
  have hbT : b ∈ T.erase r := Finset.mem_erase.mpr ⟨hrb.symm, hT (by simp)⟩
  have hc : Fintype.card (Option ↥A) < 2 * (n + 2) - 2 := by
    have hr := Finset.card_erase_add_one hrT
    have hb := Finset.card_erase_add_one hbT
    change T.card ≤ _ at hcard
    simp only [Fintype.card_option, Fintype.card_coe, A]
    omega
  let G (ρ : ContactMatching n) := matchingChartPolynomial r - matchingChartPolynomial ρ
  let p : Option ↥A → MvPolynomial (MatchingChartVariable n) ℂ
    | none => matchingChartDeficitPolynomial U r
    | some ρ => G ρ.val
  let V := Submodule.span ℂ (Set.range p)
  have hp (ι : Option ↥A) : p ι ∈ V := Submodule.subset_span (Set.mem_range_self ι)
  have hm (ρ : ContactMatching n) (hρ : ρ ∈ T) (hne : ρ ≠ b) : G ρ ∈ V := by
    by_cases hr : ρ = r
    · subst ρ
      simpa only [G, sub_self] using V.zero_mem
    · exact hp (some ⟨ρ, Finset.mem_erase.mpr ⟨hne, Finset.mem_erase.mpr ⟨hr, hρ⟩⟩⟩)
  have ht : G b = G u + G v + G w - G a := by
    have h := matchingChartPolynomial_triangle_identity r i j k hij hik hjk
    dsimp only [G, u, v, w, a, b]
    linear_combination -h
  refine exists_matchingChartContactCover_of_spanning_constraints hn U η hη r z hz hmax p hc ?_
  intro ρ
  cases ρ with
  | none => exact hp none
  | some ρ =>
    change G ρ.val ∈ V
    by_cases hρ : ρ.val = b
    · rw [hρ, ht]
      exact V.sub_mem (V.add_mem (V.add_mem (hm u (hT (by simp)) hub)
        (hm v (hT (by simp)) hvb)) (hm w (hT (by simp)) hwb)) (hm a (hT (by simp)) hab)
    · exact hm ρ.val (Finset.mem_of_mem_erase ρ.property) hρ

end MOC
