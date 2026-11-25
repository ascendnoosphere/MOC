import MOC.SharpContactRank

/-! A maximal contact witness is isolated by its old complex contact
differences alone. The complex determinant gap is allowed to move.
The contact transfer starts from Zheng (preprint DOI:
10.13140/RG.2.2.36790.25923). -/

open Matrix MvPolynomial Set
open scoped BigOperators

namespace MOC

noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A finite affine curve of exact profiles that fixes the old complex
differences through a strict starting point always raises contacts.
No hypothesis on the determinant gap on the curve is needed. -/
theorem StrictMatchingSupport.exists_more_contacts_on_affine_difference_curve
    {U : Matrix ι ι ℂ} (hU : IsUnitary U) (w : StrictMatchingSupport U)
    (Q : Ideal (ProfileRing ι)) [Q.IsPrime]
    (F : Polynomial ℂ →ₐ[ℂ] (ProfileRing ι ⧸ Q))
    (hF : F.Finite) (hFi : Function.Injective F)
    (t : ProfileRing ι) (ht : Ideal.Quotient.mk Q t = F Polynomial.X)
    (x₀ : zeroLocus Q) (hbase : x₀.val = matchingProduct w.a w.b)
    (hexact : ∀ y : zeroLocus Q, ∃ a b : ι → ℂ, matchingProduct a b = y.val)
    (hold : ∀ y : zeroLocus Q, ∀ q ∈ w.contacts,
      y.val w.pivot - y.val q = x₀.val w.pivot - x₀.val q) :
    ∃ v : StrictMatchingSupport U, v.η = w.η ∧ v.pivot = w.pivot ∧
      w.contacts ⊂ v.contacts ∧
      ∀ q ∈ w.contacts, matchingProduct v.a v.b v.pivot - matchingProduct v.a v.b q =
        matchingProduct w.a w.b w.pivot - matchingProduct w.a w.b q := by
  classical
  letI : Nonempty ι := Classical.byContradiction fun hn => by
    letI : IsEmpty ι := not_nonempty_iff.mp hn
    exact w.not_holds (conjecture_of_subsingleton w.a w.b U hU)
  let G (r : Equiv.Perm ι → ℂ) := matchingProfileDetGap U w.η w.pivot r
  let g : ProfileRing ι := ∑ q, C (realSignedWeight U q : ℂ) *
    (C w.η * (X q - X w.pivot))
  have hGe (y : zeroLocus Q) : eval y.val g = G y.val := by
    simp only [g, G, matchingProfileDetGap, map_sum, map_mul, map_sub, eval_X, eval_C]
  have hG₀ : 0 < (G x₀.val).re := by
    dsimp only [G]
    rw [hbase, matchingProfileDetGap_matchingProduct _ _ _ hU, mul_sub, Complex.sub_re]
    exact sub_pos.mpr w.strict
  have heval (y : zeroLocus Q) : (fun q => eval y.val (X q)) = y.val :=
    funext fun q => eval_X q
  by_cases hvar : ∃ x y : zeroLocus Q, eval x.val g ≠ eval y.val g
  · obtain ⟨S,s,c,hstart,hconn,hpos,hs,hsG,hhol⟩ :=
      affineGapContinuation (Equiv.Perm ι) Q F hF hFi t g ht hvar x₀ (by rwa [hGe])
    let A : Set (zeroLocus Q) := insert x₀ S
    have hA : IsPreconnected A :=
      hconn.subset_closure (Set.subset_insert _ _) (insert_subset hstart subset_closure)
    have hAc (y : zeroLocus Q) (hy : y ∈ A) : 0 < (G y.val).re := by
      rcases hy with hy | hy
      · simpa only [hy] using hG₀
      · rw [← hGe]
        exact hpos y hy
    exact w.exists_more_contacts_of_halfPlane_sheet hU hA Subtype.val (fun y _ => hexact y)
      (fun q => by
        have h (j : Equiv.Perm ι) := (continuous_apply j).comp
          (continuous_subtype_val : Continuous (Subtype.val : zeroLocus Q → _))
        exact (Complex.continuous_re.comp (continuous_const.mul ((h w.pivot).sub (h q)))).continuousOn)
      (Set.mem_insert _ _) hbase (fun y _ => hold y) hAc s c (fun z hz => Or.inr (hs z hz)) hhol
      (fun z hz => (hGe (s z)).symm.trans (hsG z hz))
  · letI : Infinite (zeroLocus Q) := Infinite.of_surjective _
      (surjective_finite_affine_projection Q F hF hFi t ht)
    have heq (y : zeroLocus Q) : G y.val = G x₀.val := by
      rw [← hGe, ← hGe]
      exact not_not.mp (fun h => hvar ⟨y,x₀,h⟩)
    obtain ⟨v, hη, hpr, hv, y, hy⟩ :=
      w.exists_more_contacts_on_infinite_affine_curve hU Q F hF hFi t ht X x₀
        ((heval _).trans hbase)
        (fun y => by simpa only [eval_X] using hexact y)
        (fun y q hq => by simpa only [eval_X] using hold y q hq)
        (fun y => by simpa only [eval_X, hbase] using heq y)
        (by simpa only [eval_X] using Set.infinite_range_of_injective (f := Subtype.val) Subtype.val_injective)
    rw [heval] at hy
    exact ⟨v,hη,hpr,hv,fun q hq => by rw [hpr,hy,hold y q hq,hbase]⟩

/-- The exact profile equations and the complex contact differences,
with no equation fixing the determinant gap. -/
def StrictMatchingSupport.differenceFibreIdeal
    {U : Matrix ι ι ℂ} (w : StrictMatchingSupport U) : Ideal (ProfileRing ι) :=
  profileIdeal ι ⊔ Ideal.span
    ((fun q : Equiv.Perm ι => X w.pivot - X q -
      C (matchingProduct w.a w.b w.pivot - matchingProduct w.a w.b q)) ''
      (w.contacts : Set (Equiv.Perm ι)))

theorem StrictMatchingSupport.mem_differenceFibre_iff
    {U : Matrix ι ι ℂ} (w : StrictMatchingSupport U) (p : Equiv.Perm ι → ℂ) :
    p ∈ zeroLocus w.differenceFibreIdeal ↔
      p ∈ zeroLocus (profileIdeal ι) ∧
      ∀ q ∈ w.contacts, p w.pivot - p q =
        matchingProduct w.a w.b w.pivot - matchingProduct w.a w.b q := by
  change w.differenceFibreIdeal ≤ RingHom.ker (eval p) ↔ _
  rw [StrictMatchingSupport.differenceFibreIdeal, sup_le_iff, Ideal.span_le]
  refine and_congr_right fun _ => ?_
  constructor
  · intro h q hq
    have hq' := h (show _ ∈ _ from ⟨q, hq, rfl⟩)
    change eval p (X w.pivot - X q -
      C (matchingProduct w.a w.b w.pivot - matchingProduct w.a w.b q)) = 0 at hq'
    simpa only [map_sub, eval_X, eval_C, sub_eq_zero] using hq'
  · rintro h _ ⟨q, hq, rfl⟩
    change eval p (X w.pivot - X q -
      C (matchingProduct w.a w.b w.pivot - matchingProduct w.a w.b q)) = 0
    simpa only [map_sub, eval_X, eval_C, sub_eq_zero] using h q hq

private theorem differenceFibre_at_base {U : Matrix ι ι ℂ} (w : StrictMatchingSupport U) :
    w.differenceFibreIdeal ≤ RingHom.ker (eval (matchingProduct w.a w.b)) :=
  (w.mem_differenceFibre_iff _).mpr
    ⟨(profileIdeal_exact (ι := ι)) ▸ ⟨w.a, w.b, rfl⟩, fun _ _ => rfl⟩

/-- Any positive-dimensional branch through the witness in the gap-free
contact fibre gives a strict contact transfer, including at singular profiles. -/
theorem StrictMatchingSupport.exists_more_contacts_of_prime_below_difference_fibre
    {U : Matrix ι ι ℂ} (hU : IsUnitary U) (w : StrictMatchingSupport U)
    (J : Ideal (ProfileRing ι)) [J.IsPrime] (hspan : w.differenceFibreIdeal ≤ J)
    (hJ : J < RingHom.ker (eval (matchingProduct w.a w.b))) :
    ∃ v : StrictMatchingSupport U, v.η = w.η ∧ v.pivot = w.pivot ∧
      w.contacts ⊂ v.contacts ∧
      ∀ q ∈ w.contacts, matchingProduct v.a v.b v.pivot - matchingProduct v.a v.b q =
        matchingProduct w.a w.b w.pivot - matchingProduct w.a w.b q := by
  classical
  let z := matchingProduct w.a w.b
  have h1 : (1 : ProfileRing ι) ∉ J :=
    J.ne_top_iff_one.mp (Ideal.IsPrime.ne_top inferInstance)
  obtain ⟨Q, hJQ, hQz, hQprime, _, F, hF, hFi, t, ht⟩ :=
    exists_finite_affine_curve_from_prime_below_point z J hJ 1 h1
  letI : Q.IsPrime := hQprime
  let x₀ : zeroLocus Q := ⟨z, hQz⟩
  have hmem (y : zeroLocus Q) : y.val ∈ zeroLocus w.differenceFibreIdeal :=
    fun p hp => y.property p (hJQ (hspan hp))
  have hexact (y : zeroLocus Q) : ∃ a b : ι → ℂ, matchingProduct a b = y.val := by
    have h := ((w.mem_differenceFibre_iff y.val).mp (hmem y)).1
    rwa [← profileIdeal_exact] at h
  exact w.exists_more_contacts_on_affine_difference_curve hU Q F hF hFi t ht x₀ rfl hexact
    (fun y => ((w.mem_differenceFibre_iff y.val).mp (hmem y)).2)

/-- At maximal contact count the exact profile is isolated even without
pinning the determinant gap. -/
theorem StrictMatchingSupport.exists_isolating_polynomial_of_max_contact_differences
    {U : Matrix ι ι ℂ} (hU : IsUnitary U) (w : StrictMatchingSupport U)
    (hmax : ∀ v : StrictMatchingSupport U, v.contacts.card ≤ w.contacts.card) :
    ∃ p : ProfileRing ι, eval (matchingProduct w.a w.b) p ≠ 0 ∧
      ∀ y ∈ zeroLocus w.differenceFibreIdeal, eval y p ≠ 0 → y = matchingProduct w.a w.b := by
  apply exists_isolating_polynomial_of_minimal_evaluation
  refine ⟨⟨RingHom.ker_isPrime _, differenceFibre_at_base w⟩, ?_⟩
  intro J hJ hle
  by_contra! hn
  letI : J.IsPrime := hJ.1
  obtain ⟨v, _, _, hv, _⟩ := w.exists_more_contacts_of_prime_below_difference_fibre hU J hJ.2
    (lt_iff_le_not_le.mpr ⟨hle, hn⟩)
  exact (not_lt_of_ge (hmax v)) (Finset.card_lt_card hv)

/-- A Euclidean contact fibre with the same complex differences is
locally a singleton even though the determinant gap was not prescribed. -/
theorem StrictMatchingSupport.exists_isolating_open_of_max_contact_differences
    {U : Matrix ι ι ℂ} (hU : IsUnitary U) (w : StrictMatchingSupport U)
    (hmax : ∀ v : StrictMatchingSupport U, v.contacts.card ≤ w.contacts.card) :
    ∃ O : Set (Equiv.Perm ι → ℂ), IsOpen O ∧ matchingProduct w.a w.b ∈ O ∧
      O ∩ zeroLocus w.differenceFibreIdeal = {matchingProduct w.a w.b} := by
  obtain ⟨p, hp, hunique⟩ := w.exists_isolating_polynomial_of_max_contact_differences hU hmax
  let O : Set (Equiv.Perm ι → ℂ) := {y | eval y p ≠ 0}
  refine ⟨O, (isClosed_eq p.continuous_eval continuous_const).isOpen_compl, hp, ?_⟩
  ext y
  constructor
  · rintro ⟨hy, hF⟩
    exact hunique y hF hy
  · intro hy
    rcases Set.mem_singleton_iff.mp hy with rfl
    exact ⟨hp, differenceFibre_at_base w⟩

end
end MOC
