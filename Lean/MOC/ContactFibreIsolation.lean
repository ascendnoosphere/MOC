import MOC.ContactDifferenceRank
import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
import Mathlib.RingTheory.Spectrum.Prime.Noetherian

/-! A maximal contact set forces an isolated fibre on the exact profile
variety. The contact-raising method starts from Zheng,
DOI: 10.13140/RG.2.2.36790.25923. -/

open Matrix MvPolynomial Set

namespace MOC

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private noncomputable def pinnedContactDifference {U : Matrix ι ι ℂ}
    (w : StrictMatchingSupport U) (q : Equiv.Perm ι) : ProfileRing ι :=
  X w.pivot - X q - C (matchingProduct w.a w.b w.pivot - matchingProduct w.a w.b q)

private noncomputable def pinnedContactGap {U : Matrix ι ι ℂ}
    (w : StrictMatchingSupport U) : ProfileRing ι :=
  (∑ q, C (realSignedWeight U q : ℂ) * (C w.η * (X q - X w.pivot))) -
    C (matchingProfileDetGap U w.η w.pivot (matchingProduct w.a w.b))

/-- Equations of the exact profile locus, the active complex differences
and the fixed complex determinant gap. -/
noncomputable def StrictMatchingSupport.contactFibreIdeal
    {U : Matrix ι ι ℂ} (w : StrictMatchingSupport U) : Ideal (ProfileRing ι) :=
  profileIdeal ι ⊔ Ideal.span (insert (pinnedContactGap w)
    (pinnedContactDifference w '' (w.contacts : Set (Equiv.Perm ι))))

theorem StrictMatchingSupport.mem_contactFibre_iff
    {U : Matrix ι ι ℂ} (w : StrictMatchingSupport U) (p : Equiv.Perm ι → ℂ) :
    p ∈ zeroLocus w.contactFibreIdeal ↔
      p ∈ zeroLocus (profileIdeal ι) ∧
      (∀ q ∈ w.contacts, p w.pivot - p q =
        matchingProduct w.a w.b w.pivot - matchingProduct w.a w.b q) ∧
      matchingProfileDetGap U w.η w.pivot p =
        matchingProfileDetGap U w.η w.pivot (matchingProduct w.a w.b) := by
  change w.contactFibreIdeal ≤ RingHom.ker (eval p) ↔ _
  rw [StrictMatchingSupport.contactFibreIdeal, sup_le_iff, Ideal.span_le]
  constructor
  · rintro ⟨hp, h⟩
    refine ⟨hp, ?_, ?_⟩
    · intro q hq
      have hq' := h (Set.mem_insert_of_mem _ ⟨q, hq, rfl⟩)
      change eval p (pinnedContactDifference w q) = 0 at hq'
      simpa only [pinnedContactDifference, map_sub, eval_X, eval_C,
        sub_eq_zero] using hq'
    · have hg := h (Set.mem_insert _ _)
      change eval p (pinnedContactGap w) = 0 at hg
      simpa only [pinnedContactGap, map_sub, map_mul, map_sum, eval_X,
        eval_C, matchingProfileDetGap, sub_eq_zero] using hg
  · rintro ⟨hp, hd, hg⟩
    refine ⟨hp, ?_⟩
    rintro q (rfl | ⟨j, hj, rfl⟩)
    · change eval p (pinnedContactGap w) = 0
      simpa only [pinnedContactGap, map_sub, map_mul, map_sum, eval_X,
        eval_C, matchingProfileDetGap, sub_eq_zero] using hg
    · change eval p (pinnedContactDifference w j) = 0
      simpa only [pinnedContactDifference, map_sub, eval_X, eval_C,
        sub_eq_zero] using hd j hj

private theorem contactFibreIdeal_le_evaluation {U : Matrix ι ι ℂ} (w : StrictMatchingSupport U) :
    w.contactFibreIdeal ≤ RingHom.ker (eval (matchingProduct w.a w.b)) :=
  (w.mem_contactFibre_iff _).mpr
    ⟨(profileIdeal_exact (ι := ι)) ▸ ⟨w.a, w.b, rfl⟩, fun _ _ => rfl, rfl⟩

/-- A positive-dimensional branch through the pinned profile raises contacts,
even if the contact count or the functional rank already meets its threshold. -/
theorem StrictMatchingSupport.exists_more_contacts_of_prime_below_fibre
    {U : Matrix ι ι ℂ} (hU : IsUnitary U) (w : StrictMatchingSupport U)
    (J : Ideal (ProfileRing ι)) [J.IsPrime] (hspan : w.contactFibreIdeal ≤ J)
    (hJ : J < RingHom.ker (eval (matchingProduct w.a w.b))) :
    ∃ v : StrictMatchingSupport U, w.contacts ⊂ v.contacts ∧ w.PreservesContactData v := by
  classical
  let z := matchingProduct w.a w.b
  have h1 : (1 : ProfileRing ι) ∉ J :=
    J.ne_top_iff_one.mp (Ideal.IsPrime.ne_top inferInstance)
  obtain ⟨Q, hJQ, hQz, hQprime, _, F, hF, hFi, t, ht⟩ :=
    exists_finite_affine_curve_from_prime_below_point z J hJ 1 h1
  letI : Q.IsPrime := hQprime
  let z₀ : zeroLocus Q := ⟨z, hQz⟩
  letI : Infinite (zeroLocus Q) := Infinite.of_surjective _
    (surjective_finite_affine_projection Q F hF hFi t ht)
  have hmem (y : zeroLocus Q) : y.val ∈ zeroLocus w.contactFibreIdeal :=
    fun p hp => y.property p (hJQ (hspan hp))
  have hexact (y : zeroLocus Q) : ∃ a b : ι → ℂ, matchingProduct a b = y.val := by
    have h := ((w.mem_contactFibre_iff y.val).mp (hmem y)).1
    rwa [← profileIdeal_exact] at h
  have heval (x : Equiv.Perm ι → ℂ) : (fun q => eval x (X q)) = x := by
    funext q
    exact eval_X q
  obtain ⟨v, hη, hp, hv, y, hy⟩ := w.exists_more_contacts_on_infinite_affine_curve
    hU Q F hF hFi t ht X z₀ (heval _)
    (fun y => by simpa only [eval_X] using hexact y)
    (fun y q hq => by simpa only [eval_X] using ((w.mem_contactFibre_iff _).mp (hmem y)).2.1 q hq)
    (fun y => by simpa only [eval_X] using ((w.mem_contactFibre_iff _).mp (hmem y)).2.2)
    (by simpa only [eval_X] using Set.infinite_range_of_injective (f := Subtype.val) Subtype.val_injective)
  rw [heval] at hy
  refine ⟨v, hv, ⟨hη, hp, hv.subset, ?_, ?_⟩⟩
  · intro q hq
    rw [hp, hy]
    exact ((w.mem_contactFibre_iff _).mp (hmem y)).2.1 q hq
  · rw [hη, hp, hy]
    exact ((w.mem_contactFibre_iff _).mp (hmem y)).2.2

/-- If no strict witness for this mixer has more contacts, the evaluation
prime must be minimal over the pinned fibre equations. -/
theorem StrictMatchingSupport.evaluation_mem_minimalPrimes_of_max_contacts
    {U : Matrix ι ι ℂ} (hU : IsUnitary U) (w : StrictMatchingSupport U)
    (hmax : ∀ v : StrictMatchingSupport U, v.contacts.card ≤ w.contacts.card) :
    RingHom.ker (eval (matchingProduct w.a w.b)) ∈ w.contactFibreIdeal.minimalPrimes := by
  refine ⟨⟨RingHom.ker_isPrime _, contactFibreIdeal_le_evaluation w⟩, ?_⟩
  intro J hJ hle
  by_contra! hn
  letI : J.IsPrime := hJ.1
  obtain ⟨v, hv, _⟩ := w.exists_more_contacts_of_prime_below_fibre hU J hJ.2
    (lt_iff_le_not_le.mpr ⟨hle, hn⟩)
  exact (not_lt_of_ge (hmax v)) (Finset.card_lt_card hv)

/-- A minimal evaluation ideal is isolated by one polynomial, obtained by
removing the other finitely many minimal components. Compare the Stacks
Project, Tags 00FR and 0BX1, for finiteness and localization. -/
theorem exists_isolating_polynomial_of_minimal_evaluation
    {σ : Type*} [Fintype σ] (I : Ideal (MvPolynomial σ ℂ)) (z : σ → ℂ)
    (hmin : RingHom.ker (eval z) ∈ I.minimalPrimes) :
    ∃ p : MvPolynomial σ ℂ, eval z p ≠ 0 ∧
      ∀ y ∈ zeroLocus I, eval y p ≠ 0 → y = z := by
  classical
  let m := RingHom.ker (eval z)
  let hfinite := Ideal.finite_minimalPrimes_of_isNoetherianRing (MvPolynomial σ ℂ) I
  let S := hfinite.toFinset.erase m
  have hS (K : S) : K.val ∈ I.minimalPrimes ∧ K.val ≠ m := by
    have h := Finset.mem_erase.mp K.property
    exact ⟨(hfinite.mem_toFinset).mp h.2, h.1⟩
  have hsep (K : S) : ∃ p ∈ K.val, p ∉ m := by
    apply SetLike.not_le_iff_exists.mp
    intro hle
    exact (hS K).2 (le_antisymm hle (hmin.2 (hS K).1.1 hle))
  choose p hp hpm using hsep
  refine ⟨∏ K : S, p K, ?_, ?_⟩
  · rw [map_prod]
    exact Finset.prod_ne_zero_iff.mpr fun K _ => hpm K
  · intro y hy hpy
    letI : (RingHom.ker (eval y)).IsPrime := RingHom.ker_isPrime _
    obtain ⟨K, hK, hKy⟩ := Ideal.exists_minimalPrimes_le (show I ≤ RingHom.ker (eval y) from hy)
    by_cases hKm : K = m
    · funext q
      have hq : X q - C (z q) ∈ K := by
        rw [hKm]
        simp [m, RingHom.mem_ker]
      have hqy := hKy hq
      change eval y (X q - C (z q)) = 0 at hqy
      simpa only [map_sub, eval_X, eval_C, sub_eq_zero] using hqy
    · exfalso
      let K' : S := ⟨K, Finset.mem_erase.mpr ⟨hKm, (hfinite.mem_toFinset).mpr hK⟩⟩
      have h0 : eval y (p K') = 0 := hKy (hp K')
      rw [map_prod] at hpy
      exact (Finset.prod_ne_zero_iff.mp hpy K' (Finset.mem_univ K')) h0

/-- A strict witness with maximal contact count is Zariski isolated in
its fixed-gap exact-profile fibre, rather than merely meeting a rank count. -/
theorem StrictMatchingSupport.exists_isolating_polynomial_of_max_contacts
    {U : Matrix ι ι ℂ} (hU : IsUnitary U) (w : StrictMatchingSupport U)
    (hmax : ∀ v : StrictMatchingSupport U, v.contacts.card ≤ w.contacts.card) :
    ∃ p : ProfileRing ι, eval (matchingProduct w.a w.b) p ≠ 0 ∧
      ∀ y ∈ zeroLocus w.contactFibreIdeal, eval y p ≠ 0 → y = matchingProduct w.a w.b :=
  exists_isolating_polynomial_of_minimal_evaluation _ _
    (w.evaluation_mem_minimalPrimes_of_max_contacts hU hmax)

/-- An isolating polynomial also gives ordinary Euclidean isolation in
profile coordinates. No claim is made about the spectral parametrization. -/
theorem StrictMatchingSupport.exists_isolating_open_of_max_contacts
    {U : Matrix ι ι ℂ} (hU : IsUnitary U) (w : StrictMatchingSupport U)
    (hmax : ∀ v : StrictMatchingSupport U, v.contacts.card ≤ w.contacts.card) :
    ∃ O : Set (Equiv.Perm ι → ℂ), IsOpen O ∧ matchingProduct w.a w.b ∈ O ∧
      O ∩ zeroLocus w.contactFibreIdeal = {matchingProduct w.a w.b} := by
  obtain ⟨p, hp, hunique⟩ := w.exists_isolating_polynomial_of_max_contacts hU hmax
  let O : Set (Equiv.Perm ι → ℂ) := {y | eval y p ≠ 0}
  refine ⟨O, (isClosed_eq p.continuous_eval continuous_const).isOpen_compl, hp, ?_⟩
  ext y
  constructor
  · rintro ⟨hy, hF⟩
    exact hunique y hF hy
  · intro hy
    rcases Set.mem_singleton_iff.mp hy with rfl
    exact ⟨hp, contactFibreIdeal_le_evaluation w⟩

/-- If there is a strict witness then there is one whose contact count
is maximal among all unitary mixers in the same order. -/
theorem exists_globally_maximal_contact_count {U : Matrix ι ι ℂ}
    (hU : IsUnitary U) (w : StrictMatchingSupport U) :
    ∃ (V : Matrix ι ι ℂ), IsUnitary V ∧ ∃ v : StrictMatchingSupport V,
      w.contacts.card ≤ v.contacts.card ∧
      ∀ (W : Matrix ι ι ℂ), IsUnitary W → ∀ u : StrictMatchingSupport W,
        u.contacts.card ≤ v.contacts.card := by
  classical
  let C := Fintype.card (Equiv.Perm ι)
  let P (k : ℕ) := ∃ (V : Matrix ι ι ℂ), IsUnitary V ∧
    ∃ v : StrictMatchingSupport V, v.contacts.card = k
  have hw : P w.contacts.card := ⟨U, hU, w, rfl⟩
  have hw' : w.contacts.card ≤ C := Finset.card_le_univ _
  obtain ⟨V, hV, v, hv⟩ := Nat.findGreatest_spec (P := P) hw' hw
  refine ⟨V, hV, v, ?_, ?_⟩
  · rw [hv]
    exact Nat.le_findGreatest hw' hw
  · intro W hW u
    rw [hv]
    exact Nat.le_findGreatest (Finset.card_le_univ _) ⟨W, hW, u, rfl⟩

/-- The terminal exclusion can simultaneously require functional rank,
the quartic moment bound, global mixer maximality and local isolation in
the pinned affine fibre. Select maximal contact count before rebalancing;
the preserving operations then cannot lose that maximality. -/
theorem conjecture_iff_isolated_rank_moment_contact_bound [Nonempty ι] :
    Conjecture ι ↔ ¬ ∃ (U : Matrix ι ι ℂ), IsUnitary U ∧ ∃ v : StrictMatchingSupport U,
      2 * Fintype.card ι - 2 ≤ v.contacts.card ∧
      2 * Fintype.card ι - 3 ≤ Module.finrank ℂ (contactDifferenceSpan v.pivot v.contacts) ∧
      spectralEnergy v.a v.b = 1 ∧ Complex.normSq v.η = 1 ∧
      (∑ i, v.a i) = (∑ i, v.b i) ∧
      (∑ i, (Complex.normSq (v.a i) : ℂ) * v.a i) =
        (∑ i, (Complex.normSq (v.b i) : ℂ) * v.b i) ∧
      ¬ IsStarNormal (diagonal v.a + U * diagonal v.b * Uᴴ) ∧
      (∀ V : Matrix ι ι ℂ, IsUnitary V →
        (v.η * determinantValue v.a v.b V).re ≤ (v.η * determinantValue v.a v.b U).re) ∧
      MobiusMomentBound v.a v.b ∧
      (∀ (V : Matrix ι ι ℂ), IsUnitary V → ∀ u : StrictMatchingSupport V,
        u.contacts.card ≤ v.contacts.card) ∧
      ∃ p : ProfileRing ι, eval (matchingProduct v.a v.b) p ≠ 0 ∧
        ∀ y ∈ zeroLocus v.contactFibreIdeal, eval y p ≠ 0 → y = matchingProduct v.a v.b := by
  rw [conjecture_iff_global_contact_bound]
  constructor
  · rintro h ⟨U, hU, v, hc, _⟩
    exact h ⟨U, hU, v, hc⟩
  · rintro h ⟨U, hU, w, hw⟩
    obtain ⟨V, hV, v, hv, hmax⟩ := exists_globally_maximal_contact_count hU w
    obtain ⟨u, hd, hr⟩ := v.exists_contactDifferenceRank_ge hV
    obtain ⟨W, hW, w', hs, hp, he, hη, ht, hc, hn, hopt, hm⟩ :=
      u.exists_moment_tested_orbit_maximizer hV
    have hsub := Finset.card_le_card (hd.contacts.trans hs)
    have hr' := hr.trans (contactDifferenceSpan_finrank_mono u.pivot hs)
    rw [← hp] at hr'
    have hmax' (X : Matrix ι ι ℂ) (hX : IsUnitary X) (q : StrictMatchingSupport X) :=
      (hmax X hX q).trans hsub
    have hi := w'.exists_isolating_polynomial_of_max_contacts hW (hmax' W hW)
    exact h ⟨W, hW, w', hw.trans (hv.trans hsub), hr', he, hη, ht, hc, hn, hopt, hm, hmax', hi⟩

end MOC
