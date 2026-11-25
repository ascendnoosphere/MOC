import MOC.BalancedContactReduction
import MOC.MobiusMomentWitness
import MOC.ContactEquationBudget
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! The contact budget can use the rank of the actual profile functions
rather than the number of labels. The fixed-gap strategy follows Zheng,
DOI: 10.13140/RG.2.2.36790.25923. -/

open Matrix MvPolynomial

namespace MOC

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The difference of two matching coordinates, as a function of both spectra.
In particular, identities on the exact profile locus are built into the span. -/
def contactDifference (r q : Equiv.Perm ι) (x : (ι → ℂ) × (ι → ℂ)) : ℂ :=
  matchingProduct x.1 x.2 r - matchingProduct x.1 x.2 q

/-- The complex span of the pivot differences for the given labels. -/
noncomputable def contactDifferenceSpan (r : Equiv.Perm ι) (S : Finset (Equiv.Perm ι)) :
    Submodule ℂ (((ι → ℂ) × (ι → ℂ)) → ℂ) :=
  Submodule.span ℂ (contactDifference r '' (S : Set (Equiv.Perm ι)))

omit [DecidableEq ι] in
private theorem finite_contactDifferenceSpan (r : Equiv.Perm ι)
    (S : Finset (Equiv.Perm ι)) : Module.Finite ℂ (contactDifferenceSpan r S) :=
  Module.Finite.span_of_finite ℂ (S.finite_toSet.image _)

omit [DecidableEq ι] in
/-- Retaining contacts and their pivot cannot decrease the rank. -/
theorem contactDifferenceSpan_finrank_mono (r : Equiv.Perm ι)
    {S T : Finset (Equiv.Perm ι)} (h : S ⊆ T) :
    Module.finrank ℂ (contactDifferenceSpan r S) ≤
      Module.finrank ℂ (contactDifferenceSpan r T) := by
  letI := finite_contactDifferenceSpan r T
  exact Submodule.finrank_mono (Submodule.span_mono (Set.image_mono h))

/-- The pivot difference functions of a strict witness can be made to span
at least 2n-3 dimensions. One more controlling observable fixes the gap. -/
theorem StrictMatchingSupport.exists_contactDifferenceRank_ge
    {U : Matrix ι ι ℂ} (hU : IsUnitary U) (w : StrictMatchingSupport U) :
    ∃ v : StrictMatchingSupport U, w.PreservesContactData v ∧
      2 * Fintype.card ι - 3 ≤ Module.finrank ℂ (contactDifferenceSpan v.pivot v.contacts) := by
  classical
  obtain ⟨v, hdata, hsat⟩ := global_exists_contact_equation_saturated hU w
  let r := v.pivot
  let I : Set (((ι → ℂ) × (ι → ℂ)) → ℂ) := contactDifference r '' (v.contacts : Set _)
  letI : Module.Finite ℂ (Submodule.span ℂ I) := finite_contactDifferenceSpan r v.contacts
  obtain ⟨T, hT, hcard, hspan, _⟩ := Submodule.exists_finset_span_eq_linearIndepOn ℂ I
  have hpre (f : T) : ∃ q : Equiv.Perm ι, contactDifference r q = f.val := by
    obtain ⟨q, _, hq⟩ := hT f.property
    exact ⟨q, hq⟩
  choose q hq using hpre
  let pin (f : T) : ProfileRing ι := X r - X (q f)
  let gap : ProfileRing ι := ∑ j, C (realSignedWeight U j : ℂ) * (C v.η * (X j - X r))
  let E : Finset (ProfileRing ι) := insert gap (T.attach.image pin)
  have hEq (a b : ι → ℂ)
      (he : ∀ p ∈ E, eval (matchingProduct a b) p = eval (matchingProduct v.a v.b) p) :
      (∀ j ∈ v.contacts, matchingProduct a b r - matchingProduct a b j =
        matchingProduct v.a v.b r - matchingProduct v.a v.b j) ∧
      matchingProfileDetGap U v.η r (matchingProduct a b) =
        matchingProfileDetGap U v.η r (matchingProduct v.a v.b) := by
    constructor
    · intro j hj
      let D : (((ι → ℂ) × (ι → ℂ)) → ℂ) →ₗ[ℂ] ℂ :=
        (LinearMap.proj (a,b) : (((ι → ℂ) × (ι → ℂ)) → ℂ) →ₗ[ℂ] ℂ) -
          LinearMap.proj (v.a,v.b)
      have hker : Submodule.span ℂ (T : Set _) ≤ LinearMap.ker D := by
        rw [Submodule.span_le]
        intro f hf
        let f' : T := ⟨f, hf⟩
        have hh := he (pin f') (Finset.mem_insert_of_mem
          (Finset.mem_image_of_mem pin (Finset.mem_attach T f')))
        change f'.val ∈ LinearMap.ker D
        rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.proj_apply,
          LinearMap.proj_apply, sub_eq_zero]
        rw [← hq f']
        simpa only [pin, map_sub, eval_X, contactDifference] using hh
      have hm : contactDifference r j ∈ Submodule.span ℂ (T : Set _) := by
        rw [hspan]
        exact Submodule.subset_span ⟨j, hj, rfl⟩
      have hh := hker hm
      simpa only [D, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.proj_apply, sub_eq_zero,
        contactDifference] using hh
    · have hh := he gap (Finset.mem_insert_self ..)
      simpa only [gap, matchingProfileDetGap, map_sum, map_mul, map_sub, eval_C, eval_X] using hh
  have hlo := hsat E hEq
  have hhi := Finset.card_insert_le gap (T.attach.image pin)
  have him := Finset.card_image_le (f := pin) (s := T.attach)
  rw [Finset.card_attach] at him
  change E.card ≤ _ at hhi
  change T.card = Module.finrank ℂ (contactDifferenceSpan v.pivot v.contacts) at hcard
  exact ⟨v, hdata, by omega⟩

/-- Erasing the pivot does not change the span because its difference is zero. -/
theorem contactDifferenceSpan_eq_span_erase (r : Equiv.Perm ι)
    (S : Finset (Equiv.Perm ι)) (hr : r ∈ S) :
    contactDifferenceSpan r S =
      Submodule.span ℂ (Set.range (fun q : S.erase r => contactDifference r q)) := by
  have he : (S : Set (Equiv.Perm ι)) = insert r (S.erase r : Set (Equiv.Perm ι)) := by
    rw [← Finset.coe_insert, Finset.insert_erase hr]
  have hzero : contactDifference r r = 0 := by ext x; simp [contactDifference]
  rw [contactDifferenceSpan, he, Set.image_insert_eq, hzero, Submodule.span_insert_zero]
  congr 1
  ext y
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact ⟨⟨q, hq⟩, rfl⟩
  · rintro ⟨q, rfl⟩
    exact ⟨q, q.property, rfl⟩

/-- The pivot counts as a contact but does not supply a difference. -/
theorem StrictMatchingSupport.contactDifferenceRank_le
    {U : Matrix ι ι ℂ} (v : StrictMatchingSupport U) :
    Module.finrank ℂ (contactDifferenceSpan v.pivot v.contacts) ≤ v.contacts.card - 1 := by
  have hp : v.pivot ∈ v.contacts := by simp [StrictMatchingSupport.contacts]
  rw [contactDifferenceSpan_eq_span_erase _ _ hp]
  simpa only [Fintype.card_coe, Finset.card_erase_of_mem hp] using
    (finrank_range_le_card (R := ℂ)
      (fun q : v.contacts.erase v.pivot => contactDifference v.pivot q))

/-- At the minimum possible count, the nonpivot contact differences must
be linearly independent. This applies to the functions, not their values at the witness. -/
theorem StrictMatchingSupport.linearIndependent_differences_of_minimal_count
    {U : Matrix ι ι ℂ} (v : StrictMatchingSupport U)
    (hcard : v.contacts.card = 2 * Fintype.card ι - 2)
    (hrank : 2 * Fintype.card ι - 3 ≤
      Module.finrank ℂ (contactDifferenceSpan v.pivot v.contacts)) :
    LinearIndependent ℂ (fun q : v.contacts.erase v.pivot => contactDifference v.pivot q) := by
  have hp : v.pivot ∈ v.contacts := by simp [StrictMatchingSupport.contacts]
  apply (linearIndependent_iff_card_le_finrank_span).mpr
  change Fintype.card (v.contacts.erase v.pivot) ≤
    Module.finrank ℂ (Submodule.span ℂ (Set.range (fun q : v.contacts.erase v.pivot =>
      contactDifference v.pivot q)))
  rw [← contactDifferenceSpan_eq_span_erase _ _ hp, Fintype.card_coe,
    Finset.card_erase_of_mem hp, hcard]
  exact hrank


/-- The unrotated determinant gap itself supplies an additional
independent function: it is not a complex linear combination of active
pivot differences. Evaluation at the witness and its conjugate gives
a complex-linear separator even though the contacts use real parts. -/
theorem StrictMatchingSupport.gap_not_mem_contactDifferenceSpan
    {U : Matrix ι ι ℂ} (hU : IsUnitary U) (v : StrictMatchingSupport U) :
    (fun x : (ι → ℂ) × (ι → ℂ) =>
      matchingProfileDetGap U 1 v.pivot (matchingProduct x.1 x.2)) ∉
        contactDifferenceSpan v.pivot v.contacts := by
  classical
  let x : (ι → ℂ) × (ι → ℂ) := (v.a, v.b)
  let y : (ι → ℂ) × (ι → ℂ) := (star ∘ v.a, star ∘ v.b)
  let g (w : (ι → ℂ) × (ι → ℂ)) :=
    matchingProfileDetGap U 1 v.pivot (matchingProduct w.1 w.2)
  let L : (((ι → ℂ) × (ι → ℂ)) → ℂ) →ₗ[ℂ] ℂ :=
    v.η • (LinearMap.proj x : (((ι → ℂ) × (ι → ℂ)) → ℂ) →ₗ[ℂ] ℂ) +
      (star v.η) • (LinearMap.proj y : (((ι → ℂ) × (ι → ℂ)) → ℂ) →ₗ[ℂ] ℂ)
  have hL (f : ((ι → ℂ) × (ι → ℂ)) → ℂ) (hf : f y = star (f x)) :
      (L f).re = 2 * (v.η * f x).re := by
    have hh : L f = v.η * f x + star (v.η * f x) := by simp [L, hf, star_mul']
    rw [hh, Complex.add_re, Complex.star_def, Complex.conj_re]
    ring
  have hP (q : Equiv.Perm ι) :
      matchingProduct y.1 y.2 q = star (matchingProduct x.1 x.2 q) := by
    simp only [matchingProduct, x, y, Function.comp_apply, star_prod, star_add]
  have hker : contactDifferenceSpan v.pivot v.contacts ≤ LinearMap.ker L := by
    apply Submodule.span_le.mpr
    rintro _ ⟨q, hq, rfl⟩
    have he := (Finset.mem_filter.mp hq).2
    have hz : (v.η * contactDifference v.pivot q x).re = 0 := by
      simp only [contactDifference, x, mul_sub, Complex.sub_re, he, sub_self]
    have hy : contactDifference v.pivot q y = star (contactDifference v.pivot q x) := by
      simp only [contactDifference, hP, star_sub]
    change contactDifference v.pivot q ∈ LinearMap.ker L
    rw [LinearMap.mem_ker]
    have hsum : L (contactDifference v.pivot q) =
        v.η * contactDifference v.pivot q x + star (v.η * contactDifference v.pivot q x) := by
      simp [L, hy, star_mul']
    rw [hsum]
    apply Complex.ext
    · rw [Complex.add_re, Complex.star_def, Complex.conj_re, hz, add_zero, Complex.zero_re]
    · rw [Complex.add_im, Complex.star_def, Complex.conj_im, add_neg_cancel, Complex.zero_im]
  have hg : g y = star (g x) := by
    simp only [g, matchingProfileDetGap, hP, star_sum, star_mul', star_sub, star_one,
      Complex.star_def, Complex.conj_ofReal, map_sub]
  have hpos : 0 < (v.η * g x).re := by
    simp only [g, x, matchingProfileDetGap_matchingProduct _ _ _ hU, one_mul, mul_sub,
      Complex.sub_re, sub_pos]
    exact v.strict
  intro h
  have hz := LinearMap.mem_ker.mp (hker h)
  have h := hL g hg
  rw [hz, Complex.zero_re] at h
  linarith

/-- Counterexamples can be chosen to meet the functional rank condition
and the centered quartic moment bound simultaneously, as well as the
first-order balances and unrestricted mixer maximality. Pivot and contact
retention are what let the two reductions compose. -/
theorem conjecture_iff_rank_moment_global_contact_bound [Nonempty ι] :
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
      MobiusMomentBound v.a v.b := by
  rw [conjecture_iff_global_contact_bound]
  constructor
  · rintro h ⟨U, hU, v, hcard, _⟩
    exact h ⟨U, hU, v, hcard⟩
  · rintro h ⟨U, hU, w, hcard⟩
    obtain ⟨u, hd, hrank⟩ := w.exists_contactDifferenceRank_ge hU
    obtain ⟨V, hV, v, hsub, hp, he, hη, ht, hc, hn, hs, hm⟩ :=
      u.exists_moment_tested_orbit_maximizer hU
    have hrank' := hrank.trans (contactDifferenceSpan_finrank_mono u.pivot hsub)
    rw [← hp] at hrank'
    exact h ⟨V, hV, v, hcard.trans (Finset.card_le_card (hd.contacts.trans hsub)),
      hrank', he, hη, ht, hc, hn, hs, hm⟩

end MOC
