import MOC.ExactProfileLocus
import MOC.FiniteFiberDimension
import MOC.FixedContactData
import MOC.PolynomialContactSlice
import MOC.PinnedPrimeHeight

/-! Global contact transfer, including zero matching products. The
contact-count strategy follows Zheng, DOI: 10.13140/RG.2.2.36790.25923. -/

open MvPolynomial Set Matrix
open scoped BigOperators

namespace MOC

noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

abbrev ProfileRing (ι : Type*) := MvPolynomial (Equiv.Perm ι) ℂ

def profileIdeal (ι : Type*) [Fintype ι] [DecidableEq ι] : Ideal (ProfileRing ι) :=
  RingHom.ker (aeval matchingProfile_coordinate)

instance profileIdeal_prime : (profileIdeal ι).IsPrime := RingHom.ker_isPrime _

theorem profileIdeal_exact :
    {p : Equiv.Perm ι → ℂ | ∃ a b : ι → ℂ, matchingProduct a b = p} =
      zeroLocus (profileIdeal ι) :=
  exact_matching_profiles_eq_prime_zeroLocus

open PolynomialContactChart in
/-- Any finite normalization of the global profile ring has at least
the $2n-2$ variables forced by an injective nonzero chart. This estimate
will apply to prime chains at other profiles, including degenerate ones. -/
theorem profile_normalization_lower_bound [Nontrivial ι] {d : ℕ}
    (f : MvPolynomial (Fin d) ℂ →ₐ[ℂ] (ProfileRing ι ⧸ profileIdeal ι))
    (hf : f.Finite) : 2 * Fintype.card ι - 2 ≤ d := by
  classical
  obtain ⟨o, i, hi⟩ := exists_pair_ne ι
  let x : Point o i := fun _ => 1
  have hxcol (j : ι) : colAt o i x j = if j = o then 0 else 1 := by
    by_cases hj : j = o <;> simp [colAt, PolynomialContactChart.col, x, hj]
  have hxrow (j : ι) : rowAt o i x j = if j = o then 0 else 1 := by
    by_cases hj : j = o <;> by_cases hp : j = i <;> simp [rowAt, PolynomialContactChart.row, x, hj, hp]
  have hnz : ∀ q, profile o i x q ≠ 0 := by
    intro q
    rw [profile_evaluation, show x (.inl ()) = 1 from rfl, one_mul]
    apply Finset.prod_ne_zero_iff.mpr
    intro j _
    rw [hxrow, hxcol]
    split <;> split <;> simp
  have hcol : colAt o i x i ≠ 0 := by rw [hxcol, if_neg hi.symm]; exact one_ne_zero
  obtain ⟨r, hr, _⟩ := (existsUnique_inverseEquation_iff o i i x).mpr ⟨hcol, hnz⟩
  let z := adjoin o i x r
  let B : Finset (LocalPoly o i) := {inverseEquation o i i}
  have hz : ∀ b ∈ B, eval z b = 0 := by
    intro b hb
    rw [Finset.mem_singleton.mp hb]
    exact hr
  have hh (y : LocalPoint o i) (hy : ∀ b ∈ B, eval y b = 0) :
      eval y (inverseEquation o i i) = 0 := hy _ (Finset.mem_singleton_self _)
  have h :=
    le_base_dimension_of_injective_polynomial_chart (profileIdeal ι) f hf B
      (liftedProfile o i) z hz
      (fun y hy => (profileIdeal_exact (ι := ι)) ▸ exists_spectra_on_inverse y (hh y hy))
      (fun y hy y' hy' he => localProfile_injective_on_inverse hi.symm
        (hh y hy) (hh y' hy') he)
  rw [card_varLocalized hi.symm, Fintype.card_fin, show B.card = 1 by simp [B]] at h
  omega

/-- When fewer than $2n-2$ observables determine the old differences and gap
on the exact profile locus, another contact can be forced, irrespective of
the number of old labels. The observables need not be linear. -/
theorem global_contact_transfer_of_controlling_observables {U : Matrix ι ι ℂ}
    (hU : IsUnitary U) (w : StrictMatchingSupport U) (E : Finset (ProfileRing ι))
    (hk : E.card < 2 * Fintype.card ι - 2)
    (hdetermine : ∀ a b : ι → ℂ,
      (∀ p ∈ E, eval (matchingProduct a b) p = eval (matchingProduct w.a w.b) p) →
      (∀ q ∈ w.contacts, matchingProduct a b w.pivot - matchingProduct a b q =
        matchingProduct w.a w.b w.pivot - matchingProduct w.a w.b q) ∧
      matchingProfileDetGap U w.η w.pivot (matchingProduct a b) =
        matchingProfileDetGap U w.η w.pivot (matchingProduct w.a w.b)) :
    ∃ v : StrictMatchingSupport U, w.contacts ⊂ v.contacts ∧ w.PreservesContactData v ∧
      ∀ p ∈ E, eval (matchingProduct v.a v.b) p = eval (matchingProduct w.a w.b) p := by
  classical
  letI : Nontrivial ι := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  let R := ProfileRing ι
  let I := profileIdeal ι
  let B := R ⧸ I
  let z := matchingProduct w.a w.b
  have hz : z ∈ zeroLocus I := (profileIdeal_exact (ι := ι)) ▸ ⟨w.a, w.b, rfl⟩
  letI : I.IsPrime := profileIdeal_prime
  letI : Algebra.FiniteType ℂ B := Algebra.FiniteType.of_surjective inferInstance (Ideal.Quotient.mkₐ ℂ I)
    (Ideal.Quotient.mkₐ_surjective _ _)
  obtain ⟨d, f, hfi, hf⟩ := exists_finite_inj_algHom_of_fg ℂ B
  have hd := profile_normalization_lower_bound f hf
  let pinned (p : R) : R := p - C (eval z p)
  let cuts := E.image pinned
  have hcuts (p : R) (hp : p ∈ cuts) : eval z p = 0 := by
    obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp hp
    simp [pinned]
  obtain ⟨Q, hIQ, hQz, hQprime, hmem, F, hF, hFi, t, ht⟩ :=
    exists_finite_curve_at_prime_affine_after_equations I f hf hfi ⟨z, hz⟩ cuts hcuts
      (Finset.card_image_le.trans_lt (hk.trans_le hd))
  letI : Q.IsPrime := hQprime
  let z₀ : zeroLocus Q := ⟨z, fun p hp => hQz hp⟩
  letI : Infinite (zeroLocus Q) := Infinite.of_surjective _
    (surjective_finite_affine_projection Q F hF hFi t ht)
  have heval (x : Equiv.Perm ι → ℂ) : (fun q => eval x (X q)) = x := by
    funext q
    exact eval_X q
  have hexact (y : zeroLocus Q) : ∃ a b : ι → ℂ, matchingProduct a b = y.val := by
    have hy : y.val ∈ zeroLocus I := fun p hp => y.property p (hIQ hp)
    rwa [← profileIdeal_exact] at hy
  have hpin (y : zeroLocus Q) (p : R) (hp : p ∈ E) : eval y.val p = eval z p := by
    have he := y.property _ (hmem _ (Finset.mem_image_of_mem pinned hp))
    simpa only [pinned, map_sub, eval_C, sub_eq_zero] using he
  have hfixed (y : zeroLocus Q) :
      (∀ q ∈ w.contacts, y.val w.pivot - y.val q = z w.pivot - z q) ∧
      matchingProfileDetGap U w.η w.pivot y.val = matchingProfileDetGap U w.η w.pivot z := by
    obtain ⟨a,b,hab⟩ := hexact y
    rw [← hab]
    exact hdetermine a b (fun p hp => hab ▸ hpin y p hp)
  obtain ⟨v, hη, hp, hv, y, hy⟩ := w.exists_more_contacts_on_infinite_affine_curve
    hU Q F hF hFi t ht X z₀ (heval _)
    (fun y => by simpa only [eval_X] using hexact y)
    (fun y q hq => by simpa only [eval_X] using (hfixed y).1 q hq)
    (fun y => by simpa only [eval_X] using (hfixed y).2)
    (by simpa only [eval_X] using Set.infinite_range_of_injective (f := Subtype.val) Subtype.val_injective)
  rw [heval] at hy
  refine ⟨v, hv, ⟨hη, hp, hv.subset, ?_, ?_⟩, ?_⟩
  · intro q hq
    rw [hp, hy]
    exact (hfixed y).1 q hq
  · rw [hη, hp, hy]
    exact (hfixed y).2
  · intro p hp
    rw [hy]
    exact hpin y p hp

/-- One can pin extra complex polynomial observables along the same curve.
Each observable spends at most one dimension, even at a zero-bearing profile. -/
theorem global_contact_transfer_with_observables {U : Matrix ι ι ℂ} (hU : IsUnitary U)
    (w : StrictMatchingSupport U) (observables : Finset (ProfileRing ι))
    (hk : w.contacts.card + observables.card < 2 * Fintype.card ι - 2) :
    ∃ v : StrictMatchingSupport U, w.contacts ⊂ v.contacts ∧ w.PreservesContactData v ∧
      ∀ p ∈ observables, eval (matchingProduct v.a v.b) p =
        eval (matchingProduct w.a w.b) p := by
  classical
  let contact (q : Equiv.Perm ι) : ProfileRing ι := X w.pivot - X q
  let gap : ProfileRing ι := ∑ q, C (realSignedWeight U q : ℂ) *
    (C w.η * (X q - X w.pivot))
  let old := insert gap ((w.contacts.erase w.pivot).image contact)
  let E := old ∪ observables
  have hbudget : E.card < 2 * Fintype.card ι - 2 := by
    have hp : w.pivot ∈ w.contacts := by simp [StrictMatchingSupport.contacts]
    have hkpos := Finset.card_pos.mpr ⟨w.pivot, hp⟩
    have he := Finset.card_erase_of_mem hp
    have hin := Finset.card_image_le (f := contact) (s := w.contacts.erase w.pivot)
    have hE := Finset.card_insert_le gap ((w.contacts.erase w.pivot).image contact)
    have hU := Finset.card_union_le old observables
    change old.card ≤ _ at hE
    change E.card ≤ _ at hU
    omega
  obtain ⟨v, hv, hdata, hobs⟩ :=
    global_contact_transfer_of_controlling_observables hU w E hbudget (by
      intro a b h
      constructor
      · intro q hq
        by_cases he : q = w.pivot
        · simp [he]
        have hm : contact q ∈ E := Finset.mem_union_left _
          (Finset.mem_insert_of_mem (Finset.mem_image_of_mem contact (Finset.mem_erase.mpr ⟨he, hq⟩)))
        simpa only [contact, map_sub, eval_X] using h _ hm
      · have hg : gap ∈ E := Finset.mem_union_left _ (Finset.mem_insert_self ..)
        simpa only [gap, matchingProfileDetGap, map_sum, map_mul, map_sub, eval_C, eval_X]
          using h _ hg)
  exact ⟨v, hv, hdata, fun p hp => hobs p (Finset.mem_union_right _ hp)⟩

/-- No auxiliary constraint is needed to reach the full contact threshold. -/
theorem global_contact_transfer {U : Matrix ι ι ℂ} (hU : IsUnitary U)
    (w : StrictMatchingSupport U) (hk : w.contacts.card < 2 * Fintype.card ι - 2) :
    ∃ v : StrictMatchingSupport U, w.contacts ⊂ v.contacts ∧ w.PreservesContactData v := by
  obtain ⟨v, hv, hdata, _⟩ := global_contact_transfer_with_observables hU w ∅ (by simpa using hk)
  exact ⟨v, hv, hdata⟩

/-- Iterate while keeping a fixed list of observables. Pinning $m$
polynomials gives at least $2n-2-m$ contacts, without any genericity premise. -/
theorem global_reaches_contact_threshold_with_observables {U : Matrix ι ι ℂ}
    (hU : IsUnitary U) (w : StrictMatchingSupport U) (observables : Finset (ProfileRing ι)) :
    ∃ v : StrictMatchingSupport U, 2 * Fintype.card ι - 2 ≤ v.contacts.card + observables.card ∧
      w.PreservesContactData v ∧ ∀ p ∈ observables, eval (matchingProduct v.a v.b) p =
        eval (matchingProduct w.a w.b) p := by
  let k := 2 * Fintype.card ι - 2
  have step (d : ℕ) (u : StrictMatchingSupport U)
      (hd : k - (u.contacts.card + observables.card) = d) :
      ∃ v : StrictMatchingSupport U, k ≤ v.contacts.card + observables.card ∧
        u.PreservesContactData v ∧ ∀ p ∈ observables, eval (matchingProduct v.a v.b) p =
          eval (matchingProduct u.a u.b) p := by
    induction d using Nat.strong_induction_on generalizing u with
    | h d ih =>
      by_cases hk : k ≤ u.contacts.card + observables.card
      · exact ⟨u, hk, .refl u, fun _ _ => rfl⟩
      · obtain ⟨u', hlt, hdata, hobs⟩ :=
          global_contact_transfer_with_observables hU u observables (Nat.lt_of_not_ge hk)
        have hcard := Finset.card_lt_card hlt
        obtain ⟨v, hv, huv, hfixed⟩ :=
          ih (k - (u'.contacts.card + observables.card)) (by omega) u' rfl
        exact ⟨v, hv, hdata.trans huv, fun p hp => (hfixed p hp).trans (hobs p hp)⟩
  exact step _ w rfl

/-- Starting from any strict witness, reach at least $2n-2$ contacts
without changing the mixer, direction, pivot, fixed complex gap, or
the old complex differences. No nonzero-profile premise is imposed. -/
theorem global_reaches_contact_threshold {U : Matrix ι ι ℂ} (hU : IsUnitary U)
    (w : StrictMatchingSupport U) :
    ∃ v : StrictMatchingSupport U, 2 * Fintype.card ι - 2 ≤ v.contacts.card ∧
      w.PreservesContactData v := by
  obtain ⟨v, hv, hdata, _⟩ := global_reaches_contact_threshold_with_observables hU w ∅
  exact ⟨v, by simpa using hv, hdata⟩

/-- Terminal support on the full exact profile locus is equivalent to MOC. -/
theorem conjecture_iff_global_contact_bound :
    Conjecture ι ↔ ¬ ∃ (U : Matrix ι ι ℂ), IsUnitary U ∧
      ∃ w : StrictMatchingSupport U, 2 * Fintype.card ι - 2 ≤ w.contacts.card := by
  constructor
  · rintro h ⟨U, hU, w, -⟩
    obtain ⟨q, hq⟩ := ((holds_iff_directional _ _ _).mp (h w.a w.b U hU)) w.η
    exact (not_lt_of_ge (hq.trans (w.maximal q))) w.strict
  · intro h a b U hU
    classical
    by_contra hh
    rw [holds_iff_directional, not_forall] at hh
    obtain ⟨η, hη⟩ := hh
    push_neg at hη
    obtain ⟨p, _, hp⟩ := Finset.exists_max_image Finset.univ
      (fun q : Equiv.Perm ι => (η * matchingProduct a b q).re)
      ⟨1, Finset.mem_univ _⟩
    let w : StrictMatchingSupport U := ⟨a, b, η, p, fun q => hp q (Finset.mem_univ _), hη p⟩
    obtain ⟨v, hv, _⟩ := global_reaches_contact_threshold hU w
    exact h ⟨U, hU, v, hv⟩

end
end MOC
