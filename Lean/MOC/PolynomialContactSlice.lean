import MOC.PolynomialContactChart
import MOC.PolynomialEvaluationHeight
import MOC.AffineContactCurve
import MOC.ContactChartIteration

/-! Polynomial contact constraints and their pinned positive-dimensional
prime slice. The reciprocal equation keeps every point in the exact chart. -/

open Finset Matrix MvPolynomial
open scoped BigOperators

namespace MOC.PolynomialContactChart

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

abbrev LocalPoly (o i₀ : ι) := MvPolynomial (VarLocalized o i₀) ℂ
abbrev LocalPoint (o i₀ : ι) := VarLocalized o i₀ → ℂ

def liftedProfile (o i₀ : ι) (q : Equiv.Perm ι) : LocalPoly o i₀ :=
  rename Sum.inr (profilePolynomial o i₀ q)

def localProfile (o i₀ : ι) (z : LocalPoint o i₀) (q : Equiv.Perm ι) : ℂ :=
  eval z (liftedProfile o i₀ q)

theorem localProfile_evaluation (o i₀ : ι) (z : LocalPoint o i₀) (q : Equiv.Perm ι) :
    localProfile o i₀ z q = profile o i₀ (fun k => z (.inr k)) q := by
  simp [localProfile, liftedProfile, profile, eval_rename, Function.comp_def]

@[simp] theorem eval_liftedProfile (o i₀ : ι) (z : LocalPoint o i₀) (q : Equiv.Perm ι) :
    eval z (liftedProfile o i₀ q) = localProfile o i₀ z q := rfl

def contactEquation (o i₀ : ι) {U : Matrix ι ι ℂ} (w : StrictMatchingSupport U)
    (q : Equiv.Perm ι) : LocalPoly o i₀ :=
  liftedProfile o i₀ w.pivot - liftedProfile o i₀ q -
    C (matchingProduct w.a w.b w.pivot - matchingProduct w.a w.b q)

def gapEquation (o i₀ : ι) {U : Matrix ι ι ℂ} (w : StrictMatchingSupport U) : LocalPoly o i₀ :=
  (∑ q, C (realSignedWeight U q : ℂ) *
    (C w.η * (liftedProfile o i₀ q - liftedProfile o i₀ w.pivot))) -
    C (matchingProfileDetGap U w.η w.pivot (matchingProduct w.a w.b))

def equations (o i₀ j₀ : ι) {U : Matrix ι ι ℂ} (w : StrictMatchingSupport U) :
    Finset (LocalPoly o i₀) := by
  classical
  exact insert (inverseEquation o i₀ j₀) (insert (gapEquation o i₀ w)
    ((w.contacts.erase w.pivot).image (contactEquation o i₀ w)))

theorem pivot_mem_contacts {U : Matrix ι ι ℂ} (w : StrictMatchingSupport U) :
    w.pivot ∈ w.contacts := by
  classical
  simp [StrictMatchingSupport.contacts]

/-- Erase the tautological pivot contact. There are at most k+1
equations for k contacts, including the gap and reciprocal equations. -/
theorem equations_card_le (o i₀ j₀ : ι) {U : Matrix ι ι ℂ} (w : StrictMatchingSupport U) :
    (equations o i₀ j₀ w).card ≤ w.contacts.card + 1 := by
  classical
  unfold equations
  have he := Finset.card_erase_of_mem (pivot_mem_contacts w)
  have hI := Finset.card_image_le (s := w.contacts.erase w.pivot)
    (f := contactEquation o i₀ w)
  have h₁ := Finset.card_insert_le (gapEquation o i₀ w)
    ((w.contacts.erase w.pivot).image (contactEquation o i₀ w))
  have h₂ := Finset.card_insert_le (inverseEquation o i₀ j₀)
    (insert (gapEquation o i₀ w) ((w.contacts.erase w.pivot).image (contactEquation o i₀ w)))
  have hn : 0 < w.contacts.card := Finset.card_pos.mpr ⟨w.pivot, pivot_mem_contacts w⟩
  omega

theorem inverse_mem_equations (o i₀ j₀ : ι) {U : Matrix ι ι ℂ}
    (w : StrictMatchingSupport U) : inverseEquation o i₀ j₀ ∈ equations o i₀ j₀ w := by
  classical
  simp [equations]

theorem gap_mem_equations (o i₀ j₀ : ι) {U : Matrix ι ι ℂ}
    (w : StrictMatchingSupport U) : gapEquation o i₀ w ∈ equations o i₀ j₀ w := by
  classical
  simp [equations]

/-- All old contact equations lie in the generated ideal, including
the identically zero one at the erased pivot. -/
theorem contact_mem_of_span_le (o i₀ j₀ : ι) {U : Matrix ι ι ℂ}
    (w : StrictMatchingSupport U) (Q : Ideal (LocalPoly o i₀))
    (hQ : Ideal.span (equations o i₀ j₀ w : Set (LocalPoly o i₀)) ≤ Q)
    (q : Equiv.Perm ι) (hq : q ∈ w.contacts) : contactEquation o i₀ w q ∈ Q := by
  classical
  by_cases h : q = w.pivot
  · subst q
    simp [contactEquation]
  · apply hQ
    apply Ideal.subset_span
    show contactEquation o i₀ w q ∈ equations o i₀ j₀ w
    unfold equations
    exact mem_insert_of_mem (mem_insert_of_mem (mem_image.mpr ⟨q, mem_erase.mpr ⟨h,hq⟩, rfl⟩))

/-- The polynomial evaluation-height step supplies a positive-dimensional
prime through the given chart point, containing the exact equations. -/
theorem exists_prime_contact_slice {o i₀ j₀ : ι} (hi : i₀ ≠ o)
    {U : Matrix ι ι ℂ} (w : StrictMatchingSupport U)
    (z : LocalPoint o i₀) (hbase : localProfile o i₀ z = matchingProduct w.a w.b)
    (hinv : eval z (inverseEquation o i₀ j₀) = 0)
    (hk : w.contacts.card < 2 * Fintype.card ι - 2) :
    ∃ Q : PrimeSpectrum (LocalPoly o i₀),
      Q.asIdeal < RingHom.ker (eval z) ∧
        Ideal.span (equations o i₀ j₀ w : Set (LocalPoly o i₀)) ≤ Q.asIdeal := by
  classical
  apply exists_prime_lt_polynomial_eval_of_few_equations z (equations o i₀ j₀ w)
  · intro p hp
    unfold equations at hp
    rcases mem_insert.mp hp with h | hp
    · rwa [h]
    rcases mem_insert.mp hp with h | hp
    · rw [h]
      simp only [gapEquation, map_sub, map_sum, map_mul, eval_C,
        eval_liftedProfile, hbase, matchingProfileDetGap, sub_self]
    · obtain ⟨q, _, rfl⟩ := mem_image.mp hp
      simp only [contactEquation, map_sub, eval_C, eval_liftedProfile, hbase, sub_self]
  · rw [card_varLocalized hi]
    have h := equations_card_le o i₀ j₀ w
    omega

/-- Any zero of the inverse polynomial evaluates to a genuine chart
point, and both pivot and all profile values are nonzero. -/
theorem permitted_of_inverse {o i₀ j₀ : ι} (z : LocalPoint o i₀)
    (h : eval z (inverseEquation o i₀ j₀) = 0) :
    colAt o i₀ (fun k => z (.inr k)) j₀ ≠ 0 ∧ ∀ q, localProfile o i₀ z q ≠ 0 := by
  let x : Point o i₀ := fun k => z (.inr k)
  have he : adjoin o i₀ x (z (.inl ())) = z := by
    funext k
    rcases k with (_|_) <;> rfl
  have hloc : eval x (localizer o i₀ j₀) ≠ 0 := by
    have h' := (inverseEquation_evaluation o i₀ j₀ x (z (.inl ()))).symm.trans (he ▸ h)
    intro hz
    simp [hz] at h'
  simpa only [localProfile_evaluation] using (eval_localizer_ne_zero_iff o i₀ j₀ x).mp hloc

theorem exists_spectra_on_inverse {o i₀ j₀ : ι} (z : LocalPoint o i₀)
    (h : eval z (inverseEquation o i₀ j₀) = 0) :
    ∃ a b : ι → ℂ, matchingProduct a b = localProfile o i₀ z := by
  have hn := (permitted_of_inverse z h).2
  simp_rw [localProfile_evaluation] at hn
  rw [show localProfile o i₀ z = profile o i₀ (fun k => z (.inr k)) from
    funext (localProfile_evaluation o i₀ z)]
  exact exists_spectra_on_nonzero o i₀ _ hn

/-- No two distinct points surviving the inverse equation have the
same matching profile, including their adjoined inverse coordinate. -/
theorem localProfile_injective_on_inverse {o i₀ j₀ : ι} (hi : i₀ ≠ o)
    {x y : LocalPoint o i₀}
    (hx : eval x (inverseEquation o i₀ j₀) = 0)
    (hy : eval y (inverseEquation o i₀ j₀) = 0)
    (h : localProfile o i₀ x = localProfile o i₀ y) : x = y := by
  let x' : Point o i₀ := fun k => x (.inr k)
  let y' : Point o i₀ := fun k => y (.inr k)
  obtain ⟨hc, hn⟩ := permitted_of_inverse x hx
  simp_rw [localProfile_evaluation] at hn
  have he : x' = y' := profile_injective_on_nonzero hi hc hn (by
    funext σ
    simpa only [localProfile_evaluation] using congrFun h σ)
  have hX : adjoin o i₀ x' (x (.inl ())) = x := by funext k; rcases k with (_|_) <;> rfl
  have hY : adjoin o i₀ y' (y (.inl ())) = y := by funext k; rcases k with (_|_) <;> rfl
  have h₁ : eval (adjoin o i₀ x' (x (.inl ()))) (inverseEquation o i₀ j₀) = 0 := hX ▸ hx
  have h₂ : eval (adjoin o i₀ x' (y (.inl ()))) (inverseEquation o i₀ j₀) = 0 := by rw [he, hY, hy]
  have hL := (eval_localizer_ne_zero_iff o i₀ j₀ x').mpr ⟨hc, hn⟩
  simp only [inverseEquation_evaluation, sub_eq_zero] at h₁ h₂
  have hi' := mul_right_cancel₀ hL (h₁.trans h₂.symm)
  rw [← hX, ← hY, hi', he]


/-- A strict support witness with nonzero vertices admits a pinned
polynomial chart point and a positive-dimensional prime below its
evaluation ideal whenever the contact budget permits. -/
theorem exists_initial_prime_contact_slice {U : Matrix ι ι ℂ} (hU : IsUnitary U)
    (w : StrictMatchingSupport U) (o : ι)
    (hnz : ∀ q, matchingProduct w.a w.b q ≠ 0)
    (hk : w.contacts.card < 2 * Fintype.card ι - 2) :
    ∃ (i₀ j₀ : ι) (z : LocalPoint o i₀) (Q : PrimeSpectrum (LocalPoly o i₀)),
      i₀ ≠ o ∧ localProfile o i₀ z = matchingProduct w.a w.b ∧
      Q.asIdeal < RingHom.ker (eval z) ∧
      Ideal.span (equations o i₀ j₀ w : Set (LocalPoly o i₀)) ≤ Q.asIdeal := by
  obtain ⟨i₀, j₀, hi, x, hx, hb⟩ :=
    exists_point_of_nonconstant_profile o _ ⟨w.a, w.b, rfl⟩ hnz (w.profile_nonconstant hU)
  obtain ⟨r, hr, _⟩ := (existsUnique_inverseEquation_iff o i₀ j₀ x).mpr
    ⟨hx, fun q => congrFun hb q ▸ hnz q⟩
  let z := adjoin o i₀ x r
  have he : localProfile o i₀ z = matchingProduct w.a w.b := by
    funext q
    simpa [localProfile_evaluation, z, adjoin] using congrFun hb q
  obtain ⟨Q, hQ, hspan⟩ := exists_prime_contact_slice hi w z he hr hk
  exact ⟨i₀, j₀, z, Q, hi, he, hQ, hspan⟩

/-- Exact profile map on the zero locus of any ideal containing the
localized contact equations; this also applies to a smaller curve
cut inside the positive-dimensional prime slice. -/
theorem localProfile_on_slice {o i₀ j₀ : ι} (hi : i₀ ≠ o) {U : Matrix ι ι ℂ}
    (w : StrictMatchingSupport U) (Q : Ideal (LocalPoly o i₀))
    (hQ : Ideal.span (equations o i₀ j₀ w : Set (LocalPoly o i₀)) ≤ Q) :
    (∀ z : zeroLocus Q, ∃ a b : ι → ℂ, matchingProduct a b = localProfile o i₀ z.val) ∧
      Function.Injective (fun z : zeroLocus Q => localProfile o i₀ z.val) := by
  have hI : inverseEquation o i₀ j₀ ∈ Q := hQ (Ideal.subset_span (inverse_mem_equations o i₀ j₀ w))
  refine ⟨fun z => exists_spectra_on_inverse z.val (z.property _ hI), ?_⟩
  intro z y h
  exact Subtype.ext (localProfile_injective_on_inverse hi (z.property _ hI) (y.property _ hI) h)


/-- Once a prime finite curve through the pinned point is supplied
inside the localized slice, contact growth is unconditional on that
curve. Exactness and infinite profile image come from the chart. -/
theorem exists_more_contacts_on_localized_slice_of_finite_projection
    {o i₀ j₀ : ι} (hi : i₀ ≠ o) {U : Matrix ι ι ℂ} (hU : IsUnitary U)
    (w : StrictMatchingSupport U) (z : LocalPoint o i₀)
    (hbase : localProfile o i₀ z = matchingProduct w.a w.b)
    (Q : Ideal (LocalPoly o i₀)) [Q.IsPrime] (hpin : Q ≤ RingHom.ker (eval z))
    (hQ : Ideal.span (equations o i₀ j₀ w : Set (LocalPoly o i₀)) ≤ Q)
    (f : Polynomial ℂ →ₐ[ℂ] (LocalPoly o i₀ ⧸ Q))
    (hf : f.Finite) (hfi : Function.Injective f)
    (t : LocalPoly o i₀) (ht : Ideal.Quotient.mk Q t = f Polynomial.X) :
    ∃ w' : StrictMatchingSupport U, w.contacts ⊂ w'.contacts ∧
      ∃ y : zeroLocus Q, matchingProduct w'.a w'.b = localProfile o i₀ y.val := by
  let z₀ : zeroLocus Q := ⟨z, fun _ hp => hpin hp⟩
  obtain ⟨hex, hinj⟩ := localProfile_on_slice hi w Q hQ
  letI : Infinite (zeroLocus Q) := Infinite.of_surjective _
    (surjective_finite_affine_projection Q f hf hfi t ht)
  refine w.exists_more_contacts_on_affine_constraints hU Q f hf hfi t ht
    (liftedProfile o i₀) z₀ hbase hex ?_ ?_ (Set.infinite_range_of_injective hinj)
  · intro q hq
    have hp := congrFun hbase w.pivot
    have he := congrFun hbase q
    change eval z (liftedProfile o i₀ w.pivot) = _ at hp
    change eval z (liftedProfile o i₀ q) = _ at he
    change liftedProfile o i₀ w.pivot - liftedProfile o i₀ q -
      C (eval z (liftedProfile o i₀ w.pivot) - eval z (liftedProfile o i₀ q)) ∈ Q
    rw [hp, he]
    exact contact_mem_of_span_le o i₀ j₀ w Q hQ q hq
  · exact hQ (Ideal.subset_span (gap_mem_equations o i₀ j₀ w))

end

end MOC.PolynomialContactChart
