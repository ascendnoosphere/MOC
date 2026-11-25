import MOC.AffineGapCover
import MOC.ContactFibreIsolation

/-! The varying-gap transfer spends all remaining affine dimensions on
independent contact differences, not on the determinant gap. -/

open Matrix MvPolynomial

namespace MOC

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A strict witness that already maximizes contact count for its mixer
has at least $2n-2$ independent contact-difference functions on the
exact profile locus. This is not a statement about a Jacobian rank. -/
theorem StrictMatchingSupport.sharp_contact_rank_of_maximal_count
    {U : Matrix ι ι ℂ} (hU : IsUnitary U) (w : StrictMatchingSupport U)
    (hmax : ∀ v : StrictMatchingSupport U, v.contacts.card ≤ w.contacts.card) :
    2 * Fintype.card ι - 2 ≤ Module.finrank ℂ (contactDifferenceSpan w.pivot w.contacts) := by
  classical
  let r := w.pivot
  let I : Set (((ι → ℂ) × (ι → ℂ)) → ℂ) := contactDifference r '' (w.contacts : Set _)
  letI : Module.Finite ℂ (Submodule.span ℂ I) :=
    Module.Finite.span_of_finite ℂ (w.contacts.finite_toSet.image _)
  obtain ⟨T, hT, hcard, hspan, _⟩ := Submodule.exists_finset_span_eq_linearIndepOn ℂ I
  have hpre (f : T) : ∃ q : Equiv.Perm ι, contactDifference r q = f.val := by
    obtain ⟨q, _, hq⟩ := hT f.property
    exact ⟨q, hq⟩
  choose q hq using hpre
  let pin (f : T) : ProfileRing ι := X r - X (q f)
  let E : Finset (ProfileRing ι) := T.attach.image pin
  have hEq (a b : ι → ℂ)
      (he : ∀ p ∈ E, eval (matchingProduct a b) p = eval (matchingProduct w.a w.b) p) :
      ∀ j ∈ w.contacts, matchingProduct a b r - matchingProduct a b j =
        matchingProduct w.a w.b r - matchingProduct w.a w.b j := by
    intro j hj
    let D : (((ι → ℂ) × (ι → ℂ)) → ℂ) →ₗ[ℂ] ℂ :=
      (LinearMap.proj (a,b) : (((ι → ℂ) × (ι → ℂ)) → ℂ) →ₗ[ℂ] ℂ) -
        LinearMap.proj (w.a,w.b)
    have hker : Submodule.span ℂ (T : Set _) ≤ LinearMap.ker D := by
      rw [Submodule.span_le]
      intro f hf
      let f' : T := ⟨f, hf⟩
      have hh := he (pin f') (Finset.mem_image_of_mem pin (Finset.mem_attach T f'))
      change f'.val ∈ LinearMap.ker D
      rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.proj_apply,
        LinearMap.proj_apply, sub_eq_zero, ← hq f']
      simpa only [pin, map_sub, eval_X, contactDifference] using hh
    have hm : contactDifference r j ∈ Submodule.span ℂ (T : Set _) := by
      rw [hspan]
      exact Submodule.subset_span ⟨j,hj,rfl⟩
    exact sub_eq_zero.mp (hker hm)
  apply le_of_not_gt
  intro h
  have him : E.card ≤ T.card := by simpa [E] using
    (Finset.card_image_le (f := pin) (s := T.attach))
  have hh : E.card < 2 * Fintype.card ι - 2 := him.trans_lt (hcard ▸ h)
  obtain ⟨v,_,_,hv,_⟩ :=
    global_varying_gap_transfer_of_controlling_observables
      (affineGapContinuation (Equiv.Perm ι)) hU w E hh hEq
  exact (not_lt_of_ge (hmax v)) (Finset.card_lt_card hv)

/-- The full conjecture has a terminal formulation in terms of the
rank of the exact contact functions, rather than contact count alone. -/
theorem conjecture_iff_sharp_contact_rank_bound :
    Conjecture ι ↔ ¬ ∃ (U : Matrix ι ι ℂ), IsUnitary U ∧
      ∃ w : StrictMatchingSupport U,
        2 * Fintype.card ι - 2 ≤ Module.finrank ℂ (contactDifferenceSpan w.pivot w.contacts) := by
  constructor
  · rintro h ⟨U,hU,w,-⟩
    obtain ⟨q,hq⟩ := (holds_iff_directional _ _ _).mp (h w.a w.b U hU) w.η
    exact (not_lt_of_ge (hq.trans (w.maximal q))) w.strict
  · intro h
    apply conjecture_iff_sharp_terminal_contact_bound.mpr
    rintro ⟨U,hU,w,-⟩
    obtain ⟨V,hV,v,_,hmax⟩ := exists_globally_maximal_contact_count hU w
    exact h ⟨V,hV,v,v.sharp_contact_rank_of_maximal_count hV (hmax V hV)⟩

/-- The sharp count and rank can be imposed on the same balanced,
moment-tested, fixed-gap-isolated orbit maximum. -/
theorem conjecture_iff_sharp_isolated_rank_moment_contact_bound [Nonempty ι] :
    Conjecture ι ↔ ¬ ∃ (U : Matrix ι ι ℂ), IsUnitary U ∧ ∃ v : StrictMatchingSupport U,
      2 * Fintype.card ι - 1 ≤ v.contacts.card ∧
      2 * Fintype.card ι - 2 ≤ Module.finrank ℂ (contactDifferenceSpan v.pivot v.contacts) ∧
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
  constructor
  · rintro h ⟨U,hU,v,-⟩
    obtain ⟨q,hq⟩ := ((holds_iff_directional _ _ _).mp (h v.a v.b U hU)) v.η
    exact (not_lt_of_ge (hq.trans (v.maximal q))) v.strict
  · intro h
    apply conjecture_iff_isolated_rank_moment_contact_bound.mpr
    rintro ⟨U,hU,v,_,_,he,hη,ht,hc,hn,hopt,hm,hmax,hi⟩
    have hr := v.sharp_contact_rank_of_maximal_count hU (hmax U hU)
    have hcard := v.contactDifferenceRank_le
    have hp : v.pivot ∈ v.contacts := by simp [StrictMatchingSupport.contacts]
    have hpos := Finset.card_pos.mpr ⟨v.pivot,hp⟩
    exact h ⟨U,hU,v,by omega,hr,he,hη,ht,hc,hn,hopt,hm,hmax,hi⟩

end MOC
