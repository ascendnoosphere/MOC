import MOC.GlobalContactSlice
import MOC.HalfPlaneContactTransfer

/-! The sharpened terminal contact reduction. Its explicit remaining
input is a positive-path half-plane sheet for a varying polynomial
coordinate of a prime finite complex affine curve. For the
fixed-gap contact strategy, see Zheng (preprint DOI:
10.13140/RG.2.2.36790.25923). -/

open Matrix MvPolynomial Set
open scoped BigOperators

namespace MOC

/-- The precise affine continuation input for the sharpened contact
threshold. The connected set is in the positive real gap locus and
contains the half-plane sheet. Its closure contains the starting point. -/
def AffineGapContinuation (σ : Type*) [Fintype σ] : Prop :=
  ∀ (Q : Ideal (MvPolynomial σ ℂ)) [Q.IsPrime]
    (f : Polynomial ℂ →ₐ[ℂ] (MvPolynomial σ ℂ ⧸ Q)), f.Finite → Function.Injective f →
    ∀ (t g : MvPolynomial σ ℂ), Ideal.Quotient.mk Q t = f Polynomial.X →
    (∃ x y : zeroLocus Q, eval x.val g ≠ eval y.val g) →
    ∀ x₀ : zeroLocus Q, 0 < (eval x₀.val g).re →
    ∃ (S : Set (zeroLocus Q)) (s : ℂ → zeroLocus Q) (c : ℝ),
      x₀ ∈ closure S ∧ IsPreconnected S ∧
      (∀ x ∈ S, 0 < (eval x.val g).re) ∧
      (∀ z, 0 < z.re → s z ∈ S) ∧
      (∀ z, 0 < z.re → eval (s z).val g = z + c) ∧
      ∀ i : σ, DifferentiableOn ℂ (fun z => (s z).val i) {z | 0 < z.re}

noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Pin polynomial observables determining the old complex differences,
but do not spend an extra equation on the gap. -/
theorem global_varying_gap_transfer_of_controlling_observables
    (hcont : AffineGapContinuation (Equiv.Perm ι))
    {U : Matrix ι ι ℂ} (hU : IsUnitary U) (w : StrictMatchingSupport U)
    (E : Finset (ProfileRing ι)) (hk : E.card < 2 * Fintype.card ι - 2)
    (hdetermine : ∀ a b : ι → ℂ,
      (∀ p ∈ E, eval (matchingProduct a b) p = eval (matchingProduct w.a w.b) p) →
      ∀ q ∈ w.contacts, matchingProduct a b w.pivot - matchingProduct a b q =
        matchingProduct w.a w.b w.pivot - matchingProduct w.a w.b q) :
    ∃ v : StrictMatchingSupport U, v.η = w.η ∧ v.pivot = w.pivot ∧
      w.contacts ⊂ v.contacts ∧
      ∀ q ∈ w.contacts, matchingProduct v.a v.b v.pivot - matchingProduct v.a v.b q =
        matchingProduct w.a w.b w.pivot - matchingProduct w.a w.b q := by
  classical
  let p := matchingProduct w.a w.b
  have hz : p ∈ zeroLocus (profileIdeal ι) := (profileIdeal_exact (ι := ι)) ▸ ⟨w.a,w.b,rfl⟩
  obtain ⟨Q, hIQ, hpQ, hQ, hpin, F, hF, hFi, t, ht⟩ :=
    exists_prime_profile_curve_fixing_observables p hz E hk
  letI : Q.IsPrime := hQ
  let x₀ : zeroLocus Q := ⟨p,hpQ⟩
  let G (r : Equiv.Perm ι → ℂ) := matchingProfileDetGap U w.η w.pivot r
  let g : ProfileRing ι := ∑ q, C (realSignedWeight U q : ℂ) *
    (C w.η * (X q - X w.pivot))
  have hGe (y : zeroLocus Q) : eval y.val g = G y.val := by
    simp only [g, G, matchingProfileDetGap, map_sum, map_mul, map_sub, eval_X, eval_C]
  have hG₀ : 0 < (G p).re := by
    dsimp only [G, p]
    rw [matchingProfileDetGap_matchingProduct _ _ _ hU, mul_sub, Complex.sub_re]
    exact sub_pos.mpr w.strict
  have heval (y : zeroLocus Q) : (fun q => eval y.val (X q)) = y.val :=
    funext fun q => eval_X q
  have hexact (y : zeroLocus Q) : ∃ a b : ι → ℂ, matchingProduct a b = y.val := by
    have hy : y.val ∈ zeroLocus (profileIdeal ι) := fun q hq => y.property q (hIQ hq)
    rwa [← profileIdeal_exact] at hy
  have hold (y : zeroLocus Q) (q : Equiv.Perm ι) (hq : q ∈ w.contacts) :
      y.val w.pivot - y.val q = p w.pivot - p q := by
    obtain ⟨a,b,hab⟩ := hexact y
    rw [← hab]
    exact hdetermine a b (by simpa only [hab] using hpin y) q hq
  by_cases hvar : ∃ x y : zeroLocus Q, eval x.val g ≠ eval y.val g
  · obtain ⟨S,s,c,hstart,hconn,hpos,hs,hsG,hhol⟩ :=
      hcont Q F hF hFi t g ht hvar x₀ (by rw [hGe]; exact hG₀)
    let A : Set (zeroLocus Q) := insert x₀ S
    have hA : IsPreconnected A :=
      hconn.subset_closure (Set.subset_insert _ _) (insert_subset hstart subset_closure)
    have hAc (y : zeroLocus Q) (hy : y ∈ A) : 0 < (G y.val).re := by
      rcases hy with hy | hy
      · simpa only [hy] using hG₀
      · rw [← hGe]
        exact hpos y hy
    letI : Nonempty ι := Fintype.card_pos_iff.mp (by
      omega)
    exact w.exists_more_contacts_of_halfPlane_sheet hU hA Subtype.val (fun y _ => hexact y)
      (fun q => by
        have h (j : Equiv.Perm ι) := (continuous_apply j).comp
          (continuous_subtype_val : Continuous (Subtype.val : zeroLocus Q → _))
        exact (Complex.continuous_re.comp (continuous_const.mul ((h w.pivot).sub (h q)))).continuousOn)
      (Set.mem_insert _ _) rfl (fun y _ => hold y) hAc s c (fun z hz => Or.inr (hs z hz)) hhol
      (fun z hz => (hGe (s z)).symm.trans (hsG z hz))
  · letI : Infinite (zeroLocus Q) := Infinite.of_surjective _
      (surjective_finite_affine_projection Q F hF hFi t ht)
    have heq (y : zeroLocus Q) : G y.val = G p := by
      rw [← hGe y, ← show eval x₀.val g = G p from hGe x₀]
      exact not_not.mp (fun h => hvar ⟨y,x₀,h⟩)
    obtain ⟨v, hη, hpr, hlt, y, hy⟩ :=
      w.exists_more_contacts_on_infinite_affine_curve hU Q F hF hFi t ht X x₀ (heval _)
      (fun y => by simpa only [eval_X] using hexact y)
      (fun y q hq => by simpa only [eval_X] using hold y q hq)
      (fun y => by simpa only [eval_X] using heq y)
      (by simpa only [eval_X] using Set.infinite_range_of_injective (f := Subtype.val) Subtype.val_injective)
    rw [heval] at hy
    exact ⟨v,hη,hpr,hlt,fun q hq => by rw [hpr,hy]; exact hold y q hq⟩

/-- With varying-gap continuation as the only additional input, pinning
the old differences uses no equation for the determinant gap. -/
theorem global_varying_gap_contact_transfer
    (hcont : AffineGapContinuation (Equiv.Perm ι))
    {U : Matrix ι ι ℂ} (hU : IsUnitary U) (w : StrictMatchingSupport U)
    (hk : w.contacts.card ≤ 2 * Fintype.card ι - 2) :
    ∃ v : StrictMatchingSupport U, v.η = w.η ∧ v.pivot = w.pivot ∧
      w.contacts ⊂ v.contacts ∧
      ∀ q ∈ w.contacts, matchingProduct v.a v.b v.pivot - matchingProduct v.a v.b q =
        matchingProduct w.a w.b w.pivot - matchingProduct w.a w.b q := by
  classical
  let contact (q : Equiv.Perm ι) : ProfileRing ι := X w.pivot - X q
  let E := (w.contacts.erase w.pivot).image contact
  have hp : w.pivot ∈ w.contacts := by simp [StrictMatchingSupport.contacts]
  have hx : E.card < 2 * Fintype.card ι - 2 := by
    have h := Finset.card_image_le (f := contact) (s := w.contacts.erase w.pivot)
    rw [Finset.card_erase_of_mem hp] at h
    exact h.trans_lt (by have := Finset.card_pos.mpr ⟨w.pivot,hp⟩; omega)
  apply global_varying_gap_transfer_of_controlling_observables hcont hU w E hx
  intro a b h q hq
  by_cases he : q = w.pivot
  · simp [he]
  · simpa only [contact, map_sub, eval_X] using
      h (contact q) (Finset.mem_image_of_mem contact (Finset.mem_erase.mpr ⟨he,hq⟩))

/-- The extra contact is counted in every finite order once the affine
continuation input has been instantiated. No simple-spectrum premise is
needed for the reduction. -/
theorem conjecture_iff_varying_gap_terminal
    (hcont : AffineGapContinuation (Equiv.Perm ι)) :
    Conjecture ι ↔ ¬ ∃ (U : Matrix ι ι ℂ), IsUnitary U ∧
      ∃ w : StrictMatchingSupport U, 2 * Fintype.card ι - 1 ≤ w.contacts.card := by
  constructor
  · rintro h ⟨U, hU, w, -⟩
    exact w.not_holds (h w.a w.b U hU)
  · intro h a b U hU
    classical
    by_contra hh
    obtain ⟨w⟩ := nonempty_strictMatchingSupport_of_failure a b hh
    let k := 2 * Fintype.card ι - 1
    obtain ⟨v, hv⟩ := exists_strictMatchingSupport_at_least k w (fun u hu => by
      have hbound : u.contacts.card ≤ 2 * Fintype.card ι - 2 := by
        simpa only [k, Nat.sub_sub] using Nat.le_sub_one_of_lt hu
      obtain ⟨v, _, _, hinc, _⟩ := global_varying_gap_contact_transfer hcont hU u hbound
      exact ⟨v, Finset.card_lt_card hinc⟩)
    exact h ⟨U, hU, v, hv⟩

end
end MOC
