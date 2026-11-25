import MOC.FixedZeroProfiles
import MOC.GlobalContactSlice

/-! Relative fixed-gap contact transfer inside a prescribed entry-zero locus.
The dimension of that locus is an input, not inferred from the global one. -/

open MvPolynomial Set Matrix
open scoped BigOperators

namespace MOC

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

def markedZeroProfileIdeal (Z : ι → ι → Prop) : Ideal (ProfileRing ι) :=
  RingHom.ker (aeval (markedZeroProfileCoordinate Z))

instance markedZeroProfileIdeal_prime (Z : ι → ι → Prop) :
    (markedZeroProfileIdeal Z).IsPrime :=
  markedZeroProfileIdeal_isPrime Z

/-- Given a relative normalization, fewer equations than its number of
variables leave a prime curve inside the marked zero locus. Fixed zero
coordinates rule out translation without a translation-line theorem. -/
theorem fixed_zero_contact_transfer_of_controlling_observables
    {U : Matrix ι ι ℂ} (hU : IsUnitary U) (w : StrictMatchingSupport U)
    (Z : ι → ι → Prop) (hmark : ∃ i j, Z i j)
    (hZ₀ : ∀ i j, Z i j → w.a i + w.b j = 0)
    {d : ℕ} (f : MvPolynomial (Fin d) ℂ →ₐ[ℂ] (ProfileRing ι ⧸ markedZeroProfileIdeal Z))
    (hf : f.Finite) (hfi : Function.Injective f)
    (E : Finset (ProfileRing ι)) (hk : E.card < d)
    (hdetermine : ∀ a b : ι → ℂ, (∀ i j, Z i j → a i + b j = 0) →
      (∀ p ∈ E, eval (matchingProduct a b) p = eval (matchingProduct w.a w.b) p) →
      (∀ q ∈ w.contacts, matchingProduct a b w.pivot - matchingProduct a b q =
        matchingProduct w.a w.b w.pivot - matchingProduct w.a w.b q) ∧
      matchingProfileDetGap U w.η w.pivot (matchingProduct a b) =
        matchingProfileDetGap U w.η w.pivot (matchingProduct w.a w.b)) :
    ∃ v : StrictMatchingSupport U, w.contacts ⊂ v.contacts ∧ w.PreservesContactData v ∧
      (∀ p ∈ E, eval (matchingProduct v.a v.b) p = eval (matchingProduct w.a w.b) p) ∧
      (∀ i j, Z i j → v.a i + v.b j = 0) := by
  classical
  let p := matchingProduct w.a w.b
  let I := markedZeroProfileIdeal Z
  have hI : {q : Equiv.Perm ι → ℂ | ∃ a b : ι → ℂ,
      (∀ i j, Z i j → a i + b j = 0) ∧ matchingProduct a b = q} = zeroLocus I :=
    exact_matching_profiles_with_zeros_eq_prime_zeroLocus Z
  letI : I.IsPrime := markedZeroProfileIdeal_prime Z
  have hp : p ∈ zeroLocus I := hI ▸ ⟨w.a, w.b, hZ₀, rfl⟩
  let pinned (q : ProfileRing ι) : ProfileRing ι := q - C (eval p q)
  let cuts := E.image pinned
  have hcuts (q : ProfileRing ι) (hq : q ∈ cuts) : eval p q = 0 := by
    obtain ⟨q', _, rfl⟩ := Finset.mem_image.mp hq
    simp [pinned]
  obtain ⟨Q, hIQ, hQp, hQprime, hmem, F, hF, hFi, t, ht⟩ :=
    exists_finite_curve_at_prime_affine_after_equations I f hf hfi ⟨p, hp⟩ cuts hcuts
      (Finset.card_image_le.trans_lt hk)
  letI : Q.IsPrime := hQprime
  let p₀ : zeroLocus Q := ⟨p, hQp⟩
  letI : Infinite (zeroLocus Q) := Infinite.of_surjective _
    (surjective_finite_affine_projection Q F hF hFi t ht)
  have hpin (y : zeroLocus Q) (q : ProfileRing ι) (hq : q ∈ E) :
      eval y.val q = eval p q := by
    have he := y.property _ (hmem _ (Finset.mem_image_of_mem pinned hq))
    simpa only [pinned, map_sub, eval_C, sub_eq_zero] using he
  have heval (x : Equiv.Perm ι → ℂ) : (fun q => eval x (X q)) = x := funext fun q => eval_X q
  have hexact (y : zeroLocus Q) : ∃ a b : ι → ℂ,
      (∀ i j, Z i j → a i + b j = 0) ∧ matchingProduct a b = y.val := by
    have hy : y.val ∈ zeroLocus I := fun g hg => y.property _ (hIQ hg)
    rwa [← hI] at hy
  have hfixed (y : zeroLocus Q) :
      (∀ q ∈ w.contacts, y.val w.pivot - y.val q = p w.pivot - p q) ∧
      matchingProfileDetGap U w.η w.pivot y.val = matchingProfileDetGap U w.η w.pivot p := by
    obtain ⟨a, b, hZ, hab⟩ := hexact y
    rw [← hab]
    exact hdetermine a b hZ (fun q hq => hab ▸ hpin y q hq)
  have hη : w.η ≠ 0 := by
    intro h
    have hs := w.strict
    simp [h] at hs
  have hvar : ∃ q : Equiv.Perm ι, ∃ x y : zeroLocus Q,
      w.η * (x.val w.pivot - x.val q) ≠ w.η * (y.val w.pivot - y.val q) := by
    obtain ⟨i, j, hij⟩ := hmark
    let z := Equiv.swap j i
    have hz (y : zeroLocus Q) : y.val z = 0 := by
      obtain ⟨a, b, hZ, hab⟩ := hexact y
      rw [← hab]
      change matchingProduct a b (Equiv.swap j i) = 0
      unfold matchingProduct
      exact Finset.prod_eq_zero (Finset.mem_univ j)
        (by simpa only [Equiv.swap_apply_left] using hZ i j hij)
    by_contra! h
    have hsingle (y : zeroLocus Q) : y = p₀ := by
      apply Subtype.ext
      have he := mul_left_cancel₀ hη (h z y p₀)
      rw [hz y, hz p₀, sub_zero, sub_zero] at he
      funext q
      have hq := mul_left_cancel₀ hη (h q y p₀)
      rw [he] at hq
      exact (sub_right_inj.mp hq)
    letI : Subsingleton (zeroLocus Q) := ⟨fun x y => (hsingle x).trans (hsingle y).symm⟩
    exact not_finite (zeroLocus Q)
  have hgap₀ : 0 < (matchingProfileDetGap U w.η w.pivot p).re := by
    dsimp only [p]
    rw [matchingProfileDetGap_matchingProduct _ _ _ hU, mul_sub, Complex.sub_re]
    exact sub_pos.mpr w.strict
  obtain ⟨v, hηv, hpv, hv, y, hy⟩ := w.exists_more_contacts_on_affine_curve
    hU Q F hF hFi t ht X p₀ (heval _)
    (fun y => by
      obtain ⟨a, b, _, hab⟩ := hexact y
      exact ⟨a, b, hab.trans (heval _).symm⟩)
    (fun y q hq => by
      simp only [eval_X]
      rw [(hfixed y).1 q hq, mul_sub, Complex.sub_re, (Finset.mem_filter.mp hq).2, sub_self])
    (fun y => by simpa only [heval, (hfixed y).2] using hgap₀)
    (by simpa only [eval_X] using hvar)
  rw [heval] at hy
  obtain ⟨a, b, hZ, hab⟩ := hexact y
  have hprof : matchingProduct a b = matchingProduct v.a v.b := hab.trans hy.symm
  have hdet : determinantValue a b U = determinantValue v.a v.b U := by
    rw [← real_signed_determinant a b U hU, ← real_signed_determinant v.a v.b U hU, hprof]
  let v' : StrictMatchingSupport U := ⟨a, b, v.η, v.pivot,
    fun q => by simpa only [hprof] using v.maximal q,
    by simpa only [hprof, hdet] using v.strict⟩
  have hco : v'.contacts = v.contacts := by
    ext q
    simp only [StrictMatchingSupport.contacts, Finset.mem_filter, Finset.mem_univ, true_and]
    change (v.η * matchingProduct a b q).re = (v.η * matchingProduct a b v.pivot).re ↔ _
    rw [hprof]
  refine ⟨v', hco ▸ hv, ⟨hηv, hpv, hco ▸ hv.subset, ?_, ?_⟩, ?_, hZ⟩
  · intro q hq
    change matchingProduct a b v.pivot - matchingProduct a b q = _
    rw [hpv, hab]
    exact (hfixed y).1 q hq
  · change matchingProfileDetGap U v.η v.pivot (matchingProduct a b) = _
    rw [hηv, hpv, hab]
    exact (hfixed y).2
  · intro q hq
    change eval (matchingProduct a b) q = _
    rw [hab]
    exact hpin y q hq

end

end MOC
