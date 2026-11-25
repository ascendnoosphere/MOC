import MOC.DisjointContactRectangle
import MOC.ContactCrossRatios
import Mathlib.GroupTheory.Perm.Cycle.Factors
import MOC.ContactIteration
import MOC.PolynomialProfileContact

/-! Disjoint changes of a matching give exact constraints at an exposed
support line. In particular, opposite corners with coincident products
cannot conceal a transposition when the upper height is negative.
At zero height, two same-ray contacts force both complementary splits
of their relative permutation to be contacts. -/

namespace MOC

/-- The signed height difference of one reciprocal corner, given the
other. Neither a division nor a nonsingularity assumption is needed. -/
theorem reciprocal_pair_height_identity {p u v : ℂ} (h : u * v = p ^ 2) :
    (v.re - p.re) * Complex.normSq u =
      (p.re - u.re) * Complex.normSq p - p.re * Complex.normSq (u - p) := by
  have hr := congrArg Complex.re h
  have hi := congrArg Complex.im h
  simp only [pow_two, Complex.mul_re, Complex.mul_im] at hr hi
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
  linear_combination u.re * hr + u.im * hi

/-- An equal-product pair of opposite rectangle corners forces nonnegative
upper support height unless a neighboring product also equals the pivot. -/
theorem nonnegative_height_of_reciprocal_pair {p u v : ℂ}
    (hmul : u * v = p ^ 2) (hu : u.re ≤ p.re) (hv : v.re ≤ p.re)
    (hne : u ≠ p) : 0 ≤ p.re := by
  have he := reciprocal_pair_height_identity hmul
  by_contra! hn
  have hpos : 0 < Complex.normSq (u - p) := Complex.normSq_pos.mpr (sub_ne_zero.mpr hne)
  have hleft := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hv) (Complex.normSq_nonneg u)
  have hfirst := mul_nonneg (sub_nonneg.mpr hu) (Complex.normSq_nonneg p)
  have hsecond := mul_neg_of_neg_of_pos hn hpos
  linarith

/-- Opposite corners on the same nonzero imaginary ray force the two
intermediate corners onto the support line. Its use does not require
the opposite corner products to coincide. -/
theorem zero_height_pair_of_negative_product {u v : ℂ} {c : ℝ}
    (h : u * v = (c : ℂ)) (hc : c < 0) (hu : u.re ≤ 0) (hv : v.re ≤ 0) :
    u.re = 0 ∧ v.re = 0 := by
  have key {x y : ℂ} (hxy : x * y = (c : ℂ)) (hx : x.re ≤ 0) (hy : y.re ≤ 0) :
      x.re = 0 := by
    have hr := congrArg Complex.re hxy
    have hi := congrArg Complex.im hxy
    simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im] at hr hi
    have he : y.re * (x.re ^ 2 + x.im ^ 2) = c * x.re := by
      linear_combination x.re * hr + x.im * hi
    have hleft := mul_nonpos_of_nonpos_of_nonneg hy (add_nonneg (sq_nonneg x.re) (sq_nonneg x.im))
    by_contra hn
    have hright := mul_pos_of_neg_of_neg hc (lt_of_le_of_ne hx hn)
    linarith
  exact ⟨key h hu hv, key (by simpa only [mul_comm] using h) hv hu⟩

open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

-- Splitting a permutation on an invariant set and its complement.
private theorem complement_factor
    (q : Equiv.Perm ι) (S : Finset ι) (hS : ∀ i, i ∈ S ↔ q i ∈ S) :
    let s := Equiv.Perm.ofSubtype (q.subtypePerm hS)
    let t := Equiv.Perm.ofSubtype (q.subtypePerm (fun i => by simpa only [Finset.mem_compl] using not_congr (hS i) :
      ∀ i, i ∈ Sᶜ ↔ q i ∈ Sᶜ))
    s * t = q ∧ (∀ i, s i = i ∨ t i = i) := by
  intro s t
  have hs (i : ι) (hi : i ∈ S) : s i = q i := by
    dsimp [s]
    exact Equiv.Perm.ofSubtype_apply_of_mem _ hi
  have hs' (i : ι) (hi : i ∉ S) : s i = i :=
    Equiv.Perm.ofSubtype_apply_of_not_mem _ hi
  have ht (i : ι) (hi : i ∉ S) : t i = q i := by
    dsimp [t]
    exact Equiv.Perm.ofSubtype_apply_of_mem _ (Finset.mem_compl.mpr hi)
  have ht' (i : ι) (hi : i ∈ S) : t i = i :=
    Equiv.Perm.ofSubtype_apply_of_not_mem _ (fun h => (Finset.mem_compl.mp h) hi)
  refine ⟨?_, fun i => ?_⟩
  · ext i
    change s (t i) = q i
    by_cases hi : i ∈ S
    · rw [ht' i hi, hs i hi]
    · rw [ht i hi, hs' _ (mt (hS i).mpr hi)]
  · by_cases hi : i ∈ S
    · exact Or.inr (ht' i hi)
    · exact Or.inl (hs' i hi)

/-- Given zero upper height, between two contacts on the same nonzero
imaginary ray every restriction of their relative permutation to an
invariant set is again active. A union of any collection of relative
cycles can be used as the set; no distinct-spectrum premise is needed. -/
theorem zeroHeight_sameRay_invariant_split
    (a b : ι → ℂ) (η : ℂ) (r q : Equiv.Perm ι)
    (hmax : ∀ σ, (η * matchingProduct a b σ).re ≤ 0)
    (h₀ : (η * matchingProduct a b r).re = 0)
    (h₁ : (η * matchingProduct a b (r * q)).re = 0)
    (hsign : 0 < (η * matchingProduct a b r).im *
      (η * matchingProduct a b (r * q)).im)
    (S : Finset ι) (hS : ∀ i, i ∈ S ↔ q i ∈ S) :
    (η * matchingProduct a b (r * Equiv.Perm.ofSubtype (q.subtypePerm hS))).re = 0 := by
  classical
  let s := Equiv.Perm.ofSubtype (q.subtypePerm hS)
  let t := Equiv.Perm.ofSubtype (q.subtypePerm (fun i => by simpa only [Finset.mem_compl] using not_congr (hS i) :
    ∀ i, i ∈ Sᶜ ↔ q i ∈ Sᶜ))
  let z (σ : Equiv.Perm ι) := η * matchingProduct a b σ
  have ⟨hprod,hdisj⟩ : s * t = q ∧ (∀ i, s i = i ∨ t i = i) :=
    complement_factor q S hS
  have hdiag : z (r * s) * z (r * t) = z r * z (r * q) := by
    have h := matchingProduct_disjoint_perms_identity a b r s t hdisj
    rw [mul_assoc r, hprod] at h
    dsimp only [z]
    linear_combination -η ^ 2 * h
  have hp : z r * z (r * q) = ((-((z r).im * (z (r * q)).im) : ℝ) : ℂ) := by
    have hzr : (z r).re = 0 := h₀
    have hzq : (z (r * q)).re = 0 := h₁
    apply Complex.ext
    · simp only [Complex.mul_re, Complex.ofReal_re, hzr, hzq, zero_mul, zero_sub]
    · simp only [Complex.mul_im, Complex.ofReal_im, hzr, hzq, zero_mul, mul_zero, add_zero]
  rw [hp] at hdiag
  exact (zero_height_pair_of_negative_product hdiag (neg_neg_of_pos hsign) (hmax _) (hmax _)).1

/-- If two exposed products coincide and their relative permutation
contains a transposition cycle, then their upper support height is
nonnegative. Only the pivot product needs to be nonzero. -/
theorem collision_height_nonneg_of_swap_cycle
    (a b : ι → ℂ) (η : ℂ) (r q : Equiv.Perm ι)
    (ha : Function.Injective a) (hb : Function.Injective b)
    (hr : matchingProduct a b r ≠ 0) (hη : η ≠ 0)
    (hmax : ∀ σ, (η * matchingProduct a b σ).re ≤ (η * matchingProduct a b r).re)
    (hcollision : matchingProduct a b (r * q) = matchingProduct a b r)
    {i j : ι} (hij : i ≠ j) (hi : q i = j) (hj : q j = i) :
    0 ≤ (η * matchingProduct a b r).re := by
  let s := Equiv.swap i j
  let t := s * q
  let z (σ : Equiv.Perm ι) := η * matchingProduct a b σ
  have hh : ∀ k, s k = k ∨ t k = k := by
    intro k
    by_cases hki : k = i
    · subst k
      exact Or.inr (by simp [t,s,Equiv.Perm.mul_apply,hi])
    by_cases hkj : k = j
    · subst k
      exact Or.inr (by simp [t,s,Equiv.Perm.mul_apply,hj])
    · exact Or.inl (Equiv.swap_apply_of_ne_of_ne hki hkj)
  have hp : s * t = q := by
    rw [← mul_assoc]
    simp [s]
  have hdiag : z (r * s) * z (r * t) = (z r) ^ 2 := by
    have h := matchingProduct_disjoint_perms_identity a b r s t hh
    rw [mul_assoc r, hp, hcollision] at h
    dsimp only [z]
    linear_combination -η ^ 2 * h
  have hn : z (r * s) ≠ z r := fun h =>
    matchingProduct_swap_gap_ne_of_simple a b ha hb r hr i j hij
      (sub_eq_zero.mpr (mul_left_cancel₀ hη h).symm)
  exact nonnegative_height_of_reciprocal_pair hdiag (hmax _) (hmax _) hn

/-- Same-ray exposed endpoints separated by k disjoint relative cycles
force at least 2^k contact labels preserving any invariant cut. -/
theorem zeroHeight_sameRay_contact_card_invariant_cut {U : Matrix ι ι ℂ}
    (w : StrictMatchingSupport U) (q : Equiv.Perm ι)
    (h₀ : (w.η * matchingProduct w.a w.b w.pivot).re = 0)
    (h₁ : w.pivot * q ∈ w.contacts)
    (hsign : 0 < (w.η * matchingProduct w.a w.b w.pivot).im *
      (w.η * matchingProduct w.a w.b (w.pivot * q)).im)
    (B : Finset ι) (hB : ∀ i, i ∈ B ↔ q i ∈ B) :
    2 ^ q.cycleFactorsFinset.card ≤
      (w.contacts.filter fun p => ∀ i, i ∈ B ↔ w.pivot.symm (p i) ∈ B).card := by
  classical
  let T := q.cycleFactorsFinset.powerset
  let S (A : T) := A.val.biUnion Equiv.Perm.support
  have hsub (A : T) := Finset.mem_powerset.mp A.property
  have hS (A : T) (i : ι) : i ∈ S A ↔ q i ∈ S A := by
    simp only [S, Finset.mem_biUnion]
    constructor
    · rintro ⟨c,hc,hi⟩
      exact ⟨c,hc,(Equiv.Perm.mem_cycleFactorsFinset_support (hsub A hc) i).mp hi⟩
    · rintro ⟨c,hc,hi⟩
      exact ⟨c,hc,(Equiv.Perm.mem_cycleFactorsFinset_support (hsub A hc) i).mpr hi⟩
  let r (A : T) := Equiv.Perm.ofSubtype (q.subtypePerm (hS A))
  have hr (A : T) : w.pivot * r A ∈ w.contacts := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [h₀]
    exact zeroHeight_sameRay_invariant_split w.a w.b w.η w.pivot q
      (fun p => (w.maximal p).trans_eq h₀) h₀
      ((Finset.mem_filter.mp h₁).2.trans h₀) hsign (S A) (hS A)
  let cut := w.contacts.filter fun p => ∀ i, i ∈ B ↔ w.pivot.symm (p i) ∈ B
  have hcut (A : T) : w.pivot * r A ∈ cut := by
    refine Finset.mem_filter.mpr ⟨hr A, fun i => ?_⟩
    simp only [Equiv.Perm.mul_apply, Equiv.symm_apply_apply]
    by_cases hi : i ∈ S A
    · rw [show r A i = q i from Equiv.Perm.ofSubtype_apply_of_mem _ hi]
      exact hB i
    · rw [show r A i = i from Equiv.Perm.ofSubtype_apply_of_not_mem _ hi]
  let F (A : T) : cut := ⟨w.pivot * r A, hcut A⟩
  have eqsets (A B : T) (he : r A = r B) : A.val ⊆ B.val := by
    intro c hc
    obtain ⟨i, hi⟩ := (Equiv.Perm.mem_cycleFactorsFinset_iff.mp (hsub A hc)).1.nonempty_support
    have hiA : i ∈ S A := Finset.mem_biUnion.mpr ⟨c,hc,hi⟩
    have hin : q i ≠ i := Equiv.Perm.mem_support.mp
      (Equiv.Perm.mem_cycleFactorsFinset_support_le (hsub A hc) hi)
    have hval : r A i = q i := Equiv.Perm.ofSubtype_apply_of_mem _ hiA
    have hiB : i ∈ S B := by
      by_contra hn
      have heB : r B i = i := Equiv.Perm.ofSubtype_apply_of_not_mem _ hn
      exact hin (hval.symm.trans ((congrArg (fun p : Equiv.Perm ι => p i) he).trans heB))
    obtain ⟨d,hd,hiD⟩ := Finset.mem_biUnion.mp hiB
    by_cases hcd : c = d
    · rwa [hcd]
    · have hdisj := Equiv.Perm.cycleFactorsFinset_pairwise_disjoint q (hsub A hc) (hsub B hd) hcd
      exact False.elim ((hdisj i).elim (Equiv.Perm.mem_support.mp hi) (Equiv.Perm.mem_support.mp hiD))
  have hc := Finset.card_le_card_of_injective (f := F) (fun A B he => by
    have h := mul_left_cancel (congrArg Subtype.val he)
    exact Subtype.ext (Finset.Subset.antisymm (eqsets A B h) (eqsets B A h.symm)))
  simpa only [T, Finset.card_powerset] using hc

/-- A contact-maximal zero-height witness has an additional crossing
contact outside the cycle cube for every nontrivial invariant cut. -/
theorem zeroHeight_sameRay_contact_card_with_crossing {U : Matrix ι ι ℂ}
    (hU : IsUnitary U) (w : StrictMatchingSupport U)
    (hmax : ∀ v : StrictMatchingSupport U, v.contacts.card ≤ w.contacts.card)
    (q : Equiv.Perm ι) (h₀ : (w.η * matchingProduct w.a w.b w.pivot).re = 0)
    (h₁ : w.pivot * q ∈ w.contacts)
    (hsign : 0 < (w.η * matchingProduct w.a w.b w.pivot).im *
      (w.η * matchingProduct w.a w.b (w.pivot * q)).im)
    (B : Finset ι) (hB : ∀ i, i ∈ B ↔ q i ∈ B)
    (hB₀ : B.Nonempty) (hB₁ : ∃ j, j ∉ B) :
    2 ^ q.cycleFactorsFinset.card < w.contacts.card := by
  classical
  apply lt_of_le_of_lt (zeroHeight_sameRay_contact_card_invariant_cut w q h₀ h₁ hsign B hB)
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_subset_ne]
  refine ⟨Finset.filter_subset _ _, fun he => ?_⟩
  obtain ⟨p,hp,i,hi⟩ := w.contact_crosses_every_nontrivial_cut hU hmax B hB₀ hB₁
  have hp' : p ∈ (w.contacts.filter fun p => ∀ i, i ∈ B ↔ w.pivot.symm (p i) ∈ B) := by
    rwa [he]
  exact hi ((Finset.mem_filter.mp hp').2 i).symm

/-- Same-ray endpoints force at least one contact for every selection
of their relative cycles. -/
theorem zeroHeight_sameRay_contact_card {U : Matrix ι ι ℂ}
    (w : StrictMatchingSupport U) (q : Equiv.Perm ι)
    (h₀ : (w.η * matchingProduct w.a w.b w.pivot).re = 0)
    (h₁ : w.pivot * q ∈ w.contacts)
    (hsign : 0 < (w.η * matchingProduct w.a w.b w.pivot).im *
      (w.η * matchingProduct w.a w.b (w.pivot * q)).im) :
    2 ^ q.cycleFactorsFinset.card ≤ w.contacts.card := by
  classical
  simpa using zeroHeight_sameRay_contact_card_invariant_cut w q h₀ h₁ hsign Finset.univ (by simp)

/-- The exposed gaps of the two complementary splits of a collision
have a strict weighted sum at positive height if one split changes
the complex product. In particular the splits cannot both be contacts. -/
theorem positive_height_collision_split_strict
    (a b : ι → ℂ) (η : ℂ) (r s t : Equiv.Perm ι)
    (hdisj : ∀ i, s i = i ∨ t i = i)
    (hcollision : matchingProduct a b (r * s * t) = matchingProduct a b r)
    (hη : η ≠ 0) (hchange : matchingProduct a b (r * s) ≠ matchingProduct a b r)
    (hpos : 0 < (η * matchingProduct a b r).re)
    (hmax : ∀ σ, (η * matchingProduct a b σ).re ≤ (η * matchingProduct a b r).re) :
    (η * matchingProduct a b (r * s)).re < (η * matchingProduct a b r).re ∨
      (η * matchingProduct a b (r * t)).re < (η * matchingProduct a b r).re := by
  let z (σ : Equiv.Perm ι) := η * matchingProduct a b σ
  have hdiag : z (r * s) * z (r * t) = (z r)^2 := by
    have h := matchingProduct_disjoint_perms_identity a b r s t hdisj
    rw [hcollision] at h
    dsimp only [z]
    linear_combination -η ^ 2 * h
  have hneq : z (r * s) ≠ z r := fun h => hchange (mul_left_cancel₀ hη h)
  by_contra! h
  have hS : (z (r * s)).re = (z r).re := (hmax _).antisymm h.1
  have hT : (z (r * t)).re = (z r).re := (hmax _).antisymm h.2
  have hp := reciprocal_pair_height_identity hdiag
  rw [hS, hT, sub_self, zero_mul, zero_mul, zero_sub, zero_eq_neg] at hp
  exact (mul_ne_zero hpos.ne' (Complex.normSq_pos.mpr (sub_ne_zero.mpr hneq)).ne') hp

end MOC
