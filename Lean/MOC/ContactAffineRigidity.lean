import MOC.ContactPencilRigidity
import MOC.CollinearKernelSupport
import MOC.MatchingProfileClosed

/-! A nonconstant exact affine profile line cannot preserve all contacts
of a contact-maximal strict witness. Unlike the fixed-gap fibre argument,
the determinant gap may vary. For the fixed-gap contact strategy, see
Zheng (preprint DOI: 10.13140/RG.2.2.36790.25923). -/

open BigOperators Matrix Set
open scoped Topology

namespace MOC

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem affine_profile_direction_is_exact [Nonempty ι]
    (p s : Equiv.Perm ι → ℂ)
    (hex : ∀ z : ℂ, ∃ a b : ι → ℂ, matchingProduct a b = fun q => p q + z * s q) :
    ∃ a b : ι → ℂ, matchingProduct a b = s := by
  let C : Set (Equiv.Perm ι → ℂ) := {r | ∃ a b : ι → ℂ, matchingProduct a b = r}
  let f (t : ℂ) (q : Equiv.Perm ι) := s q + t * p q
  have hf : Continuous f := continuous_pi fun q => by dsimp [f]; fun_prop
  have hc : IsClosed (f ⁻¹' C) := isClosed_additive_matching_profiles.preimage hf
  have hp : ({0} : Set ℂ)ᶜ ⊆ f ⁻¹' C := by
    intro t ht
    have ht' : t ≠ 0 := by simpa using ht
    obtain ⟨a,b,hab⟩ := hex t⁻¹
    obtain ⟨c,hc'⟩ := IsAlgClosed.exists_pow_nat_eq t (Fintype.card_pos (α := ι))
    refine ⟨fun i => c * a i, fun i => c * b i, ?_⟩
    funext q
    rw [matchingProduct_scale, hc', congrFun hab q]
    dsimp [f]
    rw [mul_add, ← mul_assoc, mul_inv_cancel₀ ht', one_mul, add_comm]
  have hd : (0 : ℂ) ∈ closure (({0} : Set ℂ)ᶜ) := dense_compl_singleton (0 : ℂ) 0
  have hm := hc.closure_subset_iff.mpr hp hd
  simpa only [Set.mem_preimage, C, f, zero_mul, add_zero] using hm

private theorem matchingProfileDetGap_affine
    (U : Matrix ι ι ℂ) (η : ℂ) (r : Equiv.Perm ι)
    (p s : Equiv.Perm ι → ℂ) (z : ℂ) :
    matchingProfileDetGap U η r (fun q => p q + z * s q) =
      matchingProfileDetGap U η r p + z * matchingProfileDetGap U η r s := by
  unfold matchingProfileDetGap
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun _ _ => by ring

private theorem matchingProfileDetGap_div_direction
    (U : Matrix ι ι ℂ) (η t : ℂ) (r : Equiv.Perm ι) (s : Equiv.Perm ι → ℂ) :
    matchingProfileDetGap U (η / t) r s = matchingProfileDetGap U η r s / t := by
  unfold matchingProfileDetGap
  rw [Finset.sum_div]
  exact Finset.sum_congr rfl fun _ _ => by ring

/-- If the old complex contact differences are constant on a nonconstant
exact affine line, a strict witness can gain a contact. The determinant gap
does not have to be fixed on the line. -/
theorem StrictMatchingSupport.exists_more_contacts_on_exact_affine_line [Nonempty ι]
    {U : Matrix ι ι ℂ} (hU : IsUnitary U) (w : StrictMatchingSupport U)
    (s : Equiv.Perm ι → ℂ) (hs : s ≠ 0)
    (hold : ∀ q ∈ w.contacts, s q = s w.pivot)
    (hex : ∀ z : ℂ, ∃ a b : ι → ℂ,
      matchingProduct a b = fun q => matchingProduct w.a w.b q + z * s q) :
    ∃ v : StrictMatchingSupport U, v.η = w.η ∧ v.pivot = w.pivot ∧
      w.contacts ⊂ v.contacts := by
  classical
  let p := matchingProduct w.a w.b
  let P (z : ℂ) (q : Equiv.Perm ι) := p q + z * s q
  let g := matchingProfileDetGap U w.η w.pivot p
  let A := matchingProfileDetGap U w.η w.pivot s
  let c (q : Equiv.Perm ι) := w.η * (p w.pivot - p q)
  let B (q : Equiv.Perm ι) := w.η * (s w.pivot - s q)
  let D : Set ℂ := {z | 0 < (g + z * A).re}
  have hg : 0 < g.re := by
    dsimp only [g, p]
    rw [matchingProfileDetGap_matchingProduct _ _ _ hU, mul_sub, Complex.sub_re]
    exact sub_pos.mpr w.strict
  have hη : w.η ≠ 0 := by
    intro he
    have h := w.strict
    simp [he] at h
  have hc (q : Equiv.Perm ι) : 0 ≤ (c q).re := by
    dsimp only [c, p]
    rw [mul_sub, Complex.sub_re]
    exact sub_nonneg.mpr (w.maximal q)
  have hP (z : ℂ) (q : Equiv.Perm ι) :
      w.η * (P z w.pivot - P z q) = c q + z * B q := by
    dsimp only [P, c, B]
    ring
  have h0 : (0 : ℂ) ∈ D := by simpa [D] using hg
  have hconv : Convex ℝ D := by
    let L : ℂ →ₗ[ℝ] ℝ := Complex.reLm.comp (LinearMap.mulLeft ℝ A)
    convert convex_halfSpace_gt L.isLinear (-g.re) using 1
    ext z
    change 0 < (g + z * A).re ↔ -g.re < (A * z).re
    rw [Complex.add_re, mul_comm A z]
    constructor <;> intro h <;> linarith only [h]
  apply Classical.byContradiction
  intro hmax
  have hD (z : ℂ) (hz : z ∈ D) (q : Equiv.Perm ι) :
      0 ≤ (c q + z * B q).re := by
    apply le_of_not_gt
    intro hneg
    have Hcont (q : Equiv.Perm ι) :
        ContinuousOn (fun x => (w.η * (P x w.pivot - P x q)).re) D := by
      simp_rw [hP]
      exact (show Continuous (fun x : ℂ => (c q + x * B q).re) by fun_prop).continuousOn
    have hneg' : (w.η * (P z w.pivot - P z q)).re < 0 := by rwa [hP]
    obtain ⟨v, hphase, hpiv, hlt, _⟩ := w.exists_more_contacts_on_connected_profiles
      hU hconv.isPreconnected P (fun z _ => hex z) Hcont h0 (by ext q; simp [P, p])
      (fun y _ j hj => by
        rw [hP, show B j = 0 by simp only [B, hold j hj, sub_self, mul_zero], mul_zero,
          add_zero]
        dsimp only [c, p]
        rw [mul_sub, Complex.sub_re, (Finset.mem_filter.mp hj).2, sub_self])
      (fun y hy => by rw [matchingProfileDetGap_affine]; exact hy)
      ⟨z,hz,q,hneg'⟩
    exact hmax ⟨v,hphase,hpiv,hlt⟩
  by_cases hA : A = 0
  · have hB (q : Equiv.Perm ι) : B q = 0 := by
      apply Classical.byContradiction
      intro hq
      let z := -((c q).re + 1 : ℝ) / B q
      have hz : z ∈ D := by simpa [D, hA] using hg
      have hh := hD z hz q
      rw [show z * B q = -(↑((c q).re + 1) : ℂ) by
        exact div_mul_cancel₀ _ hq] at hh
      simp only [Complex.add_re, Complex.neg_re, Complex.ofReal_re] at hh
      linarith
    have hsconst (q : Equiv.Perm ι) : s q = s w.pivot :=
      (sub_eq_zero.mp ((mul_eq_zero.mp (hB q)).resolve_left hη)).symm
    have hsp : s w.pivot ≠ 0 := fun h => hs (funext fun q => (hsconst q).trans h)
    have hholds : Holds w.a w.b U := holds_of_matching_translation_line w.a w.b U hU
      (fun t => by
        obtain ⟨a,b,hab⟩ := hex (t / s w.pivot)
        exact ⟨a,b,fun q => by rw [congrFun hab q, hsconst q, div_mul_cancel₀ _ hsp]⟩)
    obtain ⟨q,hq⟩ := (holds_iff_directional _ _ _).mp hholds w.η
    exact (not_lt_of_ge (hq.trans (w.maximal q))) w.strict
  have hIm (q : Equiv.Perm ι) : (B q / A).im = 0 := by
    apply Classical.byContradiction
    intro hq
    let t : ℝ := ((c q).re + 1) / (B q / A).im
    let z : ℂ := Complex.I * t / A
    have hz : z ∈ D := by
      change 0 < (g + (Complex.I * ↑t / A) * A).re
      rw [div_mul_cancel₀ _ hA, Complex.add_re, Complex.mul_re, Complex.I_re,
        Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero]
      exact hg
    have h := hD z hz q
    have he : z * B q = Complex.I * (t : ℂ) * (B q / A) := by
      dsimp [z]
      ring
    have hI (v : ℂ) : (Complex.I * v).re = -v.im := by simp [Complex.mul_re]
    rw [he, mul_assoc, mul_left_comm Complex.I, Complex.add_re, Complex.re_ofReal_mul,
      hI, mul_neg] at h
    dsimp only [t] at h
    rw [div_mul_cancel₀ _ hq] at h
    linarith
  have hRe (q : Equiv.Perm ι) : 0 ≤ (B q / A).re := by
    apply le_of_not_gt
    intro hq
    let t : ℝ := -((c q).re + 1) / (B q / A).re
    let z : ℂ := (t : ℂ) / A
    have ht : 0 < t := div_pos_of_neg_of_neg (by linarith only [hc q]) hq
    have hz : z ∈ D := by
      change 0 < (g + ((t : ℂ) / A) * A).re
      rw [div_mul_cancel₀ _ hA, Complex.add_re, Complex.ofReal_re]
      exact add_pos hg ht
    have h := hD z hz q
    rw [show z * B q = (t : ℂ) * (B q / A) by dsimp [z]; ring,
      Complex.add_re, Complex.re_ofReal_mul] at h
    dsimp only [t] at h
    rw [div_mul_cancel₀ _ hq.ne] at h
    linarith
  obtain ⟨a,b,hab⟩ := affine_profile_direction_is_exact p s hex
  let k := w.η / A
  have hdiff (q : Equiv.Perm ι) : k * (s w.pivot - s q) = B q / A := by
    dsimp [k,B]
    ring
  have hcol (q : Equiv.Perm ι) :
      ((Complex.I * k) * matchingProduct a b q).re =
        ((Complex.I * k) * s w.pivot).re := by
    have he := hIm q
    rw [← hdiff, mul_sub, Complex.sub_im, sub_eq_zero] at he
    rw [congrFun hab q, mul_assoc, mul_assoc]
    simpa only [Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_sub] using
      congrArg Neg.neg he.symm
  have hhold := holds_of_collinear_matching_profile a b _ (mul_ne_zero Complex.I_ne_zero (div_ne_zero hη hA))
    _ hcol U hU
  obtain ⟨q,hq⟩ := (holds_iff_directional _ _ _).mp hhold k
  have hup := hRe q
  rw [← hdiff, mul_sub, Complex.sub_re] at hup
  have hOne : matchingProfileDetGap U k w.pivot s = 1 := by
    dsimp only [k]
    rw [matchingProfileDetGap_div_direction, show matchingProfileDetGap U w.η w.pivot s = A from rfl,
      div_self hA]
  rw [← hab, matchingProfileDetGap_matchingProduct _ _ _ hU, mul_sub] at hOne
  have hval := congrArg Complex.re hOne
  rw [Complex.sub_re, Complex.one_re, congrFun hab w.pivot] at hval
  rw [congrFun hab q] at hq
  linarith

/-- At a contact-maximal strict witness the contacts alone detect every
free partner entry. No determinant-gap alternative is needed. -/
theorem StrictMatchingSupport.contact_detects_partner_entry
    {U : Matrix ι ι ℂ} (hU : IsUnitary U) (w : StrictMatchingSupport U)
    (hmax : ∀ v : StrictMatchingSupport U, v.contacts.card ≤ w.contacts.card)
    (j : ι) :
    ∃ q ∈ w.contacts, matchingEntrySlope w.a w.b j w.pivot ≠
      matchingEntrySlope w.a w.b j q := by
  classical
  letI : Nonempty ι := ⟨j⟩
  let s := matchingEntrySlope w.a w.b j
  have hp (q : Equiv.Perm ι) : matchingProduct w.a w.b q =
      (w.a (q j) + w.b j) * s q := by
    simpa only [Function.update_eq_self] using matchingProduct_update_partner w.a w.b j (w.b j) q
  have hs : s ≠ 0 := by
    intro h
    have hzero (q : Equiv.Perm ι) : matchingProduct w.a w.b q = 0 := by
      rw [hp, show s q = 0 from congrFun h q, mul_zero]
    have hdet := real_signed_determinant w.a w.b U hU
    simp only [hzero, mul_zero, Finset.sum_const_zero] at hdet
    have hbad := w.strict
    rw [← hdet, hzero] at hbad
    simp at hbad
  have hline (z : ℂ) : ∃ a b : ι → ℂ,
      matchingProduct a b = fun q => matchingProduct w.a w.b q + z * s q := by
    refine ⟨w.a, Function.update w.b j (w.b j + z), ?_⟩
    funext q
    rw [matchingProduct_update_partner, hp, show matchingEntrySlope w.a w.b j q = s q from rfl]
    ring
  apply Classical.byContradiction
  intro h
  have hconst (q) (hq : q ∈ w.contacts) : s q = s w.pivot :=
    (Classical.not_not.mp (fun hne => h ⟨q,hq,hne⟩)).symm
  obtain ⟨v, _, _, hv⟩ := w.exists_more_contacts_on_exact_affine_line hU s hs hconst hline
  exact (not_lt_of_ge (hmax v)) (Finset.card_lt_card hv)

end MOC
