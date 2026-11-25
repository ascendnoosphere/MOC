import MOC.AffineGapCover
import MOC.DisjointContactRectangle
import MOC.FourCoincidence
import MOC.TwoExceptions

/-! A contact-budget argument for Zheng's (T_{85}) pattern
(preprint DOI: 10.13140/RG.2.2.36790.25923, Section 5).
The proofs below use identities of matching products directly, rather than
the fourteen-coordinate matching cubic or the supplementary case tables. -/

open Matrix MvPolynomial

namespace MOC
namespace ZhengRectangleContact

abbrev Perm4 := Equiv.Perm (Fin 4)

-- Inverse labels: matchingProduct assigns the first spectrum to the second.
def s₅ : Perm4 := Equiv.swap 1 3
def s₇ : Perm4 := Equiv.swap 0 1 * Equiv.swap 2 3
def s₉ : Perm4 := Equiv.swap 2 3 * Equiv.swap 1 2 * Equiv.swap 0 1
def s₁₄ : Perm4 := Equiv.swap 0 2
def s₁₆ : Perm4 := Equiv.swap 0 2 * Equiv.swap 1 3
def s₁₈ : Perm4 := Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 2 3
def s₂₃ : Perm4 := Equiv.swap 0 3 * Equiv.swap 1 2

def diff (a b : Fin 4 → ℂ) (q : Perm4) : ℂ :=
  matchingProduct a b q - matchingProduct a b 1

/-- An exact quadratic relation on seven labels. This gives the mixed
identity in Zheng's Section 5.4 directly in terms of permutation products. -/
theorem rectangle_quadratic (a b : Fin 4 → ℂ) :
    diff a b s₁₈ * diff a b s₉ - diff a b s₅ * diff a b s₁₄ =
      diff a b s₇ * diff a b s₂₃ := by
  simp [diff, matchingProduct, Fin.prod_univ_four, s₁₈, s₉, s₅, s₁₄, s₇, s₂₃,
    Equiv.Perm.mul_apply, Equiv.swap_apply_def]
  ring

/-- These two additional labels must become contacts together. -/
theorem rectangle_linear (a b : Fin 4 → ℂ) :
    diff a b s₁₆ - diff a b s₂₃ =
      diff a b s₅ + diff a b s₇ - diff a b s₉ + diff a b s₁₄ - diff a b s₁₈ := by
  simp [diff, matchingProduct, Fin.prod_univ_four, s₁₆, s₂₃, s₅, s₇, s₉, s₁₄, s₁₈,
    Equiv.Perm.mul_apply, Equiv.swap_apply_def]
  ring

theorem diff_five (a b : Fin 4 → ℂ) :
    diff a b s₅ = (a 0 + b 0) * (a 3 - a 1) * (a 2 + b 2) * (b 3 - b 1) := by
  simp [diff, matchingProduct, Fin.prod_univ_four, s₅, Equiv.swap_apply_def]
  ring

private theorem eq_zero_of_projected_rectangle {a b c d e f : ℂ}
    (h : a * b - c * d = e * f)
    (ha : a.re = 0) (hb : b.re = 0) (hc : c.re = 0) (hd : d.re = 0)
    (he : e.re = 0) (hf : f.re ≠ 0) : e = 0 := by
  have him := congrArg Complex.im h
  simp only [Complex.sub_im, Complex.mul_im, ha, hb, hc, hd, he, zero_mul, mul_zero,
    zero_add, sub_self] at him
  exact Complex.ext he ((mul_eq_zero.mp him.symm).resolve_right hf)

local macro "different_labels" : tactic => `(tactic|
  (intro he
   have hh := congrArg (fun q : Perm4 => (q 0, q 1)) he
   simp [s₅, s₇, s₉, s₁₄, s₁₆, s₁₈, s₂₃, Equiv.Perm.mul_apply, Equiv.swap_apply_def]
     at hh))

/-- The six (T_{85}) labels, with the identity as support pivot. -/
def Pattern {U : Matrix (Fin 4) (Fin 4) ℂ} (w : StrictMatchingSupport U) : Prop :=
  w.pivot = 1 ∧ s₅ ∈ w.contacts ∧ s₇ ∈ w.contacts ∧ s₉ ∈ w.contacts ∧
    s₁₄ ∈ w.contacts ∧ s₁₈ ∈ w.contacts

private theorem re_diff_zero_iff {U : Matrix (Fin 4) (Fin 4) ℂ}
    (w : StrictMatchingSupport U) (hp : w.pivot = 1) (q : Perm4) :
    (w.η * diff w.a w.b q).re = 0 ↔ q ∈ w.contacts := by
  simp [diff, StrictMatchingSupport.contacts, hp, mul_sub, Complex.sub_re, sub_eq_zero]

private theorem same_projected_gap {U : Matrix (Fin 4) (Fin 4) ℂ}
    (w : StrictMatchingSupport U) (hT : Pattern w) :
    (w.η * diff w.a w.b s₁₆).re = (w.η * diff w.a w.b s₂₃).re := by
  obtain ⟨hp,h₅,h₇,h₉,h₁₄,h₁₈⟩ := hT
  have h := congrArg (fun z => (w.η * z).re) (rectangle_linear w.a w.b)
  simp only [mul_sub, mul_add, Complex.sub_re, Complex.add_re,
    (re_diff_zero_iff w hp _).mpr h₅, (re_diff_zero_iff w hp _).mpr h₇,
    (re_diff_zero_iff w hp _).mpr h₉, (re_diff_zero_iff w hp _).mpr h₁₄,
    (re_diff_zero_iff w hp _).mpr h₁₈, sub_zero, add_zero] at h
  exact sub_eq_zero.mp h

/-- Inactive label 23 forces a collision between the *complex* values at
labels 0 and 7. If label 23 is active, label 16 is active as well. -/
theorem collision_or_paired_contact {U : Matrix (Fin 4) (Fin 4) ℂ}
    (w : StrictMatchingSupport U) (hT : Pattern w) :
    (s₂₃ ∉ w.contacts ∧ diff w.a w.b s₇ = 0) ∨
      (s₂₃ ∈ w.contacts ∧ s₁₆ ∈ w.contacts) := by
  have ⟨hp,h₅,h₇,h₉,h₁₄,h₁₈⟩ := hT
  let g (q : Perm4) := w.η * diff w.a w.b q
  have hre (q : Perm4) : (g q).re = 0 ↔ q ∈ w.contacts := re_diff_zero_iff w hp q
  by_cases h₂₃ : s₂₃ ∈ w.contacts
  · right
    refine ⟨h₂₃, (hre s₁₆).mp ?_⟩
    exact (same_projected_gap w hT).trans ((hre _).mpr h₂₃)
  · left
    refine ⟨h₂₃, ?_⟩
    have hq : g s₁₈ * g s₉ - g s₅ * g s₁₄ = g s₇ * g s₂₃ := by
      dsimp [g]
      linear_combination w.η ^ 2 * rectangle_quadratic w.a w.b
    have hzero : g s₇ = 0 :=
      eq_zero_of_projected_rectangle hq ((hre _).mpr h₁₈) ((hre _).mpr h₉)
        ((hre _).mpr h₅) ((hre _).mpr h₁₄) ((hre _).mpr h₇) (mt (hre _).mp h₂₃)
    exact (mul_eq_zero.mp hzero).resolve_left (fun he => by simpa [he] using w.strict)

private theorem nondegenerate_spectra {U : Matrix (Fin 4) (Fin 4) ℂ} (hU : IsUnitary U)
    (w : StrictMatchingSupport U) :
    Function.Injective w.a ∧ Function.Injective w.b ∧ ∀ i j, w.a i + w.b j ≠ 0 := by
  have hbad : ¬ Holds w.a w.b U := fun h => by
    obtain ⟨q, hq⟩ := (holds_iff_directional _ _ _).mp h w.η
    exact (not_lt_of_ge (hq.trans (w.maximal q))) w.strict
  refine ⟨?_, ?_, fun i j h => hbad (holds_four_of_opposite_entries _ _ _ hU h)⟩
  · exact Classical.byContradiction fun h =>
      hbad (holds_four_of_repeated_spectrum _ _ _ hU (Or.inl h))
  · exact Classical.byContradiction fun h =>
      hbad (holds_four_of_repeated_spectrum _ _ _ hU (Or.inr h))

private theorem diff_fourteen (a b : Fin 4 → ℂ) :
    diff a b s₁₄ = (a 1 + b 1) * (a 2 - a 0) * (a 3 + b 3) * (b 2 - b 0) := by
  simp [diff, matchingProduct, Fin.prod_univ_four, s₁₄, Equiv.swap_apply_def]
  ring

private theorem active_swap_diffs_ne_zero {U : Matrix (Fin 4) (Fin 4) ℂ} (hU : IsUnitary U)
    (w : StrictMatchingSupport U) : diff w.a w.b s₅ ≠ 0 ∧ diff w.a w.b s₁₄ ≠ 0 := by
  obtain ⟨ha,hb,hz⟩ := nondegenerate_spectra hU w
  rw [diff_five, diff_fourteen]
  constructor <;> exact mul_ne_zero (mul_ne_zero (mul_ne_zero (hz _ _) (sub_ne_zero.mpr
    (ha.ne (by simp)))) (hz _ _)) (sub_ne_zero.mpr (hb.ne (by simp)))

/-- The paired-contact branch is exactly the branch whose support line
passes through zero. This uses the two genuinely nontrivial disjoint
swaps in the pattern, not a generic distinctness assumption on products. -/
theorem paired_contact_iff_zero_height {U : Matrix (Fin 4) (Fin 4) ℂ} (hU : IsUnitary U)
    (w : StrictMatchingSupport U) (hT : Pattern w) :
    s₂₃ ∈ w.contacts ↔ (w.η * matchingProduct w.a w.b 1).re = 0 := by
  have ⟨hp,h₅,_,_,h₁₄,_⟩ := hT
  let z (q : Perm4) := w.η * matchingProduct w.a w.b q
  have hre (q : Perm4) : (z q).re = (z 1).re ↔ q ∈ w.contacts := by
    simp [z, StrictMatchingSupport.contacts, hp]
  have hpair : s₁₆ ∈ w.contacts ↔ s₂₃ ∈ w.contacts := by
    rw [← re_diff_zero_iff w hp, ← re_diff_zero_iff w hp, same_projected_gap w hT]
  have hη : w.η ≠ 0 := fun h => by simpa [h] using w.strict
  have hz0 : z 1 ≠ 0 :=
    mul_ne_zero hη (Finset.prod_ne_zero_iff.mpr fun j _ => (nondegenerate_spectra hU w).2.2 _ _)
  have hswap : ∀ i, s₁₄ i = i ∨ s₅ i = i := by
    intro i
    fin_cases i <;> simp [s₁₄, s₅, Equiv.swap_apply_def]
  have hrec := matchingProduct_disjoint_perms_fourth_gap w.a w.b 1 s₁₄ s₅ hswap w.η
    (z 1).re rfl (by simpa only [one_mul] using (hre _).mpr h₁₄)
      (by simpa only [one_mul] using (hre _).mpr h₅)
  simp only [one_mul] at hrec
  change ((z 1).re - (z s₁₆).re) * ((z 1).re ^ 2 + (z 1).im ^ 2) =
    (z 1).re * ((z s₁₄).im - (z 1).im) * ((z s₅).im - (z 1).im) at hrec
  constructor
  · intro h
    rw [(hre _).mpr (hpair.mpr h), sub_self, zero_mul, mul_assoc] at hrec
    have him (q : Perm4) (hq : q ∈ w.contacts) (hneq : diff w.a w.b q ≠ 0) :
        (z q).im - (z 1).im ≠ 0 := fun hh => by
      have he := Complex.ext ((hre _).mpr hq) (sub_eq_zero.mp hh)
      exact hneq (sub_eq_zero.mpr (mul_left_cancel₀ hη he))
    obtain ⟨hd5,hd14⟩ := active_swap_diffs_ne_zero hU w
    exact (mul_eq_zero.mp hrec.symm).resolve_right
      (mul_ne_zero (him _ h₁₄ hd14) (him _ h₅ hd5))
  · intro h
    change (z 1).re = 0 at h
    rw [h, zero_mul, zero_mul] at hrec
    have hn : (0 : ℝ)^2 + (z 1).im^2 ≠ 0 := by
      intro he
      have hi : (z 1).im = 0 := by nlinarith
      exact hz0 (Complex.ext h hi)
    have he := (mul_eq_zero.mp hrec).resolve_right hn
    exact hpair.mp ((hre _).mp ((sub_eq_zero.mp he).symm.trans h.symm))

private theorem transfer_omitting {U : Matrix (Fin 4) (Fin 4) ℂ} (hU : IsUnitary U)
    (w : StrictMatchingSupport U) (hp : w.pivot = 1) (D : Finset Perm4)
    (hk : ((w.contacts.erase 1) \ D).card < 6)
    (hd : ∀ a b : Fin 4 → ℂ,
      (∀ q ∈ (w.contacts.erase 1) \ D, diff a b q = diff w.a w.b q) →
      ∀ q ∈ w.contacts, diff a b q = diff w.a w.b q) :
    ∃ v : StrictMatchingSupport U, v.η = w.η ∧ v.pivot = w.pivot ∧
      w.contacts ⊂ v.contacts ∧
      ∀ q ∈ w.contacts, diff v.a v.b q = diff w.a w.b q := by
  classical
  let S := (w.contacts.erase 1) \ D
  let f (q : Perm4) : ProfileRing (Fin 4) := X q - X 1
  let E := S.image f
  have hE : E.card < 2 * Fintype.card (Fin 4) - 2 := by
    rw [Fintype.card_fin]
    exact lt_of_le_of_lt Finset.card_image_le hk
  obtain ⟨v, hη, hp', hs, h⟩ :=
    global_varying_gap_transfer_of_controlling_observables
      (affineGapContinuation Perm4) hU w E hE (by
        intro a b he q hq
        have h' := hd a b (fun j hj => by
          simpa only [f, map_sub, eval_X, diff] using he (f j) (Finset.mem_image_of_mem f hj)) q hq
        rw [hp]
        simpa only [diff, neg_sub] using congrArg Neg.neg h')
  refine ⟨v, hη, hp', hs, fun q hq => ?_⟩
  have h' := h q hq
  simpa only [hp'.trans hp, hp, diff, neg_sub] using congrArg Neg.neg h'

/-- Up to seven contacts on the (T_{85}) pattern always allow one more.
When 23 is already active, eight contacts still allow one more. The
transfer uses the same mixer, direction and old complex differences. -/
theorem grow_contacts {U : Matrix (Fin 4) (Fin 4) ℂ} (hU : IsUnitary U)
    (w : StrictMatchingSupport U) (hT : Pattern w)
    (hcard : w.contacts.card ≤ 7 ∨ (s₂₃ ∈ w.contacts ∧ w.contacts.card ≤ 8)) :
    ∃ v : StrictMatchingSupport U, v.η = w.η ∧ v.pivot = w.pivot ∧
      w.contacts ⊂ v.contacts ∧
      ∀ q ∈ w.contacts, diff v.a v.b q = diff w.a w.b q := by
  classical
  obtain ⟨hp,h₅,h₇,h₉,h₁₄,h₁₈⟩ := hT
  have hid : (1 : Perm4) ∈ w.contacts := by
    simp [StrictMatchingSupport.contacts, hp]
  have hne := (active_swap_diffs_ne_zero hU w).1
  have hbudget : ∀ {S : Finset Perm4}, S ⊆ w.contacts.erase 1 →
      w.contacts.card ≤ S.card + 6 →
      ((w.contacts.erase 1) \ S).card < 6 := by
    intro S hS hcardS
    rw [Finset.card_sdiff hS, Finset.card_erase_of_mem hid]
    by_cases hz : w.contacts.card = 0
    · simp [hz]
    · omega
  rcases collision_or_paired_contact w ⟨hp,h₅,h₇,h₉,h₁₄,h₁₈⟩ with ⟨h₂₃,hzero⟩ | ⟨h₂₃,h₁₆⟩
  · have hcard' : w.contacts.card ≤ 7 := hcard.resolve_right (fun h => h₂₃ h.1)
    apply transfer_omitting hU w hp ({s₁₄} : Finset Perm4)
    · apply hbudget (Finset.singleton_subset_iff.mpr (Finset.mem_erase.mpr ⟨by different_labels, h₁₄⟩))
      simpa using hcard'
    · intro a b h q hq
      have fix (r : Perm4) (hr : r ∈ w.contacts) (h0 : r ≠ 1) (h14 : r ≠ s₁₄) :=
        h r (by simp [hr, h0, h14])
      have hg₇ := fix s₇ h₇ (by different_labels) (by different_labels)
      have hg₅ := fix s₅ h₅ (by different_labels) (by different_labels)
      have hg₉ := fix s₉ h₉ (by different_labels) (by different_labels)
      have hg₁₈ := fix s₁₈ h₁₈ (by different_labels) (by different_labels)
      by_cases hq0 : q = 1
      · simp [hq0, diff]
      by_cases hq14 : q = s₁₄
      · subst q
        have hnew := rectangle_quadratic a b
        have hold := rectangle_quadratic w.a w.b
        rw [hg₇, hzero, zero_mul, hg₅, hg₉, hg₁₈] at hnew
        rw [hzero, zero_mul] at hold
        apply mul_left_cancel₀ hne
        linear_combination hold - hnew
      · exact fix q hq hq0 hq14
  · have hcard' : w.contacts.card ≤ 8 := hcard.elim (fun h => h.trans (by omega)) And.right
    apply transfer_omitting hU w hp ({s₁₄, s₁₆} : Finset Perm4)
    · apply hbudget
      · simp [Finset.insert_subset_iff, Finset.mem_erase, h₁₄, h₁₆,
          show s₁₄ ≠ 1 by different_labels, show s₁₆ ≠ 1 by different_labels]
      · simpa [Finset.card_pair (show s₁₄ ≠ s₁₆ by different_labels)] using hcard'
    · intro a b h q hq
      have fix (r : Perm4) (hr : r ∈ w.contacts) (h0 : r ≠ 1)
          (h14 : r ≠ s₁₄) (h16 : r ≠ s₁₆) := h r (by simp [hr, h0, h14, h16])
      have hg₅ := fix s₅ h₅ (by different_labels) (by different_labels) (by different_labels)
      have hg₇ := fix s₇ h₇ (by different_labels) (by different_labels) (by different_labels)
      have hg₉ := fix s₉ h₉ (by different_labels) (by different_labels) (by different_labels)
      have hg₁₈ := fix s₁₈ h₁₈ (by different_labels) (by different_labels) (by different_labels)
      have hg₂₃ := fix s₂₃ h₂₃ (by different_labels) (by different_labels) (by different_labels)
      have hg₁₄ : diff a b s₁₄ = diff w.a w.b s₁₄ := by
        have hnew := rectangle_quadratic a b
        rw [hg₅, hg₇, hg₉, hg₁₈, hg₂₃] at hnew
        apply mul_left_cancel₀ hne
        linear_combination rectangle_quadratic w.a w.b - hnew
      by_cases hq0 : q = 1
      · simp [hq0, diff]
      by_cases hq14 : q = s₁₄
      · simpa only [hq14] using hg₁₄
      by_cases hq16 : q = s₁₆
      · subst q
        have hnew := rectangle_linear a b
        rw [hg₅, hg₇, hg₉, hg₁₄, hg₁₈, hg₂₃] at hnew
        linear_combination hnew - rectangle_linear w.a w.b
      · exact fix q hq hq0 hq14 hq16

/-- An equal-product pair of opposite rectangle corners forces nonnegative
upper support height unless a neighboring product also equals the pivot. -/
theorem nonnegative_height_of_reciprocal_pair {p u v : ℂ}
    (hmul : u * v = p ^ 2) (hu : u.re ≤ p.re) (hv : v.re ≤ p.re)
    (hne : u ≠ p) : 0 ≤ p.re := by
  have he : (v.re - p.re) * Complex.normSq u =
      (p.re - u.re) * Complex.normSq p - p.re * Complex.normSq (u - p) := by
    have hr := congrArg Complex.re hmul
    have hi := congrArg Complex.im hmul
    simp only [pow_two, Complex.mul_re, Complex.mul_im] at hr hi
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
    linear_combination u.re * hr + u.im * hi
  by_contra! hn
  have hpos : 0 < Complex.normSq (u - p) := Complex.normSq_pos.mpr (sub_ne_zero.mpr hne)
  have hleft := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hv) (Complex.normSq_nonneg u)
  have hfirst := mul_nonneg (sub_nonneg.mpr hu) (Complex.normSq_nonneg p)
  have hsecond := mul_neg_of_neg_of_pos hn hpos
  linarith

/-- Off the paired-contact branch, any strict (T_{85}) witness lies on
a support line of strictly positive upper height. -/
theorem positive_height_of_inactive_23 {U : Matrix (Fin 4) (Fin 4) ℂ} (hU : IsUnitary U)
    (w : StrictMatchingSupport U) (hT : Pattern w) (h₂₃ : s₂₃ ∉ w.contacts) :
    0 < (w.η * matchingProduct w.a w.b 1).re := by
  let s : Perm4 := Equiv.swap 0 1
  let t : Perm4 := Equiv.swap 2 3
  let z (q : Perm4) := w.η * matchingProduct w.a w.b q
  have hp := hT.1
  have hη : w.η ≠ 0 := fun h => by simpa [h] using w.strict
  have hzero := ((collision_or_paired_contact w hT).resolve_right (fun h => h₂₃ h.1)).2
  have hdiag : z s₇ = z 1 := by
    dsimp only [diff] at hzero
    simp only [z, sub_eq_zero.mp hzero]
  have hswap : ∀ i, s i = i ∨ t i = i := by
    intro i
    fin_cases i <;> simp [s,t,Equiv.swap_apply_def]
  have hmul : z s * z t = z 1 * z s₇ := by
    have h := matchingProduct_disjoint_perms_identity w.a w.b 1 s t hswap
    simp only [one_mul] at h
    change matchingProduct w.a w.b 1 * matchingProduct w.a w.b s₇ = _ at h
    dsimp only [z]
    linear_combination -w.η ^ 2 * h
  have hsep : z s ≠ z 1 := by
    intro he
    obtain ⟨ha,hb,hz⟩ := nondegenerate_spectra hU w
    have hf : diff w.a w.b s =
        (w.a 2 + w.b 2) * (w.a 1 - w.a 0) * (w.a 3 + w.b 3) * (w.b 1 - w.b 0) := by
      simp [diff, matchingProduct, Fin.prod_univ_four, s, Equiv.swap_apply_def]
      ring
    have hn : diff w.a w.b s ≠ 0 := by
      rw [hf]
      exact mul_ne_zero (mul_ne_zero (mul_ne_zero (hz _ _) (sub_ne_zero.mpr
        (ha.ne (by simp)))) (hz _ _)) (sub_ne_zero.mpr (hb.ne (by simp)))
    exact hn (sub_eq_zero.mpr (mul_left_cancel₀ hη he))
  have hn : 0 ≤ (z 1).re := nonnegative_height_of_reciprocal_pair
    (by simpa only [hdiag, pow_two] using hmul)
    (by simpa only [z, hp] using w.maximal s)
    (by simpa only [z, hp] using w.maximal t) hsep
  exact lt_of_le_of_ne hn (fun h => h₂₃ ((paired_contact_iff_zero_height hU w hT).mpr h.symm))

/-- An order-four strict witness containing the six labels can be moved to
at least eight contacts without losing the pattern. -/
theorem exists_eight_contacts {U : Matrix (Fin 4) (Fin 4) ℂ} (hU : IsUnitary U)
    (w : StrictMatchingSupport U) (hT : Pattern w) :
    ∃ v : StrictMatchingSupport U, Pattern v ∧ 8 ≤ v.contacts.card := by
  have go (d : ℕ) (u : StrictMatchingSupport U) (hu : Pattern u)
      (hd : 8 - u.contacts.card = d) :
      ∃ v : StrictMatchingSupport U, Pattern v ∧ 8 ≤ v.contacts.card := by
    induction d using Nat.strong_induction_on generalizing u with
    | h d ih =>
      by_cases h : 8 ≤ u.contacts.card
      · exact ⟨u,hu,h⟩
      obtain ⟨v,_,hp,hinc,_⟩ := grow_contacts hU u hu (Or.inl (by omega))
      have hv : Pattern v := ⟨hp.trans hu.1, hinc.subset hu.2.1,
        hinc.subset hu.2.2.1, hinc.subset hu.2.2.2.1,
        hinc.subset hu.2.2.2.2.1, hinc.subset hu.2.2.2.2.2⟩
      have hlt := Finset.card_lt_card hinc
      exact ih (8 - v.contacts.card) (by omega) v hv rfl
  exact go _ w hT rfl

-- The adjacent mixed rectangle in the complementary-pair decomposition.
theorem mixed_block_rectangle (a b : Fin 4 → ℂ) :
    let q : Perm4 := Equiv.swap 1 2
    let s : Perm4 := Equiv.swap 0 2
    matchingProduct a b q - matchingProduct a b (q * s) -
      matchingProduct a b (s * q) + matchingProduct a b (s * q * s) =
    matchingProduct a b 1 - matchingProduct a b s := by
  simp [matchingProduct, Fin.prod_univ_four, Equiv.Perm.mul_apply, Equiv.swap_apply_def]
  ring

end ZhengRectangleContact
end MOC
