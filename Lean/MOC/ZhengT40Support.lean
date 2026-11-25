import MOC.ZhengPairedContacts

/-! The zero-height T40 boundary closes without the supplement to Zheng
(preprint DOI: 10.13140/RG.2.2.36790.25923, Section 5). -/

open Matrix

namespace MOC.ZhengRectangleContact

/-- On the common five-label core of T40 and T85, zero support height
forces the two missing block contacts. The paired minor certificate
then excludes every strict witness, even without the extra T40 label 1. -/
theorem not_zero_height_common_core {U : Matrix (Fin 4) (Fin 4) ℂ} (hU : IsUnitary U)
    (w : StrictMatchingSupport U) (hp : w.pivot = 1)
    (h5 : s₅ ∈ w.contacts) (h9 : s₉ ∈ w.contacts)
    (h14 : s₁₄ ∈ w.contacts) (h18 : s₁₈ ∈ w.contacts)
    (hzero : (w.η * matchingProduct w.a w.b 1).re = 0) : False := by
  let z (q : Perm4) := w.η * matchingProduct w.a w.b q
  have hcontact (q : Perm4) : q ∈ w.contacts ↔ (z q).re = 0 := by
    simp [StrictMatchingSupport.contacts, z, hp, hzero]
  have hnonpos (q : Perm4) : (z q).re ≤ 0 := by
    simpa only [z,hp,hzero] using w.maximal q
  have hbad : ¬ Holds w.a w.b U := fun h => by
    obtain ⟨p, he⟩ := (holds_iff_directional _ _ _).mp h w.η
    exact (not_lt_of_ge (he.trans (w.maximal p))) w.strict
  have hn (i j : Fin 4) : w.a i + w.b j ≠ 0 := fun h =>
    hbad (holds_four_of_opposite_entries _ _ _ hU h)
  have hnz : z 1 ≠ 0 := mul_ne_zero (fun h => by simpa [h] using w.strict)
    (Finset.prod_ne_zero_iff.mpr fun j _ => hn _ _)
  have hsq : (z 1).re ^ 2 + (z 1).im ^ 2 ≠ 0 := by
    intro he
    have hi : (z 1).im = 0 := by nlinarith
    exact hnz (Complex.ext hzero hi)
  have hd : ∀ i, s₁₄ i = i ∨ s₅ i = i := by
    intro i
    fin_cases i <;> simp [s₁₄,s₅,Equiv.swap_apply_def]
  have hrec := matchingProduct_disjoint_perms_fourth_gap w.a w.b 1 s₁₄ s₅ hd
    w.η 0 hzero (by simpa only [one_mul] using (hcontact _).mp h14)
    (by simpa only [one_mul] using (hcontact _).mp h5)
  simp only [one_mul] at hrec
  change (0 - (z s₁₆).re) * ((0 : ℝ)^2 + (z 1).im^2) = _ at hrec
  change (z 1).re = 0 at hzero
  rw [hzero] at hsq
  simp only [zero_mul] at hrec
  have h16 : (z s₁₆).re = 0 := by
    have he := (mul_eq_zero.mp hrec).resolve_right hsq
    linarith
  have hlin := congrArg (fun x : ℂ => (w.η * x).re) (rectangle_linear w.a w.b)
  simp only [diff,mul_sub,mul_add,Complex.sub_re,Complex.add_re] at hlin
  change (z s₁₆).re - (z 1).re - ((z s₂₃).re - (z 1).re) =
    (z s₅).re - (z 1).re + ((z s₇).re - (z 1).re) -
      ((z s₉).re - (z 1).re) + ((z s₁₄).re - (z 1).re) -
      ((z s₁₈).re - (z 1).re) at hlin
  have h7 : s₇ ∈ w.contacts := (hcontact _).mpr (by
    linarith [hnonpos s₇,hnonpos s₂₃,h16,hzero,(hcontact _).mp h5,
      (hcontact _).mp h9,(hcontact _).mp h14,(hcontact _).mp h18])
  have h23 : s₂₃ ∈ w.contacts := (hcontact _).mpr (by
    linarith [h16,hzero,(hcontact _).mp h5,(hcontact _).mp h7,
      (hcontact _).mp h9,(hcontact _).mp h14,(hcontact _).mp h18])
  exact ZhengPairedContacts.not_paired_witness hU w ⟨hp,h5,h7,h9,h14,h18⟩ h23

end MOC.ZhengRectangleContact
