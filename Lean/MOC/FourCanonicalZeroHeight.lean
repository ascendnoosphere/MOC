import MOC.FourCanonicalHeightSquares
import MOC.FourTerminalCoverage
import Mathlib.Data.Finset.Powerset

/-! Rectangle closure limits the contacts at zero support height. The
terminal contact count uses the canonical cubic compensation alternatives. -/

open BigOperators

namespace MOC

noncomputable section

private theorem compensation_center_ne_zero {center x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (h : x * y + x + y < center * x * y) : center ≠ 0 := by
  intro he
  have hnonneg : 0 ≤ x * y + x + y := by positivity
  simp only [he, zero_mul] at h
  exact (not_lt_of_ge hnonneg) h

private def seedZeros : Finset (Fin 24) := {1, 6, 7, 8, 9, 12, 14, 15, 17, 18, 20, 22, 23}

private def zeroLabel (j : Fin 13) : Fin 24 :=
  ![1, 17, 6, 22, 12, 18, 20, 8, 14, 15, 9, 23, 7] j

private theorem seed_zero_iff (p : Fin 24) :
    mixedCostRayInt 0 p = 0 ↔ p ∈ seedZeros :=
  (by decide +kernel : ∀ p : Fin 24, mixedCostRayInt 0 p = 0 ↔ p ∈ seedZeros) p

private theorem seed_nonneg (p : Fin 24) : 0 ≤ mixedCostRay 0 p := by
  have hi : ∀ p : Fin 24, 0 ≤ mixedCostRayInt 0 p := by decide +kernel
  change (0 : ℝ) ≤ (mixedCostRayInt 0 p : ℝ)
  exact_mod_cast hi p

private theorem ray_nonneg (r : Fin 34) (p : Fin 24) : 0 ≤ ordinaryCostRay r p := by
  unfold ordinaryCostRay
  rw [ordinaryCostRayInt_indicator]
  split <;> norm_num

private theorem seed_ray_at_zeroLabel (j k : Fin 13) :
    ordinaryCostRayInt (fourCanonicalZeroHeightRay j) (zeroLabel k) =
      if j = k then 1 else 0 :=
  (by decide +kernel : ∀ j k : Fin 13,
    ordinaryCostRayInt (fourCanonicalZeroHeightRay j) (zeroLabel k) =
      if j = k then 1 else 0) j k

private theorem canonicalProfile_zeroLabel (c : Fin 13 → ℝ) (k : Fin 13) :
    fourCanonicalZeroHeightProfile c (zeroLabel k) = c k := by
  have hz : ∀ k : Fin 13, mixedCostRayInt 0 (zeroLabel k) = 0 := by decide +kernel
  classical
  simp only [fourCanonicalZeroHeightProfile, mixedCostRay, hz, Int.cast_zero, zero_add,
    ordinaryCostRay, seed_ray_at_zeroLabel, apply_ite, Int.cast_one, mul_ite, mul_one,
    mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]

private def contactRectangle (r : Fin 6) : Fin 4 → Fin 24 :=
  ![![0, 1, 6, 7], ![1, 3, 20, 22], ![6, 11, 12, 17], ![8, 9, 14, 15],
    ![12, 14, 18, 20], ![16, 17, 22, 23]] r

private abbrev RectangleClosed (s : Finset (Fin 24)) : Prop :=
  ∀ r : Fin 6,
    let p := contactRectangle r
    (p 0 ∈ s → p 1 ∈ s → p 2 ∈ s → p 3 ∈ s) ∧
    (p 0 ∈ s → p 1 ∈ s → p 3 ∈ s → p 2 ∈ s) ∧
    (p 0 ∈ s → p 2 ∈ s → p 3 ∈ s → p 1 ∈ s) ∧
    (p 1 ∈ s → p 2 ∈ s → p 3 ∈ s → p 0 ∈ s)

private def forbiddenContactTriples (t k : Fin 3) : Finset (Fin 24) :=
  ![![{1, 6, 7}, {8, 14, 15}, {17, 22, 23}],
    ![{1, 20, 22}, {6, 12, 17}, {8, 9, 15}],
    ![{1, 6, 7}, {12, 14, 20}, {17, 22, 23}]] t k

private def excludedContacts (t : Fin 3) : Finset (Fin 24) :=
  ![{9, 12, 20}, {14, 23, 7}, {18, 8, 15}] t

private theorem forbiddenContactTriples_not_subset (s : Finset (Fin 24)) {t : Fin 3}
    (hs : s ⊆ seedZeros \ excludedContacts t) (hc : RectangleClosed s)
    (k : Fin 3) : ¬ forbiddenContactTriples t k ⊆ s := by
  have hnot (p : Fin 24) (hp : p ∉ seedZeros \ excludedContacts t) : p ∉ s :=
    fun hm => hp (hs hm)
  intro h
  fin_cases t <;> fin_cases k
  · exact hnot 0 (by decide) ((hc 0).2.2.2 (h (by decide : 1 ∈ forbiddenContactTriples 0 0)) (h (by decide : 6 ∈ forbiddenContactTriples 0 0))
      (h (by decide : 7 ∈ forbiddenContactTriples 0 0)))
  · exact hnot 9 (by decide) ((hc 3).2.2.1 (h (by decide : 8 ∈ forbiddenContactTriples 0 1)) (h (by decide : 14 ∈ forbiddenContactTriples 0 1))
      (h (by decide : 15 ∈ forbiddenContactTriples 0 1)))
  · exact hnot 16 (by decide) ((hc 5).2.2.2 (h (by decide : 17 ∈ forbiddenContactTriples 0 2)) (h (by decide : 22 ∈ forbiddenContactTriples 0 2))
      (h (by decide : 23 ∈ forbiddenContactTriples 0 2)))
  · exact hnot 3 (by decide) ((hc 1).2.2.1 (h (by decide : 1 ∈ forbiddenContactTriples 1 0)) (h (by decide : 20 ∈ forbiddenContactTriples 1 0))
      (h (by decide : 22 ∈ forbiddenContactTriples 1 0)))
  · exact hnot 11 (by decide) ((hc 2).2.2.1 (h (by decide : 6 ∈ forbiddenContactTriples 1 1)) (h (by decide : 12 ∈ forbiddenContactTriples 1 1))
      (h (by decide : 17 ∈ forbiddenContactTriples 1 1)))
  · exact hnot 14 (by decide) ((hc 3).2.1 (h (by decide : 8 ∈ forbiddenContactTriples 1 2)) (h (by decide : 9 ∈ forbiddenContactTriples 1 2))
      (h (by decide : 15 ∈ forbiddenContactTriples 1 2)))
  · exact hnot 0 (by decide) ((hc 0).2.2.2 (h (by decide : 1 ∈ forbiddenContactTriples 2 0)) (h (by decide : 6 ∈ forbiddenContactTriples 2 0))
      (h (by decide : 7 ∈ forbiddenContactTriples 2 0)))
  · exact hnot 18 (by decide) ((hc 4).2.1 (h (by decide : 12 ∈ forbiddenContactTriples 2 1)) (h (by decide : 14 ∈ forbiddenContactTriples 2 1))
      (h (by decide : 20 ∈ forbiddenContactTriples 2 1)))
  · exact hnot 16 (by decide) ((hc 5).2.2.2 (h (by decide : 17 ∈ forbiddenContactTriples 2 2)) (h (by decide : 22 ∈ forbiddenContactTriples 2 2))
      (h (by decide : 23 ∈ forbiddenContactTriples 2 2)))

private theorem closed_contacts_under_exclusion (s : Finset (Fin 24)) (t : Fin 3)
    (hs : s ⊆ seedZeros \ excludedContacts t) (hc : RectangleClosed s) : s.card < 8 := by
  have hfail (k : Fin 3) := forbiddenContactTriples_not_subset s hs hc k
  obtain ⟨a, ha, hna⟩ := Finset.not_subset.mp (hfail 0)
  obtain ⟨b, hb, hnb⟩ := Finset.not_subset.mp (hfail 1)
  obtain ⟨c, hc', hnc⟩ := Finset.not_subset.mp (hfail 2)
  have hsub (k : Fin 3) : forbiddenContactTriples t k ⊆ seedZeros \ excludedContacts t :=
    (by decide +kernel : ∀ t k : Fin 3,
      forbiddenContactTriples t k ⊆ seedZeros \ excludedContacts t) t k
  have hne (i j : Fin 3) (hij : i ≠ j) : Disjoint (forbiddenContactTriples t i)
      (forbiddenContactTriples t j) :=
    (by decide +kernel : ∀ t i j : Fin 3, i ≠ j →
      Disjoint (forbiddenContactTriples t i) (forbiddenContactTriples t j)) t i j hij
  have hab : a ≠ b := fun h => Finset.disjoint_left.mp (hne 0 1 (by decide)) ha (h.symm ▸ hb)
  have hac : a ≠ c := fun h => Finset.disjoint_left.mp (hne 0 2 (by decide)) ha (h.symm ▸ hc')
  have hbc : b ≠ c := fun h => Finset.disjoint_left.mp (hne 1 2 (by decide)) hb (h.symm ▸ hc')
  have hcard : ({a, b, c} : Finset (Fin 24)).card = 3 := by simp [hab, hac, hbc]
  have hinc : ({a, b, c} : Finset (Fin 24)) ⊆ (seedZeros \ excludedContacts t) \ s := by
    simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
    exact ⟨Finset.mem_sdiff.mpr ⟨hsub 0 ha, hna⟩, Finset.mem_sdiff.mpr ⟨hsub 1 hb, hnb⟩,
      Finset.mem_sdiff.mpr ⟨hsub 2 hc', hnc⟩⟩
  have hbound := Finset.card_le_card hinc
  rw [hcard, Finset.card_sdiff hs] at hbound
  have hsize : (seedZeros \ excludedContacts t).card = 10 :=
    (by decide +kernel : ∀ t : Fin 3, (seedZeros \ excludedContacts t).card = 10) t
  omega

private theorem eight_closed_contacts :
    ∀ s ∈ seedZeros.powerset, 8 ≤ s.card → RectangleClosed s →
      (9 ∈ s ∨ 12 ∈ s ∨ 20 ∈ s) ∧
      (14 ∈ s ∨ 23 ∈ s ∨ 7 ∈ s) ∧
      (18 ∈ s ∨ 8 ∈ s ∨ 15 ∈ s) := by
  intro s hs hn hc
  have hss := Finset.mem_powerset.mp hs
  have hcannot (t : Fin 3) (h : ∀ p ∈ excludedContacts t, p ∉ s) : False := by
    have hsub : s ⊆ seedZeros \ excludedContacts t := by
      intro p hp
      exact Finset.mem_sdiff.mpr ⟨hss hp, fun he => h p he hp⟩
    exact (not_lt_of_ge hn) (closed_contacts_under_exclusion s t hsub hc)
  constructor
  · by_contra! h
    apply hcannot 0
    intro p hp
    change p ∈ ({9, 12, 20} : Finset (Fin 24)) at hp
    rcases (by simpa only [Finset.mem_insert, Finset.mem_singleton] using hp :
      p = 9 ∨ p = 12 ∨ p = 20) with rfl | rfl | rfl
    · exact h.1
    · exact h.2.1
    · exact h.2.2
  constructor
  · by_contra! h
    apply hcannot 1
    intro p hp
    change p ∈ ({14, 23, 7} : Finset (Fin 24)) at hp
    rcases (by simpa only [Finset.mem_insert, Finset.mem_singleton] using hp :
      p = 14 ∨ p = 23 ∨ p = 7) with rfl | rfl | rfl
    · exact h.1
    · exact h.2.1
    · exact h.2.2
  · by_contra! h
    apply hcannot 2
    intro p hp
    change p ∈ ({18, 8, 15} : Finset (Fin 24)) at hp
    rcases (by simpa only [Finset.mem_insert, Finset.mem_singleton] using hp :
      p = 18 ∨ p = 8 ∨ p = 15) with rfl | rfl | rfl
    · exact h.1
    · exact h.2.1
    · exact h.2.2

private def matchingEdges (p : Fin 24) : List (Fin 4 × Fin 4) :=
  List.ofFn fun j => ((fourPerm p).symm j, j)

private theorem contactRectangle_edges (r : Fin 6) :
    let p := contactRectangle r
    (matchingEdges (p 0) ++ matchingEdges (p 3)).Perm
      (matchingEdges (p 1) ++ matchingEdges (p 2)) :=
  (by decide +kernel : ∀ r : Fin 6,
    let p := contactRectangle r
    (matchingEdges (p 0) ++ matchingEdges (p 3)).Perm
      (matchingEdges (p 1) ++ matchingEdges (p 2))) r

private theorem contactRectangle_product (a b : Fin 4 → ℂ) (η : ℂ) (r : Fin 6) :
    let z (p : Fin 24) := η * matchingProduct a b (fourPerm p).symm
    let p := contactRectangle r
    z (p 0) * z (p 3) = z (p 1) * z (p 2) := by
  let f (e : Fin 4 × Fin 4) := a e.1 + b e.2
  have hf (i : Fin 24) : ((matchingEdges i).map f).prod =
      matchingProduct a b (fourPerm i).symm := by
    simp only [matchingEdges, List.map_ofFn, Function.comp_apply, List.prod_ofFn, f,
      matchingProduct]
  let p := contactRectangle r
  have hp : matchingProduct a b (fourPerm (p 0)).symm *
      matchingProduct a b (fourPerm (p 3)).symm =
      matchingProduct a b (fourPerm (p 1)).symm *
      matchingProduct a b (fourPerm (p 2)).symm := by
    have h := ((contactRectangle_edges r).map f).prod_eq
    simpa only [List.map_append, List.prod_append, hf] using h
  dsimp only
  rw [mul_mul_mul_comm η _ η _, mul_mul_mul_comm η _ η _, hp]

private theorem rectangle_fourth_real_zero {x y z w : ℂ} (h : x * w = y * z) (hx : x ≠ 0)
    (h₀ : x.re = 0) (h₁ : y.re = 0) (h₂ : z.re = 0) : w.re = 0 := by
  have hi : x.im ≠ 0 := by
    intro he
    exact hx (Complex.ext (h₀.trans Complex.zero_re.symm) (he.trans Complex.zero_im.symm))
  have him := congrArg Complex.im h
  simp only [Complex.mul_im, h₀, h₁, h₂, zero_mul, zero_add, mul_zero] at him
  exact (mul_eq_zero.mp him).resolve_left hi

private theorem zeroHeight_rectangleClosed (a b : Fin 4 → ℂ) (η : ℂ) (hη : η ≠ 0)
    (hn : ∀ i j, a i + b j ≠ 0) :
    RectangleClosed (Finset.univ.filter fun p : Fin 24 =>
      (η * matchingProduct a b (fourPerm p).symm).re = 0) := by
  let z (p : Fin 24) := η * matchingProduct a b (fourPerm p).symm
  have hz (p : Fin 24) : z p ≠ 0 :=
    mul_ne_zero hη (Finset.prod_ne_zero_iff.mpr fun j _ => hn _ j)
  intro r
  let p := contactRectangle r
  have hm : z (p 0) * z (p 3) = z (p 1) * z (p 2) := contactRectangle_product a b η r
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  change ((z (p 0)).re = 0 → (z (p 1)).re = 0 → (z (p 2)).re = 0 → (z (p 3)).re = 0) ∧
    ((z (p 0)).re = 0 → (z (p 1)).re = 0 → (z (p 3)).re = 0 → (z (p 2)).re = 0) ∧
    ((z (p 0)).re = 0 → (z (p 2)).re = 0 → (z (p 3)).re = 0 → (z (p 1)).re = 0) ∧
    ((z (p 1)).re = 0 → (z (p 2)).re = 0 → (z (p 3)).re = 0 → (z (p 0)).re = 0)
  refine ⟨fun h₀ h₁ h₂ => rectangle_fourth_real_zero hm (hz _) h₀ h₁ h₂,
    fun h₀ h₁ h₃ => rectangle_fourth_real_zero hm.symm (hz _) h₁ h₀ h₃,
    fun h₀ h₂ h₃ => rectangle_fourth_real_zero ?_ (hz _) h₂ h₀ h₃,
    fun h₁ h₂ h₃ => rectangle_fourth_real_zero ?_ (hz _) h₃ h₁ h₂⟩
  · rw [mul_comm (z (p 2)), hm]
  · rw [mul_comm (z (p 3)), hm]

/-- A canonical mixed profile realized by nonzero matching products at zero
support height has fewer than eight contacts. -/
theorem fourCanonicalZeroHeight_contacts_lt_eight
    (a b : Fin 4 → ℂ) (η : ℂ) (hη : η ≠ 0) (hn : ∀ i j, a i + b j ≠ 0)
    (c : Fin 13 → ℝ) (hc : ∀ j, 0 ≤ c j)
    (hvalues : ∀ p : Fin 24, (η * matchingProduct a b (fourPerm p).symm).re =
      fourCanonicalZeroHeightProfile c p) :
    (Finset.univ.filter fun p : Fin 24 =>
      (η * matchingProduct a b (fourPerm p).symm).re = 0).card < 8 := by
  let s := Finset.univ.filter fun p : Fin 24 =>
    (η * matchingProduct a b (fourPerm p).symm).re = 0
  have hs (p : Fin 24) : p ∈ s ↔ fourCanonicalZeroHeightProfile c p = 0 := by
    simp only [s, Finset.mem_filter, Finset.mem_univ, true_and, hvalues]
  have hseed : s ⊆ seedZeros := by
    intro p hp
    apply (seed_zero_iff p).mp
    have hsum : 0 ≤ ∑ j, c j * ordinaryCostRay (fourCanonicalZeroHeightRay j) p :=
      Finset.sum_nonneg fun j _ => mul_nonneg (hc j) (ray_nonneg _ p)
    have hzero := (hs p).mp hp
    unfold fourCanonicalZeroHeightProfile at hzero
    have hz : mixedCostRay 0 p = 0 := by linarith only [hzero, hsum, seed_nonneg p]
    change (mixedCostRayInt 0 p : ℝ) = 0 at hz
    exact_mod_cast hz
  have hz (j : Fin 13) (hj : zeroLabel j ∈ s) : c j = 0 :=
    (canonicalProfile_zeroLabel c j).symm.trans ((hs _).mp hj)
  change s.card < 8
  by_contra! hcard
  obtain ⟨h₁, h₂, h₃⟩ :=
    eight_closed_contacts s (Finset.mem_powerset.mpr hseed) hcard
      (zeroHeight_rectangleClosed a b η hη hn)
  rcases fourCanonicalZeroHeight_compensation a b η c hc hvalues with h | h | h
  · rcases h₁ with hp | hp | hp
    · exact compensation_center_ne_zero h.1.le h.2.1.le h.2.2 (hz 10 hp)
    · exact h.1.ne' (hz 4 hp)
    · exact h.2.1.ne' (hz 6 hp)
  · rcases h₂ with hp | hp | hp
    · exact compensation_center_ne_zero h.1.le h.2.1.le h.2.2 (hz 8 hp)
    · exact h.1.ne' (hz 11 hp)
    · exact h.2.1.ne' (hz 12 hp)
  · rcases h₃ with hp | hp | hp
    · exact compensation_center_ne_zero h.1.le h.2.1.le h.2.2 (hz 5 hp)
    · exact h.1.ne' (hz 7 hp)
    · exact h.2.1.ne' (hz 9 hp)

private theorem sum_zeroHeightRays {c : Fin 34 → ℝ}
    (hc : ∀ j ∉ fourCanonicalCapOrdinaryRays, c j = 0) (p : Fin 24) :
    (∑ j : Fin 13, c (fourCanonicalZeroHeightRay j) *
      ordinaryCostRay (fourCanonicalZeroHeightRay j) p) =
      ∑ j : Fin 34, c j * ordinaryCostRay j p := by
  have hi : Function.Injective fourCanonicalZeroHeightRay := by
    change ∀ i j : Fin 13, fourCanonicalZeroHeightRay i = fourCanonicalZeroHeightRay j → i = j
    decide +kernel
  have hcap : Finset.univ.image fourCanonicalZeroHeightRay = fourCanonicalCapOrdinaryRays := by
    decide +kernel
  calc
    _ = ∑ j ∈ Finset.univ.image fourCanonicalZeroHeightRay, c j * ordinaryCostRay j p :=
      (Finset.sum_image (fun _ _ _ _ h => hi h)).symm
    _ = _ := by
      rw [hcap]
      exact Finset.sum_subset (Finset.subset_univ _) (fun j _ hj => by rw [hc j hj, zero_mul])

/-- A regular canonical mixed terminal witness at zero support height has
exactly seven contacts. -/
theorem fourCanonicalZeroHeight_terminal_contacts_eq_seven
    {U : Matrix (Fin 4) (Fin 4) ℂ} (w : StrictMatchingSupport U)
    (hreg : FourRegularSpectra w) (hterminal : 7 ≤ w.contacts.card)
    (hheight : (w.η * matchingProduct w.a w.b w.pivot).re = 0)
    (c : Fin 34 → ℝ) (hc : ∀ j, 0 ≤ c j)
    (hcs : ∀ j ∉ fourCanonicalCapOrdinaryRays, c j = 0)
    (hgap : fourTerminalGap w = (∑ j, c j • ordinaryCostRay j) + mixedCostRay 0) :
    w.contacts.card = 7 := by
  let c' : Fin 13 → ℝ := fun j => c (fourCanonicalZeroHeightRay j)
  have hη : w.η ≠ 0 := by
    intro he
    have hs := w.strict
    simp [he] at hs
  have hscore (p : Fin 24) :
      ((-w.η) * matchingProduct w.a w.b (fourPerm p).symm).re = fourTerminalGap w p := by
    rw [fourTerminalGap, matchingGap, hheight, neg_mul, Complex.neg_re, zero_sub]
  have heval (p : Fin 24) :
      ((-w.η) * matchingProduct w.a w.b (fourPerm p).symm).re =
        fourCanonicalZeroHeightProfile c' p := by
    rw [hscore, hgap, fourCanonicalZeroHeightProfile]
    simp only [c', Finset.sum_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      sum_zeroHeightRays hcs, add_comm]
  have he := fourCanonicalZeroHeight_contacts_lt_eight w.a w.b (-w.η)
    (neg_ne_zero.mpr hη) hreg.1 c' (fun j => hc _) heval
  simp only [hscore, fourTerminalGap_zero_count] at he
  omega

end

end MOC
