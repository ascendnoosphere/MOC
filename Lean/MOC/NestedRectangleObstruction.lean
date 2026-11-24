import MOC.DisjointContactRectangle
import MOC.MatchingQuartet
import MOC.NestedContactObjective

/-! A directional obstruction to representing a matching objective by a
single chain of subset-image terms. Independent swaps test the missing
mixed interaction without enumerating the matching profiles. -/

open BigOperators

namespace MOC

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

omit [Fintype ι] [DecidableEq ι] in
private theorem map_perm_mul (J : Finset ι) (r s : Equiv.Perm ι) :
    J.map (r * s).toEmbedding = (J.map s.toEmbedding).map r.toEmbedding := by
  rw [Finset.map_map]
  rfl

omit [Fintype ι] [DecidableEq ι] in
/-- If every observed subset is preserved by at least one of two commuting
assignment changes, additive objectives on the subset images have zero
mixed difference. The functions on the images need not be nonnegative. -/
theorem additive_images_rectangle
    (J : κ → Finset ι) (f : κ → Finset ι → ℝ) (r s t : Equiv.Perm ι)
    (hcomm : Commute s t)
    (hJ : ∀ k, (J k).map s.toEmbedding = J k ∨ (J k).map t.toEmbedding = J k) :
    (∑ k, f k ((J k).map r.toEmbedding)) +
      (∑ k, f k ((J k).map (r * s * t).toEmbedding)) =
    (∑ k, f k ((J k).map (r * s).toEmbedding)) +
      (∑ k, f k ((J k).map (r * t).toEmbedding)) := by
  simp only [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  rcases hJ k with hs | ht
  · have hres : r * s * t = r * t * s := by rw [mul_assoc, hcomm.eq, ← mul_assoc]
    rw [hres, map_perm_mul _ r s, hs, map_perm_mul _ (r * t) s, hs]
  · rw [map_perm_mul _ r t, ht, map_perm_mul _ (r * s) t, ht, add_comm]

/-- A real matching rectangle with two nontrivial independent changes
cannot have an additive image representation by subsets that never
distinguish both changes. Real products may arise after a common rotation. -/
theorem no_additive_images_of_real_matching_rectangle
    (a b : ι → ℂ) (η : ℂ) (J : κ → Finset ι) (r s t : Equiv.Perm ι)
    (hcomm : Commute s t) (hdisj : ∀ i, s i = i ∨ t i = i)
    (hJ : ∀ k, (J k).map s.toEmbedding = J k ∨ (J k).map t.toEmbedding = J k)
    (hreal : ∀ q, (η * matchingProduct a b q).im = 0)
    (hs : (η * matchingProduct a b (r * s)).re ≠ (η * matchingProduct a b r).re)
    (ht : (η * matchingProduct a b (r * t)).re ≠ (η * matchingProduct a b r).re) :
    ¬ ∃ f : κ → Finset ι → ℝ, ∀ q,
      (η * matchingProduct a b q).re = ∑ k, f k ((J k).map q.toEmbedding) := by
  intro ⟨f, hf⟩
  let p (q : Equiv.Perm ι) := (η * matchingProduct a b q).re
  have hsum : p r + p (r * s * t) = p (r * s) + p (r * t) := by
    simp only [p, hf]
    exact additive_images_rectangle J f r s t hcomm hJ
  have hprod : p r * p (r * s * t) = p (r * s) * p (r * t) := by
    have h := matchingProduct_disjoint_perms_identity a b r s t hdisj
    have hη : (η * matchingProduct a b r) * (η * matchingProduct a b (r * s * t)) =
        (η * matchingProduct a b (r * s)) * (η * matchingProduct a b (r * t)) := by
      calc
        _ = η^2 * (matchingProduct a b r * matchingProduct a b (r * s * t)) := by ring
        _ = η^2 * (matchingProduct a b (r * s) * matchingProduct a b (r * t)) := by rw [h]
        _ = _ := by ring
    simpa only [Complex.mul_re, hreal, zero_mul, sub_zero] using congrArg Complex.re hη
  have hz : (p (r * s) - p r) * (p (r * t) - p r) = 0 := by
    linear_combination -hprod + p r * hsum
  rcases mul_eq_zero.mp hz with h | h
  · exact hs (sub_eq_zero.mp h)
  · exact ht (sub_eq_zero.mp h)


omit [Fintype ι] in
private theorem map_swap_eq_of_mem_iff (J : Finset ι) {i j : ι}
    (h : i ∈ J ↔ j ∈ J) : J.map (Equiv.swap i j).toEmbedding = J := by
  ext x
  rw [Finset.mem_map_equiv, Equiv.symm_swap]
  rcases eq_or_ne x i with rfl | hi
  · simpa using h.symm
  rcases eq_or_ne x j with rfl | hj
  · simpa using h
  rw [Equiv.swap_apply_of_ne_of_ne hi hj]

/-- All cuts in a single column ordering cannot account for a mixed swap
interaction if the two swaps use separated position intervals. This
obstructs even arbitrary signed scores on those prefixes, including the
two nested scores in `projected_hull_of_nested_image_scores`. It does not
obstruct arbitrary objectives on the whole flag or sums of certificates
on different chains. -/
theorem no_prefix_scores_of_matching_rectangle
    (a b : ι → ℂ) (η : ℂ) (rank : ι → ℕ) (cut : κ → ℕ)
    (r : Equiv.Perm ι) (i j k l : ι)
    (hij : rank i < rank j) (hjk : rank j < rank k) (hkl : rank k < rank l)
    (hΓ : (η * ((∏ m ∈ ({i, j, k, l} : Finset ι)ᶜ, (a (r m) + b m)) *
      ((a (r i) - a (r j)) * (b j - b i)) * ((a (r k) - a (r l)) * (b l - b k)))).re ≠ 0) :
    let J (p : κ) : Finset ι := Finset.univ.filter (fun x => rank x < cut p)
    ¬ ∃ f : κ → Finset ι → ℝ, ∀ q,
      (η * matchingProduct a b q).re = ∑ p, f p ((J p).map q.toEmbedding) := by
  intro J ⟨f, hf⟩
  let s := Equiv.swap i j
  let t := Equiv.swap k l
  have nij : i ≠ j := fun h => hij.ne (congrArg rank h)
  have nik : i ≠ k := fun h => (hij.trans hjk).ne (congrArg rank h)
  have nil : i ≠ l := fun h => (hij.trans (hjk.trans hkl)).ne (congrArg rank h)
  have njk : j ≠ k := fun h => hjk.ne (congrArg rank h)
  have njl : j ≠ l := fun h => (hjk.trans hkl).ne (congrArg rank h)
  have nkl : k ≠ l := fun h => hkl.ne (congrArg rank h)
  have hdisj : s.Disjoint t := by
    intro x
    by_cases hix : x = i
    · subst x
      exact Or.inr (Equiv.swap_apply_of_ne_of_ne nik nil)
    by_cases hjx : x = j
    · subst x
      exact Or.inr (Equiv.swap_apply_of_ne_of_ne njk njl)
    exact Or.inl (Equiv.swap_apply_of_ne_of_ne hix hjx)
  have hcuts (p : κ) : (J p).map s.toEmbedding = J p ∨ (J p).map t.toEmbedding = J p := by
    by_cases hj : rank j < cut p
    · left
      apply map_swap_eq_of_mem_iff
      simp [J, hj, hij.trans hj]
    · right
      have hk : ¬ rank k < cut p := fun h => hj (hjk.trans h)
      have hl : ¬ rank l < cut p := fun h => hk (hkl.trans h)
      apply map_swap_eq_of_mem_iff
      simp [J, hk, hl]
  have hsum := additive_images_rectangle J f r s t hdisj.commute hcuts
  rw [← hf, ← hf, ← hf, ← hf] at hsum
  apply hΓ
  rw [← matchingProduct_disjoint_swaps_alternating_sum a b r i j k l nij nik nil njk njl nkl]
  simp only [mul_sub, mul_add, Complex.sub_re, Complex.add_re]
  change (η * matchingProduct a b r).re +
    (η * matchingProduct a b (r * s * t)).re -
    (η * matchingProduct a b (r * s)).re -
    (η * matchingProduct a b (r * t)).re = 0
  rw [hsum]
  ring


private def labelFive : Fin 3 ⊕ Fin 2 ≃ Fin 5 :=
  finSumFinEquiv.trans (Equiv.swap 3 4 * Equiv.swap 1 3)

private def twoLevelFive (x y : ℝ) (i : Fin 5) : ℂ :=
  Sum.elim (fun _ => (x : ℂ)) (fun _ => (y : ℂ)) (labelFive.symm i)

private theorem twoLevelFive_row_symmetry (x y : ℝ)
    (v : Equiv.Perm (Fin 3) × Equiv.Perm (Fin 2)) (i : Fin 5) :
    twoLevelFive x y (labelFive.permCongr (Equiv.sumCongr v.1 v.2) i) =
      twoLevelFive x y i := by
  simp only [twoLevelFive, Equiv.permCongr_apply, Equiv.symm_apply_apply]
  cases labelFive.symm i <;> rfl

private theorem twoLevelFive_swap_scores (x y : ℝ) (b : Fin 5 → ℝ)
    (hxy : x ≠ y) (hx : 0 < x) (hy : 0 < y) (hb : ∀ j, 0 < b j)
    (hb' : Function.Injective b) (e : Equiv.Perm (Fin 5)) (cut : κ → ℕ) :
    let J (p : κ) : Finset (Fin 5) := Finset.univ.filter (fun i => (e.symm i).val < cut p)
    ¬ ∃ f : κ → Finset (Fin 5) → ℝ, ∀ q,
      (matchingProduct (twoLevelFive x y) (fun j => (b j : ℂ)) q).re =
        ∑ p, f p ((J p).map q.toEmbedding) := by
  let a := twoLevelFive x y
  let r := e.symm
  have h0 : a 0 = (x : ℂ) := rfl
  have h1 : a 1 = (y : ℂ) := rfl
  have h2 : a 2 = (x : ℂ) := rfl
  have h3 : a 3 = (y : ℂ) := rfl
  have hr (i : Fin 5) : r (e i) = i := e.symm_apply_apply i
  have h : ∀ i, ∃ u : ℝ, 0 < u ∧ a i = (u : ℂ) := by
    intro i
    unfold a twoLevelFive
    cases labelFive.symm i
    · exact ⟨x, hx, rfl⟩
    · exact ⟨y, hy, rfl⟩
  have ha_pos (i j : Fin 5) : 0 < (a i + (b j : ℂ)).re := by
    obtain ⟨u, hu, hi⟩ := h i
    simpa only [hi, Complex.add_re, Complex.ofReal_re] using add_pos hu (hb j)
  have ha_im (i j : Fin 5) : (a i + (b j : ℂ)).im = 0 := by
    obtain ⟨u, _, hi⟩ := h i
    simp [hi]
  let S : Finset (Fin 5) := ({e 0, e 1, e 2, e 3} : Finset (Fin 5))ᶜ
  have hg : ∃ P : ℝ, 0 < P ∧
      (∏ m ∈ S, (a (r m) + (b m : ℂ))) = (P : ℂ) := by
    refine ⟨∏ m ∈ S, (a (r m) + (b m : ℂ)).re,
      Finset.prod_pos (fun m _ => ha_pos (r m) m), ?_⟩
    rw [Complex.ofReal_prod]
    exact Finset.prod_congr rfl fun m _ => Complex.ext rfl (ha_im (r m) m)
  obtain ⟨P, hP, hprod⟩ := hg
  have h01 : b (e 1) - b (e 0) ≠ 0 := sub_ne_zero.mpr (hb'.ne (e.injective.ne (fun he => Nat.one_ne_zero (congrArg Fin.val he))))
  have h23 : b (e 3) - b (e 2) ≠ 0 := sub_ne_zero.mpr (hb'.ne (e.injective.ne (fun he => Nat.succ_ne_self 2 (congrArg Fin.val he))))
  have hval : ∀ i : Fin 5, (e.symm (e i)).val = i.val := fun i => congrArg Fin.val (hr i)
  have hh₁ : (e.symm (e 0)).val < (e.symm (e 1)).val := by rw [hval, hval]; exact Nat.zero_lt_one
  have hh₂ : (e.symm (e 1)).val < (e.symm (e 2)).val := by rw [hval, hval]; exact Nat.lt_succ_self _
  have hh₃ : (e.symm (e 2)).val < (e.symm (e 3)).val := by rw [hval, hval]; exact Nat.lt_succ_self _
  have ho := no_prefix_scores_of_matching_rectangle a (fun j => (b j : ℂ)) 1
    (fun i => (e.symm i).val) cut r (e 0) (e 1) (e 2) (e 3) hh₁ hh₂ hh₃
  simp only [one_mul] at ho
  apply ho
  change ((∏ m ∈ S, (a (r m) + (b m : ℂ))) *
    ((a (r (e 0)) - a (r (e 1))) * ((b (e 1) : ℂ) - (b (e 0) : ℂ))) *
    ((a (r (e 2)) - a (r (e 3))) * ((b (e 3) : ℂ) - (b (e 2) : ℂ)))).re ≠ 0
  rw [hprod, hr, hr, hr, hr, h0, h1, h2, h3]
  simp only [← Complex.ofReal_sub, ← Complex.ofReal_mul, Complex.ofReal_re]
  exact mul_ne_zero (mul_ne_zero hP.ne' (mul_ne_zero (sub_ne_zero.mpr hxy) h01))
    (mul_ne_zero (sub_ne_zero.mpr hxy) h23)

/-- There are realizable order-five profiles with all matching products
nonzero and at least twelve maximizing labels which are not additive
over any one chain of column prefixes. The twelve labels come from the
permutation group of the two equal-value row blocks, not a list of labels.
This is not an obstruction to a transposed chain or to a different
positive law. -/
theorem exists_saturated_five_no_column_prefix_scores
    (x y : ℝ) (b : Fin 5 → ℝ) (hxy : x ≠ y)
    (hx : 0 < x) (hy : 0 < y) (hb : ∀ j, 0 < b j) (hb' : Function.Injective b) :
    ∃ a : Fin 5 → ℂ,
      (∀ q, matchingProduct a (fun j => (b j : ℂ)) q ≠ 0) ∧
      (∃ r : Equiv.Perm (Fin 5),
        (∀ q, (matchingProduct a (fun j => (b j : ℂ)) q).re ≤
          (matchingProduct a (fun j => (b j : ℂ)) r).re) ∧
        Nat.factorial 3 * Nat.factorial 2 ≤
          (Finset.univ.filter fun q : Equiv.Perm (Fin 5) =>
            (matchingProduct a (fun j => (b j : ℂ)) q).re =
              (matchingProduct a (fun j => (b j : ℂ)) r).re).card) ∧
      ∀ (e : Equiv.Perm (Fin 5)) (cut : κ → ℕ),
        let J (p : κ) : Finset (Fin 5) := Finset.univ.filter (fun i => (e.symm i).val < cut p)
        ¬ ∃ f : κ → Finset (Fin 5) → ℝ, ∀ q,
          (matchingProduct a (fun j => (b j : ℂ)) q).re =
            ∑ p, f p ((J p).map q.toEmbedding) := by
  classical
  let a := twoLevelFive x y
  let B := fun j => (b j : ℂ)
  let P (q : Equiv.Perm (Fin 5)) := matchingProduct a B q
  refine ⟨a, ?_, ?_, twoLevelFive_swap_scores x y b hxy hx hy hb hb'⟩
  · intro q
    unfold matchingProduct
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    have hh : 0 < (a (q i) + B i).re := by
      unfold a twoLevelFive B
      cases labelFive.symm (q i)
      · simpa only [Sum.elim_inl, Complex.add_re, Complex.ofReal_re] using add_pos hx (hb i)
      · simpa only [Sum.elim_inr, Complex.add_re, Complex.ofReal_re] using add_pos hy (hb i)
    exact fun hz => hh.ne' (by rw [hz, Complex.zero_re])
  obtain ⟨r, _, hr⟩ := Finset.exists_max_image Finset.univ (fun q => (P q).re) ⟨1, Finset.mem_univ _⟩
  refine ⟨r, fun q => hr q (Finset.mem_univ _), ?_⟩
  let C := Finset.univ.filter fun q => (P q).re = (P r).re
  let L := Equiv.Perm (Fin 3) × Equiv.Perm (Fin 2)
  let f (v : L) := labelFive.permCongr (Equiv.sumCongr v.1 v.2) * r
  have hf (v : L) : f v ∈ C := by
    apply Finset.mem_filter.mpr; refine ⟨Finset.mem_univ _, ?_⟩
    have he : P (f v) = P r := by
      unfold P matchingProduct
      apply Finset.prod_congr rfl
      intro i _
      change a (labelFive.permCongr (Equiv.sumCongr v.1 v.2) (r i)) + B i = a (r i) + B i
      dsimp only [a]
      rw [twoLevelFive_row_symmetry]
    exact congrArg Complex.re he
  have hinj : Function.Injective f := by
    intro v w he
    have hq : Equiv.sumCongr v.1 v.2 = Equiv.sumCongr w.1 w.2 :=
      labelFive.permCongr.injective (mul_right_cancel he)
    apply Prod.ext
    · apply Equiv.ext
      intro i
      exact Sum.inl.inj (Equiv.congr_fun hq (Sum.inl i))
    · apply Equiv.ext
      intro i
      exact Sum.inr.inj (Equiv.congr_fun hq (Sum.inr i))
  have hd := Fintype.card_le_of_injective (fun v : L => (⟨f v, hf v⟩ : C))
    (fun v w he => hinj (congrArg Subtype.val he))
  rw [Fintype.card_coe] at hd
  simpa [L, C, P, B, Fintype.card_prod, Fintype.card_perm] using hd

end MOC
