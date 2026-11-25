import MOC.ContactCensus
import Mathlib.Algebra.BigOperators.Group.List.Basic

/-! A balanced exchange of matchings forces a missing zero-height contact. -/

open BigOperators

namespace MOC

private theorem matching_list_prod {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a b : ι → ℂ) (L : List (Equiv.Perm ι)) :
    (L.map (matchingProduct a b)).prod =
      ∏ j, (L.map (fun σ => a (σ j) + b j)).prod := by
  induction L with
  | nil => simp
  | cons σ L ih =>
      rw [List.map_cons, List.prod_cons, ih, matchingProduct]
      simp only [List.map_cons, List.prod_cons, Finset.prod_mul_distrib]

private theorem matching_list_prod_scaled {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a b : ι → ℂ) (z : ℂ) (L : List (Equiv.Perm ι)) :
    (L.map (fun σ => z * matchingProduct a b σ)).prod =
      z ^ L.length * (L.map (matchingProduct a b)).prod := by
  induction L with
  | nil => simp
  | cons σ L ih =>
      simp only [List.map_cons, List.prod_cons, List.length_cons, pow_succ, ih]
      ring

private theorem prod_map_real_ne_zero {α : Type*} (f : α → ℂ) (L : List α)
    (h : ∀ i ∈ L, (f i).im = 0 ∧ f i ≠ 0) :
    ((L.map f).prod).im = 0 ∧ (L.map f).prod ≠ 0 := by
  induction L with
  | nil => simp
  | cons i L ih =>
      obtain ⟨hi, hi₀⟩ := h i (by simp)
      obtain ⟨hL, hL₀⟩ := ih (fun j hj => h j (by simp [hj]))
      simp only [List.map_cons, List.prod_cons]
      exact ⟨by simp [Complex.mul_im, hi, hL], mul_ne_zero hi₀ hL₀⟩

/-- If two lists of matchings assign the same multiset of rows to each
column, one missing contact at zero height is forced by all the other
contacts. Repeated matchings in either list are allowed. -/
theorem matchingProduct_re_eq_zero_of_balanced_exchange
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (a b : ι → ℂ) (η : ℂ) (hη : η ≠ 0) (hab : ∀ i j, a i + b j ≠ 0)
    (σ : Equiv.Perm ι) (L R : List (Equiv.Perm ι))
    (hcols : ∀ j, ((σ :: L).map (fun τ => τ j)).Perm (R.map (fun τ => τ j)))
    (hL : ∀ τ ∈ L, (η * matchingProduct a b τ).re = 0)
    (hR : ∀ τ ∈ R, (η * matchingProduct a b τ).re = 0) :
    (η * matchingProduct a b σ).re = 0 := by
  let z := -Complex.I * η
  let f (τ : Equiv.Perm ι) := z * matchingProduct a b τ
  have hh (τ : Equiv.Perm ι) : (f τ).im = -(η * matchingProduct a b τ).re := by
    dsimp only [f, z]
    rw [mul_assoc]
    simp [Complex.mul_im]
  have hne (τ : Equiv.Perm ι) : f τ ≠ 0 :=
    mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) hη)
      (Finset.prod_ne_zero_iff.mpr (fun j _ => hab (τ j) j))
  have hlen : (σ :: L).length = R.length := by
    simpa only [List.length_map] using (hcols (Classical.choice (inferInstance : Nonempty ι))).length_eq
  have hprod : ((σ :: L).map (matchingProduct a b)).prod = (R.map (matchingProduct a b)).prod := by
    rw [matching_list_prod, matching_list_prod]
    apply Finset.prod_congr rfl
    intro j _
    simpa only [List.map_map, Function.comp_apply] using
      ((hcols j).map (fun i => a i + b j)).prod_eq
  have he : ((σ :: L).map f).prod = (R.map f).prod := by
    dsimp only [f]
    rw [matching_list_prod_scaled, matching_list_prod_scaled, hlen, hprod]
  obtain ⟨hLim, hLn⟩ := prod_map_real_ne_zero f L
    (fun τ hτ => ⟨by simp only [hh, hL τ hτ, neg_zero], hne τ⟩)
  obtain ⟨hRim, _⟩ := prod_map_real_ne_zero f R
    (fun τ hτ => ⟨by simp only [hh, hR τ hτ, neg_zero], hne τ⟩)
  have hLre : ((L.map f).prod).re ≠ 0 := fun h => hLn (Complex.ext h hLim)
  have him := congrArg Complex.im he
  change (f σ * (L.map f).prod).im = ((R.map f).prod).im at him
  rw [Complex.mul_im, hLim, hRim, mul_zero, zero_add, hh] at him
  exact neg_eq_zero.mp ((mul_eq_zero.mp him).resolve_right hLre)

/-- The forced matching indices for face representatives
5, 11, 12, 19, 22, 24, 31, 38, 43, and 45 in the zero-height census. -/
def fourZeroHeightForcedIndex : Fin 10 → Fin 24 :=
  ![10, 13, 15, 17, 13, 6, 7, 10, 14, 21]

/-- Known contacts on the same side of each exchange as its forced matching. -/
def fourZeroHeightExchangeLeft : Fin 10 → List (Fin 24) :=
  ![[0, 3], [0, 4], [2, 6], [2, 7], [0, 4], [3, 10], [5, 12], [1, 12], [2, 7], [2, 10, 13]]

/-- Known contacts on the opposite side of each balanced exchange. -/
def fourZeroHeightExchangeRight : Fin 10 → List (Fin 24) :=
  ![[1, 5, 8], [1, 5, 12], [0, 9, 12], [4, 9, 12], [1, 5, 12],
    [5, 7, 8], [4, 6, 13], [4, 7, 14], [1, 8, 12], [5, 9, 14, 18]]

private theorem fourZeroHeight_exchange_columns : ∀ (k : Fin 10) (j : Fin 4),
    (((fourPerm (fourZeroHeightForcedIndex k)).symm :: (fourZeroHeightExchangeLeft k).map
      (fun i => (fourPerm i).symm)).map (fun σ => σ j)).Perm
      (((fourZeroHeightExchangeRight k).map (fun i => (fourPerm i).symm)).map (fun σ => σ j)) := by
  intro k j
  fin_cases k <;> fin_cases j <;> decide

/-- The ten explicit exchanges each force an additional zero-height
contact, so their listed forced matching cannot be strictly inactive. -/
theorem fourZeroHeight_exchange_forces_contact (a b : Fin 4 → ℂ) (η : ℂ)
    (hη : η ≠ 0) (hab : ∀ i j, a i + b j ≠ 0) (k : Fin 10)
    (hc : ∀ i ∈ fourZeroHeightExchangeLeft k ++ fourZeroHeightExchangeRight k,
      (η * matchingProduct a b (fourPerm i).symm).re = 0) :
    (η * matchingProduct a b (fourPerm (fourZeroHeightForcedIndex k)).symm).re = 0 := by
  apply matchingProduct_re_eq_zero_of_balanced_exchange a b η hη hab _ _ _
    (fourZeroHeight_exchange_columns k)
  · intro σ hσ
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hσ
    exact hc i (List.mem_append.mpr (Or.inl hi))
  · intro σ hσ
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hσ
    exact hc i (List.mem_append.mpr (Or.inr hi))

end MOC
