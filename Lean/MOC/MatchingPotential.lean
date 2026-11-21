import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Fintype.List
import Mathlib.GroupTheory.Perm.List

/-! A modulus-maximizing diagonal gives positive diagonal scaling factors. -/

open BigOperators
open scoped NNReal

namespace MOC

variable {ι : Type*} [Fintype ι]

private def pathProduct (w : ι → ι → ℝ≥0) : ι → List ι → ℝ≥0
  | _, [] => 1
  | i, j :: l => w i j * pathProduct w j l

private theorem pathProduct_split (w : ι → ι → ℝ≥0) (i j : ι) (l r : List ι) :
    pathProduct w i (l ++ j :: r) =
      pathProduct w i (l ++ [j]) * pathProduct w j r := by
  induction l generalizing i with
  | nil => simp [pathProduct]
  | cons a l ih => simp [pathProduct, ih, mul_assoc]

private theorem pathProduct_snoc (w : ι → ι → ℝ≥0) (i j : ι) (l : List ι) :
    pathProduct w i (l ++ [j]) = (List.zipWith w (i :: l) (l ++ [j])).prod := by
  induction l generalizing i with
  | nil => simp [pathProduct]
  | cons a l ih => simp [pathProduct, ih]

private theorem pathProduct_cycle_le_one (w : ι → ι → ℝ≥0) (hdiag : ∀ i, w i i = 1)
    (hperm : ∀ σ : Equiv.Perm ι, (∏ i, w i (σ i)) ≤ 1)
    (i : ι) (l : List ι) (hl : (i :: l).Nodup) :
    pathProduct w i (l ++ [i]) ≤ 1 := by
  classical
  let σ := (i :: l).formPerm
  have hzip : (i :: l).map (fun j => w j (σ j)) = List.zipWith w (i :: l) (l ++ [i]) := by
    apply List.ext_getElem
    · simp
    · intro k hk _
      have hk' : k < (i :: l).length := by simpa only [List.length_map] using hk
      have hkTail : k < (l ++ [i]).length := by simpa using hk'
      simp only [List.getElem_map, List.getElem_zipWith]
      change w ((i :: l)[k]'hk') (σ ((i :: l)[k]'hk')) =
        w ((i :: l)[k]'hk') ((l ++ [i])[k]'hkTail)
      by_cases h : k < l.length
      · have hnext : k + 1 < (i :: l).length := by simpa using h
        rw [show σ (i :: l)[k] = (i :: l)[k + 1] from List.formPerm_apply_lt_getElem _ hl _ hnext,
          List.getElem_append_left h, List.getElem_cons_succ]
      · have hk'' : k = l.length := by simp only [List.length_cons] at hk'; omega
        subst k
        rw [show σ (i :: l)[l.length] = i from List.formPerm_apply_getElem_length _ _,
          List.getElem_append_right (Nat.le_refl _)]
        simp
  have hprod : (∏ j ∈ (i :: l).toFinset, w j (σ j)) = ∏ j, w j (σ j) := by
    apply Finset.prod_subset (Finset.subset_univ _)
    intro j _ hj
    have hj' : j ∉ i :: l := fun h => hj (List.mem_toFinset.mpr h)
    rw [show σ j = j from List.formPerm_eq_self_of_not_mem _ _ hj', hdiag]
  rw [pathProduct_snoc, ← hzip, ← List.prod_toFinset _ hl, hprod]
  exact hperm σ

/-- If the diagonal has weight one and maximizes the matching product,
there are positive potentials making every directed edge weight at most one
after diagonal scaling. Zeros are allowed among the off-diagonal weights. -/
theorem exists_matching_potential (w : ι → ι → ℝ≥0) (hdiag : ∀ i, w i i = 1)
    (hperm : ∀ σ : Equiv.Perm ι, (∏ i, w i (σ i)) ≤ 1) :
    ∃ s : ι → ℝ≥0, (∀ i, 1 ≤ s i) ∧ ∀ i j, w i j * s j ≤ s i := by
  classical
  let Word := {l : List ι // l.Nodup}
  let paths (i : ι) : Finset Word := Finset.univ.filter fun l => i ∉ l.val
  have hpaths (i : ι) (l : Word) : l ∈ paths i ↔ (i :: l.val).Nodup := by
    simp [paths, List.nodup_cons, l.property]
  let empty : Word := ⟨[], List.nodup_nil⟩
  have hmax (i : ι) : ∃ l ∈ paths i, ∀ r ∈ paths i,
      pathProduct w i r.val ≤ pathProduct w i l.val :=
    (paths i).exists_max_image (fun r => pathProduct w i r.val)
      ⟨empty, (hpaths i empty).mpr (by simp [empty])⟩
  choose l hl hbest using hmax
  let s (i : ι) := pathProduct w i (l i).val
  have hbound (i : ι) (r : List ι) (hr : (i :: r).Nodup) : pathProduct w i r ≤ s i :=
    hbest i ⟨r, hr.of_cons⟩ ((hpaths i ⟨r, hr.of_cons⟩).mpr hr)
  refine ⟨s, fun i => hbound i [] (by simp), fun i j => ?_⟩
  have hsimp : (j :: (l j).val).Nodup := (hpaths j _).mp (hl j)
  change pathProduct w i (j :: (l j).val) ≤ s i
  by_cases hi : i ∈ j :: (l j).val
  · obtain ⟨pre, post, hp⟩ := List.append_of_mem hi
    have hn : (pre ++ i :: post).Nodup := hp ▸ hsimp
    obtain ⟨hpre, hpost, hd⟩ := List.nodup_append.mp hn
    have hcycle : (i :: pre).Nodup :=
      List.nodup_cons.mpr ⟨fun h => hd h (by simp), hpre⟩
    rw [hp, pathProduct_split]
    exact (mul_le_mul_right' (pathProduct_cycle_le_one w hdiag hperm i pre hcycle) _).trans
      (by simpa only [one_mul] using hbound i post hpost)
  · exact hbound i _ (List.nodup_cons.mpr ⟨hi, hsimp⟩)

/-- A complex kernel with diagonal entries one and no matching of modulus
larger than one admits positive real modulus potentials. -/
theorem exists_matching_norm_potential (m : ι → ι → ℂ) (hdiag : ∀ i, m i i = 1)
    (hperm : ∀ σ : Equiv.Perm ι, ‖∏ i, m i (σ i)‖ ≤ 1) :
    ∃ s : ι → ℝ≥0, (∀ i, 1 ≤ s i) ∧ ∀ i j, ‖m i j‖₊ * s j ≤ s i := by
  apply exists_matching_potential (fun i j => ‖m i j‖₊)
  · intro i
    simp [hdiag]
  · intro σ
    change (∏ i, (nnnormHom : ℂ →*₀ ℝ≥0) (m i (σ i))) ≤ 1
    rw [← map_prod]
    exact NNReal.coe_le_coe.mp (hperm σ)

end MOC
