import MOC.HarmonicSubsetMatchingTests
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset

/-! Coefficients and harmonicity of iterated differences along a finite matching. -/

namespace MOC

open Finset

variable {α K : Type*} [DecidableEq α] [Field K]

def subsetMatchingCoefficient : List (α × α) → Finset α → K
  | [], _ => 1
  | (l, r) :: p, S =>
    ((if l ∈ S then 1 else 0) - (if r ∈ S then 1 else 0)) * subsetMatchingCoefficient p S

theorem SubsetMatchingList.endpoints {L R : Finset α} {p : List (α × α)}
    (hp : SubsetMatchingList L R p) {v : α × α} (hv : v ∈ p) : v.1 ∈ L ∧ v.2 ∈ R := by
  induction hp with
  | nil => simp at hv
  | cons hl hr hp ih =>
    rcases List.mem_cons.mp hv with h | h
    · subst v; exact ⟨mem_insert_self _ _, mem_insert_self _ _⟩
    · exact ⟨mem_insert_of_mem (ih h).1, mem_insert_of_mem (ih h).2⟩

theorem SubsetMatchingList.coefficient_insert_outside {L R : Finset α} {p : List (α × α)}
    (hp : SubsetMatchingList L R p) {x : α} (hx : x ∉ L ∪ R) (S : Finset α) :
    subsetMatchingCoefficient (K := K) p (insert x S) = subsetMatchingCoefficient p S := by
  induction hp with
  | nil => rfl
  | @cons L R l r p hl hr hp ih =>
    have hlx : l ≠ x := by intro h; subst x; exact hx (mem_union_left _ (mem_insert_self _ _))
    have hrx : r ≠ x := by intro h; subst x; exact hx (mem_union_right _ (mem_insert_self _ _))
    have hx' : x ∉ L ∪ R := by simpa [mem_union, hx] using
      (show x ∉ L ∪ R from fun h => hx (by rcases mem_union.mp h with a | a
                                            · exact mem_union_left _ (mem_insert_of_mem a)
                                            · exact mem_union_right _ (mem_insert_of_mem a)))
    simp only [subsetMatchingCoefficient, mem_insert, hlx, hrx, false_or, ih hx']

private theorem fresh_matching_endpoints {L R : Finset α} {l r : α} (hl : l ∉ L) (hr : r ∉ R)
    (hd : Disjoint (insert l L) (insert r R)) :
    l ∉ L ∪ R ∧ r ∉ L ∪ R ∧ l ≠ r ∧ Disjoint L R := by
  have h := Finset.disjoint_left.mp hd (mem_insert_self l L)
  have h' := Finset.disjoint_right.mp hd (mem_insert_self r R)
  exact ⟨by simpa [mem_union, hl] using (fun hlR => h (mem_insert_of_mem hlR) : l ∉ R),
    by simpa [mem_union, hr] using (fun hrL => h' (mem_insert_of_mem hrL) : r ∉ L),
    fun e => h (mem_insert.mpr (.inl e)), hd.mono (subset_insert _ _) (subset_insert _ _)⟩

/-- The coefficient vector, paired with the input function, evaluates the matching difference. -/
theorem SubsetMatchingList.difference_sum {L R : Finset α} {p : List (α × α)}
    (hp : SubsetMatchingList L R p) (hd : Disjoint L R) (f : Finset α → K) :
    subsetMatchingDifference p f ∅ =
      ∑ S ∈ (L ∪ R).powerset, subsetMatchingCoefficient p S * f S := by
  induction hp generalizing f with
  | nil => simp [subsetMatchingDifference, subsetMatchingCoefficient]
  | @cons L R l r p hl hr hp ih =>
    obtain ⟨hlM, hrM, hne, hd'⟩ := fresh_matching_endpoints hl hr hd
    have he : insert l L ∪ insert r R = insert l (insert r (L ∪ R)) := by ext x; simp; tauto
    have hlr : l ∉ insert r (L ∪ R) := by simp [hne, hlM]
    rw [subsetMatchingDifference, ih hd', he, sum_powerset_insert hlr,
      sum_powerset_insert hrM, sum_powerset_insert hrM]
    simp only [← sum_add_distrib]
    apply sum_congr rfl
    intro S hS
    have hls := not_mem_mono (mem_powerset.mp hS) hlM
    have hrs := not_mem_mono (mem_powerset.mp hS) hrM
    simp only [subsetMatchingCoefficient, hls, hrs, if_false, mem_insert,
      hne, Ne.symm hne, false_or, eq_self_iff_true, true_or, if_true,
      hp.coefficient_insert_outside hlM, hp.coefficient_insert_outside hrM]
    ring

/-- The sum of the coefficients at all one-element extensions is zero.
Here the starting subset can have any cardinality. -/
theorem SubsetMatchingList.sum_extension_coefficient {L R : Finset α} {p : List (α × α)}
    (hp : SubsetMatchingList L R p) (hd : Disjoint L R) (S : Finset α) :
    (∑ x ∈ (L ∪ R) \ S, subsetMatchingCoefficient (K := K) p (insert x S)) = 0 := by
  induction hp with
  | nil => simp
  | @cons L R l r p hl hr hp ih =>
    obtain ⟨hlM, hrM, hne, hd'⟩ := fresh_matching_endpoints hl hr hd
    let M := L ∪ R
    have he : insert l L ∪ insert r R = insert l (insert r M) := by
      ext x; simp [M]; tauto
    have hbase : (∑ x ∈ M \ S,
        subsetMatchingCoefficient (K := K) ((l, r) :: p) (insert x S)) = 0 := by
      let a : K := (if l ∈ S then 1 else 0) - (if r ∈ S then 1 else 0)
      calc
        _ = ∑ x ∈ M \ S, a * subsetMatchingCoefficient p (insert x S) := by
          refine sum_congr rfl fun x hx => ?_
          have hxM := (mem_sdiff.mp hx).1
          have hlx : l ≠ x := fun h => hlM (h ▸ hxM)
          have hrx : r ≠ x := fun h => hrM (h ▸ hxM)
          simp only [subsetMatchingCoefficient, mem_insert, hlx, hrx, false_or, a]
        _ = 0 := by rw [← mul_sum, ih hd', mul_zero]
    have hl' : l ∉ M \ S := fun h => hlM (mem_sdiff.mp h).1
    have hr' : r ∉ M \ S := fun h => hrM (mem_sdiff.mp h).1
    have hlr : l ∉ insert r (M \ S) := by simp [hne, hl']
    rw [he]
    by_cases hls : l ∈ S <;> by_cases hrs : r ∈ S <;>
      simp only [*, insert_sdiff_of_mem, insert_sdiff_of_not_mem, sum_insert,
        subsetMatchingCoefficient, mem_insert, false_or, true_or, eq_self_iff_true,
        if_true, if_false, hp.coefficient_insert_outside hlM, hp.coefficient_insert_outside hrM]
        <;> ring

theorem SubsetMatchingList.coefficient_formula {L R : Finset α} {p : List (α × α)}
    (hp : SubsetMatchingList L R p) (S : Finset α) :
    subsetMatchingCoefficient (K := K) p S =
      if ∀ v ∈ p, (v.1 ∈ S ↔ v.2 ∉ S)
      then (-1 : K) ^ (R ∩ S).card else 0 := by
  classical
  induction hp with
  | nil => simp [subsetMatchingCoefficient]
  | @cons L R l r p hl hr hp ih =>
    rw [subsetMatchingCoefficient, ih]
    have hall : (∀ v ∈ (l, r) :: p, (v.1 ∈ S ↔ v.2 ∉ S)) ↔
        (l ∈ S ↔ r ∉ S) ∧ (∀ v ∈ p, (v.1 ∈ S ↔ v.2 ∉ S)) := by simp
    have hr' : r ∉ R ∩ S := fun h => hr (mem_inter.mp h).1
    by_cases hls : l ∈ S <;> by_cases hrs : r ∈ S <;>
      by_cases hs : ∀ v ∈ p, (v.1 ∈ S ↔ v.2 ∉ S) <;>
      simp [hall, hls, hrs, hs, insert_inter_of_mem, insert_inter_of_not_mem, hr',
        pow_succ]

end MOC
