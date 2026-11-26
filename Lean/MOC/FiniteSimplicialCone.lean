import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.Ring

/-! Signed simplicial boundary, cone and section operators on a finite
ordered vertex set. The empty face gives the augmented grading. -/

open Finset BigOperators

namespace MOC

variable {α : Type*} [Fintype α] [LinearOrder α]

private abbrev incidenceSign (s : Finset α) (v : α) : ℤ :=
  (-1 : ℤ) ^ (s.filter (fun a => a < v)).card

/-- The coefficient of the ordered simplicial boundary at each face. -/
def finiteSimplicialBoundary (c : Finset α → ℤ) (s : Finset α) : ℤ :=
  ∑ v ∈ univ \ s, incidenceSign s v * c (insert v s)

/-- Coning a chain with the specified vertex. Its coefficient is zero
on faces that omit that vertex. -/
def finiteSimplicialCone (v : α) (c : Finset α → ℤ) (s : Finset α) : ℤ :=
  if v ∈ s then incidenceSign (s.erase v) v * c (s.erase v) else 0

/-- Taking the signed section of a chain through the specified vertex. -/
def finiteSimplicialSection (v : α) (c : Finset α → ℤ) (s : Finset α) : ℤ :=
  if v ∉ s then incidenceSign s v * c (insert v s) else 0

private theorem incidenceSign_mul_self (s : Finset α) (v : α) :
    incidenceSign s v * incidenceSign s v = 1 := by
  change ((-1 : ℤ) ^ (s.filter (fun a => a < v)).card) *
    ((-1 : ℤ) ^ (s.filter (fun a => a < v)).card) = 1
  rw [← mul_pow]
  simp

private theorem incidenceSign_insert_lt (s : Finset α) (v w : α)
    (hv : v ∉ s) (hlt : v < w) :
    incidenceSign (insert v s) w = -incidenceSign s w := by
  have hfilter : v ∉ s.filter (fun a => a < w) := fun h => hv (mem_filter.mp h).1
  change (-1 : ℤ) ^ ((insert v s).filter (fun a => a < w)).card =
    -((-1 : ℤ) ^ (s.filter (fun a => a < w)).card)
  rw [filter_insert, if_pos hlt, card_insert_of_not_mem hfilter, pow_succ, mul_neg, mul_one]

private theorem incidenceSign_insert_ge (s : Finset α) (v w : α) (h : ¬v < w) :
    incidenceSign (insert v s) w = incidenceSign s w := by
  change (-1 : ℤ) ^ ((insert v s).filter (fun a => a < w)).card =
    (-1 : ℤ) ^ (s.filter (fun a => a < w)).card
  rw [filter_insert, if_neg h]

private theorem incidenceSign_two_insertions (s : Finset α) (v w : α)
    (hv : v ∉ s) (hw : w ∉ s) (hne : w ≠ v) :
    incidenceSign s w * incidenceSign (insert w s) v =
      -(incidenceSign s v * incidenceSign (insert v s) w) := by
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · rw [incidenceSign_insert_lt s w v hw hlt,
      incidenceSign_insert_ge s v w (not_lt_of_ge hlt.le)]
    ring
  · rw [incidenceSign_insert_lt s v w hv hgt,
      incidenceSign_insert_ge s w v (not_lt_of_ge hgt.le)]
    ring

private theorem incidenceSign_insert_product (s : Finset α) (v w : α)
    (hv : v ∉ s) (hw : w ∉ s) (hne : w ≠ v) :
    incidenceSign (insert v s) w * incidenceSign (insert w s) v =
      -(incidenceSign s v * incidenceSign s w) := by
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · rw [incidenceSign_insert_lt s w v hw hlt,
      incidenceSign_insert_ge s v w (not_lt_of_ge hlt.le)]
    ring
  · rw [incidenceSign_insert_lt s v w hv hgt,
      incidenceSign_insert_ge s w v (not_lt_of_ge hgt.le)]
    ring

private theorem sum_omitted_insert (s : Finset α) (v : α) (hv : v ∉ s)
    (f : α → ℤ) :
    (∑ w ∈ univ \ s, f w) = f v + ∑ w ∈ univ \ insert v s, f w := by
  have he : insert v (univ \ insert v s) = univ \ s :=
    Finset.sdiff_insert_insert_of_mem_of_not_mem (mem_univ v) hv
  have hn : v ∉ univ \ insert v s := by simp
  rw [← he, sum_insert hn]

private theorem omitted_insert_not_mem {s : Finset α} {v w : α}
    (hw : w ∈ univ \ insert v s) : w ≠ v ∧ w ∉ s := by
  have h := (mem_sdiff.mp hw).2
  exact ⟨fun he => h (mem_insert.mpr (Or.inl he)), fun hs => h (mem_insert_of_mem hs)⟩

private theorem not_mem_insert_of_omitted {s : Finset α} {v w : α}
    (hv : v ∉ s) (hw : w ∈ univ \ insert v s) : v ∉ insert w s := by
  intro h
  exact (mem_insert.mp h).elim (omitted_insert_not_mem hw).1.symm hv

private theorem cone_insert (v : α) (c : Finset α → ℤ) {s : Finset α} (hv : v ∉ s) :
    finiteSimplicialCone v c (insert v s) = incidenceSign s v * c s := by
  rw [finiteSimplicialCone, if_pos (mem_insert_self v s), erase_insert hv]

private theorem boundary_cone_of_not_mem (v : α) (c : Finset α → ℤ)
    (s : Finset α) (hv : v ∉ s) :
    finiteSimplicialBoundary (finiteSimplicialCone v c) s = c s := by
  unfold finiteSimplicialBoundary
  rw [sum_omitted_insert s v hv, cone_insert v c hv,
    ← mul_assoc, incidenceSign_mul_self, one_mul]
  have hz : (∑ w ∈ univ \ insert v s,
      incidenceSign s w * finiteSimplicialCone v c (insert w s)) = 0 := by
    apply Finset.sum_eq_zero
    intro w hw
    rw [finiteSimplicialCone, if_neg (not_mem_insert_of_omitted hv hw), mul_zero]
  rw [hz, add_zero]

private theorem boundary_cone_on_insert (v : α) (c : Finset α → ℤ)
    (s : Finset α) (hv : v ∉ s) :
    finiteSimplicialBoundary (finiteSimplicialCone v c) (insert v s) =
      -(incidenceSign s v * ∑ w ∈ univ \ insert v s,
          incidenceSign s w * c (insert w s)) := by
  unfold finiteSimplicialBoundary
  rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro w hw
  obtain ⟨hne, hws⟩ := omitted_insert_not_mem hw
  rw [Finset.insert_comm w v s, cone_insert v c (not_mem_insert_of_omitted hv hw),
    ← mul_assoc, incidenceSign_insert_product s v w hv hws hne, neg_mul, mul_assoc]

private theorem cone_boundary_on_insert (v : α) (c : Finset α → ℤ)
    (s : Finset α) (hv : v ∉ s) :
    finiteSimplicialCone v (finiteSimplicialBoundary c) (insert v s) =
      c (insert v s) + incidenceSign s v * ∑ w ∈ univ \ insert v s,
        incidenceSign s w * c (insert w s) := by
  rw [cone_insert v (finiteSimplicialBoundary c) hv]
  unfold finiteSimplicialBoundary
  rw [sum_omitted_insert s v hv, mul_add, ← mul_assoc, incidenceSign_mul_self, one_mul]

/-- The ambient cone is a contracting homotopy for the augmented
simplicial boundary on all vertex subsets. -/
theorem finiteSimplicialBoundary_cone_add_cone_boundary
    (v : α) (c : Finset α → ℤ) :
    finiteSimplicialBoundary (finiteSimplicialCone v c) +
      finiteSimplicialCone v (finiteSimplicialBoundary c) = c := by
  funext s
  change finiteSimplicialBoundary (finiteSimplicialCone v c) s +
    finiteSimplicialCone v (finiteSimplicialBoundary c) s = c s
  by_cases hv : v ∈ s
  · have hs : insert v (s.erase v) = s := insert_erase hv
    rw [← hs, boundary_cone_on_insert v c _ (not_mem_erase v s),
      cone_boundary_on_insert v c _ (not_mem_erase v s)]
    ring
  · rw [boundary_cone_of_not_mem v c s hv, finiteSimplicialCone, if_neg hv, add_zero]

private theorem boundary_section_of_mem (v : α) (c : Finset α → ℤ) (s : Finset α)
    (hv : v ∈ s) : finiteSimplicialBoundary (finiteSimplicialSection v c) s = 0 := by
  unfold finiteSimplicialBoundary
  apply Finset.sum_eq_zero
  intro w _
  have h : v ∈ insert w s := mem_insert_of_mem hv
  rw [finiteSimplicialSection, if_neg (not_not.mpr h), mul_zero]

private theorem boundary_section_of_not_mem (v : α) (c : Finset α → ℤ) (s : Finset α)
    (hv : v ∉ s) :
    finiteSimplicialBoundary (finiteSimplicialSection v c) s =
      -(incidenceSign s v * finiteSimplicialBoundary c (insert v s)) := by
  unfold finiteSimplicialBoundary
  rw [sum_omitted_insert s v hv]
  have hz : finiteSimplicialSection v c (insert v s) = 0 := by
    rw [finiteSimplicialSection, if_neg (not_not.mpr (mem_insert_self v s))]
  rw [hz, mul_zero, zero_add, Finset.mul_sum, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro w hw
  obtain ⟨hne, hws⟩ := omitted_insert_not_mem hw
  rw [finiteSimplicialSection, if_pos (not_mem_insert_of_omitted hv hw),
    ← mul_assoc, incidenceSign_two_insertions s v w hv hws hne,
    Finset.insert_comm v w s, neg_mul, mul_assoc]

/-- The section through a vertex anticommutes with the boundary. -/
theorem finiteSimplicialSection_boundary (v : α) (c : Finset α → ℤ) :
    finiteSimplicialSection v (finiteSimplicialBoundary c) =
      -finiteSimplicialBoundary (finiteSimplicialSection v c) := by
  funext s
  change finiteSimplicialSection v (finiteSimplicialBoundary c) s =
    -(finiteSimplicialBoundary (finiteSimplicialSection v c) s)
  by_cases hv : v ∈ s
  · rw [finiteSimplicialSection, if_neg (not_not.mpr hv),
      boundary_section_of_mem v c s hv, neg_zero]
  · rw [finiteSimplicialSection, if_pos hv, boundary_section_of_not_mem v c s hv, neg_neg]

/-- The section recovers a chain from its cone when that chain is
supported on faces that omit the cone vertex. -/
theorem finiteSimplicialSection_cone (v : α) (c : Finset α → ℤ)
    (hc : ∀ s, v ∈ s → c s = 0) :
    finiteSimplicialSection v (finiteSimplicialCone v c) = c := by
  funext s
  by_cases hv : v ∈ s
  · rw [finiteSimplicialSection, if_neg (not_not.mpr hv), hc s hv]
  · rw [finiteSimplicialSection, if_pos hv, cone_insert v c hv,
      ← mul_assoc, incidenceSign_mul_self, one_mul]

end MOC
