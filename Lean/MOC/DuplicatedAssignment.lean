import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.GroupTheory.Perm.Basic

/-! A maximizing multiplicative assignment remains maximizing after duplication
of a matched row and column, provided its product is positive. -/

open BigOperators

namespace MOC

noncomputable section

private def duplicatedSlots {ι : Type*} [DecidableEq ι] (i : ι) :
    (Option ι ⊕ {j : ι // j ≠ i}) ≃ ι × Bool where
  toFun
    | .inl none => (i, true)
    | .inl (.some j) => (j, false)
    | .inr j => (j, true)
  invFun
    | (j, false) => .inl (.some j)
    | (j, true) => if h : j = i then .inl none else .inr ⟨j, h⟩
  left_inv := by
    intro x
    rcases x with (o | ⟨j, hj⟩)
    · cases o <;> simp
    · simp [hj]
  right_inv := by
    rintro ⟨j, b⟩
    cases b
    · rfl
    · by_cases h : j = i
      · subst j
        simp
      · simp [h]

private theorem duplicatedSlots_fst_inl {ι : Type*} [DecidableEq ι] (i : ι)
    (j : Option ι) : (duplicatedSlots i (Sum.inl j)).1 = j.getD i := by
  cases j <;> rfl

/-- The edges of a permutation on two copies of a finite index set give
two permutations after the copies of each index are identified. -/
private theorem two_slot_assignments {ι : Type*} [Fintype ι]
    (s : Equiv.Perm (ι × Bool)) (w : ι → ι → ℝ) :
    ∃ p q : Equiv.Perm ι,
      (∏ x : ι × Bool, w (s x).1 x.1) = (∏ j, w (p j) j) * ∏ j, w (q j) j := by
  classical
  let t (j : ι) : Finset ι := { (s (j, false)).1, (s (j, true)).1 }
  have hHall (S : Finset ι) : S.card ≤ (S.biUnion t).card := by
    have hsub :
        ((S ×ˢ (Finset.univ : Finset Bool)).image s) ⊆
          (S.biUnion t) ×ˢ (Finset.univ : Finset Bool) := by
      intro y hy
      obtain ⟨⟨j, b⟩, hx, rfl⟩ := Finset.mem_image.mp hy
      rw [Finset.mem_product] at hx ⊢
      refine ⟨Finset.mem_biUnion.mpr ⟨j, hx.1, ?_⟩, Finset.mem_univ _⟩
      cases b <;> simp [t]
    have hc := Finset.card_le_card hsub
    rw [Finset.card_image_of_injective _ s.injective, Finset.card_product,
      Finset.card_product, Finset.card_univ, Fintype.card_bool] at hc
    omega
  obtain ⟨f, hf, hm⟩ :=
    (Finset.all_card_le_biUnion_card_iff_existsInjective' t).mp hHall
  have hchoose (j : ι) : ∃ b : Bool, (s (j, b)).1 = f j := by
    have hj : f j = (s (j, false)).1 ∨ f j = (s (j, true)).1 := by
      simpa [t] using hm j
    rcases hj with h | h
    · exact ⟨false, h.symm⟩
    · exact ⟨true, h.symm⟩
  choose b hb using hchoose
  let g (j : ι) := (s (j, !(b j))).1
  let p : Equiv.Perm ι := Equiv.ofBijective f (Finite.injective_iff_bijective.mp hf)
  have hne (j k : ι) : s (j, !(b j)) ≠ s (k, b k) := by
    intro h
    have hslots := s.injective h
    have hjk := congrArg Prod.fst hslots
    change j = k at hjk
    subst k
    have hbool := congrArg Prod.snd hslots
    change (!(b j)) = b j at hbool
    cases bj : b j <;> simp [bj] at hbool
  have hg : Function.Injective g := by
    intro j k hjk
    change (s (j, !(b j))).1 = (s (k, !(b k))).1 at hjk
    obtain ⟨a, ha⟩ := p.surjective (s (j, !(b j))).1
    have hrow : (s (a, b a)).1 = (s (j, !(b j))).1 := (hb a).trans ha
    have hleft : (s (j, !(b j))).2 ≠ (s (a, b a)).2 := by
      intro h
      exact hne j a (Prod.ext hrow.symm h)
    have hright : (s (k, !(b k))).2 ≠ (s (a, b a)).2 := by
      intro h
      exact hne k a (Prod.ext (hrow.trans hjk).symm h)
    have sameBool (x y z : Bool) (hx : x ≠ z) (hy : y ≠ z) : x = y := by
      cases x <;> cases y <;> cases z <;> simp_all
    have hbool : (s (j, !(b j))).2 = (s (k, !(b k))).2 := sameBool _ _ _ hleft hright
    exact congrArg Prod.fst (s.injective (Prod.ext hjk hbool))
  let q : Equiv.Perm ι := Equiv.ofBijective g (Finite.injective_iff_bijective.mp hg)
  refine ⟨p, q, ?_⟩
  rw [Fintype.prod_prod_type, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j _
  rw [Fintype.prod_bool]
  change w (s (j, true)).1 j * w (s (j, false)).1 j = w (f j) j * w (g j) j
  rw [← hb j]
  cases bj : b j
  · simp [bj, g, mul_comm]
  · simp [bj, g]

/-- Duplicate a row and column matched by the identity assignment. If the
identity assignment maximizes the product and its product is positive, its
extension to the two copies still maximizes the product. -/
theorem duplicated_assignment_le {ι : Type*} [Fintype ι] (i : ι) (w : ι → ι → ℝ)
    (hw : ∀ a b, 0 ≤ w a b) (hpos : 0 < ∏ j, w j j)
    (hmax : ∀ p : Equiv.Perm ι, (∏ j, w (p j) j) ≤ ∏ j, w j j)
    (τ : Equiv.Perm (Option ι)) :
    (∏ j, w ((τ j).getD i) (j.getD i)) ≤ w i i * ∏ j, w j j := by
  classical
  let e := duplicatedSlots i
  let u : Equiv.Perm (Option ι ⊕ {j : ι // j ≠ i}) :=
    Equiv.sumCongr τ (Equiv.refl _)
  let s : Equiv.Perm (ι × Bool) := (e.symm.trans u).trans e
  obtain ⟨p, q, hpq⟩ := two_slot_assignments s w
  have he : (∏ x : ι × Bool, w (s x).1 x.1) =
      (∏ j, w ((τ j).getD i) (j.getD i)) * ∏ j : {j : ι // j ≠ i}, w j.val j.val := by
    calc
      (∏ x : ι × Bool, w (s x).1 x.1) =
          ∏ x : Option ι ⊕ {j : ι // j ≠ i}, w (e (u x)).1 (e x).1 :=
        (Fintype.prod_equiv e (fun x => w (e (u x)).1 (e x).1)
          (fun x => w (s x).1 x.1) (fun x => by simp [s])).symm
      _ = _ := by
        rw [Fintype.prod_sum_type]
        refine congrArg₂ (· * ·) ?_ ?_
        · apply Finset.prod_congr rfl
          intro j _
          change w (duplicatedSlots i (Sum.inl (τ j))).1 (duplicatedSlots i (Sum.inl j)).1 = _
          rw [duplicatedSlots_fst_inl, duplicatedSlots_fst_inl]
        · rfl
  have hdiag : w i i * (∏ j : {j : ι // j ≠ i}, w j.val j.val) = ∏ j, w j j := by
    rw [← Finset.prod_subtype (Finset.univ.erase i)
      (by simp : ∀ j, j ∈ Finset.univ.erase i ↔ j ≠ i) (fun j => w j j)]
    exact Finset.mul_prod_erase Finset.univ (fun j => w j j) (Finset.mem_univ i)
  have hrest : 0 < ∏ j : {j : ι // j ≠ i}, w j.val j.val := by
    have hnonneg : 0 ≤ ∏ j : {j : ι // j ≠ i}, w j.val j.val :=
      Finset.prod_nonneg (fun j _ => hw j.val j.val)
    refine lt_of_le_of_ne hnonneg (Ne.symm ?_)
    intro h
    rw [h, mul_zero] at hdiag
    exact (ne_of_gt hpos) hdiag.symm
  apply le_of_mul_le_mul_right _ hrest
  rw [← he, hpq, mul_right_comm, hdiag]
  exact mul_le_mul (hmax p) (hmax q) (Finset.prod_nonneg (fun j _ => hw _ _)) hpos.le

end

end MOC
