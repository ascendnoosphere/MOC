import MOC.WeightedDiamondSparseCut

/-! Kernel-checked finite tests for sparse ray certificates. -/

namespace MOC.RayCoefficients.FiniteRayChecks

theorem witnessesValid_of_check {m n : ℕ} (d : SparseRayCutPlan m n)
    (old : Fin m → Row) (s : Finset (Fin 24))
    (hat : ∀ k : Fin m, ∀ i ∈ s, (d.positiveAt i).testBit k.val = positive (old k i))
    (coords : List (Fin 24)) (hcoords : ∀ i ∈ s, i ∈ coords)
    (h : ∀ k, (d.witnesses k).all (fun r =>
      decide (r.1 ≠ k) && coords.all (fun i =>
        (d.positiveAt i).testBit k.val || !(d.positiveAt i).testBit r.1.val ||
          r.2.contains i)) = true) :
    ∀ k r, r ∈ d.witnesses k → r.1 ≠ k ∧
      ∀ i ∈ s, zero (old k i) = true → positive (old r.1 i) = true → i ∈ r.2 := by
  intro k r hr
  have hc := List.all_eq_true.mp (h k) r hr
  simp only [Bool.and_eq_true] at hc
  refine ⟨of_decide_eq_true hc.1, ?_⟩
  intro i hi hz hp
  have hk : positive (old k i) = false := by
    apply Bool.eq_false_iff.mpr
    intro hk
    exact (eval_pos_of_check zero_lt_one hk).ne' (eval_zero_of_check 1 hz)
  have hmem := List.all_eq_true.mp hc.2 i (hcoords i hi)
  rw [hat k i hi, hat r.1 i hi, hk, hp] at hmem
  exact List.contains_iff_mem.mp hmem

theorem forallFin_of_all {n : ℕ} {P : Fin n → Prop} [DecidablePred P]
    (h : (List.finRange n).all (fun i => decide (P i)) = true) : ∀ i, P i := by
  intro i
  exact of_decide_eq_true (List.all_eq_true.mp h i (List.mem_finRange i))

def checkBlock {n : ℕ} (P : Fin n → Prop) [DecidablePred P]
    (block : Fin ((n + 15) / 16)) : Bool :=
  (List.finRange 16).all fun offset =>
    if h : 16 * block.val + offset.val < n then decide (P ⟨_, h⟩) else true

theorem forallFin_of_blocks {n : ℕ} {P : Fin n → Prop} [DecidablePred P]
    (h : ∀ block : Fin ((n + 15) / 16), checkBlock P block = true) : ∀ i, P i := by
  intro i
  have hi := i.isLt
  let block : Fin ((n + 15) / 16) := ⟨i.val / 16, by omega⟩
  let offset : Fin 16 := ⟨i.val % 16, Nat.mod_lt _ (by decide)⟩
  have hindex : 16 * block.val + offset.val = i.val := Nat.div_add_mod _ _
  have hlt : 16 * block.val + offset.val < n := hindex.symm ▸ hi
  have hrow := List.all_eq_true.mp (h block) offset (List.mem_finRange offset)
  change (if hb : 16 * block.val + offset.val < n then decide (P ⟨_, hb⟩) else true) = true at hrow
  rw [dif_pos hlt] at hrow
  exact (Fin.ext hindex : (⟨16 * block.val + offset.val, hlt⟩ : Fin n) = i) ▸ of_decide_eq_true hrow

theorem memList_of_all {α : Type} {l : List α} {P : α → Prop}
    [DecidablePred P] (h : l.all (fun x => decide (P x)) = true) :
    ∀ x ∈ l, P x :=
  fun x hx => of_decide_eq_true (List.all_eq_true.mp h x hx)

end MOC.RayCoefficients.FiniteRayChecks
