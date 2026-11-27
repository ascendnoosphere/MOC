import MOC.ContactCensus
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FinCases

/-! Integer permutation profiles for the ordinary and mixed order-four cost rays. -/

namespace MOC

/-- A permutation in lexicographic one-line order, with entries numbered from zero. -/
def fourCostPermutation (p : Fin 24) : Fin 4 → Fin 4 :=
  fourPerm p

/-- Pull back the permutation labels by a row and column relabeling. -/
def fourCostRelabelIndex (a b p : Fin 24) : Fin 24 :=
  fourPermIndex (fourPerm a * fourPerm p * fourPerm b)

/-- The six pairs of distinct order-four labels, in lexicographic order. -/
def fourCostPair (i : Fin 6) : Fin 4 × Fin 4 :=
  ![(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)] i

/-- The first sixteen rays are singleton-image indicators. The last eighteen
are pair-image indicators, with the source pair required to contain zero.
Complementing both pairs gives the other representatives. -/
def ordinaryCostRayInt (r : Fin 34) (p : Fin 24) : ℤ :=
  if r.val < 16 then
    if fourCostPermutation p ⟨r.val / 4 % 4, Nat.mod_lt _ (by decide)⟩ =
        ⟨r.val % 4, Nat.mod_lt _ (by decide)⟩ then 1 else 0
  else
    let I := fourCostPair ⟨(r.val - 16) / 6 % 6, Nat.mod_lt _ (by decide)⟩
    let J := fourCostPair ⟨(r.val - 16) % 6, Nat.mod_lt _ (by decide)⟩
    if (fourCostPermutation p I.1 = J.1 ∧ fourCostPermutation p I.2 = J.2) ∨
        (fourCostPermutation p I.1 = J.2 ∧ fourCostPermutation p I.2 = J.1)
    then 1 else 0

/-- The row set of the ordinary minor indicator. -/
def ordinaryCostRows (r : Fin 34) : Finset (Fin 4) :=
  if r.val < 16 then {⟨r.val / 4 % 4, Nat.mod_lt _ (by decide)⟩}
  else
    let I := fourCostPair ⟨(r.val - 16) / 6 % 6, Nat.mod_lt _ (by decide)⟩
    {I.1, I.2}

/-- The column set of the ordinary minor indicator. -/
def ordinaryCostColumns (r : Fin 34) : Finset (Fin 4) :=
  if r.val < 16 then {⟨r.val % 4, Nat.mod_lt _ (by decide)⟩}
  else
    let J := fourCostPair ⟨(r.val - 16) % 6, Nat.mod_lt _ (by decide)⟩
    {J.1, J.2}

private theorem finsetMapSymm_eq {α : Type*} (e : Equiv.Perm α) (I J : Finset α) :
    J.map e.symm.toEmbedding = I ↔ I.map e.toEmbedding = J := by
  constructor
  · intro h
    apply Finset.Subset.antisymm
    · apply (Finset.subset_map_symm (f := e)).mp
      rw [h]
    · apply (Finset.map_symm_subset (f := e)).mp
      rw [h]
  · intro h
    apply Finset.Subset.antisymm
    · apply (Finset.map_symm_subset (f := e)).mpr
      rw [h]
    · apply (Finset.subset_map_symm (f := e)).mpr
      rw [h]

private theorem finsetPair_eq_iff {α : Type*} [DecidableEq α] {a b c d : α} (hcd : c ≠ d) :
    ({a, b} : Finset α) = {c, d} ↔ (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  constructor
  · intro h
    have ha : a = c ∨ a = d := by
      have : a ∈ ({c, d} : Finset α) := h ▸ (by simp : a ∈ ({a, b} : Finset α))
      simpa only [Finset.mem_insert, Finset.mem_singleton] using this
    rcases ha with hac | had
    · left
      refine ⟨hac, ?_⟩
      have hd : d = a ∨ d = b := by
        have : d ∈ ({a, b} : Finset α) := h.symm ▸ (by simp : d ∈ ({c, d} : Finset α))
        simpa only [Finset.mem_insert, Finset.mem_singleton] using this
      exact (hd.resolve_left (fun hda => hcd (hac.symm.trans hda.symm))).symm
    · right
      refine ⟨had, ?_⟩
      have hc : c = a ∨ c = b := by
        have : c ∈ ({a, b} : Finset α) := h.symm ▸ (by simp : c ∈ ({c, d} : Finset α))
        simpa only [Finset.mem_insert, Finset.mem_singleton] using this
      exact (hc.resolve_left (by rwa [had])).symm
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · rfl
    · ext x
      simp only [Finset.mem_insert, Finset.mem_singleton, or_comm]

private theorem fourCostPair_distinct (i : Fin 6) : (fourCostPair i).1 ≠ (fourCostPair i).2 := by
  have hthree : ((3 : Fin 4) : ℕ) = 3 := rfl
  fin_cases i <;> intro h <;> have hv := congrArg Fin.val h <;>
    norm_num [fourCostPair, Matrix.cons_val, hthree] at hv

private theorem integerIndicator_congr {P Q : Prop} [Decidable P] [Decidable Q]
    (h : P ↔ Q) : (if P then (1 : ℤ) else 0) = if Q then 1 else 0 := by
  by_cases hp : P
  · rw [if_pos hp, if_pos (h.mp hp)]
  · rw [if_neg hp, if_neg (fun hq => hp (h.mpr hq))]

/-- Match the row-to-column profile with the column-to-row matching convention. -/
theorem ordinaryCostRayInt_indicator (r : Fin 34) (p : Fin 24) :
    ordinaryCostRayInt r p =
      if (ordinaryCostColumns r).map (fourPerm p).symm.toEmbedding = ordinaryCostRows r
      then 1 else 0 := by
  by_cases hr : r.val < 16
  · simp only [ordinaryCostRayInt, ordinaryCostRows, ordinaryCostColumns, if_pos hr,
      fourCostPermutation]
    apply integerIndicator_congr
    symm
    rw [finsetMapSymm_eq]
    simp only [Finset.map_singleton, Finset.singleton_inj, Equiv.toEmbedding_apply]
  · simp only [ordinaryCostRayInt, ordinaryCostRows, ordinaryCostColumns, if_neg hr,
      fourCostPermutation]
    apply integerIndicator_congr
    symm
    rw [finsetMapSymm_eq]
    simp only [Finset.map_insert, Finset.map_singleton,
      finsetPair_eq_iff (fourCostPair_distinct _), Equiv.toEmbedding_apply]

/-- The initial mixed ray is the sum of three ordinary profiles minus one. -/
def mixedCostSeedInt (p : Fin 24) : ℤ :=
  ordinaryCostRayInt 10 p + ordinaryCostRayInt 7 p + ordinaryCostRayInt 17 p -
    ordinaryCostRayInt 25 p

/-- The two row permutations are the identity and the swap of labels two and
three. Each row choice is combined with the twenty-four column permutations. -/
def mixedCostRayInt (r : Fin 48) (p : Fin 24) : ℤ :=
  mixedCostSeedInt
    (fourCostRelabelIndex (if r.val < 24 then 0 else 1)
      ⟨r.val % 24, Nat.mod_lt _ (by decide)⟩ p)

/-- Real form of an ordinary profile. -/
def ordinaryCostRay (r : Fin 34) (p : Fin 24) : ℝ := ordinaryCostRayInt r p

/-- Real form of a mixed profile. -/
def mixedCostRay (r : Fin 48) (p : Fin 24) : ℝ := mixedCostRayInt r p

end MOC
