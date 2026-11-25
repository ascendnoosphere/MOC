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

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
/-- Match the row-to-column profile with the column-to-row matching convention. -/
theorem ordinaryCostRayInt_indicator (r : Fin 34) (p : Fin 24) :
    ordinaryCostRayInt r p =
      if (ordinaryCostColumns r).map (fourPerm p).symm.toEmbedding = ordinaryCostRows r
      then 1 else 0 := by
  have h : ∀ (i : Fin 34) (j : Fin 24), ordinaryCostRayInt i j =
      if (ordinaryCostColumns i).map (fourPerm j).symm.toEmbedding = ordinaryCostRows i
      then 1 else 0 := by
    intro i
    fin_cases i <;> decide +kernel
  exact h r p

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
