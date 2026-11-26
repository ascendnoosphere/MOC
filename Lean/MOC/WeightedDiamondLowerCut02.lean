import MOC.WeightedDiamondSparseCut
import MOC.WeightedDiamondLowerRays

/-! Exact lower-chart transition after imposing permutation coordinate 11. -/

namespace MOC.RayCoefficients

private def keptTable : Array (Fin 31) :=
  #[
    0, 1, 2, 0, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 0, 0, 0, 15, 0, 0, 0, 16,
    17]

private def edgeTable : Array (List (Fin 25 × Fin 31 × Poly)) :=
  #[
    [],
    [],
    [],
    [(0, 18, [1, 2]), (2, 19, [1]), (5, 20, [1]), (10, 27, [0, 1, 2])],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [(5, 21, [1])],
    [(5, 22, [1])],
    [(5, 23, [1])],
    [],
    [(5, 24, [1]), (19, 28, [0, 1])],
    [(5, 25, [1]), (19, 29, [1])],
    [(5, 26, [1]), (19, 30, [1])],
    [],
    []]

private def originTable : Array (RayOrigin 25) :=
  #[
    .kept 0, .kept 1, .kept 2, .kept 4, .kept 5, .kept 6,
    .kept 7, .kept 8, .kept 9, .kept 10, .kept 11, .kept 12,
    .kept 13, .kept 14, .kept 15, .kept 19, .kept 23, .kept 24,
    .crossing 0 3, .crossing 2 3, .crossing 5 3, .crossing 5 16, .crossing 5 17, .crossing 5 18,
    .crossing 5 20, .crossing 5 21, .crossing 5 22, .crossing 10 3, .crossing 19 20, .crossing 19 21,
    .crossing 19 22]

private def positiveAtTable : Array (ℕ) :=
  #[
    1126913, 27395584,
    5580800, 23461890,
    25185284, 28679,
    8966144, 491528,
    7864336, 32,
    1053, 0,
    64, 128,
    0, 0,
    0, 0,
    256, 0,
    0, 0,
    0, 0]

private def witnessTable : Array (List (Fin 25 × List (Fin 24))) :=
  #[
    [],
    [],
    [],
    [(15, [6])],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [(11, [4]), (13, [5]), (15, [6])],
    [(1, [5]), (15, [6]), (3, [10])],
    [(1, [5]), (11, [4]), (15, [6])],
    [],
    [(11, [4]), (13, [5])],
    [(1, [5]), (24, [4])],
    [(1, [5]), (11, [4])],
    [],
    []]

private def zeroCoordTable : Array (List (Fin 24)) :=
  #[
    [1, 2, 3, 4, 6, 7, 8, 9, 12, 13, 18],
    [0, 1, 2, 4, 6, 7, 8, 9, 10, 12, 13, 18],
    [0, 1, 2, 3, 6, 7, 8, 9, 12, 13, 18],
    [0, 1, 2, 3, 4, 5, 6, 8, 9, 12, 13, 18],
    [0, 1, 2, 3, 4, 5, 6, 7, 9, 12, 13, 18],
    [0, 1, 2, 3, 4, 5, 6, 7, 8, 10, 12, 13, 18],
    [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 13, 18],
    [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 18],
    [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 13],
    [2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 13, 18],
    [0, 2, 3, 5, 6, 7, 8, 9, 12, 13, 18],
    [0, 1, 3, 5, 6, 7, 8, 9, 10, 12, 13, 18],
    [1, 2, 3, 4, 7, 8, 9, 10, 12, 13, 18],
    [1, 3, 4, 6, 7, 8, 9, 10, 12, 13, 18],
    [0, 1, 2, 3, 7, 8, 9, 10, 12, 13, 18],
    [0, 1, 2, 3, 4, 5, 8, 9, 10, 12, 13, 18],
    [1, 3, 4, 5, 6, 8, 9, 10, 12, 13, 18],
    [0, 2, 4, 5, 6, 8, 9, 10, 12, 13, 18],
    [0, 1, 4, 5, 6, 8, 9, 10, 12, 13, 18],
    [0, 1, 2, 3, 4, 5, 7, 9, 10, 12, 13, 18],
    [1, 3, 4, 5, 6, 7, 9, 10, 12, 13, 18],
    [0, 2, 4, 5, 6, 7, 9, 10, 12, 13, 18],
    [0, 1, 4, 5, 6, 7, 9, 10, 12, 13, 18],
    [0, 2, 3, 5, 7, 8, 9, 10, 12, 13, 18],
    [0, 2, 5, 6, 7, 8, 9, 10, 12, 13, 18]]

private def nextPositiveTable : Array (Fin 24) :=
  #[
    0, 3, 4, 8, 9, 12, 13, 18, 0, 1, 2, 0, 0, 4, 6, 6, 1, 1, 0, 4, 7, 0, 1, 2,
    0, 1, 2, 1, 0, 1, 2]

private def plan : SparseRayCutPlan 25 31 where
  kept k := keptTable.getD k.val 0
  edges k := edgeTable.getD k.val []
  origin l := originTable.getD l.val (.kept 0)
  positiveMask := 8934437
  positiveAt i := positiveAtTable.getD i.val 0
  witnesses k := witnessTable.getD k.val []
  zeroCoords k := zeroCoordTable.getD k.val []
  nextPositiveCoord l := nextPositiveTable.getD l.val 0

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private theorem checkedLowerCut2 : plan.Checked weightedDiamondLowerRays2 weightedDiamondLowerRays3 weightedDiamondLowerImposed2 11 := by
  refine
    { oldSigns := ?_
      nextSigns := ?_
      nextPositive := ?_
      cutSigns := ?_
      cutPositive_eq := ?_
      positiveAt_eq := ?_
      zeroCoordsValid := ?_
      antichainCover := ?_
      witnessesValid := ?_
      crossingCover := ?_
      keptValid := ?_
      edgeValid := ?_
      originsValid := ?_ }
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · simp only [ldiff_eq_xor_land]
    decide +kernel
  · decide +kernel
  · simp only [witnessMask_eq_xor_land]
    decide +kernel
  · decide +kernel
  · intro k
    fin_cases k <;> decide +kernel
  · intro k
    fin_cases k <;> decide +kernel

theorem weightedDiamondLowerCut2 :
    RayCensusPath ⟨25, weightedDiamondLowerRays2, weightedDiamondLowerImposed2⟩
      ⟨31, weightedDiamondLowerRays3, weightedDiamondLowerImposed3⟩ :=
  plan.checkedCut checkedLowerCut2

end MOC.RayCoefficients
