import MOC.WeightedDiamondSparseCut
import MOC.WeightedDiamondLowerRays

/-! Exact lower-chart transition after imposing permutation coordinate 10. -/

namespace MOC.RayCoefficients

private def keptTable : Array (Fin 25) :=
  #[
    0, 1, 2, 0, 3, 4, 5, 6, 7, 8, 9, 0, 0, 0, 10, 11]

private def edgeTable : Array (List (Fin 16 × Fin 25 × Poly)) :=
  #[
    [],
    [],
    [],
    [(0, 12, [1, 3, 2]), (2, 14, [1]), (4, 15, [1, 3, 2]), (5, 19, [1]), (14, 23, [1, 2])],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [(0, 13, [1]), (4, 16, [1]), (5, 20, [1])],
    [(4, 17, [1, 1]), (5, 21, [1]), (14, 24, [1])],
    [(4, 18, [1]), (5, 22, [1])],
    [],
    []]

private def originTable : Array (RayOrigin 16) :=
  #[
    .kept 0, .kept 1, .kept 2, .kept 4, .kept 5, .kept 6,
    .kept 7, .kept 8, .kept 9, .kept 10, .kept 14, .kept 15,
    .crossing 0 3, .crossing 0 11, .crossing 2 3, .crossing 4 3, .crossing 4 11, .crossing 4 12,
    .crossing 4 13, .crossing 5 3, .crossing 5 11, .crossing 5 12, .crossing 5 13, .crossing 14 3,
    .crossing 14 12]

private def positiveAtTable : Array (ℕ) :=
  #[
    3073, 21504,
    43008, 12290,
    49156, 7,
    8, 16,
    32, 64,
    0, 0,
    128, 256,
    0, 0,
    0, 0,
    512, 0,
    0, 0,
    0, 0]

private def witnessTable : Array (List (Fin 16 × List (Fin 24))) :=
  #[
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
    [(15, [4])],
    [(1, [5])],
    [(1, [5]), (12, [1])],
    [],
    []]

private def zeroCoordTable : Array (List (Fin 24)) :=
  #[
    [1, 2, 3, 4, 6, 7, 8, 9, 12, 13, 18],
    [0, 1, 2, 4, 6, 7, 8, 9, 12, 13, 18],
    [0, 1, 2, 3, 6, 7, 8, 9, 12, 13, 18],
    [0, 1, 2, 3, 4, 5, 7, 8, 9, 12, 13, 18],
    [0, 1, 2, 3, 4, 5, 6, 8, 9, 12, 13, 18],
    [0, 1, 2, 3, 4, 5, 6, 7, 9, 12, 13, 18],
    [0, 1, 2, 3, 4, 5, 6, 7, 8, 12, 13, 18],
    [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 13, 18],
    [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 12, 18],
    [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 12, 13],
    [2, 3, 4, 5, 6, 7, 8, 9, 12, 13, 18],
    [1, 3, 4, 5, 6, 7, 8, 9, 12, 13, 18],
    [0, 2, 4, 5, 6, 7, 8, 9, 12, 13, 18],
    [0, 1, 4, 5, 6, 7, 8, 9, 12, 13, 18],
    [0, 2, 3, 5, 6, 7, 8, 9, 12, 13, 18],
    [0, 1, 3, 5, 6, 7, 8, 9, 12, 13, 18]]

private def nextPositiveTable : Array (Fin 24) :=
  #[
    0, 3, 4, 7, 8, 9, 12, 13, 18, 0, 1, 2, 0, 0, 4, 6, 0, 1, 2, 6, 0, 1, 2, 1,
    1]

private def plan : SparseRayCutPlan 16 25 where
  kept k := keptTable.getD k.val 0
  edges k := edgeTable.getD k.val []
  origin l := originTable.getD l.val (.kept 0)
  positiveMask := 16437
  positiveAt i := positiveAtTable.getD i.val 0
  witnesses k := witnessTable.getD k.val []
  zeroCoords k := zeroCoordTable.getD k.val []
  nextPositiveCoord l := nextPositiveTable.getD l.val 0

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private theorem checked : plan.Checked weightedDiamondLowerRays1 weightedDiamondLowerRays2 weightedDiamondLowerImposed1 10 := by
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

theorem weightedDiamondLowerCut1 :
    RayCensusPath ⟨16, weightedDiamondLowerRays1, weightedDiamondLowerImposed1⟩
      ⟨25, weightedDiamondLowerRays2, weightedDiamondLowerImposed2⟩ :=
  plan.checkedCut checked

end MOC.RayCoefficients
