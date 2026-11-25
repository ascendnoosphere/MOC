import MOC.WeightedDiamondSparseCut
import MOC.WeightedDiamondLowerRays

/-! Exact lower-chart transition after imposing permutation coordinate 15. -/

namespace MOC.RayCoefficients

private def keptTable : Array (Fin 54) :=
  #[
    0, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 0, 0, 0, 12, 13, 14, 15, 16, 17, 18, 19,
    20, 0, 21, 0, 22, 23, 0, 24, 25, 0, 0, 26, 27, 28, 29, 30, 0, 0, 31]

private def edgeTable : Array (List (Fin 43 × Fin 54 × Poly)) :=
  #[
    [],
    [(4, 32, [1]), (6, 36, [1, 4, 4]), (8, 47, [1]), (12, 50, [1, 4, 4]), (19, 52, [1])],
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
    [(6, 37, [1]), (8, 48, [1])],
    [(6, 38, [1, 2])],
    [(4, 33, [1]), (6, 39, [1]), (8, 49, [1])],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [(6, 40, [1])],
    [],
    [(6, 41, [1])],
    [],
    [],
    [(4, 34, [1]), (6, 42, [1, 4, 4]), (12, 51, [1, 4, 4]), (32, 53, [1, 4, 4])],
    [],
    [],
    [(4, 35, [1]), (6, 43, [1, 4, 4])],
    [(6, 44, [1, 4, 4])],
    [],
    [],
    [],
    [],
    [],
    [(6, 45, [1, 4, 4])],
    [(6, 46, [1, 2])],
    []]

private def originTable : Array (RayOrigin 43) :=
  #[
    .kept 0, .kept 2, .kept 3, .kept 4, .kept 5, .kept 6,
    .kept 7, .kept 8, .kept 9, .kept 10, .kept 11, .kept 12,
    .kept 16, .kept 17, .kept 18, .kept 19, .kept 20, .kept 21,
    .kept 22, .kept 23, .kept 24, .kept 26, .kept 28, .kept 29,
    .kept 31, .kept 32, .kept 35, .kept 36, .kept 37, .kept 38,
    .kept 39, .kept 42, .crossing 4 1, .crossing 4 15, .crossing 4 30, .crossing 4 33,
    .crossing 6 1, .crossing 6 13, .crossing 6 14, .crossing 6 15, .crossing 6 25, .crossing 6 27,
    .crossing 6 30, .crossing 6 33, .crossing 6 34, .crossing 6 40, .crossing 6 41, .crossing 8 1,
    .crossing 8 13, .crossing 8 15, .crossing 12 1, .crossing 12 30, .crossing 19 1, .crossing 32 30]

private def positiveAtTable : Array (ℕ) :=
  #[
    8761737817345, 519702188800,
    6107868497920, 25914118146,
    5262159139332, 3848827595783,
    3805051618304, 3376953942016,
    4555078893576, 4406638510096,
    2199277068813, 419363292693,
    34091302944, 64,
    796969, 0,
    0, 0,
    128, 0,
    0, 0,
    0, 0]

private def witnessTable : Array (List (Fin 43 × List (Fin 24))) :=
  #[
    [],
    [(12, [1, 4]), (20, [2, 8, 9]), (10, [0, 6, 11])],
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
    [(8, [1]), (15, [9])],
    [(21, [1]), (15, [9])],
    [(21, [1, 4]), (3, [8, 14]), (4, [11]), (16, [0, 2])],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [(21, [1, 4]), (15, [9]), (36, [0, 1])],
    [],
    [(23, [1]), (20, [9])],
    [],
    [],
    [(36, [0, 1]), (5, [14]), (16, [0, 2, 9]), (21, [1, 4, 10])],
    [],
    [],
    [(17, [1]), (16, [0])],
    [(23, [1]), (20, [9])],
    [],
    [],
    [],
    [],
    [],
    [(36, [1]), (16, [9])],
    [(36, [1]), (15, [9])],
    []]

private def zeroCoordTable : Array (List (Fin 24)) :=
  #[
    [1, 2, 3, 4, 6, 7, 8, 9, 12, 13, 18],
    [0, 1, 2, 4, 6, 7, 8, 9, 10, 11, 12, 13, 14, 18],
    [0, 1, 2, 3, 6, 7, 8, 9, 12, 13, 14, 18],
    [0, 1, 2, 3, 4, 5, 6, 7, 9, 11, 12, 13, 18],
    [0, 1, 2, 3, 4, 5, 6, 7, 8, 10, 12, 13, 14, 18],
    [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 18],
    [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 14, 18],
    [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14],
    [2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 18],
    [0, 2, 3, 5, 6, 7, 8, 9, 12, 13, 14, 18],
    [1, 2, 3, 4, 7, 8, 9, 10, 12, 13, 14, 18],
    [1, 3, 4, 6, 7, 8, 9, 10, 11, 12, 13, 18],
    [0, 2, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 18],
    [1, 2, 3, 4, 6, 8, 9, 11, 12, 13, 18],
    [0, 1, 2, 3, 6, 8, 9, 11, 12, 13, 14, 18],
    [0, 1, 2, 3, 4, 5, 6, 8, 11, 12, 13, 14, 18],
    [1, 3, 4, 5, 6, 8, 10, 11, 12, 13, 14, 18],
    [0, 2, 4, 5, 6, 8, 10, 11, 12, 13, 14, 18],
    [1, 3, 4, 5, 6, 7, 10, 11, 12, 13, 18],
    [0, 2, 4, 5, 6, 7, 10, 11, 12, 13, 18],
    [0, 1, 4, 5, 6, 7, 10, 11, 12, 13, 14, 18],
    [0, 2, 3, 5, 6, 8, 9, 11, 12, 13, 14, 18],
    [1, 3, 4, 5, 7, 9, 10, 11, 12, 13, 14, 18],
    [0, 2, 4, 5, 7, 9, 10, 11, 12, 13, 14, 18],
    [0, 1, 3, 5, 6, 7, 9, 11, 12, 13, 14, 18],
    [0, 1, 2, 3, 4, 5, 9, 11, 12, 13, 14, 18],
    [0, 1, 2, 3, 4, 5, 7, 9, 12, 13, 14, 18],
    [0, 1, 4, 5, 7, 9, 11, 12, 13, 14, 18],
    [0, 1, 3, 5, 6, 7, 8, 9, 10, 11, 13, 14, 18],
    [0, 1, 2, 3, 7, 8, 9, 10, 13, 14, 18],
    [0, 1, 2, 3, 4, 5, 8, 9, 10, 11, 13, 14, 18],
    [0, 1, 2, 3, 4, 5, 7, 9, 10, 13, 14, 18],
    [0, 2, 3, 5, 7, 8, 9, 10, 13, 14, 18],
    [0, 1, 4, 5, 6, 8, 10, 11, 13, 14, 18],
    [0, 1, 4, 5, 7, 9, 10, 11, 13, 14, 18],
    [3, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 18],
    [2, 3, 4, 5, 8, 9, 10, 11, 12, 13, 14, 18],
    [2, 3, 4, 5, 7, 9, 10, 12, 13, 14, 18],
    [2, 3, 5, 7, 8, 9, 10, 12, 13, 14, 18],
    [1, 3, 6, 7, 8, 9, 10, 11, 12, 13, 14, 18],
    [1, 3, 4, 8, 9, 10, 11, 12, 13, 14, 18],
    [1, 2, 3, 4, 8, 9, 11, 12, 13, 14, 18],
    [1, 3, 5, 6, 7, 10, 11, 12, 13, 14, 18]]

private def nextPositiveTable : Array (Fin 24) :=
  #[
    0, 4, 8, 9, 12, 13, 18, 0, 1, 0, 0, 1, 0, 1, 0, 1, 2, 1, 0, 1, 2, 6, 2, 4,
    6, 1, 0, 0, 0, 0, 0, 0, 3, 7, 6, 2, 3, 0, 4, 7, 6, 2, 6, 2, 2, 0, 0, 0,
    0, 0, 1, 1, 1, 1]

private def plan : SparseRayCutPlan 43 54 where
  kept k := keptTable.getD k.val 0
  edges k := edgeTable.getD k.val []
  origin l := originTable.getD l.val (.kept 0)
  positiveMask := 4849018868560
  positiveAt i := positiveAtTable.getD i.val 0
  witnesses k := witnessTable.getD k.val []
  zeroCoords k := zeroCoordTable.getD k.val []
  nextPositiveCoord l := nextPositiveTable.getD l.val 0

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private theorem checked : plan.Checked weightedDiamondLowerRays4 weightedDiamondLowerRays5 weightedDiamondLowerImposed4 15 := by
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
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro k
    fin_cases k <;> decide +kernel
  · intro k
    fin_cases k <;> decide +kernel

theorem weightedDiamondLowerCut4 :
    RayCensusPath ⟨43, weightedDiamondLowerRays4, weightedDiamondLowerImposed4⟩
      ⟨54, weightedDiamondLowerRays5, weightedDiamondLowerImposed5⟩ :=
  plan.checkedCut checked

end MOC.RayCoefficients
