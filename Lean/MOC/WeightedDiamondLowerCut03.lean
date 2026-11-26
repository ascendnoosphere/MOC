import MOC.WeightedDiamondSparseCut
import MOC.WeightedDiamondLowerRays

/-! Exact lower-chart transition after imposing permutation coordinate 14. -/

namespace MOC.RayCoefficients

private def keptTable : Array (Fin 43) :=
  #[
    0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 0, 10, 11, 0, 0, 0, 0, 12, 13, 14, 15, 16, 17, 0,
    18, 19, 20, 21, 22, 23, 0]

private def edgeTable : Array (List (Fin 31 × Fin 43 × Poly)) :=
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
    [(3, 24, [1]), (5, 28, [1, 4, 4]), (8, 35, [1]), (12, 39, [1, 4, 4]), (24, 42, [1])],
    [],
    [],
    [(5, 29, [1, 2])],
    [(3, 25, [1]), (5, 30, [1]), (8, 36, [1]), (12, 40, [1]), (18, 41, [1])],
    [(3, 26, [1]), (5, 31, [1]), (8, 37, [1])],
    [(5, 32, [1]), (8, 38, [1])],
    [],
    [],
    [],
    [],
    [],
    [],
    [(5, 33, [1])],
    [],
    [],
    [],
    [],
    [],
    [],
    [(3, 27, [1]), (5, 34, [1])]]

private def originTable : Array (RayOrigin 31) :=
  #[
    .kept 0, .kept 1, .kept 2, .kept 3, .kept 4, .kept 5,
    .kept 6, .kept 7, .kept 8, .kept 9, .kept 11, .kept 12,
    .kept 17, .kept 18, .kept 19, .kept 20, .kept 21, .kept 22,
    .kept 24, .kept 25, .kept 26, .kept 27, .kept 28, .kept 29,
    .crossing 3 10, .crossing 3 14, .crossing 3 15, .crossing 3 30, .crossing 5 10, .crossing 5 13,
    .crossing 5 14, .crossing 5 15, .crossing 5 16, .crossing 5 23, .crossing 5 30, .crossing 8 10,
    .crossing 8 14, .crossing 8 15, .crossing 8 16, .crossing 12 10, .crossing 12 14, .crossing 18 14,
    .crossing 24 10]

private def positiveAtTable : Array (ℕ) :=
  #[
    287578369, 709034752,
    1436554240, 1723990018,
    134948356, 800775,
    1879173120, 150749184,
    1996521480, 133169168,
    136053261, 109077,
    32, 64,
    0, 0,
    0, 0,
    128, 0,
    0, 0,
    0, 0]

private def witnessTable : Array (List (Fin 31 × List (Fin 24))) :=
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
    [(12, [0, 5]), (17, [1, 3])],
    [],
    [],
    [(11, [0]), (15, [8])],
    [(11, [0, 5, 11]), (21, [0, 2, 9]), (22, [1, 3, 9])],
    [(11, [0, 5]), (4, [9])],
    [(8, [0]), (15, [8])],
    [],
    [],
    [],
    [],
    [],
    [],
    [(21, [0]), (26, [8])],
    [],
    [],
    [],
    [],
    [],
    [],
    [(28, [0]), (26, [9])]]

private def zeroCoordTable : Array (List (Fin 24)) :=
  #[
    [1, 2, 3, 4, 6, 7, 8, 9, 12, 13, 18],
    [0, 1, 2, 4, 6, 7, 8, 9, 10, 11, 12, 13, 18],
    [0, 1, 2, 3, 6, 7, 8, 9, 12, 13, 18],
    [0, 1, 2, 3, 4, 5, 6, 7, 9, 11, 12, 13, 18],
    [0, 1, 2, 3, 4, 5, 6, 7, 8, 10, 12, 13, 18],
    [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 18],
    [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 18],
    [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13],
    [2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 18],
    [0, 2, 3, 5, 6, 7, 8, 9, 12, 13, 18],
    [0, 1, 3, 5, 6, 7, 8, 9, 10, 11, 12, 13, 18],
    [1, 2, 3, 4, 7, 8, 9, 10, 12, 13, 18],
    [1, 3, 4, 6, 7, 8, 9, 10, 11, 12, 13, 18],
    [0, 1, 2, 3, 7, 8, 9, 10, 12, 13, 18],
    [0, 1, 2, 3, 4, 5, 8, 9, 10, 11, 12, 13, 18],
    [0, 1, 2, 3, 4, 5, 7, 9, 10, 12, 13, 18],
    [0, 2, 3, 5, 7, 8, 9, 10, 12, 13, 18],
    [0, 2, 5, 6, 7, 8, 9, 10, 11, 12, 13, 18],
    [1, 2, 3, 4, 6, 8, 9, 11, 12, 13, 18],
    [0, 1, 2, 3, 6, 8, 9, 11, 12, 13, 18],
    [0, 1, 2, 3, 4, 5, 6, 8, 11, 12, 13, 18],
    [1, 3, 4, 5, 6, 8, 10, 11, 12, 13, 18],
    [0, 2, 4, 5, 6, 8, 10, 11, 12, 13, 18],
    [0, 1, 4, 5, 6, 8, 10, 11, 12, 13, 18],
    [1, 3, 4, 5, 6, 7, 10, 11, 12, 13, 18],
    [0, 2, 4, 5, 6, 7, 10, 11, 12, 13, 18],
    [0, 1, 4, 5, 6, 7, 10, 11, 12, 13, 18],
    [0, 2, 3, 5, 6, 8, 9, 11, 12, 13, 18],
    [1, 3, 4, 5, 7, 9, 10, 11, 12, 13, 18],
    [0, 2, 4, 5, 7, 9, 10, 11, 12, 13, 18],
    [0, 1, 4, 5, 7, 9, 10, 11, 12, 13, 18]]

private def nextPositiveTable : Array (Fin 24) :=
  #[
    0, 3, 4, 8, 9, 12, 13, 18, 0, 1, 0, 0, 1, 0, 4, 7, 0, 1, 0, 1, 2, 1, 0, 1,
    2, 6, 6, 2, 2, 4, 6, 6, 1, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0]

private def plan : SparseRayCutPlan 31 43 where
  kept k := keptTable.getD k.val 0
  edges k := edgeTable.getD k.val []
  origin l := originTable.getD l.val (.kept 0)
  positiveMask := 50598185
  positiveAt i := positiveAtTable.getD i.val 0
  witnesses k := witnessTable.getD k.val []
  zeroCoords k := zeroCoordTable.getD k.val []
  nextPositiveCoord l := nextPositiveTable.getD l.val 0

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private theorem checkedLowerCut3 : plan.Checked weightedDiamondLowerRays3 weightedDiamondLowerRays4 weightedDiamondLowerImposed3 14 := by
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

theorem weightedDiamondLowerCut3 :
    RayCensusPath ⟨31, weightedDiamondLowerRays3, weightedDiamondLowerImposed3⟩
      ⟨43, weightedDiamondLowerRays4, weightedDiamondLowerImposed4⟩ :=
  plan.checkedCut checkedLowerCut3

end MOC.RayCoefficients
