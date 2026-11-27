import MOC.FiniteMinorLaw
import MOC.UnitaryPhaseCuts
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Tactic.FinCases

/-! The order-six interval certificate for three fixed source pairs.
Columns zero and one are the lower set. Columns two and three are the
optional part. Each interval has one lower set, two middle sets, and
one upper set. -/

open Matrix BigOperators
open scoped Finset Matrix.L2OpNorm

namespace MOC.SixDimensionalMixerBall

noncomputable section

-- Integer numerator of the rational orthogonal center.
private def centerNumerator : Matrix (Fin 6) (Fin 6) ℤ := !![
  863, 3348, (-1506), 984, 1266, 7320;
  (-2664), 1223, (-2700), (-2046), 6882, (-1716);
  (-1986), 1044, (-199), 7884, 936, (-1506);
  5496, (-4866), (-2592), 1727, 2580, 366;
  (-5010), (-5730), 1044, 120, 359, 3348;
  (-1812), (-264), (-7278), (-258), (-3708), (-487)
]

private def targetLabels : Fin 50 → Finset (Fin 6) := ![
  {0, 1},
  {0, 2},
  {0, 3},
  {0, 4},
  {0, 5},
  {1, 2},
  {1, 3},
  {1, 4},
  {1, 5},
  {2, 3},
  {2, 4},
  {2, 5},
  {3, 4},
  {3, 5},
  {4, 5},
  {0, 1, 2},
  {0, 1, 3},
  {0, 1, 4},
  {0, 1, 5},
  {0, 2, 3},
  {0, 2, 4},
  {0, 2, 5},
  {0, 3, 4},
  {0, 3, 5},
  {0, 4, 5},
  {1, 2, 3},
  {1, 2, 4},
  {1, 2, 5},
  {1, 3, 4},
  {1, 3, 5},
  {1, 4, 5},
  {2, 3, 4},
  {2, 3, 5},
  {2, 4, 5},
  {3, 4, 5},
  {0, 1, 2, 3},
  {0, 1, 2, 4},
  {0, 1, 2, 5},
  {0, 1, 3, 4},
  {0, 1, 3, 5},
  {0, 1, 4, 5},
  {0, 2, 3, 4},
  {0, 2, 3, 5},
  {0, 2, 4, 5},
  {0, 3, 4, 5},
  {1, 2, 3, 4},
  {1, 2, 3, 5},
  {1, 2, 4, 5},
  {1, 3, 4, 5},
  {2, 3, 4, 5}
]

private def intervalLower : Fin 90 → Finset (Fin 6) := ![
  {0, 1},
  {0, 1},
  {0, 1},
  {0, 1},
  {0, 1},
  {0, 1},
  {0, 2},
  {0, 2},
  {0, 2},
  {0, 2},
  {0, 2},
  {0, 2},
  {0, 3},
  {0, 3},
  {0, 3},
  {0, 3},
  {0, 3},
  {0, 3},
  {0, 4},
  {0, 4},
  {0, 4},
  {0, 4},
  {0, 4},
  {0, 4},
  {0, 5},
  {0, 5},
  {0, 5},
  {0, 5},
  {0, 5},
  {0, 5},
  {1, 2},
  {1, 2},
  {1, 2},
  {1, 2},
  {1, 2},
  {1, 2},
  {1, 3},
  {1, 3},
  {1, 3},
  {1, 3},
  {1, 3},
  {1, 3},
  {1, 4},
  {1, 4},
  {1, 4},
  {1, 4},
  {1, 4},
  {1, 4},
  {1, 5},
  {1, 5},
  {1, 5},
  {1, 5},
  {1, 5},
  {1, 5},
  {2, 3},
  {2, 3},
  {2, 3},
  {2, 3},
  {2, 3},
  {2, 3},
  {2, 4},
  {2, 4},
  {2, 4},
  {2, 4},
  {2, 4},
  {2, 4},
  {2, 5},
  {2, 5},
  {2, 5},
  {2, 5},
  {2, 5},
  {2, 5},
  {3, 4},
  {3, 4},
  {3, 4},
  {3, 4},
  {3, 4},
  {3, 4},
  {3, 5},
  {3, 5},
  {3, 5},
  {3, 5},
  {3, 5},
  {3, 5},
  {4, 5},
  {4, 5},
  {4, 5},
  {4, 5},
  {4, 5},
  {4, 5}
]

private def intervalUpper : Fin 90 → Finset (Fin 6) := ![
  {0, 1, 2, 3},
  {0, 1, 2, 4},
  {0, 1, 2, 5},
  {0, 1, 3, 4},
  {0, 1, 3, 5},
  {0, 1, 4, 5},
  {0, 1, 2, 3},
  {0, 1, 2, 4},
  {0, 1, 2, 5},
  {0, 2, 3, 4},
  {0, 2, 3, 5},
  {0, 2, 4, 5},
  {0, 1, 2, 3},
  {0, 1, 3, 4},
  {0, 1, 3, 5},
  {0, 2, 3, 4},
  {0, 2, 3, 5},
  {0, 3, 4, 5},
  {0, 1, 2, 4},
  {0, 1, 3, 4},
  {0, 1, 4, 5},
  {0, 2, 3, 4},
  {0, 2, 4, 5},
  {0, 3, 4, 5},
  {0, 1, 2, 5},
  {0, 1, 3, 5},
  {0, 1, 4, 5},
  {0, 2, 3, 5},
  {0, 2, 4, 5},
  {0, 3, 4, 5},
  {0, 1, 2, 3},
  {0, 1, 2, 4},
  {0, 1, 2, 5},
  {1, 2, 3, 4},
  {1, 2, 3, 5},
  {1, 2, 4, 5},
  {0, 1, 2, 3},
  {0, 1, 3, 4},
  {0, 1, 3, 5},
  {1, 2, 3, 4},
  {1, 2, 3, 5},
  {1, 3, 4, 5},
  {0, 1, 2, 4},
  {0, 1, 3, 4},
  {0, 1, 4, 5},
  {1, 2, 3, 4},
  {1, 2, 4, 5},
  {1, 3, 4, 5},
  {0, 1, 2, 5},
  {0, 1, 3, 5},
  {0, 1, 4, 5},
  {1, 2, 3, 5},
  {1, 2, 4, 5},
  {1, 3, 4, 5},
  {0, 1, 2, 3},
  {0, 2, 3, 4},
  {0, 2, 3, 5},
  {1, 2, 3, 4},
  {1, 2, 3, 5},
  {2, 3, 4, 5},
  {0, 1, 2, 4},
  {0, 2, 3, 4},
  {0, 2, 4, 5},
  {1, 2, 3, 4},
  {1, 2, 4, 5},
  {2, 3, 4, 5},
  {0, 1, 2, 5},
  {0, 2, 3, 5},
  {0, 2, 4, 5},
  {1, 2, 3, 5},
  {1, 2, 4, 5},
  {2, 3, 4, 5},
  {0, 1, 3, 4},
  {0, 2, 3, 4},
  {0, 3, 4, 5},
  {1, 2, 3, 4},
  {1, 3, 4, 5},
  {2, 3, 4, 5},
  {0, 1, 3, 5},
  {0, 2, 3, 5},
  {0, 3, 4, 5},
  {1, 2, 3, 5},
  {1, 3, 4, 5},
  {2, 3, 4, 5},
  {0, 1, 4, 5},
  {0, 2, 4, 5},
  {0, 3, 4, 5},
  {1, 2, 4, 5},
  {1, 3, 4, 5},
  {2, 3, 4, 5}
]

private def centerWeightNumerator : Fin 90 → ℤ := ![
  712543,
  3,
  701166,
  3,
  3,
  3,
  228090,
  3,
  204771,
  16824,
  360309,
  3,
  1032528,
  46641,
  164604,
  435441,
  5573253,
  5169,
  3,
  442047,
  3,
  507945,
  3,
  1038099,
  3,
  3,
  3,
  484401,
  3,
  3,
  3,
  3,
  3,
  3,
  1749,
  3,
  3,
  20721,
  3,
  532803,
  3,
  3,
  3,
  3,
  14268,
  3069381,
  2328924,
  1089921,
  85989,
  3,
  3,
  35103,
  3,
  3,
  155514,
  3,
  63498,
  3,
  3,
  3,
  129,
  21,
  685569,
  741198,
  2493480,
  3,
  36264,
  3,
  3,
  3,
  3,
  46668,
  8985,
  380730,
  46659,
  5654856,
  3,
  38264367,
  27228,
  1470936,
  3,
  3,
  3,
  3,
  239736,
  3,
  3,
  3,
  3,
  926652
]

private def selectedRows : Fin 43 → Fin 50 := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 35, 36, 37, 38, 39, 40, 41, 42, 43]

private def selectedIntervals : Fin 43 → Fin 90 := ![0, 2, 6, 8, 9, 10, 12, 13, 14, 15, 16, 17, 19, 21, 23, 27, 34, 37, 39, 44, 45, 46, 47, 48, 51, 54, 56, 60, 61, 62, 63, 64, 66, 71, 72, 73, 74, 75, 77, 78, 79, 84, 89]

private def repairInverse : Matrix (Fin 43) (Fin 43) ℤ :=
  Matrix.of ![
  ![2, 1, 1, 0, 1, 2, 1, 0, 2, 1, 0, 1, 0, 1, 0, (-1), (-1), 0, (-2), (-1), 0, (-1), 0, (-1), 0, (-1), 0, (-1), 0, (-1), 0, 0, (-1), 0, 1, 0, 1, 0, 1, 0, 0, 1, 0],
  ![(-1), (-1), (-1), 0, (-1), (-2), (-1), 0, (-2), (-1), 0, (-1), 0, (-1), 0, 1, 1, 0, 2, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, (-1), 0, (-1), 0, (-1), 0, 0, (-1), 0],
  ![(-1), 0, 0, 0, 0, (-1), 0, 0, (-1), 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, (-1), 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1), 0, 0, 0, 0, 0, 0, 0, 0, (-1), 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
  ![1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1), 0, 0, (-1), 0, 0, (-1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, (-1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1), 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, (-1), (-1), 0, (-1), 0, (-1), 0, (-1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0],
  ![0, 1, 1, 0, 1, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, (-1), 0, (-1), 0, (-1), 0, 0, 0, 0, 0, 0, 0, 0, (-1), 0, 0, 0, 0, 0, 0, 0, 0, 1, 0],
  ![(-1), (-1), (-1), 0, (-1), (-2), (-1), 0, (-1), (-1), 0, (-1), 0, (-1), 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0, (-1), 0, (-1), 0, 0, 0, 0, (-1), 0],
  ![0, (-1), 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, (-1), 0, 0, 0, 0, (-1), 0, (-1), 0, 0, 0, 0, (-1), 0],
  ![0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, (-1), 0, 0, (-1), 0, 0, 0, 0, 0, (-1), 0, 0, 0, 0, (-1), 0, 0, 0, 1, 0, 0, 0, 0, 1, 0],
  ![1, 1, 1, 0, 0, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, (-1), (-1), 0, 0, (-1), 0, 0, 0, 0, 0, (-1), 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
  ![1, 2, 2, 1, 1, 2, 1, 0, 1, 2, 1, 2, 1, 1, 1, (-1), (-1), 1, 0, (-2), (-1), (-1), (-1), (-1), 0, (-1), 0, (-1), 0, 0, 0, (-1), (-1), (-1), 1, 0, 0, 0, 0, (-1), 1, 1, 1],
  ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1), 0, 0, 0, 0, 0, 0, (-1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0],
  ![(-1), (-2), (-2), (-1), (-1), (-2), (-1), 0, (-1), (-2), (-1), (-2), (-1), (-1), (-1), 1, 1, 0, 0, 2, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0, 0, 1, 1, 1, (-1), 0, 0, 0, 0, 0, (-1), (-1), (-1)],
  ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![(-1), (-1), (-1), 0, (-1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1), 0, (-1), 0, (-1), 0, 0, (-1), 0],
  ![1, 1, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, (-1), (-1), 0, (-1), (-1), 0, (-1), 0, (-1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0],
  ![(-1), (-2), (-2), (-1), (-1), (-2), (-1), 0, (-1), (-2), (-1), (-2), (-1), (-1), (-1), 1, 1, 0, 0, 2, 1, 1, 1, 1, 0, 1, 0, 1, 0, 0, 0, 1, 1, 1, (-1), 0, 0, 0, 0, 1, (-1), (-1), (-1)],
  ![1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, (-1), (-1), 0, 0, (-2), (-1), (-1), (-1), (-1), 0, (-1), 0, (-1), 0, 0, (-1), (-1), (-1), (-1), 1, 0, 0, 0, 0, 0, 1, 1, 1],
  ![(-2), (-3), (-2), (-2), (-2), (-2), (-1), (-1), (-1), (-2), (-2), (-2), (-1), (-1), (-1), 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, (-1), (-1), (-1), 0, 0, (-1), (-1), (-1), (-1)],
  ![2, 3, 2, 2, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, (-2), (-1), (-1), (-1), (-2), (-2), (-2), (-1), (-1), (-1), (-1), (-1), (-1), 0, 0, 0, (-1), (-1), (-1), 1, 1, 1, 0, 0, 0, 1, 1, 1],
  ![1, 1, 1, 0, 1, 2, 1, 0, 2, 1, 0, 1, 0, 1, 0, (-1), (-1), 0, (-1), (-1), 0, (-1), 0, (-1), 0, (-1), 0, (-1), 0, (-1), 0, 0, (-1), 0, 1, 0, 1, 0, 1, 0, 0, 1, 0],
  ![(-1), (-1), (-1), 0, (-1), (-2), (-1), 0, (-1), (-1), 0, (-1), 0, (-1), 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, (-1), 0, (-1), 0, (-1), 0, 0, (-1), 0],
  ![(-1), (-1), (-1), 0, (-1), (-1), (-1), 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, (-1), 0, (-1), 0, (-1), 0, 0, (-1), 0],
  ![1, 1, 1, 0, 1, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, (-1), (-1), 0, (-1), (-1), 0, (-1), 0, (-1), 0, (-1), 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0],
  ![(-1), (-1), 0, (-1), (-1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1), (-1), 0, 0, (-1), 0, 0, (-1)],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
  ![0, (-1), (-2), 0, 0, (-1), (-1), 0, 0, (-2), 0, (-1), (-1), (-1), 0, 0, 1, (-1), (-1), 2, 0, 0, 1, 1, (-1), 1, 0, 0, 0, 0, 0, 1, 1, 0, (-1), 0, 1, 0, 0, 1, (-1), (-1), 0],
  ![1, 2, 2, 1, 1, 1, 1, 0, 0, 2, 1, 1, 1, 1, 0, (-1), (-1), 0, 0, (-2), (-1), (-1), (-1), (-1), 0, (-1), 0, 0, 0, 0, 0, (-1), (-1), 0, 1, 0, 0, 0, 0, 0, 1, 1, 0],
  ![0, 0, 0, 0, 0, (-1), 0, 0, (-1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, (-2), (-2), (-1), (-1), (-2), (-1), 0, (-1), (-3), (-1), (-3), (-1), (-2), (-1), 0, 0, (-1), (-1), 2, 1, 1, 1, 1, 0, 1, 0, 1, 0, 0, 0, 1, 2, 1, 0, 0, 1, 1, 1, 1, (-1), (-1), (-1)],
  ![0, 1, 0, 0, 0, 0, 0, 0, (-1), 0, 0, 0, 0, (-1), 0, (-1), 0, 0, 0, (-1), (-1), (-1), 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 1, 1, 1],
  ![(-1), 0, 0, 0, 0, 1, 0, 0, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, (-1), 0, 0, 0, (-1), (-1), (-1), (-1), (-1), (-1), (-1), (-1), (-1), 0, 0, 0],
  ![(-3), (-3), (-2), (-2), (-2), (-2), (-2), (-2), (-1), (-1), (-2), (-1), (-1), 0, (-1), 3, 2, 2, 2, 2, 2, 2, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 0, 1, (-2), (-1), (-2), (-1), (-1), (-1), (-1), (-1), (-1)],
  ![4, 4, 4, 3, 3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 1, (-3), (-3), (-2), (-2), (-3), (-2), (-2), (-2), (-2), (-1), (-2), (-1), (-1), (-1), (-1), (-1), (-1), (-1), (-1), 2, 1, 1, 1, 1, 1, 1, 1, 1],
  ![1, 1, 1, 0, 1, 2, 1, 0, 1, 1, 0, 1, 0, 1, 0, (-1), (-1), 0, (-1), (-1), 0, (-1), 0, (-1), 0, (-1), 0, (-1), 0, 0, 0, 0, (-1), 0, 1, 0, 1, 0, 1, 0, 0, 1, 0],
  ![(-1), (-1), (-1), 0, (-1), (-2), (-1), 0, (-1), (-1), 0, (-1), 0, 0, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0, (-1), 0, (-1), 0, (-1), 0, 0, (-1), 0],
  ![1, 2, 2, 1, 1, 2, 1, 0, 1, 2, 1, 2, 1, 1, 1, (-1), (-1), 0, 0, (-2), (-1), (-1), (-1), (-1), 0, (-1), 0, (-1), 0, 0, 0, (-1), (-1), (-1), 1, 0, 0, 0, 0, 0, 1, 1, 1],
  ![(-1), (-2), (-2), (-1), (-1), (-2), (-1), 0, (-1), (-2), (-1), (-2), (-1), (-1), 0, 1, 1, 0, 0, 2, 1, 1, 1, 1, 0, 1, 0, 1, 0, 0, 0, 1, 1, 1, (-1), 0, 0, 0, 0, 0, (-1), (-1), (-1)]
]

private def rowDecoder : Matrix (Fin 50) (Fin 43) ℤ :=
  Matrix.of ![
  ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, (-1), (-1), (-1), (-1), (-1), (-1), (-1), (-1), (-1), (-1), (-1), (-1), (-1), (-1), (-1), (-1), (-1), (-1), (-1), 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
  ![(-1), (-1), (-1), (-1), (-1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1), (-1), (-1), (-1), (-1), (-1), (-1), (-1), (-1)],
  ![(-1), (-1), (-1), (-1), 0, (-1), (-1), (-1), 0, (-1), (-1), 0, (-1), 0, 0, 1, 1, 1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 0, 0, (-1), (-1), 0, (-1), 0, 0, (-1), 0, 0],
  ![(-1), (-1), (-1), 0, (-1), (-1), (-1), 0, (-1), (-1), 0, (-1), 0, (-1), 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, (-1), 0, (-1), 0, (-1), 0, 0, (-1), 0],
  ![(-1), (-1), 0, (-1), (-1), (-1), 0, (-1), (-1), 0, (-1), (-1), 0, 0, (-1), 1, 0, 1, 1, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 0, 1, 0, 0, 1, 0, (-1), (-1), 0, 0, (-1), 0, 0, (-1)],
  ![2, 3, 2, 2, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, (-2), (-1), (-1), (-1), (-2), (-2), (-2), (-1), (-1), (-1), (-1), (-1), (-1), 0, 0, 0, (-1), (-1), (-1), 1, 1, 1, 0, 0, 0, 1, 1, 1],
  ![3, 2, 2, 2, 2, 2, 2, 2, 2, 1, 1, 1, 1, 1, 1, (-2), (-2), (-2), (-2), (-1), (-1), (-1), (-1), (-1), (-1), (-1), (-1), (-1), (-1), (-1), (-1), 0, 0, 0, 1, 1, 1, 1, 1, 1, 0, 0, 0]
]

private def orderedRowsTwo : Fin 15 → Fin 2 → Fin 6 :=
  ![
  ![0, 1],
  ![0, 2],
  ![0, 3],
  ![0, 4],
  ![0, 5],
  ![1, 2],
  ![1, 3],
  ![1, 4],
  ![1, 5],
  ![2, 3],
  ![2, 4],
  ![2, 5],
  ![3, 4],
  ![3, 5],
  ![4, 5]
]

private def orderedRowsThree : Fin 20 → Fin 3 → Fin 6 :=
  ![
  ![0, 1, 2],
  ![0, 1, 3],
  ![0, 1, 4],
  ![0, 1, 5],
  ![0, 2, 3],
  ![0, 2, 4],
  ![0, 2, 5],
  ![0, 3, 4],
  ![0, 3, 5],
  ![0, 4, 5],
  ![1, 2, 3],
  ![1, 2, 4],
  ![1, 2, 5],
  ![1, 3, 4],
  ![1, 3, 5],
  ![1, 4, 5],
  ![2, 3, 4],
  ![2, 3, 5],
  ![2, 4, 5],
  ![3, 4, 5]
]

private def orderedRowsFour : Fin 15 → Fin 4 → Fin 6 :=
  ![
  ![0, 1, 2, 3],
  ![0, 1, 2, 4],
  ![0, 1, 2, 5],
  ![0, 1, 3, 4],
  ![0, 1, 3, 5],
  ![0, 1, 4, 5],
  ![0, 2, 3, 4],
  ![0, 2, 3, 5],
  ![0, 2, 4, 5],
  ![0, 3, 4, 5],
  ![1, 2, 3, 4],
  ![1, 2, 3, 5],
  ![1, 2, 4, 5],
  ![1, 3, 4, 5],
  ![2, 3, 4, 5]
]

private def lower : Finset (Fin 6) := {0, 1}
private def middleLeft : Finset (Fin 6) := {0, 1, 2}
private def middleRight : Finset (Fin 6) := {0, 1, 3}
private def upper : Finset (Fin 6) := {0, 1, 2, 3}

private def intervalIndicator (I X Y : Finset (Fin 6)) : ℤ :=
  if X ⊆ I ∧ I ⊆ Y then 1 else 0

private def incidence : Matrix (Fin 50) (Fin 90) ℤ :=
  Matrix.of fun r c => intervalIndicator (targetLabels r) (intervalLower c) (intervalUpper c)

private def selectedIncidence : Matrix (Fin 43) (Fin 90) ℤ :=
  incidence.submatrix selectedRows id

private def chosenIncidence : Matrix (Fin 50) (Fin 43) ℤ :=
  incidence.submatrix id selectedIntervals

private def selectedSquare : Matrix (Fin 43) (Fin 43) ℤ :=
  incidence.submatrix selectedRows selectedIntervals

private def centerRational : Matrix (Fin 6) (Fin 6) ℚ :=
  centerNumerator.map fun z => (z : ℚ) / 8389

/-- The rational orthogonal center of the certified ball. -/
def center : Matrix (Fin 6) (Fin 6) ℂ :=
  (Rat.castHom ℂ).mapMatrix centerRational

private def centerWeight (c : Fin 90) : ℚ := (centerWeightNumerator c : ℚ) / 70375321

private def minorTarget (U : Matrix (Fin 6) (Fin 6) ℂ) (I : Finset (Fin 6)) : ℝ :=
  subsetMinorSq U I lower + subsetMinorSq U I middleLeft +
    (subsetMinorSq U I middleRight + subsetMinorSq U I upper)

/-- The squared-minor target consists of 15 lower, 20 middle, and 15 upper coordinates. -/
noncomputable def target (U : Matrix (Fin 6) (Fin 6) ℂ) : Fin 50 → ℝ :=
  fun r => minorTarget U (targetLabels r)

private def centerSquareMinor {k : ℕ} (rows cols : Fin k → Fin 6) : ℚ :=
  (centerRational.submatrix rows cols).det ^ 2

private def centerTargetRational : Fin 50 → ℚ :=
  Fin.addCases
    (fun r : Fin 15 => centerSquareMinor (orderedRowsTwo r) ![0, 1])
    (Fin.addCases
      (fun r : Fin 20 => centerSquareMinor (orderedRowsThree r) ![0, 1, 2] +
        centerSquareMinor (orderedRowsThree r) ![0, 1, 3])
      (fun r : Fin 15 => centerSquareMinor (orderedRowsFour r) ![0, 1, 2, 3]))

private theorem centerRational_orthogonal : centerRational * centerRationalᵀ = 1 := by
  ext i j : 1
  revert i j
  decide

/-- The center is a complex unitary matrix. -/
theorem center_unitary : IsUnitary center := by
  have hadj : centerᴴ = (Rat.castHom ℂ).mapMatrix centerRationalᵀ := by
    ext i j
    simp [center, Matrix.conjTranspose_apply, Complex.star_def, ← Complex.ofReal_ratCast]
  have hr : center * centerᴴ = 1 := by
    rw [hadj, center, ← (Rat.castHom ℂ).mapMatrix.map_mul, centerRational_orthogonal,
      (Rat.castHom ℂ).mapMatrix.map_one]
  exact ⟨hr, Matrix.mul_eq_one_comm.mp hr⟩

set_option maxRecDepth 40000 in
set_option maxHeartbeats 2000000 in
private theorem numerical_selected_inverse :
    selectedSquare * repairInverse = 1 := by
  ext r c : 1
  revert c
  fin_cases r <;> decide

set_option maxRecDepth 40000 in
set_option maxHeartbeats 2000000 in
private theorem numerical_decoder :
    rowDecoder * selectedIncidence = incidence := by
  ext r c : 1
  revert c
  fin_cases r <;> decide

set_option maxRecDepth 40000 in
set_option maxHeartbeats 2000000 in
private theorem numerical_decoder_eq_repair :
    chosenIncidence * repairInverse = rowDecoder := by
  ext r c : 1
  revert c
  fin_cases r <;> decide

private theorem numerical_row_bound :
    ∀ r : Fin 43, (∑ c, |repairInverse r c|) ≤ 82 := by decide

private theorem numerical_selected_injective : Function.Injective selectedIntervals := by
  change ∀ i j : Fin 43, selectedIntervals i = selectedIntervals j → i = j
  decide

private theorem numerical_center_mass :
    ∑ c : Fin 90, centerWeight c = 1 := by decide

private theorem numerical_center_weight_bound :
    ∀ c : Fin 90, (3 / 70375321 : ℚ) ≤ centerWeight c := by decide

set_option maxRecDepth 40000 in
set_option maxHeartbeats 2000000 in
private theorem numerical_center_target :
    ∀ r, ∑ c, (incidence r c : ℚ) * centerWeight c = centerTargetRational r := by decide

private theorem targetLabels_two :
    ∀ r : Fin 15,
      targetLabels (Fin.castAdd 35 r) = Finset.univ.image (orderedRowsTwo r) ∧
      Function.Injective (orderedRowsTwo r) := by
  change ∀ r : Fin 15,
    targetLabels (Fin.castAdd 35 r) = Finset.univ.image (orderedRowsTwo r) ∧
    (∀ i j : Fin 2, orderedRowsTwo r i = orderedRowsTwo r j → i = j)
  decide

private theorem targetLabels_three :
    ∀ r : Fin 20,
      targetLabels (Fin.natAdd 15 (Fin.castAdd 15 r)) = Finset.univ.image (orderedRowsThree r) ∧
      Function.Injective (orderedRowsThree r) := by
  change ∀ r : Fin 20,
    targetLabels (Fin.natAdd 15 (Fin.castAdd 15 r)) = Finset.univ.image (orderedRowsThree r) ∧
    (∀ i j : Fin 3, orderedRowsThree r i = orderedRowsThree r j → i = j)
  decide

private theorem targetLabels_four :
    ∀ r : Fin 15,
      targetLabels (Fin.natAdd 15 (Fin.natAdd 20 r)) = Finset.univ.image (orderedRowsFour r) ∧
      Function.Injective (orderedRowsFour r) := by
  change ∀ r : Fin 15,
    targetLabels (Fin.natAdd 15 (Fin.natAdd 20 r)) = Finset.univ.image (orderedRowsFour r) ∧
    (∀ i j : Fin 4, orderedRowsFour r i = orderedRowsFour r j → i = j)
  decide

private noncomputable def orderedEquiv {k : ℕ} {I : Finset (Fin 6)} (f : Fin k → Fin 6)
    (hI : I = Finset.univ.image f) (hf : Function.Injective f) : Fin k ≃ I :=
  Equiv.ofBijective (fun j => ⟨f j, by rw [hI]; exact Finset.mem_image_of_mem f (Finset.mem_univ j)⟩)
    ⟨fun _ _ h => hf (congrArg Subtype.val h),
      fun i => by
        have hi : (i : Fin 6) ∈ Finset.univ.image f := hI ▸ i.property
        obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hi
        exact ⟨j, Subtype.ext hj⟩⟩

private theorem center_minor {k : ℕ} {I J : Finset (Fin 6)} (f g : Fin k → Fin 6)
    (hI : I = Finset.univ.image f) (hf : Function.Injective f)
    (hJ : J = Finset.univ.image g) (hg : Function.Injective g) :
    subsetMinorSq center I J = (centerSquareMinor f g : ℝ) := by
  rw [subsetMinorSq_eq_normSq_det_submatrix _ center_unitary I J
    (orderedEquiv f hI hf) (orderedEquiv g hJ hg)]
  change Complex.normSq ((Rat.castHom ℂ).mapMatrix (centerRational.submatrix f g)).det =
    (centerSquareMinor f g : ℝ)
  change Complex.normSq ((centerRational.submatrix f g).map (Rat.castHom ℂ)).det =
    (centerSquareMinor f g : ℝ)
  rw [← RingHom.map_det]
  change Complex.normSq (((centerRational.submatrix f g).det : ℚ) : ℂ) = _
  rw [Complex.normSq_ratCast]
  simp only [centerSquareMinor, Rat.cast_pow, pow_two]

private theorem target_center_cast (r : Fin 50) :
    target center r = (centerTargetRational r : ℝ) := by
  refine Fin.addCases (m := 15) (n := 35) ?_ (Fin.addCases (m := 20) (n := 15) ?_ ?_) r
  · intro r
    obtain ⟨hI, hf⟩ := targetLabels_two r
    have hcard : (targetLabels (Fin.castAdd 35 r)).card = 2 := by
      simpa using (Fintype.card_congr (orderedEquiv _ hI hf)).symm
    unfold target minorTarget centerTargetRational
    rw [Fin.addCases_left, center_minor (orderedRowsTwo r) ![0, 1] hI hf (by decide) (by
      change ∀ i j : Fin 2, (![0, 1] : Fin 2 → Fin 6) i = ![0, 1] j → i = j
      decide)]
    simp only [subsetMinorSq, hcard, show middleLeft.card = 3 from by decide,
      show middleRight.card = 3 from by decide, show upper.card = 4 from by decide,
      Nat.reduceEq, dif_neg, zero_add, add_zero]
  · intro r
    obtain ⟨hI, hf⟩ := targetLabels_three r
    have hcard : (targetLabels (Fin.natAdd 15 (Fin.castAdd 15 r))).card = 3 := by
      simpa using (Fintype.card_congr (orderedEquiv _ hI hf)).symm
    unfold target minorTarget centerTargetRational
    rw [Fin.addCases_right, Fin.addCases_left,
      center_minor (orderedRowsThree r) ![0, 1, 2] hI hf (by decide) (by
        change ∀ i j : Fin 3, (![0, 1, 2] : Fin 3 → Fin 6) i = ![0, 1, 2] j → i = j
        decide),
      center_minor (orderedRowsThree r) ![0, 1, 3] hI hf (by decide) (by
        change ∀ i j : Fin 3, (![0, 1, 3] : Fin 3 → Fin 6) i = ![0, 1, 3] j → i = j
        decide)]
    simp only [subsetMinorSq, hcard, show lower.card = 2 from by decide,
      show upper.card = 4 from by decide, Nat.reduceEq, dif_neg, zero_add, add_zero, Rat.cast_add]
  · intro r
    obtain ⟨hI, hf⟩ := targetLabels_four r
    have hcard : (targetLabels (Fin.natAdd 15 (Fin.natAdd 20 r))).card = 4 := by
      simpa using (Fintype.card_congr (orderedEquiv _ hI hf)).symm
    unfold target minorTarget centerTargetRational
    rw [Fin.addCases_right, Fin.addCases_right,
      center_minor (orderedRowsFour r) ![0, 1, 2, 3] hI hf (by decide) (by
        change ∀ i j : Fin 4, (![0, 1, 2, 3] : Fin 4 → Fin 6) i = ![0, 1, 2, 3] j → i = j
        decide)]
    simp only [subsetMinorSq, hcard, show lower.card = 2 from by decide,
      show middleLeft.card = 3 from by decide, show middleRight.card = 3 from by decide,
      Nat.reduceEq, dif_neg, zero_add, add_zero]

private def incidenceReal : Matrix (Fin 50) (Fin 90) ℝ :=
  (Int.castRingHom ℝ).mapMatrix incidence

private theorem center_target_eq : incidenceReal *ᵥ (fun c => (centerWeight c : ℝ)) = target center := by
  funext r
  rw [target_center_cast]
  change (∑ c, (incidence r c : ℝ) * (centerWeight c : ℝ)) = _
  exact_mod_cast numerical_center_target r

private def selectedPart (v : Fin 50 → ℝ) : Fin 43 → ℝ := v ∘ selectedRows

private def inverseReal : Matrix (Fin 43) (Fin 43) ℝ :=
  (Int.castRingHom ℝ).mapMatrix repairInverse

private def decoderReal : Matrix (Fin 50) (Fin 43) ℝ :=
  (Int.castRingHom ℝ).mapMatrix rowDecoder

private def chosenIncidenceReal : Matrix (Fin 50) (Fin 43) ℝ :=
  (Int.castRingHom ℝ).mapMatrix chosenIncidence

private def selectedIncidenceReal : Matrix (Fin 43) (Fin 90) ℝ :=
  (Int.castRingHom ℝ).mapMatrix selectedIncidence

private def liftedCorrection (v : Fin 50 → ℝ) (c : Fin 90) : ℝ :=
  ∑ j : Fin 43, if selectedIntervals j = c then (inverseReal *ᵥ selectedPart v) j else 0

private theorem liftedCorrection_image (v : Fin 50 → ℝ) :
    incidenceReal *ᵥ liftedCorrection v = decoderReal *ᵥ selectedPart v := by
  have hm : chosenIncidenceReal * inverseReal = decoderReal := by
    simpa only [chosenIncidenceReal, inverseReal, decoderReal, map_mul] using
      congrArg (Int.castRingHom ℝ).mapMatrix numerical_decoder_eq_repair
  rw [← hm, ← Matrix.mulVec_mulVec]
  funext r
  change (∑ c : Fin 90, incidenceReal r c * liftedCorrection v c) =
    ∑ j : Fin 43, chosenIncidenceReal r j * (inverseReal *ᵥ selectedPart v) j
  simp only [liftedCorrection, Finset.mul_sum, mul_ite, mul_zero]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_eq_single (selectedIntervals j)]
  · simp [incidenceReal, chosenIncidenceReal, chosenIncidence, Matrix.submatrix_apply]
  · intro k _ hk
    simp only [if_neg (Ne.symm hk)]
  · simp

private theorem decoder_correct (v : Fin 90 → ℝ) :
    decoderReal *ᵥ selectedPart (incidenceReal *ᵥ v) = incidenceReal *ᵥ v := by
  have hm : decoderReal * selectedIncidenceReal = incidenceReal := by
    simpa only [decoderReal, selectedIncidenceReal, incidenceReal, map_mul] using
      congrArg (Int.castRingHom ℝ).mapMatrix numerical_decoder
  have hselected : selectedPart (incidenceReal *ᵥ v) = selectedIncidenceReal *ᵥ v := rfl
  rw [hselected, Matrix.mulVec_mulVec, hm]

private theorem inverseReal_bound (v : Fin 50 → ℝ) (δ : ℝ) (hδ : 0 ≤ δ)
    (hv : ∀ r, |v r| ≤ δ) (j : Fin 43) :
    |(inverseReal *ᵥ selectedPart v) j| ≤ 82 * δ := by
  change |∑ r : Fin 43, (repairInverse j r : ℝ) * v (selectedRows r)| ≤ _
  calc
    _ ≤ ∑ r : Fin 43, |(repairInverse j r : ℝ) * v (selectedRows r)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ r : Fin 43, |(repairInverse j r : ℝ)| * δ := by
      apply Finset.sum_le_sum
      intro r _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hv _) (abs_nonneg _)
    _ = (∑ r : Fin 43, |(repairInverse j r : ℝ)|) * δ := by rw [Finset.sum_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast numerical_row_bound j) hδ

private theorem liftedCorrection_bound (v : Fin 50 → ℝ) (δ : ℝ) (hδ : 0 ≤ δ)
    (hv : ∀ r, |v r| ≤ δ) (c : Fin 90) :
    |liftedCorrection v c| ≤ 82 * δ := by
  unfold liftedCorrection
  by_cases hc : c ∈ Set.range selectedIntervals
  · obtain ⟨j, rfl⟩ := hc
    rw [Finset.sum_eq_single j]
    · simpa only [if_pos rfl] using inverseReal_bound v δ hδ hv j
    · intro k _ hk
      rw [if_neg (fun h => hk (numerical_selected_injective h))]
    · simp
  · have hz (j : Fin 43) : selectedIntervals j ≠ c := fun hj => hc ⟨j, hj⟩
    simp only [hz, if_false, Finset.sum_const_zero, abs_zero]
    positivity

private theorem repair_target (q : Fin 50 → ℝ)
    (hspan : ∃ s : Fin 90 → ℝ, incidenceReal *ᵥ s = q)
    (hq : ∀ r, |q r - target center r| ≤ 12 / 23083105288) :
    ∃ w : Fin 90 → ℝ, (∀ c, 0 ≤ w c) ∧ incidenceReal *ᵥ w = q := by
  obtain ⟨s, hs⟩ := hspan
  let w₀ : Fin 90 → ℝ := fun c => centerWeight c
  let delta := q - target center
  let w := w₀ + liftedCorrection delta
  have hd : incidenceReal *ᵥ (s - w₀) = delta := by
    rw [Matrix.mulVec_sub, hs, center_target_eq] <;> rfl
  have he : incidenceReal *ᵥ liftedCorrection delta = delta := by
    rw [liftedCorrection_image, ← hd, decoder_correct]
  refine ⟨w, fun c => ?_, ?_⟩
  · have hbound := liftedCorrection_bound delta
      (12 / 23083105288) (by norm_num) hq c
    have hw : (3 / 70375321 : ℝ) ≤ w₀ c := by exact_mod_cast numerical_center_weight_bound c
    change 0 ≤ w₀ c + liftedCorrection delta c
    linarith only [hw, (abs_le.mp hbound).1]
  · dsimp only [w]
    rw [Matrix.mulVec_add, center_target_eq, he]
    change target center + (q - target center) = q
    abel

private def sourceMarker (I J : Finset (Fin 6)) : ℤ :=
  if J = I then 1 else 0

private theorem interval_four_markers :
    ∀ I : Finset (Fin 6), intervalIndicator I lower upper =
      sourceMarker I lower + sourceMarker I middleLeft +
        (sourceMarker I middleRight + sourceMarker I upper) := by decide

private theorem mapped_four_markers (I : Finset (Fin 6)) (p : Equiv.Perm (Fin 6)) :
    intervalIndicator I (lower.map p.toEmbedding) (upper.map p.toEmbedding) =
      sourceMarker I (lower.map p.toEmbedding) + sourceMarker I (middleLeft.map p.toEmbedding) +
        (sourceMarker I (middleRight.map p.toEmbedding) + sourceMarker I (upper.map p.toEmbedding)) := by
  have hmap : (I.map p.symm.toEmbedding).map p.toEmbedding = I := by
    ext i
    simp [Finset.mem_map_equiv]
  have hp (J : Finset (Fin 6)) : J = I.map p.symm.toEmbedding ↔ J.map p.toEmbedding = I := by
    constructor
    · intro h
      rw [h, hmap]
    · intro h
      apply (Finset.map_injective p.toEmbedding)
      exact h.trans hmap.symm
  have hL : lower.map p.toEmbedding ⊆ I ↔ lower ⊆ I.map p.symm.toEmbedding := by
    simpa only [hmap] using (Finset.map_subset_map :
      lower.map p.toEmbedding ⊆ (I.map p.symm.toEmbedding).map p.toEmbedding ↔ _)
  have hR : I ⊆ upper.map p.toEmbedding ↔ I.map p.symm.toEmbedding ⊆ upper := by
    simpa only [hmap] using (Finset.map_subset_map :
      (I.map p.symm.toEmbedding).map p.toEmbedding ⊆ upper.map p.toEmbedding ↔ _)
  calc
    _ = intervalIndicator (I.map p.symm.toEmbedding) lower upper := by
      unfold intervalIndicator
      rw [hL, hR]
    _ = _ := by
      rw [interval_four_markers]
      simp only [sourceMarker, hp]

private theorem signed_marker (U : Matrix (Fin 6) (Fin 6) ℂ) (hU : IsUnitary U)
    (I J : Finset (Fin 6)) :
    (∑ p, (sourceMarker I (J.map (p : Equiv.Perm (Fin 6)).toEmbedding) : ℝ) *
      realSignedWeight U p) = subsetMinorSq U I J := by
  have h := congrArg Complex.re (sum_signedWeight_image_eq_subsetMinorSq U hU I J)
  rw [Finset.sum_filter, Complex.re_sum, Complex.ofReal_re] at h
  rw [← h]
  apply Finset.sum_congr rfl
  intro p _
  by_cases hp : J.map p.toEmbedding = I
  · simp [sourceMarker, hp, realSignedWeight]
  · simp [sourceMarker, hp]

private theorem target_signed (U : Matrix (Fin 6) (Fin 6) ℂ) (hU : IsUnitary U)
    (r : Fin 50) :
    target U r = ∑ p, (intervalIndicator (targetLabels r)
      (lower.map (p : Equiv.Perm (Fin 6)).toEmbedding) (upper.map p.toEmbedding) : ℝ) *
        realSignedWeight U p := by
  unfold target minorTarget
  simp_rw [mapped_four_markers, Int.cast_add, add_mul, Finset.sum_add_distrib, signed_marker U hU]

set_option maxRecDepth 40000 in
set_option maxHeartbeats 2000000 in
private theorem intervals_exhaustive :
    ∀ X Y : Finset (Fin 6), X.card = 2 → Y.card = 4 → X ⊆ Y →
      ∃ c : Fin 90, intervalLower c = X ∧ intervalUpper c = Y := by decide

private theorem lower_subset_upper : lower ⊆ upper := by decide

private noncomputable def intervalOf (p : Equiv.Perm (Fin 6)) : Fin 90 :=
  Classical.choose (intervals_exhaustive (lower.map p.toEmbedding) (upper.map p.toEmbedding)
    (by rw [Finset.card_map]; decide) (by rw [Finset.card_map]; decide)
    (Finset.map_subset_map.mpr lower_subset_upper))

private theorem intervalOf_bounds (p : Equiv.Perm (Fin 6)) :
    intervalLower (intervalOf p) = lower.map p.toEmbedding ∧
      intervalUpper (intervalOf p) = upper.map p.toEmbedding :=
  Classical.choose_spec (intervals_exhaustive (lower.map p.toEmbedding) (upper.map p.toEmbedding)
    (by rw [Finset.card_map]; decide) (by rw [Finset.card_map]; decide)
    (Finset.map_subset_map.mpr lower_subset_upper))

private noncomputable def groupedSigned (U : Matrix (Fin 6) (Fin 6) ℂ) (c : Fin 90) : ℝ :=
  ∑ p ∈ Finset.univ.filter (fun p => intervalOf p = c), realSignedWeight U p

private theorem groupedSigned_mass (U : Matrix (Fin 6) (Fin 6) ℂ) (hU : IsUnitary U) :
    ∑ c, groupedSigned U c = 1 := by
  unfold groupedSigned
  rw [Finset.sum_fiberwise, sum_realSignedWeight U hU]

private theorem target_range (U : Matrix (Fin 6) (Fin 6) ℂ) (hU : IsUnitary U) :
    incidenceReal *ᵥ groupedSigned U = target U := by
  funext r
  change (∑ c, (incidence r c : ℝ) * groupedSigned U c) = _
  rw [target_signed U hU r]
  simp only [groupedSigned, Finset.sum_filter, Finset.mul_sum, mul_ite, mul_zero]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  rw [Finset.sum_eq_single (intervalOf p)]
  · simp [incidence, (intervalOf_bounds p).1, (intervalOf_bounds p).2]
  · intro c _ hc
    simp only [if_neg (Ne.symm hc)]
  · simp

private theorem lower_row_mass :
    ∀ c : Fin 90, (∑ r : Fin 15, incidence (Fin.castAdd 35 r) c) = 1 := by decide

private theorem weight_mass (w : Fin 90 → ℝ) :
    ∑ r : Fin 15, (incidenceReal *ᵥ w) (Fin.castAdd 35 r) = ∑ c, w c := by
  change (∑ r : Fin 15, ∑ c : Fin 90, (incidence (Fin.castAdd 35 r) c : ℝ) * w c) = _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _
  rw [← Finset.sum_mul, ← Int.cast_sum, lower_row_mass, Int.cast_one, one_mul]

/-- A unitary whose squared-minor target is within the certified coordinate
distance admits a positive normalized interval representation. -/
private theorem intervalLaw_of_target_distance (U : Matrix (Fin 6) (Fin 6) ℂ)
    (hU : IsUnitary U) (hq : ∀ r, |target U r - target center r| ≤ 12 / 23083105288) :
    ∃ w : Fin 90 → ℝ, (∀ c, 0 ≤ w c) ∧ (∑ c, w c = 1) ∧
      incidenceReal *ᵥ w = target U := by
  obtain ⟨w, hw, he⟩ := repair_target (target U)
    ⟨groupedSigned U, target_range U hU⟩ hq
  have hmass := weight_mass w
  rw [he, ← target_range U hU, weight_mass, groupedSigned_mass U hU] at hmass
  exact ⟨w, hw, hmass.symm, he⟩
private def representativeAction : Fin 90 → Fin 6 → Fin 6 := ![
  ![0, 1, 2, 3, 4, 5],
  ![0, 1, 2, 4, 3, 5],
  ![0, 1, 2, 5, 3, 4],
  ![0, 1, 3, 4, 2, 5],
  ![0, 1, 3, 5, 2, 4],
  ![0, 1, 4, 5, 2, 3],
  ![0, 2, 1, 3, 4, 5],
  ![0, 2, 1, 4, 3, 5],
  ![0, 2, 1, 5, 3, 4],
  ![0, 2, 3, 4, 1, 5],
  ![0, 2, 3, 5, 1, 4],
  ![0, 2, 4, 5, 1, 3],
  ![0, 3, 1, 2, 4, 5],
  ![0, 3, 1, 4, 2, 5],
  ![0, 3, 1, 5, 2, 4],
  ![0, 3, 2, 4, 1, 5],
  ![0, 3, 2, 5, 1, 4],
  ![0, 3, 4, 5, 1, 2],
  ![0, 4, 1, 2, 3, 5],
  ![0, 4, 1, 3, 2, 5],
  ![0, 4, 1, 5, 2, 3],
  ![0, 4, 2, 3, 1, 5],
  ![0, 4, 2, 5, 1, 3],
  ![0, 4, 3, 5, 1, 2],
  ![0, 5, 1, 2, 3, 4],
  ![0, 5, 1, 3, 2, 4],
  ![0, 5, 1, 4, 2, 3],
  ![0, 5, 2, 3, 1, 4],
  ![0, 5, 2, 4, 1, 3],
  ![0, 5, 3, 4, 1, 2],
  ![1, 2, 0, 3, 4, 5],
  ![1, 2, 0, 4, 3, 5],
  ![1, 2, 0, 5, 3, 4],
  ![1, 2, 3, 4, 0, 5],
  ![1, 2, 3, 5, 0, 4],
  ![1, 2, 4, 5, 0, 3],
  ![1, 3, 0, 2, 4, 5],
  ![1, 3, 0, 4, 2, 5],
  ![1, 3, 0, 5, 2, 4],
  ![1, 3, 2, 4, 0, 5],
  ![1, 3, 2, 5, 0, 4],
  ![1, 3, 4, 5, 0, 2],
  ![1, 4, 0, 2, 3, 5],
  ![1, 4, 0, 3, 2, 5],
  ![1, 4, 0, 5, 2, 3],
  ![1, 4, 2, 3, 0, 5],
  ![1, 4, 2, 5, 0, 3],
  ![1, 4, 3, 5, 0, 2],
  ![1, 5, 0, 2, 3, 4],
  ![1, 5, 0, 3, 2, 4],
  ![1, 5, 0, 4, 2, 3],
  ![1, 5, 2, 3, 0, 4],
  ![1, 5, 2, 4, 0, 3],
  ![1, 5, 3, 4, 0, 2],
  ![2, 3, 0, 1, 4, 5],
  ![2, 3, 0, 4, 1, 5],
  ![2, 3, 0, 5, 1, 4],
  ![2, 3, 1, 4, 0, 5],
  ![2, 3, 1, 5, 0, 4],
  ![2, 3, 4, 5, 0, 1],
  ![2, 4, 0, 1, 3, 5],
  ![2, 4, 0, 3, 1, 5],
  ![2, 4, 0, 5, 1, 3],
  ![2, 4, 1, 3, 0, 5],
  ![2, 4, 1, 5, 0, 3],
  ![2, 4, 3, 5, 0, 1],
  ![2, 5, 0, 1, 3, 4],
  ![2, 5, 0, 3, 1, 4],
  ![2, 5, 0, 4, 1, 3],
  ![2, 5, 1, 3, 0, 4],
  ![2, 5, 1, 4, 0, 3],
  ![2, 5, 3, 4, 0, 1],
  ![3, 4, 0, 1, 2, 5],
  ![3, 4, 0, 2, 1, 5],
  ![3, 4, 0, 5, 1, 2],
  ![3, 4, 1, 2, 0, 5],
  ![3, 4, 1, 5, 0, 2],
  ![3, 4, 2, 5, 0, 1],
  ![3, 5, 0, 1, 2, 4],
  ![3, 5, 0, 2, 1, 4],
  ![3, 5, 0, 4, 1, 2],
  ![3, 5, 1, 2, 0, 4],
  ![3, 5, 1, 4, 0, 2],
  ![3, 5, 2, 4, 0, 1],
  ![4, 5, 0, 1, 2, 3],
  ![4, 5, 0, 2, 1, 3],
  ![4, 5, 0, 3, 1, 2],
  ![4, 5, 1, 2, 0, 3],
  ![4, 5, 1, 3, 0, 2],
  ![4, 5, 2, 3, 0, 1]
]

private def representativeInverse : Fin 90 → Fin 6 → Fin 6 := ![
  ![0, 1, 2, 3, 4, 5],
  ![0, 1, 2, 4, 3, 5],
  ![0, 1, 2, 4, 5, 3],
  ![0, 1, 4, 2, 3, 5],
  ![0, 1, 4, 2, 5, 3],
  ![0, 1, 4, 5, 2, 3],
  ![0, 2, 1, 3, 4, 5],
  ![0, 2, 1, 4, 3, 5],
  ![0, 2, 1, 4, 5, 3],
  ![0, 4, 1, 2, 3, 5],
  ![0, 4, 1, 2, 5, 3],
  ![0, 4, 1, 5, 2, 3],
  ![0, 2, 3, 1, 4, 5],
  ![0, 2, 4, 1, 3, 5],
  ![0, 2, 4, 1, 5, 3],
  ![0, 4, 2, 1, 3, 5],
  ![0, 4, 2, 1, 5, 3],
  ![0, 4, 5, 1, 2, 3],
  ![0, 2, 3, 4, 1, 5],
  ![0, 2, 4, 3, 1, 5],
  ![0, 2, 4, 5, 1, 3],
  ![0, 4, 2, 3, 1, 5],
  ![0, 4, 2, 5, 1, 3],
  ![0, 4, 5, 2, 1, 3],
  ![0, 2, 3, 4, 5, 1],
  ![0, 2, 4, 3, 5, 1],
  ![0, 2, 4, 5, 3, 1],
  ![0, 4, 2, 3, 5, 1],
  ![0, 4, 2, 5, 3, 1],
  ![0, 4, 5, 2, 3, 1],
  ![2, 0, 1, 3, 4, 5],
  ![2, 0, 1, 4, 3, 5],
  ![2, 0, 1, 4, 5, 3],
  ![4, 0, 1, 2, 3, 5],
  ![4, 0, 1, 2, 5, 3],
  ![4, 0, 1, 5, 2, 3],
  ![2, 0, 3, 1, 4, 5],
  ![2, 0, 4, 1, 3, 5],
  ![2, 0, 4, 1, 5, 3],
  ![4, 0, 2, 1, 3, 5],
  ![4, 0, 2, 1, 5, 3],
  ![4, 0, 5, 1, 2, 3],
  ![2, 0, 3, 4, 1, 5],
  ![2, 0, 4, 3, 1, 5],
  ![2, 0, 4, 5, 1, 3],
  ![4, 0, 2, 3, 1, 5],
  ![4, 0, 2, 5, 1, 3],
  ![4, 0, 5, 2, 1, 3],
  ![2, 0, 3, 4, 5, 1],
  ![2, 0, 4, 3, 5, 1],
  ![2, 0, 4, 5, 3, 1],
  ![4, 0, 2, 3, 5, 1],
  ![4, 0, 2, 5, 3, 1],
  ![4, 0, 5, 2, 3, 1],
  ![2, 3, 0, 1, 4, 5],
  ![2, 4, 0, 1, 3, 5],
  ![2, 4, 0, 1, 5, 3],
  ![4, 2, 0, 1, 3, 5],
  ![4, 2, 0, 1, 5, 3],
  ![4, 5, 0, 1, 2, 3],
  ![2, 3, 0, 4, 1, 5],
  ![2, 4, 0, 3, 1, 5],
  ![2, 4, 0, 5, 1, 3],
  ![4, 2, 0, 3, 1, 5],
  ![4, 2, 0, 5, 1, 3],
  ![4, 5, 0, 2, 1, 3],
  ![2, 3, 0, 4, 5, 1],
  ![2, 4, 0, 3, 5, 1],
  ![2, 4, 0, 5, 3, 1],
  ![4, 2, 0, 3, 5, 1],
  ![4, 2, 0, 5, 3, 1],
  ![4, 5, 0, 2, 3, 1],
  ![2, 3, 4, 0, 1, 5],
  ![2, 4, 3, 0, 1, 5],
  ![2, 4, 5, 0, 1, 3],
  ![4, 2, 3, 0, 1, 5],
  ![4, 2, 5, 0, 1, 3],
  ![4, 5, 2, 0, 1, 3],
  ![2, 3, 4, 0, 5, 1],
  ![2, 4, 3, 0, 5, 1],
  ![2, 4, 5, 0, 3, 1],
  ![4, 2, 3, 0, 5, 1],
  ![4, 2, 5, 0, 3, 1],
  ![4, 5, 2, 0, 3, 1],
  ![2, 3, 4, 5, 0, 1],
  ![2, 4, 3, 5, 0, 1],
  ![2, 4, 5, 3, 0, 1],
  ![4, 2, 3, 5, 0, 1],
  ![4, 2, 5, 3, 0, 1],
  ![4, 5, 2, 3, 0, 1]
]

private theorem representative_left :
    ∀ (c : Fin 90) (i : Fin 6), representativeInverse c (representativeAction c i) = i := by decide

private theorem representative_right :
    ∀ (c : Fin 90) (i : Fin 6), representativeAction c (representativeInverse c i) = i := by decide

private def representative (c : Fin 90) : Equiv.Perm (Fin 6) :=
  ⟨representativeAction c, representativeInverse c, representative_left c, representative_right c⟩

private theorem representative_bounds :
    ∀ c : Fin 90, intervalLower c = lower.map (representative c).toEmbedding ∧
      intervalUpper c = upper.map (representative c).toEmbedding := by decide

private theorem targetLabels_injective : Function.Injective targetLabels := by
  change ∀ r s : Fin 50, targetLabels r = targetLabels s → r = s
  decide

private theorem targetLabels_exhaustive :
    ∀ S : Finset (Fin 6), 2 ≤ S.card → S.card ≤ 4 → ∃ r, targetLabels r = S := by decide

/-- The second spectrum assigns one value to each fixed pair of columns. -/
def pairedSpectrum (b₀ b₁ b₂ : ℂ) : Fin 6 → ℂ := ![b₁, b₁, b₂, b₂, b₀, b₀]

private def subsetMonomial (x y : Fin 6 → ℂ) (S : Finset (Fin 6)) : ℂ :=
  (∏ i ∈ Sᶜ, x i) * ∏ i ∈ S, y i

private theorem subsetMonomial_map (x y : Fin 6 → ℂ) (S : Finset (Fin 6))
    (p : Equiv.Perm (Fin 6)) :
    subsetMonomial x y (S.map p.toEmbedding) =
      (∏ i ∈ Sᶜ, x (p i)) * ∏ i ∈ S, y (p i) := by
  have h : (S.map p.toEmbedding)ᶜ = Sᶜ.map p.toEmbedding := by
    ext j
    simp [Finset.mem_map_equiv]
  unfold subsetMonomial
  rw [h, Finset.prod_map, Finset.prod_map] <;> rfl

private theorem sum_one_marker (x y : Fin 6 → ℂ)
    (S : Finset (Fin 6)) (hlo : 2 ≤ S.card) (hhi : S.card ≤ 4) :
    (∑ r : Fin 50, (sourceMarker (targetLabels r) S : ℂ) *
      subsetMonomial x y (targetLabels r)) = subsetMonomial x y S := by
  obtain ⟨r, hr⟩ := targetLabels_exhaustive S hlo hhi
  rw [Finset.sum_eq_single r]
  · simp [sourceMarker, hr]
  · intro s _ hs
    have hn : S ≠ targetLabels s := fun he => hs (targetLabels_injective (he.symm.trans hr.symm))
    simp [sourceMarker, hn]
  · simp

private theorem matching_four_monomials (a : Fin 6 → ℂ) (b₀ b₁ b₂ : ℂ)
    (p : Equiv.Perm (Fin 6)) :
    let t₀ := b₁ - b₂
    let t₁ := b₂ - b₀
    let t₂ := b₁ - b₀
    let x (i : Fin 6) := t₀ * (a i + b₀)
    let y (i : Fin 6) := t₁ * (a i + b₁)
    (t₀ * t₁ * t₂)^2 * matchingProduct a (pairedSpectrum b₀ b₁ b₂) p =
      ∑ r : Fin 50, (intervalIndicator (targetLabels r)
        (lower.map p.toEmbedding) (upper.map p.toEmbedding) : ℂ) *
        subsetMonomial x y (targetLabels r) := by
  dsimp only
  let x (i : Fin 6) := (b₁ - b₂) * (a i + b₀)
  let y (i : Fin 6) := (b₂ - b₀) * (a i + b₁)
  have hxy (i : Fin 6) : x i + y i = (b₁ - b₀) * (a i + b₂) := by
    dsimp only [x, y]
    ring
  have hfactor :
      ((b₁ - b₂) * (b₂ - b₀) * (b₁ - b₀))^2 *
        matchingProduct a (pairedSpectrum b₀ b₁ b₂) p =
      y (p 0) * y (p 1) * ((x (p 2) + y (p 2)) * (x (p 3) + y (p 3))) * x (p 4) * x (p 5) := by
    rw [hxy, hxy]
    simp [x, y, matchingProduct, pairedSpectrum, Fin.prod_univ_succ] <;> ring
  change _ = ∑ r, (intervalIndicator (targetLabels r)
    (lower.map p.toEmbedding) (upper.map p.toEmbedding) : ℂ) *
      subsetMonomial x y (targetLabels r)
  rw [hfactor]
  simp_rw [mapped_four_markers, Int.cast_add, add_mul, Finset.sum_add_distrib]
  rw [sum_one_marker x y _ (by rw [Finset.card_map]; decide) (by rw [Finset.card_map]; decide),
    sum_one_marker x y _ (by rw [Finset.card_map]; decide) (by rw [Finset.card_map]; decide),
    sum_one_marker x y _ (by rw [Finset.card_map]; decide) (by rw [Finset.card_map]; decide),
    sum_one_marker x y _ (by rw [Finset.card_map]; decide) (by rw [Finset.card_map]; decide)]
  simp only [subsetMonomial_map]
  have hL : lowerᶜ = {2, 3, 4, 5} := by decide
  have hM : middleLeftᶜ = {3, 4, 5} := by decide
  have hN : middleRightᶜ = {2, 4, 5} := by decide
  have hU : upperᶜ = {4, 5} := by decide
  rw [hL, hM, hN, hU]
  simp [lower, middleLeft, middleRight, upper, Finset.prod_insert] <;> ring

/-- A unitary with squared-minor target close to the center has the determinant
hull for the fixed three pairs, with no restriction on the first spectrum. -/
theorem holds_of_target_distance (U : Matrix (Fin 6) (Fin 6) ℂ)
    (hU : IsUnitary U) (hq : ∀ r, |target U r - target center r| ≤ 12 / 23083105288)
    (a : Fin 6 → ℂ) (b₀ b₁ b₂ : ℂ) : Holds a (pairedSpectrum b₀ b₁ b₂) U := by
  by_cases h₀₁ : b₀ = b₁
  · apply holds_of_two_values a _ U hU b₀ b₂
    intro i
    fin_cases i <;> simp [pairedSpectrum, h₀₁]
  by_cases h₀₂ : b₀ = b₂
  · apply holds_of_two_values a _ U hU b₀ b₁
    intro i
    fin_cases i <;> simp [pairedSpectrum, h₀₂]
  by_cases h₁₂ : b₁ = b₂
  · apply holds_of_two_values a _ U hU b₀ b₁
    intro i
    fin_cases i <;> simp [pairedSpectrum, h₁₂]
  obtain ⟨w, hw, hmass, he⟩ := intervalLaw_of_target_distance U hU hq
  let b := pairedSpectrum b₀ b₁ b₂
  let K := ((b₁ - b₂) * (b₂ - b₀) * (b₁ - b₀))^2
  let x (i : Fin 6) := (b₁ - b₂) * (a i + b₀)
  let y (i : Fin 6) := (b₂ - b₀) * (a i + b₁)
  have hK : K ≠ 0 := pow_ne_zero 2 (mul_ne_zero
    (mul_ne_zero (sub_ne_zero.mpr h₁₂) (sub_ne_zero.mpr h₀₂.symm)) (sub_ne_zero.mpr h₀₁.symm))
  have hf (p : Equiv.Perm (Fin 6)) :
      K * matchingProduct a b p = ∑ r, (intervalIndicator (targetLabels r)
        (lower.map p.toEmbedding) (upper.map p.toEmbedding) : ℂ) *
          subsetMonomial x y (targetLabels r) :=
    matching_four_monomials a b₀ b₁ b₂ p
  have hm (s : Fin 90 → ℝ) :
      K * (∑ c, (s c : ℂ) * matchingProduct a b (representative c)) =
      ∑ r, ((incidenceReal *ᵥ s) r : ℂ) * subsetMonomial x y (targetLabels r) := by
    rw [Finset.mul_sum]
    simp_rw [mul_left_comm K, hf, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro r _
    change _ = ((∑ c : Fin 90, (incidence r c : ℝ) * s c : ℝ) : ℂ) * _
    simp only [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_intCast, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro c _
    have h := representative_bounds c
    simp only [incidence, Matrix.of_apply, h.1, h.2, x, y]
    ring
  have hdet :
      K * determinantValue a b U =
        ∑ r, (target U r : ℂ) * subsetMonomial x y (targetLabels r) := by
    rw [← real_signed_determinant a b U hU, Finset.mul_sum]
    simp_rw [mul_left_comm K, hf, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro r _
    rw [target_signed U hU r]
    simp only [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_intCast, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro p _
    dsimp only [x, y]
    ring
  have hweighted : (∑ c, (w c : ℂ) * matchingProduct a b (representative c)) =
      determinantValue a b U :=
    mul_left_cancel₀ hK (by rw [hm w, he, hdet])
  change determinantValue a b U ∈ convexHull ℝ (Set.range (matchingProduct a b))
  refine mem_convexHull_of_exists_fintype w (fun c => matchingProduct a b (representative c)) hw hmass
    (fun c => ⟨representative c, rfl⟩) ?_
  simpa only [Complex.real_smul] using hweighted

/-- The fixed-pair hull at the rational center. -/
theorem holds_at_center (a : Fin 6 → ℂ) (b₀ b₁ b₂ : ℂ) :
    Holds a (pairedSpectrum b₀ b₁ b₂) center := by
  apply holds_of_target_distance center center_unitary
  intro r
  norm_num

private theorem det_norm_le_one_of_columns {k : ℕ} (A : Matrix (Fin k) (Fin k) ℂ)
    (hA : ∀ j, ∑ i, Complex.normSq (A i j) ≤ 1) : ‖A.det‖ ≤ 1 := by
  have hdiag (j : Fin k) : ((Aᴴ * A) j j).re = ∑ i, Complex.normSq (A i j) := by
    rw [Matrix.mul_apply, Complex.re_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Matrix.conjTranspose_apply, Complex.star_def,
      ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re]
  have htrace : (Aᴴ * A).trace.re ≤ Fintype.card (Fin k) := by
    simp only [Matrix.trace, Matrix.diag_apply, Complex.re_sum, hdiag]
    simpa using Finset.sum_le_sum (s := (Finset.univ : Finset (Fin k))) (fun j _ => hA j)
  have h := posSemidef_det_re_le_one_of_trace_le_card (Matrix.posSemidef_conjTranspose_mul_self A) htrace
  rw [Matrix.det_mul, Matrix.det_conjTranspose, Complex.star_def,
    ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re, Complex.normSq_eq_norm_sq] at h
  nlinarith only [norm_nonneg A.det, h]

private theorem det_difference_bound {k : ℕ} (A B : Matrix (Fin k) (Fin k) ℂ)
    (ε : ℝ) (hε : 0 < ε)
    (hA : ∀ j, ∑ i, Complex.normSq (A i j) ≤ 1)
    (hB : ∀ j, ∑ i, Complex.normSq (B i j) ≤ 1)
    (hD : ∀ j, ∑ i, Complex.normSq (A i j - B i j) ≤ ε ^ 2) :
    ‖A.det - B.det‖ ≤ (k : ℝ) * ε := by
  let mix (s : Finset (Fin k)) : Matrix (Fin k) (Fin k) ℂ :=
    Matrix.of fun i j => if j ∈ s then A i j else B i j
  have hmix (s : Finset (Fin k)) :
      ‖(mix s).det - B.det‖ ≤ (s.card : ℝ) * ε := by
    induction s using Finset.induction_on with
    | empty =>
      have h : mix ∅ = B := by ext i j; simp [mix]
      simp [h]
    | @insert j s hj ih =>
      let d (i : Fin k) := A i j - B i j
      let C := (mix s).updateCol j (fun i => (ε : ℂ)⁻¹ * d i)
      have hC (l : Fin k) : ∑ i, Complex.normSq (C i l) ≤ 1 := by
        by_cases hl : l = j
        · subst l
          simp only [C, Matrix.updateCol_apply, if_pos rfl, Complex.normSq_mul,
            Complex.normSq_inv, Complex.normSq_ofReal, ← pow_two, ← Finset.mul_sum]
          change (ε ^ 2)⁻¹ * (∑ i, Complex.normSq (d i)) ≤ 1
          simpa only [inv_mul_cancel₀ (pow_ne_zero 2 hε.ne')] using
            mul_le_mul_of_nonneg_left (hD j) (inv_nonneg.mpr (by positivity : 0 ≤ ε ^ 2))
        · by_cases hs : l ∈ s
          · simpa [C, Matrix.updateCol_apply, hl, Ne.symm hl, mix, hs] using hA l
          · simpa [C, Matrix.updateCol_apply, hl, Ne.symm hl, mix, hs] using hB l
      have hCdet := det_norm_le_one_of_columns C hC
      have hreplace : (mix s).updateCol j (fun i => B i j + d i) = mix (insert j s) := by
        ext i l
        by_cases h : l = j
        · subst l
          simp [mix, Matrix.updateCol_apply, d]
        · simp [mix, Matrix.updateCol_apply, h, Ne.symm h]
      have hself : (mix s).updateCol j (fun i => B i j) = mix s := by
        ext i l
        by_cases h : l = j <;> simp [mix, Matrix.updateCol_apply, hj, h, Ne.symm h]
      have hfactor :
          (mix s).updateCol j d = (mix s).updateCol j ((ε : ℂ) • (fun i => (ε : ℂ)⁻¹ * d i)) := by
        congr 1
        funext i
        have hne : (ε : ℂ) ≠ 0 := by exact_mod_cast hε.ne'
        simp only [Pi.smul_apply, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hne, one_mul]
      have hdiff : (mix (insert j s)).det - (mix s).det = (ε : ℂ) * C.det := by
        rw [← hreplace, Matrix.det_updateCol_add, hself, hfactor, Matrix.det_updateCol_smul]
        abel
      have hstep : ‖(mix (insert j s)).det - (mix s).det‖ ≤ ε := by
        rw [hdiff, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε]
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hCdet hε.le
      rw [Finset.card_insert_of_not_mem hj, Nat.cast_add, Nat.cast_one, add_mul, one_mul]
      have htriangle := dist_triangle ((mix (insert j s)).det) ((mix s).det) B.det
      simp only [dist_eq_norm] at htriangle
      exact htriangle.trans (by linarith only [hstep, ih])
  have h : mix Finset.univ = A := by ext i j; simp [mix]
  simpa only [h, Finset.card_univ, Fintype.card_fin] using hmix Finset.univ

private theorem unitary_column_mass (U : Matrix (Fin 6) (Fin 6) ℂ) (hU : IsUnitary U)
    (j : Fin 6) : ∑ i, Complex.normSq (U i j) = 1 := by
  have h := congrArg (fun M : Matrix (Fin 6) (Fin 6) ℂ => (M j j).re) hU.2
  simpa only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply_eq,
    Complex.re_sum, Complex.star_def, ← Complex.normSq_eq_conj_mul_self,
    Complex.one_re, Complex.ofReal_re] using h

private theorem matrix_column_op_bound (A : Matrix (Fin 6) (Fin 6) ℂ)
    (ε : ℝ) (hε : ‖A‖ ≤ ε) (j : Fin 6) : ∑ i, Complex.normSq (A i j) ≤ ε ^ 2 := by
  let e : EuclideanSpace ℂ (Fin 6) := (EuclideanSpace.equiv (Fin 6) ℂ).symm (Pi.single j 1)
  have he : ‖e‖ = 1 := by
    have h : ‖e‖^2 = 1 := by
      rw [PiLp.norm_sq_eq_of_L2]
      change (∑ i, ‖Pi.single j (1 : ℂ) i‖ ^ 2) = 1
      simp [Pi.single_apply, apply_ite]
    nlinarith only [h, norm_nonneg e]
  have hvec : A *ᵥ e = fun i => A i j := by
    change (A *ᵥ Pi.single j 1) = _
    exact Matrix.mulVec_single_one _ _
  have h := A.l2_opNorm_mulVec e
  rw [he, mul_one] at h
  have hs := pow_le_pow_left₀ (norm_nonneg _) (h.trans hε) 2
  rw [PiLp.norm_sq_eq_of_L2] at hs
  change (∑ i, ‖(A *ᵥ e) i‖ ^ 2) ≤ ε ^ 2 at hs
  simpa only [hvec, ← Complex.normSq_eq_norm_sq] using hs

private theorem restrict_column_mass {k : ℕ} (v : Fin 6 → ℂ)
    (f : Fin k → Fin 6) (hf : Function.Injective f) :
    ∑ i, Complex.normSq (v (f i)) ≤ ∑ j, Complex.normSq (v j) := by
  classical
  rw [← Finset.sum_image (fun i _ j _ he => hf he)]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    (fun i _ _ => Complex.normSq_nonneg _)

private theorem squared_minor_lipschitz (U V : Matrix (Fin 6) (Fin 6) ℂ)
    (hU : IsUnitary U) (hV : IsUnitary V) (I J : Finset (Fin 6)) (hIJ : I.card = J.card)
    (ε : ℝ) (hε : 0 < ε) (hUV : ‖U - V‖ ≤ ε) :
    |subsetMinorSq U I J - subsetMinorSq V I J| ≤ 2 * (I.card : ℝ) * ε := by
  let f : Fin I.card ≃ I := Fintype.equivOfCardEq (by simp)
  let g : Fin I.card ≃ J := Fintype.equivOfCardEq (by simp [hIJ])
  let A := U.submatrix (Subtype.val ∘ f) (Subtype.val ∘ g)
  let B := V.submatrix (Subtype.val ∘ f) (Subtype.val ∘ g)
  have hA (j : Fin I.card) : ∑ i, Complex.normSq (A i j) ≤ 1 :=
    (restrict_column_mass (fun i => U i (g j).val) (Subtype.val ∘ f)
      (Subtype.val_injective.comp f.injective)).trans_eq (unitary_column_mass U hU _)
  have hB (j : Fin I.card) : ∑ i, Complex.normSq (B i j) ≤ 1 :=
    (restrict_column_mass (fun i => V i (g j).val) (Subtype.val ∘ f)
      (Subtype.val_injective.comp f.injective)).trans_eq (unitary_column_mass V hV _)
  have hD (j : Fin I.card) : ∑ i, Complex.normSq (A i j - B i j) ≤ ε ^ 2 :=
    (restrict_column_mass (fun i => (U - V) i (g j).val) (Subtype.val ∘ f)
      (Subtype.val_injective.comp f.injective)).trans (matrix_column_op_bound _ ε hUV _)
  rw [subsetMinorSq_eq_normSq_det_submatrix _ hU I J f g,
    subsetMinorSq_eq_normSq_det_submatrix _ hV I J f g]
  change |Complex.normSq A.det - Complex.normSq B.det| ≤ _
  have hsq : ‖A.det‖^2 - ‖B.det‖^2 = (‖A.det‖ - ‖B.det‖) * (‖A.det‖ + ‖B.det‖) := by ring
  rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq, hsq, abs_mul,
    abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
  have h := (abs_norm_sub_norm_le A.det B.det).trans
    (det_difference_bound A B ε hε hA hB hD)
  have hsum : ‖A.det‖ + ‖B.det‖ ≤ 2 := by
    linarith only [det_norm_le_one_of_columns A hA, det_norm_le_one_of_columns B hB]
  calc
    _ ≤ (I.card : ℝ) * ε * 2 :=
      mul_le_mul h hsum (add_nonneg (norm_nonneg _) (norm_nonneg _)) (by positivity)
    _ = _ := by ring

private theorem targetLabels_card :
    ∀ r : Fin 50, (targetLabels r).card = 2 ∨ (targetLabels r).card = 3 ∨
      (targetLabels r).card = 4 := by decide

private theorem target_of_card_two (U : Matrix (Fin 6) (Fin 6) ℂ) (r : Fin 50)
    (hr : (targetLabels r).card = 2) : target U r = subsetMinorSq U (targetLabels r) lower := by
  have h₁ : (targetLabels r).card ≠ middleLeft.card := by rw [hr]; decide
  have h₂ : (targetLabels r).card ≠ middleRight.card := by rw [hr]; decide
  have h₃ : (targetLabels r).card ≠ upper.card := by rw [hr]; decide
  have hz (J : Finset (Fin 6)) (hne : (targetLabels r).card ≠ J.card) :
      subsetMinorSq U (targetLabels r) J = 0 := by simp only [subsetMinorSq, dif_neg hne]
  simp only [target, minorTarget, hz _ h₁, hz _ h₂, hz _ h₃, add_zero]

private theorem target_of_card_three (U : Matrix (Fin 6) (Fin 6) ℂ) (r : Fin 50)
    (hr : (targetLabels r).card = 3) :
    target U r = subsetMinorSq U (targetLabels r) middleLeft +
      subsetMinorSq U (targetLabels r) middleRight := by
  have h₁ : (targetLabels r).card ≠ lower.card := by rw [hr]; decide
  have h₂ : (targetLabels r).card ≠ upper.card := by rw [hr]; decide
  have hz (J : Finset (Fin 6)) (hne : (targetLabels r).card ≠ J.card) :
      subsetMinorSq U (targetLabels r) J = 0 := by simp only [subsetMinorSq, dif_neg hne]
  simp only [target, minorTarget, hz _ h₁, hz _ h₂, zero_add, add_zero]

private theorem target_of_card_four (U : Matrix (Fin 6) (Fin 6) ℂ) (r : Fin 50)
    (hr : (targetLabels r).card = 4) : target U r = subsetMinorSq U (targetLabels r) upper := by
  have h₁ : (targetLabels r).card ≠ lower.card := by rw [hr]; decide
  have h₂ : (targetLabels r).card ≠ middleLeft.card := by rw [hr]; decide
  have h₃ : (targetLabels r).card ≠ middleRight.card := by rw [hr]; decide
  have hz (J : Finset (Fin 6)) (hne : (targetLabels r).card ≠ J.card) :
      subsetMinorSq U (targetLabels r) J = 0 := by simp only [subsetMinorSq, dif_neg hne]
  simp only [target, minorTarget, hz _ h₁, hz _ h₂, hz _ h₃, zero_add]

/-- Each of the 50 target coordinates changes by at most 12 times a positive
operator-norm upper bound for the change in the mixer. -/
theorem target_lipschitz_bound (U V : Matrix (Fin 6) (Fin 6) ℂ)
    (hU : IsUnitary U) (hV : IsUnitary V)
    (ε : ℝ) (hε : 0 < ε) (hUV : ‖U - V‖ ≤ ε) (r : Fin 50) :
    |target U r - target V r| ≤ 12 * ε := by
  rcases targetLabels_card r with h | h | h
  · rw [target_of_card_two U r h, target_of_card_two V r h]
    have hm := squared_minor_lipschitz U V hU hV (targetLabels r) lower
      (h.trans (by decide : lower.card = 2).symm) ε hε hUV
    rw [h] at hm
    linarith only [hm, hε]
  · rw [target_of_card_three U r h, target_of_card_three V r h]
    have hm := squared_minor_lipschitz U V hU hV (targetLabels r) middleLeft
      (h.trans (by decide : middleLeft.card = 3).symm) ε hε hUV
    have hn := squared_minor_lipschitz U V hU hV (targetLabels r) middleRight
      (h.trans (by decide : middleRight.card = 3).symm) ε hε hUV
    rw [h] at hm hn
    rw [add_sub_add_comm]
    exact (abs_add_le _ _).trans (by linarith only [hm, hn])
  · rw [target_of_card_four U r h, target_of_card_four V r h]
    have hm := squared_minor_lipschitz U V hU hV (targetLabels r) upper
      (h.trans (by decide : upper.card = 4).symm) ε hε hUV
    rw [h] at hm
    linarith only [hm, hε]

/-- All unitary mixers in the indicated closed operator-norm ball satisfy the
determinant hull for every first spectrum and every second spectrum with the
three prescribed pairs of source columns. -/
theorem holds_of_operatorNorm_distance (U : Matrix (Fin 6) (Fin 6) ℂ)
    (hU : IsUnitary U) (hnear : ‖U - center‖ ≤ 1 / 23083105288)
    (a : Fin 6 → ℂ) (b₀ b₁ b₂ : ℂ) : Holds a (pairedSpectrum b₀ b₁ b₂) U := by
  apply holds_of_target_distance U hU _ a b₀ b₁ b₂
  intro r
  have hm := target_lipschitz_bound U center hU center_unitary
    (1 / 23083105288) (by norm_num) hnear r
  rw [← mul_div_assoc, mul_one] at hm
  exact hm

end

end MOC.SixDimensionalMixerBall
