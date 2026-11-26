import MOC.FourMatchingRelations

/-! Fourteen subset-image indicators generate the order-four matching functions. -/

open Matrix BigOperators

namespace MOC

/-- The masks for the constant, nine singleton and four pair indicators. -/
def fourIndicatorBasisSmallMasks : Fin 14 → Fin 8 × Fin 8 :=
  ![(0,0), (1,1), (1,2), (1,4), (2,1), (2,2), (2,4), (4,1), (4,2), (4,4),
    (3,3), (3,5), (5,3), (5,5)]

def fourIndicatorBasisMasks (j : Fin 14) : Fin 16 × Fin 16 :=
  ((fourIndicatorBasisSmallMasks j).1.castLE (by decide),
    (fourIndicatorBasisSmallMasks j).2.castLE (by decide))

def fourIndicatorMask (m : Fin 16) : Finset (Fin 4) :=
  Finset.univ.filter fun i => m.val.testBit i.val

def fourIndicatorInt (k : Fin 14) (p : Fin 24) : ℤ :=
  if (fourIndicatorMask (fourIndicatorBasisMasks k).1).map (fourPerm p).toEmbedding =
      fourIndicatorMask (fourIndicatorBasisMasks k).2 then 1 else 0

def fourIndicatorCoefficient : Fin 14 → Fin 14 → ℤ :=
  ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0],
    ![0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0],
    ![-1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0],
    ![-2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0],
    ![0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![-1, 1, 1, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0],
    ![0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0],
    ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]

set_option maxRecDepth 12000 in
set_option maxHeartbeats 12000000 in
theorem fourIndicatorCoefficient_identity : ∀ k : Fin 14, ∀ p : Fin 24,
    (∑ j : Fin 14, fourIndicatorInt j p * fourIndicatorCoefficient k j) =
      fourMatchingEvaluation (Pi.single k (1 : ℤ)) p := by
  decide +kernel

/-- The fourteen matching indicator columns written as a real matrix. -/
noncomputable def fourIndicatorBasis : Matrix (Fin 24) (Fin 14) ℝ :=
  fun p k => fourIndicatorInt k p

end MOC
