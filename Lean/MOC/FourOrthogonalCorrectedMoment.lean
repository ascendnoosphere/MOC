import MOC.FourCliffordColumnAlignment
import MOC.FourCliffordMinorCoefficients
import MOC.FourCorrectedIndicatorMoment

/-! The unconditional corrected subset-image moment for an orthogonal matrix of order four. -/

open Matrix BigOperators
open scoped symmDiff

namespace MOC

open FourCliffordFrame

private abbrev FourReal := Matrix (Fin 4) (Fin 4) ℝ

private def alignmentWitness : Fin 14 → Fin 14 → Fin 24 :=
 ![  ![0, 0, 6, 12, 6, 0, 2, 8, 2, 0, 0, 2, 2, 0],
  ![0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 2, 2, 0],
  ![6, 0, 6, 0, 6, 0, 8, 8, 0, 6, 6, 0, 8, 0],
  ![12, 0, 0, 12, 12, 14, 0, 14, 12, 0, 0, 12, 0, 14],
  ![6, 0, 6, 12, 6, 0, 0, 0, 12, 6, 6, 12, 0, 0],
  ![0, 0, 0, 14, 0, 0, 0, 14, 0, 0, 0, 0, 0, 0],
  ![2, 2, 8, 0, 0, 0, 2, 8, 2, 0, 0, 2, 2, 0],
  ![8, 0, 8, 14, 0, 14, 8, 8, 0, 0, 0, 0, 8, 14],
  ![2, 2, 0, 12, 12, 0, 2, 0, 2, 0, 0, 2, 2, 0],
  ![0, 0, 6, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 6, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![2, 2, 0, 12, 12, 0, 2, 0, 2, 0, 0, 2, 2, 0],
  ![2, 2, 8, 0, 0, 0, 2, 8, 2, 0, 0, 2, 2, 0],
  ![0, 0, 0, 14, 0, 0, 0, 14, 0, 0, 0, 0, 0, 0]]

private theorem alignmentWitness_correct : ∀ i j : Fin 14,
    smallMaskCard (xorSmall (fourIndicatorBasisSmallMasks i).1 (fourIndicatorBasisSmallMasks j).1) =
      smallMaskCard (xorSmall (fourIndicatorBasisSmallMasks j).2 (fourIndicatorBasisSmallMasks i).2) →
      FourIndicatorCompatible (fourPerm (alignmentWitness i j)) i j := by
  decide +kernel

private theorem smallColumnSet_eq_mask : ∀ a : Fin 8,
    smallColumnSet a = fourIndicatorMask (smallMask a) := by decide +kernel

private theorem subset_xor : ∀ a b,
    fourIndicatorMask (smallMask (xorSmall a b)) =
      fourIndicatorMask (smallMask a) ∆ fourIndicatorMask (smallMask b) := by decide +kernel

private noncomputable def frameMinor (O : FourReal) (r s : Fin 8) : ℝ :=
  bladeCoefficient (smallMask r) (smallFrame O s)

private theorem mask_explicit : ∀ a : Fin 8, fourIndicatorMask (smallMask a) =
    (![∅,{0},{1},{0,1},{2},{0,2},{1,2},{0,1,2}] : Fin 8 → Finset (Fin 4)) a := by
  decide +kernel

private theorem frameMinor_principal (O : FourReal) (a : Fin 8) :
    frameMinor O a a = principalRowDet O (fourIndicatorMask (smallMask a)) := by
  rw [mask_explicit]
  fin_cases a
  · change bladeCoefficient 0 (1 : Matrix (Fin 16) (Fin 16) ℝ) = principalRowDet O ∅
    simp [bladeCoefficient_one, principalRowDet_empty]
  · change bladeCoefficient 1 (generator O 0) = principalRowDet O {0}
    rw [bladeCoefficient_generator, principalRowDet_singleton]
    simp (disch := decide) [Fin.sum_univ_four, Matrix.cons_val, columnGeneratorMask_eq]
  · change bladeCoefficient 2 (generator O 1) = principalRowDet O {1}
    rw [bladeCoefficient_generator, principalRowDet_singleton]
    simp (disch := decide) [Fin.sum_univ_four, Matrix.cons_val, columnGeneratorMask_eq]
  · change bladeCoefficient 3 (generator O 0 * generator O 1) = principalRowDet O {0,1}
    rw [bladeCoefficient_generator_mul, principalRowDet_pair O 0 1 (by decide)]
    change twoMinor O 0 1 0 1 = principalPair O 0 1
    unfold twoMinor principalPair secondMinor
    ring
  · change bladeCoefficient 4 (generator O 2) = principalRowDet O {2}
    rw [bladeCoefficient_generator, principalRowDet_singleton]
    simp (disch := decide) [Fin.sum_univ_four, Matrix.cons_val, columnGeneratorMask_eq]
  · change bladeCoefficient 5 (generator O 0 * generator O 2) = principalRowDet O {0,2}
    rw [bladeCoefficient_generator_mul, principalRowDet_pair O 0 2 (by decide)]
    change twoMinor O 0 2 0 2 = principalPair O 0 2
    unfold twoMinor principalPair secondMinor
    ring
  · change bladeCoefficient 6 (generator O 1 * generator O 2) = principalRowDet O {1,2}
    rw [bladeCoefficient_generator_mul, principalRowDet_pair O 1 2 (by decide)]
    change twoMinor O 1 2 1 2 = principalPair O 1 2
    unfold twoMinor principalPair secondMinor
    ring
  · change bladeCoefficient 7 (generator O 0 * generator O 1 * generator O 2) =
      principalRowDet O {0,1,2}
    rw [bladeCoefficient_generator_mul_mul, principalRowDet_three]
    change threeMinor O 0 1 2 0 1 2 = _
    unfold threeMinor twoMinor secondMinor
    ring

private noncomputable def indicatorBlade (O : FourReal) (i : Fin 14) : Matrix (Fin 16) (Fin 16) ℝ :=
  let r := (fourIndicatorBasisSmallMasks i).1
  let s := (fourIndicatorBasisSmallMasks i).2
  frameMinor O r s • ((blade (smallMask r))ᵀ * smallFrame O s)

private theorem indicatorBlade_trace (O : FourReal) (hO : Oᵀ * O = 1) (i j : Fin 14) :
    let a := (fourIndicatorBasisSmallMasks i).1
    let b := (fourIndicatorBasisSmallMasks i).2
    let c := (fourIndicatorBasisSmallMasks j).1
    let d := (fourIndicatorBasisSmallMasks j).2
    (((indicatorBlade O i)ᵀ * indicatorBlade O j).trace / 16) =
      (traceColumnSign a b c d : ℝ) * frameMinor O a b * frameMinor O c d *
        frameMinor O (xorSmall a c) (xorSmall d b) := by
  intro a b c d
  calc
    _ = frameMinor O a b * frameMinor O c d *
        (((((blade (smallMask a))ᵀ * smallFrame O b)ᵀ *
            ((blade (smallMask c))ᵀ * smallFrame O d))).trace / 16) := by
        simp only [indicatorBlade, Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul,
          Matrix.trace_smul, smul_eq_mul]
        dsimp only [a, b, c, d]
        ring
    _ = _ := by
        rw [trace_mixed_smallFrame O hO]
        unfold traceColumnSign frameMinor
        ring

private theorem indicatorBlade_zero (O : FourReal) (hO : Oᵀ * O = 1) (i j : Fin 14)
    (h : ¬∃ σ : FourPerm, FourIndicatorCompatible σ i j) :
    ((indicatorBlade O i)ᵀ * indicatorBlade O j).trace / 16 = 0 := by
  have hne : smallMaskCard (xorSmall (fourIndicatorBasisSmallMasks i).1
      (fourIndicatorBasisSmallMasks j).1) ≠ smallMaskCard (xorSmall
      (fourIndicatorBasisSmallMasks j).2 (fourIndicatorBasisSmallMasks i).2) :=
    fun hp => h ⟨_, alignmentWitness_correct i j hp⟩
  rw [indicatorBlade_trace O hO, show frameMinor O (xorSmall (fourIndicatorBasisSmallMasks i).1
      (fourIndicatorBasisSmallMasks j).1) (xorSmall (fourIndicatorBasisSmallMasks j).2
      (fourIndicatorBasisSmallMasks i).2) = 0 from smallFrame_coefficient_eq_zero_of_card_ne O hO _ _ hne,
    mul_zero]

private theorem indicatorBlade_aligned (O : FourReal) (hO : Oᵀ * O = 1)
    (i j : Fin 14) (σ : FourPerm) (h : FourIndicatorCompatible σ i j) :
    ((indicatorBlade O i)ᵀ * indicatorBlade O j).trace / 16 =
      fourPrincipalGram (O.submatrix id σ) (fourIndicatorRowSet i) (fourIndicatorRowSet j) := by
  let a := (fourIndicatorBasisSmallMasks i).1
  let b := (fourIndicatorBasisSmallMasks i).2
  let c := (fourIndicatorBasisSmallMasks j).1
  let d := (fourIndicatorBasisSmallMasks j).2
  have hab : (smallColumnSet a).map σ.toEmbedding = smallColumnSet b := by
    rw [smallColumnSet_eq_mask, smallColumnSet_eq_mask]
    exact h.1
  have hcd : (smallColumnSet c).map σ.toEmbedding = smallColumnSet d := by
    rw [smallColumnSet_eq_mask, smallColumnSet_eq_mask]
    exact h.2
  let A := O.submatrix id σ
  rw [indicatorBlade_trace O hO]
  change (traceColumnSign a b c d : ℝ) * frameMinor O a b * frameMinor O c d *
      frameMinor O (xorSmall a c) (xorSmall d b) = _
  calc
    _ = frameMinor A a a * frameMinor A c c * frameMinor A (xorSmall a c) (xorSmall a c) :=
      (compatible_column_alignment O hO σ a b c d hab hcd).symm
    _ = _ := by
      rw [frameMinor_principal, frameMinor_principal, frameMinor_principal, subset_xor] <;> rfl

/-- Every order-four real orthogonal matrix has a positive corrected moment
on the fourteen subset-image indicator columns. -/
theorem fourCorrectedIndicatorMoment_posSemidef (O : FourReal) (hO : Oᵀ * O = 1) :
    (fourIndicatorBasisᵀ * Matrix.diagonal (fun p => fourCorrectedIndicatorWeight O (fourPerm p)) *
      fourIndicatorBasis).PosSemidef :=
  correctedIndicatorMoment_posSemidef_of_trace_gram O (Matrix.mul_eq_one_comm.mp hO)
    (indicatorBlade O) (indicatorBlade_aligned O hO) (indicatorBlade_zero O hO)

end MOC
