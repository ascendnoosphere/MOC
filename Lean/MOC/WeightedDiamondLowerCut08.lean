import MOC.WeightedDiamondLowerRows
import MOC.WeightedDiamondPackedCut

/-! Add the inequality at permutation 16 to the order-four ray census. -/

namespace MOC.RayCoefficients

namespace LowerCut8

set_option maxRecDepth 32000
set_option maxHeartbeats 60000000

private def positiveIndex : Array ℕ :=
  #[0, 1, 2, 0, 3, 0, 0, 0, 4, 5, 0, 0, 6, 0, 0, 7, 0, 0, 0, 8, 0, 9, 10, 11, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12, 13, 0, 0, 0, 14, 15, 16, 17, 0, 0, 0, 0, 18, 0, 0, 0, 0, 0, 0, 19, 20, 0, 0, 0, 0, 0, 0, 21, 0, 22, 0, 23, 24, 25, 0, 0, 26, 0, 27, 0, 28, 29, 30, 0, 0, 0, 31, 32, 0, 0, 0, 0, 0, 0, 0, 0]

private def negativeIndex : Array ℕ :=
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 13, 0, 0, 0, 14, 0, 0, 15, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 0, 18, 0, 0, 19, 0]

private def edges : Array (Crossing 93 194) :=
  #[.keep 73 [1], .skip 1, .skip 2, .skip 16, .skip 15, .skip 9, .keep 74 [1], .keep 75 [1], .keep 76 [1], .keep 77 [1], .skip 7, .skip 10, .keep 78 [1], .keep 79 [1], .keep 80 [1], .keep 81 [1], .skip 14, .skip 20, .skip 3, .skip 12, .keep 82 [1], .skip 6, .keep 83 [1], .keep 84 [1], .keep 85 [1], .keep 86 [1], .keep 87 [1], .keep 88 [1], .keep 89 [1], .skip 18, .skip 5, .keep 90 [1], .keep 91 [1, 2], .keep 92 [1, 3, 2], .keep 93 [1, 3, 2], .keep 94 [1], .keep 95 [1, 2], .keep 96 [1, 3, 2], .keep 97 [1, 3, 2], .keep 98 [1], .keep 99 [1, 3, 2], .keep 100 [1, 2], .skip 24, .keep 101 [1], .keep 102 [1], .keep 103 [1], .keep 104 [1], .skip 4, .keep 105 [1], .keep 106 [1], .keep 107 [1], .keep 108 [1], .skip 39, .skip 46, .skip 40, .keep 109 [1], .keep 110 [0, 1, 2], .keep 111 [0, 1, 2], .keep 112 [0, 1, 2], .keep 113 [0, 1, 2], .keep 114 [0, 1, 2], .keep 115 [1, 2], .keep 116 [1, 2], .keep 117 [1, 2], .skip 33, .keep 118 [1], .keep 119 [1], .keep 120 [1], .keep 121 [1, 2], .keep 122 [1, 3, 2], .keep 123 [1, 3, 2], .keep 124 [1, 2], .keep 125 [1, 3, 2], .keep 126 [1, 3, 2], .keep 127 [1, 3, 2], .skip 17, .keep 128 [1, 2], .keep 129 [1], .keep 130 [1], .keep 131 [1], .keep 132 [0, 1, 2], .keep 133 [0, 1, 2], .keep 134 [0, 1, 2], .keep 135 [0, 1, 2], .keep 136 [0, 1, 2], .keep 137 [1, 2], .keep 138 [1, 2], .keep 139 [1, 2], .keep 140 [1], .keep 141 [1], .keep 142 [1], .keep 143 [1], .keep 144 [1], .keep 145 [1], .keep 146 [1], .keep 147 [1], .keep 148 [1], .keep 149 [1], .skip 52, .skip 47, .keep 150 [1], .keep 151 [0, 1, 2], .skip 23, .keep 152 [0, 1, 2], .skip 22, .keep 153 [0, 1, 2], .skip 38, .skip 28, .keep 154 [1], .keep 155 [0, 1, 2], .skip 21, .keep 156 [0, 1, 2], .keep 157 [1, 2], .skip 13, .skip 25, .skip 29, .keep 158 [1], .keep 159 [0, 1, 2], .keep 160 [0, 1, 2], .keep 161 [1, 2], .skip 26, .skip 30, .keep 162 [1], .skip 0, .skip 8, .keep 163 [1], .keep 164 [1], .keep 165 [1, 2], .keep 166 [1, 3, 2], .keep 167 [1, 3, 2], .keep 168 [1], .keep 169 [1, 2], .keep 170 [1, 3, 2], .keep 171 [1, 3, 2], .keep 172 [0, 1, 2], .keep 173 [0, 1, 3, 2], .skip 11, .keep 174 [1], .skip 32, .skip 34, .keep 175 [1, 3, 2], .keep 176 [1, 3, 2], .keep 177 [1, 3, 2], .keep 178 [1], .skip 19, .skip 44, .keep 179 [0, 1, 3, 2], .keep 180 [1, 3, 2], .keep 181 [1], .keep 182 [1], .keep 183 [1], .skip 36, .keep 184 [1], .skip 42, .keep 185 [1], .keep 186 [1], .skip 41, .keep 187 [0, 1, 2], .keep 188 [0, 1, 3, 2], .keep 189 [0, 1, 3, 2], .skip 50, .keep 190 [1, 3, 2], .keep 191 [1], .keep 192 [1], .keep 193 [1]]

private def edgeIndex : Array (Array ℕ) :=
  #[
    #[0, 1, 1, 1, 1, 2, 2, 2, 2, 3, 4, 5, 5, 2, 1, 1, 1, 1, 1, 2],
    #[6, 7, 8, 9, 10, 11, 12, 13, 10, 14, 4, 15, 16, 4, 17, 17, 18, 19, 19, 4],
    #[20, 21, 22, 23, 21, 24, 25, 26, 21, 27, 28, 5, 5, 29, 5, 5, 30, 19, 19, 29],
    #[31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 30, 18, 18, 18, 30, 30, 41, 42, 42, 18],
    #[43, 44, 45, 46, 47, 47, 48, 49, 47, 50, 5, 51, 18, 52, 5, 5, 47, 53, 53, 54],
    #[55, 21, 56, 57, 30, 30, 58, 59, 30, 60, 61, 62, 63, 64, 65, 66, 30, 16, 16, 64],
    #[67, 68, 69, 70, 10, 71, 72, 73, 10, 74, 75, 16, 16, 75, 16, 16, 76, 77, 78, 75],
    #[79, 18, 80, 81, 18, 11, 82, 83, 18, 84, 85, 86, 87, 88, 64, 64, 18, 75, 75, 89],
    #[90, 47, 91, 92, 47, 93, 94, 95, 47, 96, 97, 4, 30, 4, 98, 98, 47, 99, 99, 4],
    #[100, 101, 21, 102, 21, 103, 104, 11, 21, 105, 104, 102, 5, 18, 30, 30, 106, 42, 107, 18],
    #[108, 21, 109, 102, 21, 110, 111, 102, 21, 110, 112, 5, 5, 113, 5, 5, 30, 114, 115, 113],
    #[116, 110, 104, 117, 21, 11, 104, 118, 21, 110, 5, 119, 5, 113, 5, 5, 18, 120, 121, 113],
    #[122, 110, 104, 1, 123, 110, 2, 102, 123, 110, 104, 102, 123, 2, 1, 5, 47, 124, 19, 124],
    #[125, 21, 21, 123, 123, 2, 2, 123, 123, 110, 104, 123, 123, 123, 123, 30, 2, 2, 2, 123],
    #[126, 127, 128, 129, 47, 47, 114, 120, 47, 42, 17, 120, 18, 29, 17, 17, 47, 19, 19, 29],
    #[130, 47, 115, 121, 47, 131, 132, 133, 47, 107, 115, 29, 30, 29, 17, 17, 47, 19, 19, 29],
    #[107, 47, 47, 47, 47, 134, 135, 136, 47, 30, 30, 30, 30, 18, 30, 30, 47, 47, 19, 18],
    #[137, 138, 17, 139, 18, 138, 64, 29, 18, 140, 141, 142, 3, 29, 17, 17, 47, 19, 19, 29],
    #[104, 123, 1, 1, 123, 123, 2, 2, 123, 123, 5, 5, 123, 2, 1, 1, 123, 1, 1, 2],
    #[143, 47, 144, 1, 1, 19, 144, 1, 1, 145, 144, 1, 1, 1, 1, 144, 47, 19, 19, 1],
    #[104, 30, 52, 5, 18, 30, 146, 5, 18, 30, 147, 5, 30, 4, 5, 5, 30, 5, 5, 5],
    #[148, 124, 124, 124, 47, 144, 144, 144, 47, 110, 5, 4, 5, 124, 5, 5, 47, 124, 144, 124],
    #[149, 1, 123, 1, 123, 11, 123, 11, 123, 110, 123, 102, 123, 123, 123, 123, 1, 1, 1, 18],
    #[150, 19, 2, 124, 2, 47, 2, 124, 2, 106, 2, 124, 2, 2, 2, 2, 47, 124, 124, 124],
    #[151, 47, 2, 1, 123, 47, 2, 1, 123, 47, 2, 1, 1, 1, 1, 2, 47, 124, 124, 1],
    #[152, 19, 2, 124, 2, 153, 2, 29, 2, 145, 2, 29, 2, 2, 2, 2, 47, 124, 19, 124],
    #[154, 47, 47, 1, 1, 153, 30, 11, 47, 145, 30, 11, 30, 18, 1, 30, 47, 47, 19, 18],
    #[155, 156, 21, 18, 18, 47, 2, 18, 2, 145, 21, 18, 18, 2, 18, 47, 47, 124, 47, 18],
    #[42, 157, 10, 158, 47, 47, 47, 47, 47, 18, 18, 18, 18, 18, 47, 47, 18, 19, 47, 18],
    #[102, 18, 5, 159, 18, 18, 5, 160, 18, 18, 5, 161, 18, 5, 5, 5, 18, 16, 16, 4],
    #[162, 124, 124, 124, 47, 110, 5, 102, 47, 110, 5, 102, 5, 124, 5, 5, 47, 124, 113, 124],
    #[163, 156, 17, 1, 1, 19, 19, 1, 1, 145, 17, 1, 1, 1, 1, 113, 47, 19, 19, 1],
    #[164, 110, 104, 124, 18, 113, 113, 113, 18, 110, 104, 113, 5, 113, 5, 5, 47, 124, 113, 124]]

private def maskTable : Array ℕ :=
  #[3165217, 3120, 1066240, 2132480, 2662400, 3932160, 3194883, 3181586, 61440, 1331200, 2623585, 3673408, 1300, 195, 266260, 2600, 3411584, 780, 4032, 532520, 1311890, 2113573, 1065003, 22625, 2129943, 1081370, 38994, 3704915, 2621765, 1573194, 530752, 3705155, 2359941, 1311370, 268992, 3414668, 25761, 3425443, 2147077, 1098506, 41610, 42130, 533952, 3679564, 272000, 3425923, 20805, 536908, 275084, 1080361, 56128, 1084362, 1835066, 792688, 798912, 1841362, 795824, 1852202, 1839322, 1104195, 1102155, 1084882, 1575035, 1576402, 28717, 63, 2117345, 2115525, 59264, 583088, 26565, 2883637, 2917141, 2893025, 2892005, 2156163, 2155143, 2145302, 318064, 291045, 291525, 2363105, 2360503, 271543, 25263, 45086, 37215, 569562, 528735, 569802, 271023, 39882, 530555]

private def kept : Array (Fin 194) :=
  #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 0, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 0, 38, 39, 40, 0, 41, 42, 0, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 0, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 0, 69, 0, 70, 71, 0, 72]

private def origin : Array (RayOrigin 93) :=
  #[.kept 0, .kept 1, .kept 2, .kept 3, .kept 4, .kept 5, .kept 6, .kept 7, .kept 8, .kept 9, .kept 10, .kept 11, .kept 12, .kept 14, .kept 15, .kept 16, .kept 17, .kept 18, .kept 19, .kept 20, .kept 21, .kept 22, .kept 23, .kept 36, .kept 37, .kept 38, .kept 39, .kept 40, .kept 41, .kept 42, .kept 43, .kept 44, .kept 45, .kept 46, .kept 47, .kept 48, .kept 49, .kept 50, .kept 52, .kept 53, .kept 54, .kept 56, .kept 57, .kept 59, .kept 60, .kept 61, .kept 62, .kept 63, .kept 64, .kept 65, .kept 66, .kept 67, .kept 68, .kept 69, .kept 70, .kept 71, .kept 73, .kept 74, .kept 75, .kept 76, .kept 77, .kept 78, .kept 79, .kept 80, .kept 81, .kept 82, .kept 83, .kept 84, .kept 85, .kept 87, .kept 89, .kept 90, .kept 92, .crossing 0 13, .crossing 1 13, .crossing 1 24, .crossing 1 25, .crossing 1 26, .crossing 1 29, .crossing 1 30, .crossing 1 32, .crossing 1 34, .crossing 2 13, .crossing 2 25, .crossing 2 26, .crossing 2 28, .crossing 2 29, .crossing 2 30, .crossing 2 32, .crossing 2 33, .crossing 4 13, .crossing 4 24, .crossing 4 25, .crossing 4 26, .crossing 4 27, .crossing 4 28, .crossing 4 29, .crossing 4 30, .crossing 4 31, .crossing 4 32, .crossing 4 72, .crossing 8 13, .crossing 8 24, .crossing 8 25, .crossing 8 26, .crossing 8 29, .crossing 8 30, .crossing 8 32, .crossing 8 34, .crossing 9 13, .crossing 9 25, .crossing 9 26, .crossing 9 29, .crossing 9 30, .crossing 9 32, .crossing 9 33, .crossing 9 34, .crossing 9 35, .crossing 9 55, .crossing 9 58, .crossing 12 13, .crossing 12 24, .crossing 12 25, .crossing 12 26, .crossing 12 28, .crossing 12 29, .crossing 12 30, .crossing 12 32, .crossing 12 72, .crossing 12 86, .crossing 12 88, .crossing 15 13, .crossing 15 25, .crossing 15 26, .crossing 15 29, .crossing 15 30, .crossing 15 32, .crossing 15 33, .crossing 15 34, .crossing 15 35, .crossing 15 51, .crossing 15 91, .crossing 19 13, .crossing 19 25, .crossing 19 26, .crossing 19 28, .crossing 19 29, .crossing 19 30, .crossing 19 32, .crossing 19 33, .crossing 21 13, .crossing 21 24, .crossing 21 28, .crossing 21 32, .crossing 22 13, .crossing 22 25, .crossing 22 29, .crossing 22 33, .crossing 23 13, .crossing 23 26, .crossing 23 30, .crossing 23 34, .crossing 36 13, .crossing 37 13, .crossing 41 13, .crossing 41 24, .crossing 41 25, .crossing 41 26, .crossing 42 13, .crossing 42 28, .crossing 42 29, .crossing 42 30, .crossing 43 28, .crossing 43 29, .crossing 44 13, .crossing 44 32, .crossing 44 33, .crossing 44 34, .crossing 56 13, .crossing 57 29, .crossing 57 33, .crossing 64 13, .crossing 66 13, .crossing 68 13, .crossing 70 13, .crossing 73 13, .crossing 75 13, .crossing 77 24, .crossing 77 26, .crossing 78 26, .crossing 78 34, .crossing 79 13, .crossing 83 13, .crossing 84 13]

private def mask (p : Fin 93) : ℕ := maskTable.getD p.val 0

def plan : RayCutPlan 93 194 where
  kept p := kept.getD p.val 0
  crossing p k := edges.getD ((edgeIndex.getD (positiveIndex.getD p.val 0) #[]).getD
    (negativeIndex.getD k.val 0) 0) (.skip p)
  origin l := origin.getD l.val (.kept 0)

private abbrev old := lowerStage8.rays
private abbrev nextRows := lowerStage9.rays
private abbrev imposed := lowerStage8.imposed

private theorem oldSigns : ∀ p i, i ∈ imposed → zero (old p i) = true ∨ positive (old p i) = true := by
  apply checkRayBlocks
  intro k
  fin_cases k <;> decide +kernel

private theorem mask_eq : ∀ p i, (mask p).testBit i.val =
    (decide (i ∈ imposed) && positive (old p i)) := by
  apply checkRayBlocks
  intro k
  fin_cases k <;> decide +kernel

private theorem separate : ∀ p k, p ≠ k → let i := separationIndex mask p k
    (mask p).testBit i.val = true ∧ (mask k).testBit i.val = false := by
  apply checkRayBlocks
  intro k
  fin_cases k <;> decide +kernel

private theorem crossing : ∀ p k, positive (old p 16) = true → negative (old k 16) = true →
    maskCrossing old nextRows imposed 16 mask p k (plan.crossing p k) := by
  apply checkRayBlocks
  intro k
  fin_cases k <;> decide +kernel

theorem valid : plan.Valid old nextRows imposed 16 := by
  obtain ⟨sep, cross⟩ := validateRayMasks plan mask oldSigns mask_eq separate crossing
  refine ⟨oldSigns, ?_, ?_, ?_, sep, ?_, cross, ?_⟩ <;> apply checkRayBlocks <;>
    intro k <;> fin_cases k <;> decide +kernel

end LowerCut8

end MOC.RayCoefficients
