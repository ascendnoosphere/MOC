import MOC.FourMatchingRelations
import MOC.FourMinorCertificate
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

/-! Squared-minor certificates for the supporting faces of cases T18, T19 and T20. -/

namespace MOC

open BigOperators

noncomputable section

private def rectangleMinorRows : Fin 13 → Finset (Fin 4) :=
  ![{0}, {0, 1}, {0, 2}, {0, 3}, {0}, {0, 1}, {3}, {0, 1}, {1}, {3}, {0, 3}, {2}, {0, 1}]

private def rectangleMinorColumns : Fin 13 → Finset (Fin 4) :=
  ![{3}, {2, 3}, {2, 3}, {2, 3}, {2}, {1, 3}, {0}, {0, 3}, {3}, {1}, {0, 1}, {1}, {0, 2}]

private def rectangleMinorSupport : Fin 13 → Finset ℕ :=
  ![{18, 19, 20, 21, 22, 23}, {16, 17, 22, 23}, {13, 15, 19, 21}, {12, 14, 18, 20}, {12, 13, 14, 15, 16, 17}, {10, 11, 20, 21}, {9, 11, 15, 17, 21, 23}, {4, 5, 18, 19}, {4, 5, 10, 11, 16, 17}, {3, 5, 13, 16, 19, 22}, {3, 5, 9, 11}, {2, 4, 12, 17, 18, 23}, {2, 3, 12, 13}]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem rectangleMinorSupport_spec (j : Fin 13) (i : Fin 24) :
    i.val ∈ rectangleMinorSupport j ↔
      (rectangleMinorColumns j).map (fourPerm i).symm.toEmbedding = rectangleMinorRows j := by
  fin_cases j <;> fin_cases i <;> decide

/-- The six prescribed contacts of case T18. -/
def fourT18ContactIndices : Finset (Fin 24) := {0, 1, 3, 6, 7, 8}

private def t18GapProfile (g : Fin 24 → ℝ) : Fin 24 → ℝ :=
  ![0,
    0,
    g 2,
    0,
    g 4,
    -g 2 + g 4,
    0,
    0,
    0,
    g 9,
    g 10,
    g 10 + g 9,
    g 12,
    g 13,
    g 12 - g 2,
    g 13 + g 9,
    g 16,
    g 16 + g 2 + g 9,
    g 18,
    -g 12 + g 13 + g 18,
    g 10 + g 18 - g 4,
    g 10 - g 12 + g 13 + g 18 + g 2 - g 4 + g 9,
    -g 12 + g 16 + g 18 + g 2 - g 4,
    -g 12 + g 16 + g 18 + 2 * g 2 - g 4 + g 9]

private def t18MinorWeights (g : Fin 24 → ℝ) (x y : ℝ) : Fin 13 → ℝ :=
  ![-g 12 + g 18 + g 2 - g 4 + x + y,
    g 16 - x - y,
    g 13 - x,
    g 12 - g 2 - x,
    x,
    g 10 - y,
    g 9,
    -g 2 + g 4 - y,
    y,
    0,
    0,
    g 2,
    0]

set_option maxHeartbeats 3000000 in
private theorem t18_gapProfile_of_contacts (m : Fin 14 → ℝ) (H : ℝ)
    (h0 : fourMatchingEvaluation m 0 = H) (h1 : fourMatchingEvaluation m 1 = H) (h3 : fourMatchingEvaluation m 3 = H)
    (h6 : fourMatchingEvaluation m 6 = H) (h7 : fourMatchingEvaluation m 7 = H) (h8 : fourMatchingEvaluation m 8 = H)
    (i : Fin 24) :
    let g (j : Fin 24) := fourMatchingEvaluation m j - H
    g i = t18GapProfile g i := by
  let g (j : Fin 24) := fourMatchingEvaluation m j - H
  change g i = t18GapProfile g i
  dsimp only [fourMatchingEvaluation, Matrix.cons_val] at h0 h1 h3 h6 h7 h8
  fin_cases i
  · change g 0 = 0
    dsimp only [g, fourMatchingEvaluation, Matrix.cons_val] <;> linear_combination h0
  · change g 1 = 0
    dsimp only [g, fourMatchingEvaluation, Matrix.cons_val] <;> linear_combination h1
  · change g 2 = g 2
    dsimp only [g, fourMatchingEvaluation, Matrix.cons_val] <;> ring
  · change g 3 = 0
    dsimp only [g, fourMatchingEvaluation, Matrix.cons_val] <;> linear_combination h3
  · change g 4 = g 4
    dsimp only [g, fourMatchingEvaluation, Matrix.cons_val] <;> ring
  · change g 5 = -g 2 + g 4
    dsimp only [g, fourMatchingEvaluation, Matrix.cons_val] <;> linear_combination h0 - h1 + h3
  · change g 6 = 0
    dsimp only [g, fourMatchingEvaluation, Matrix.cons_val] <;> linear_combination h6
  · change g 7 = 0
    dsimp only [g, fourMatchingEvaluation, Matrix.cons_val] <;> linear_combination h7
  · change g 8 = 0
    dsimp only [g, fourMatchingEvaluation, Matrix.cons_val] <;> linear_combination h8
  · change g 9 = g 9
    dsimp only [g, fourMatchingEvaluation, Matrix.cons_val] <;> ring
  · change g 10 = g 10
    dsimp only [g, fourMatchingEvaluation, Matrix.cons_val] <;> ring
  · change g 11 = g 10 + g 9
    dsimp only [g, fourMatchingEvaluation, Matrix.cons_val] <;> linear_combination h6 - h7 - h8
  · change g 12 = g 12
    dsimp only [g, fourMatchingEvaluation, Matrix.cons_val] <;> ring
  · change g 13 = g 13
    dsimp only [g, fourMatchingEvaluation, Matrix.cons_val] <;> ring
  · change g 14 = g 12 - g 2
    dsimp only [g, fourMatchingEvaluation, Matrix.cons_val] <;> linear_combination h0 - h6 + h8
  · change g 15 = g 13 + g 9
    dsimp only [g, fourMatchingEvaluation, Matrix.cons_val] <;> linear_combination h1 - h3 - h7
  · change g 16 = g 16
    dsimp only [g, fourMatchingEvaluation, Matrix.cons_val] <;> ring
  · change g 17 = g 16 + g 2 + g 9
    dsimp only [g, fourMatchingEvaluation, Matrix.cons_val] <;> linear_combination -h0 + h1 - h3 + h6 - h7 - h8
  · change g 18 = g 18
    dsimp only [g, fourMatchingEvaluation, Matrix.cons_val] <;> ring
  · change g 19 = -g 12 + g 13 + g 18
    dsimp only [g, fourMatchingEvaluation, Matrix.cons_val] <;> linear_combination h6 - h7
  · change g 20 = g 10 + g 18 - g 4
    dsimp only [g, fourMatchingEvaluation, Matrix.cons_val] <;> linear_combination h1 - h7
  · change g 21 = g 10 - g 12 + g 13 + g 18 + g 2 - g 4 + g 9
    dsimp only [g, fourMatchingEvaluation, Matrix.cons_val] <;> linear_combination h1 - h3 + h6 - 2 * h7 - h8
  · change g 22 = -g 12 + g 16 + g 18 + g 2 - g 4
    dsimp only [g, fourMatchingEvaluation, Matrix.cons_val] <;> linear_combination -h0 + h1 + h6 - h7
  · change g 23 = -g 12 + g 16 + g 18 + 2 * g 2 - g 4 + g 9
    dsimp only [g, fourMatchingEvaluation, Matrix.cons_val] <;> linear_combination -h0 + h1 - h3 + h6 - h7 - h8

set_option maxHeartbeats 3000000 in
private theorem t18_gapProfile_eq_minorSum (g : Fin 24 → ℝ) (x y : ℝ) (i : Fin 24) :
    t18GapProfile g i = ∑ j : Fin 13, if i.val ∈ rectangleMinorSupport j then
      t18MinorWeights g x y j else 0 := by
  let rhs (i : ℕ) := ∑ j : Fin 13, if i ∈ rectangleMinorSupport j then t18MinorWeights g x y j else 0
  change t18GapProfile g i = rhs i.val
  fin_cases i
  case' «0» => change 0 = rhs 0
  case' «1» => change 0 = rhs 1
  case' «2» => change g 2 = rhs 2
  case' «3» => change 0 = rhs 3
  case' «4» => change g 4 = rhs 4
  case' «5» => change -g 2 + g 4 = rhs 5
  case' «6» => change 0 = rhs 6
  case' «7» => change 0 = rhs 7
  case' «8» => change 0 = rhs 8
  case' «9» => change g 9 = rhs 9
  case' «10» => change g 10 = rhs 10
  case' «11» => change g 10 + g 9 = rhs 11
  case' «12» => change g 12 = rhs 12
  case' «13» => change g 13 = rhs 13
  case' «14» => change g 12 - g 2 = rhs 14
  case' «15» => change g 13 + g 9 = rhs 15
  case' «16» => change g 16 = rhs 16
  case' «17» => change g 16 + g 2 + g 9 = rhs 17
  case' «18» => change g 18 = rhs 18
  case' «19» => change -g 12 + g 13 + g 18 = rhs 19
  case' «20» => change g 10 + g 18 - g 4 = rhs 20
  case' «21» => change g 10 - g 12 + g 13 + g 18 + g 2 - g 4 + g 9 = rhs 21
  case' «22» => change -g 12 + g 16 + g 18 + g 2 - g 4 = rhs 22
  case' «23» => change -g 12 + g 16 + g 18 + 2 * g 2 - g 4 + g 9 = rhs 23
  all_goals
    norm_num [rhs, Fin.sum_univ_succ, rectangleMinorSupport, t18MinorWeights, Matrix.cons_val] <;> ring

/-- The six prescribed contacts of case T19. -/
def fourT19ContactIndices : Finset (Fin 24) := {0, 1, 4, 6, 7, 8}

private def t19GapProfile (g : Fin 24 → ℝ) : Fin 24 → ℝ :=
  ![0,
    0,
    g 2,
    g 3,
    0,
    -g 2 + g 3,
    0,
    0,
    0,
    g 9,
    g 10,
    g 10 + g 9,
    g 12,
    g 13,
    g 12 - g 2,
    g 13 - g 3 + g 9,
    g 16,
    g 16 + g 2 - g 3 + g 9,
    g 18,
    -g 12 + g 13 + g 18,
    g 10 + g 18,
    g 10 - g 12 + g 13 + g 18 + g 2 - g 3 + g 9,
    -g 12 + g 16 + g 18 + g 2,
    -g 12 + g 16 + g 18 + 2 * g 2 - g 3 + g 9]

private def t19MinorWeights (g : Fin 24 → ℝ) (x y : ℝ) : Fin 13 → ℝ :=
  ![-g 12 + g 18 + g 2 + x,
    g 16 + g 2 - g 3 - x + y,
    g 13 - g 3 - x + y,
    g 12 - g 2 - x,
    x,
    g 10,
    g 9 - y,
    0,
    0,
    -g 2 + g 3 - y,
    y,
    0,
    g 2]

set_option maxHeartbeats 3000000 in
private theorem t19_gapProfile_of_contacts (m : Fin 14 → ℝ) (H : ℝ)
    (h0 : fourMatchingEvaluation m 0 = H) (h1 : fourMatchingEvaluation m 1 = H) (h4 : fourMatchingEvaluation m 4 = H)
    (h6 : fourMatchingEvaluation m 6 = H) (h7 : fourMatchingEvaluation m 7 = H) (h8 : fourMatchingEvaluation m 8 = H)
    (i : Fin 24) :
    let g (j : Fin 24) := fourMatchingEvaluation m j - H
    g i = t19GapProfile g i := by
  let g (j : Fin 24) := fourMatchingEvaluation m j - H
  change g i = t19GapProfile g i
  dsimp only [fourMatchingEvaluation, Matrix.cons_val] at h0 h1 h4 h6 h7 h8
  fin_cases i
  · change g 0 = 0
    dsimp only [g, fourMatchingEvaluation, Matrix.cons_val] <;> linear_combination h0
  · change g 1 = 0
    dsimp only [g, fourMatchingEvaluation, Matrix.cons_val] <;> linear_combination h1
  · change g 2 = g 2
    dsimp only [g, fourMatchingEvaluation, Matrix.cons_val] <;> ring
  · change g 3 = g 3
    dsimp only [g, fourMatchingEvaluation, Matrix.cons_val] <;> ring
  · change g 4 = 0
    dsimp only [g, fourMatchingEvaluation, Matrix.cons_val] <;> linear_combination h4
  · change g 5 = -g 2 + g 3
    dsimp only [g, fourMatchingEvaluation, Matrix.cons_val] <;> linear_combination h0 - h1 + h4
  · change g 6 = 0
    dsimp only [g, fourMatchingEvaluation, Matrix.cons_val] <;> linear_combination h6
  · change g 7 = 0
    dsimp only [g, fourMatchingEvaluation, Matrix.cons_val] <;> linear_combination h7
  · change g 8 = 0
    dsimp only [g, fourMatchingEvaluation, Matrix.cons_val] <;> linear_combination h8
  · change g 9 = g 9
    dsimp only [g, fourMatchingEvaluation, Matrix.cons_val] <;> ring
  · change g 10 = g 10
    dsimp only [g, fourMatchingEvaluation, Matrix.cons_val] <;> ring
  · change g 11 = g 10 + g 9
    dsimp only [g, fourMatchingEvaluation, Matrix.cons_val] <;> linear_combination h6 - h7 - h8
  · change g 12 = g 12
    dsimp only [g, fourMatchingEvaluation, Matrix.cons_val] <;> ring
  · change g 13 = g 13
    dsimp only [g, fourMatchingEvaluation, Matrix.cons_val] <;> ring
  · change g 14 = g 12 - g 2
    dsimp only [g, fourMatchingEvaluation, Matrix.cons_val] <;> linear_combination h0 - h6 + h8
  · change g 15 = g 13 - g 3 + g 9
    dsimp only [g, fourMatchingEvaluation, Matrix.cons_val] <;> linear_combination h1 - h7
  · change g 16 = g 16
    dsimp only [g, fourMatchingEvaluation, Matrix.cons_val] <;> ring
  · change g 17 = g 16 + g 2 - g 3 + g 9
    dsimp only [g, fourMatchingEvaluation, Matrix.cons_val] <;> linear_combination -h0 + h1 + h6 - h7 - h8
  · change g 18 = g 18
    dsimp only [g, fourMatchingEvaluation, Matrix.cons_val] <;> ring
  · change g 19 = -g 12 + g 13 + g 18
    dsimp only [g, fourMatchingEvaluation, Matrix.cons_val] <;> linear_combination h6 - h7
  · change g 20 = g 10 + g 18
    dsimp only [g, fourMatchingEvaluation, Matrix.cons_val] <;> linear_combination h1 - h4 - h7
  · change g 21 = g 10 - g 12 + g 13 + g 18 + g 2 - g 3 + g 9
    dsimp only [g, fourMatchingEvaluation, Matrix.cons_val] <;> linear_combination h1 - h4 + h6 - 2 * h7 - h8
  · change g 22 = -g 12 + g 16 + g 18 + g 2
    dsimp only [g, fourMatchingEvaluation, Matrix.cons_val] <;> linear_combination -h0 + h1 - h4 + h6 - h7
  · change g 23 = -g 12 + g 16 + g 18 + 2 * g 2 - g 3 + g 9
    dsimp only [g, fourMatchingEvaluation, Matrix.cons_val] <;> linear_combination -h0 + h1 - h4 + h6 - h7 - h8

set_option maxHeartbeats 3000000 in
private theorem t19_gapProfile_eq_minorSum (g : Fin 24 → ℝ) (x y : ℝ) (i : Fin 24) :
    t19GapProfile g i = ∑ j : Fin 13, if i.val ∈ rectangleMinorSupport j then
      t19MinorWeights g x y j else 0 := by
  let rhs (i : ℕ) := ∑ j : Fin 13, if i ∈ rectangleMinorSupport j then t19MinorWeights g x y j else 0
  change t19GapProfile g i = rhs i.val
  fin_cases i
  case' «0» => change 0 = rhs 0
  case' «1» => change 0 = rhs 1
  case' «2» => change g 2 = rhs 2
  case' «3» => change g 3 = rhs 3
  case' «4» => change 0 = rhs 4
  case' «5» => change -g 2 + g 3 = rhs 5
  case' «6» => change 0 = rhs 6
  case' «7» => change 0 = rhs 7
  case' «8» => change 0 = rhs 8
  case' «9» => change g 9 = rhs 9
  case' «10» => change g 10 = rhs 10
  case' «11» => change g 10 + g 9 = rhs 11
  case' «12» => change g 12 = rhs 12
  case' «13» => change g 13 = rhs 13
  case' «14» => change g 12 - g 2 = rhs 14
  case' «15» => change g 13 - g 3 + g 9 = rhs 15
  case' «16» => change g 16 = rhs 16
  case' «17» => change g 16 + g 2 - g 3 + g 9 = rhs 17
  case' «18» => change g 18 = rhs 18
  case' «19» => change -g 12 + g 13 + g 18 = rhs 19
  case' «20» => change g 10 + g 18 = rhs 20
  case' «21» => change g 10 - g 12 + g 13 + g 18 + g 2 - g 3 + g 9 = rhs 21
  case' «22» => change -g 12 + g 16 + g 18 + g 2 = rhs 22
  case' «23» => change -g 12 + g 16 + g 18 + 2 * g 2 - g 3 + g 9 = rhs 23
  all_goals
    norm_num [rhs, Fin.sum_univ_succ, rectangleMinorSupport, t19MinorWeights, Matrix.cons_val] <;> ring

/-- The six prescribed contacts of case T20. -/
def fourT20ContactIndices : Finset (Fin 24) := {0, 1, 5, 6, 7, 8}

private def t20GapProfile (g : Fin 24 → ℝ) : Fin 24 → ℝ :=
  ![0,
    0,
    g 2,
    g 3,
    g 2 - g 3,
    0,
    0,
    0,
    0,
    g 9,
    g 10,
    g 10 + g 9,
    g 12,
    g 13,
    g 12 - g 2,
    g 13 - g 3 + g 9,
    g 16,
    g 16 + g 2 - g 3 + g 9,
    g 18,
    -g 12 + g 13 + g 18,
    g 10 + g 18 - g 2 + g 3,
    g 10 - g 12 + g 13 + g 18 + g 9,
    -g 12 + g 16 + g 18 + g 3,
    -g 12 + g 16 + g 18 + g 2 + g 9]

private def t20MinorWeights (g : Fin 24 → ℝ) (x : ℝ) : Fin 13 → ℝ :=
  ![-g 12 + g 18 + g 3 + x,
    g 16 - x,
    g 13 - g 3 - x,
    g 12 - g 2 - x,
    x,
    g 10,
    g 9,
    0,
    0,
    0,
    0,
    g 2 - g 3,
    g 3]

set_option maxHeartbeats 3000000 in
private theorem t20_gapProfile_of_contacts (m : Fin 14 → ℝ) (H : ℝ)
    (h0 : fourMatchingEvaluation m 0 = H) (h1 : fourMatchingEvaluation m 1 = H) (h5 : fourMatchingEvaluation m 5 = H)
    (h6 : fourMatchingEvaluation m 6 = H) (h7 : fourMatchingEvaluation m 7 = H) (h8 : fourMatchingEvaluation m 8 = H)
    (i : Fin 24) :
    let g (j : Fin 24) := fourMatchingEvaluation m j - H
    g i = t20GapProfile g i := by
  let g (j : Fin 24) := fourMatchingEvaluation m j - H
  change g i = t20GapProfile g i
  dsimp only [fourMatchingEvaluation, Matrix.cons_val] at h0 h1 h5 h6 h7 h8
  fin_cases i
  · change g 0 = 0
    dsimp only [g, fourMatchingEvaluation, Matrix.cons_val] <;> linear_combination h0
  · change g 1 = 0
    dsimp only [g, fourMatchingEvaluation, Matrix.cons_val] <;> linear_combination h1
  · change g 2 = g 2
    dsimp only [g, fourMatchingEvaluation, Matrix.cons_val] <;> ring
  · change g 3 = g 3
    dsimp only [g, fourMatchingEvaluation, Matrix.cons_val] <;> ring
  · change g 4 = g 2 - g 3
    dsimp only [g, fourMatchingEvaluation, Matrix.cons_val] <;> linear_combination -h0 + h1 + h5
  · change g 5 = 0
    dsimp only [g, fourMatchingEvaluation, Matrix.cons_val] <;> linear_combination h5
  · change g 6 = 0
    dsimp only [g, fourMatchingEvaluation, Matrix.cons_val] <;> linear_combination h6
  · change g 7 = 0
    dsimp only [g, fourMatchingEvaluation, Matrix.cons_val] <;> linear_combination h7
  · change g 8 = 0
    dsimp only [g, fourMatchingEvaluation, Matrix.cons_val] <;> linear_combination h8
  · change g 9 = g 9
    dsimp only [g, fourMatchingEvaluation, Matrix.cons_val] <;> ring
  · change g 10 = g 10
    dsimp only [g, fourMatchingEvaluation, Matrix.cons_val] <;> ring
  · change g 11 = g 10 + g 9
    dsimp only [g, fourMatchingEvaluation, Matrix.cons_val] <;> linear_combination h6 - h7 - h8
  · change g 12 = g 12
    dsimp only [g, fourMatchingEvaluation, Matrix.cons_val] <;> ring
  · change g 13 = g 13
    dsimp only [g, fourMatchingEvaluation, Matrix.cons_val] <;> ring
  · change g 14 = g 12 - g 2
    dsimp only [g, fourMatchingEvaluation, Matrix.cons_val] <;> linear_combination h0 - h6 + h8
  · change g 15 = g 13 - g 3 + g 9
    dsimp only [g, fourMatchingEvaluation, Matrix.cons_val] <;> linear_combination h1 - h7
  · change g 16 = g 16
    dsimp only [g, fourMatchingEvaluation, Matrix.cons_val] <;> ring
  · change g 17 = g 16 + g 2 - g 3 + g 9
    dsimp only [g, fourMatchingEvaluation, Matrix.cons_val] <;> linear_combination -h0 + h1 + h6 - h7 - h8
  · change g 18 = g 18
    dsimp only [g, fourMatchingEvaluation, Matrix.cons_val] <;> ring
  · change g 19 = -g 12 + g 13 + g 18
    dsimp only [g, fourMatchingEvaluation, Matrix.cons_val] <;> linear_combination h6 - h7
  · change g 20 = g 10 + g 18 - g 2 + g 3
    dsimp only [g, fourMatchingEvaluation, Matrix.cons_val] <;> linear_combination h0 - h5 - h7
  · change g 21 = g 10 - g 12 + g 13 + g 18 + g 9
    dsimp only [g, fourMatchingEvaluation, Matrix.cons_val] <;> linear_combination h0 - h5 + h6 - 2 * h7 - h8
  · change g 22 = -g 12 + g 16 + g 18 + g 3
    dsimp only [g, fourMatchingEvaluation, Matrix.cons_val] <;> linear_combination -h5 + h6 - h7
  · change g 23 = -g 12 + g 16 + g 18 + g 2 + g 9
    dsimp only [g, fourMatchingEvaluation, Matrix.cons_val] <;> linear_combination -h5 + h6 - h7 - h8

set_option maxHeartbeats 3000000 in
private theorem t20_gapProfile_eq_minorSum (g : Fin 24 → ℝ) (x : ℝ) (i : Fin 24) :
    t20GapProfile g i = ∑ j : Fin 13, if i.val ∈ rectangleMinorSupport j then
      t20MinorWeights g x j else 0 := by
  let rhs (i : ℕ) := ∑ j : Fin 13, if i ∈ rectangleMinorSupport j then t20MinorWeights g x j else 0
  change t20GapProfile g i = rhs i.val
  fin_cases i
  case' «0» => change 0 = rhs 0
  case' «1» => change 0 = rhs 1
  case' «2» => change g 2 = rhs 2
  case' «3» => change g 3 = rhs 3
  case' «4» => change g 2 - g 3 = rhs 4
  case' «5» => change 0 = rhs 5
  case' «6» => change 0 = rhs 6
  case' «7» => change 0 = rhs 7
  case' «8» => change 0 = rhs 8
  case' «9» => change g 9 = rhs 9
  case' «10» => change g 10 = rhs 10
  case' «11» => change g 10 + g 9 = rhs 11
  case' «12» => change g 12 = rhs 12
  case' «13» => change g 13 = rhs 13
  case' «14» => change g 12 - g 2 = rhs 14
  case' «15» => change g 13 - g 3 + g 9 = rhs 15
  case' «16» => change g 16 = rhs 16
  case' «17» => change g 16 + g 2 - g 3 + g 9 = rhs 17
  case' «18» => change g 18 = rhs 18
  case' «19» => change -g 12 + g 13 + g 18 = rhs 19
  case' «20» => change g 10 + g 18 - g 2 + g 3 = rhs 20
  case' «21» => change g 10 - g 12 + g 13 + g 18 + g 9 = rhs 21
  case' «22» => change -g 12 + g 16 + g 18 + g 3 = rhs 22
  case' «23» => change -g 12 + g 16 + g 18 + g 2 + g 9 = rhs 23
  all_goals
    norm_num [rhs, Fin.sum_univ_succ, rectangleMinorSupport, t20MinorWeights, Matrix.cons_val] <;> ring

private theorem t18_weights_nonneg (g : Fin 24 → ℝ) (hn : ∀ i, 0 ≤ g i)
    (hp : ∀ i, g i = t18GapProfile g i)
    (hA : 0 ≤ g 18 - g 2) (hB : 0 ≤ g 2 - g 4 + g 10 - g 12 + g 13 + g 18) :
    let y := min (g 10) (min (g 4 - g 2) (g 16))
    let x := max 0 (g 12 - g 18 - g 2 + g 4 - y)
    ∀ j, 0 ≤ t18MinorWeights g x y j := by
  let y := min (g 10) (min (g 4 - g 2) (g 16))
  let x := max 0 (g 12 - g 18 - g 2 + g 4 - y)
  have h5 : 0 ≤ g 4 - g 2 := by
    have h := hn 5
    rw [hp 5] at h
    change 0 ≤ -g 2 + g 4 at h
    linarith only [h]
  have h14 : 0 ≤ g 12 - g 2 := by
    have h := hn 14
    rw [hp 14] at h
    change 0 ≤ g 12 - g 2 at h
    linarith only [h]
  have h19 : 0 ≤ -g 12 + g 13 + g 18 := by
    have h := hn 19
    rw [hp 19] at h
    change 0 ≤ -g 12 + g 13 + g 18 at h
    linarith only [h]
  have h20 : 0 ≤ g 10 + g 18 - g 4 := by
    have h := hn 20
    rw [hp 20] at h
    change 0 ≤ g 10 + g 18 - g 4 at h
    linarith only [h]
  have h22 : 0 ≤ -g 12 + g 16 + g 18 + g 2 - g 4 := by
    have h := hn 22
    rw [hp 22] at h
    change 0 ≤ -g 12 + g 16 + g 18 + g 2 - g 4 at h
    linarith only [h]
  have hy0 : 0 ≤ y := le_min (hn 10) (le_min h5 (hn 16))
  have hy10 : y ≤ g 10 := min_le_left _ _
  have hy5 : y ≤ g 4 - g 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hy16 : y ≤ g 16 := (min_le_right _ _).trans (min_le_right _ _)
  have hy13 : g 12 - g 18 - g 2 + g 4 - g 13 ≤ y :=
    le_min (by linarith only [hB]) (le_min (by linarith only [h19]) (by linarith only [h22, hn 13]))
  have hy12 : g 4 - g 18 ≤ y :=
    le_min (by linarith only [h20]) (le_min (by linarith only [hA]) (by linarith only [h22, h14]))
  have hx0 : 0 ≤ x := le_max_left _ _
  have hxB : g 12 - g 18 - g 2 + g 4 - y ≤ x := le_max_right _ _
  have hx16 : x ≤ g 16 - y := max_le (sub_nonneg.mpr hy16) (by linarith only [h22])
  have hx13 : x ≤ g 13 := max_le (hn 13) (by linarith only [hy13])
  have hx12 : x ≤ g 12 - g 2 := max_le h14 (by linarith only [hy12])
  change ∀ j : Fin 13, 0 ≤ t18MinorWeights g x y j
  intro j
  fin_cases j
  case' «0» => change 0 ≤ -g 12 + g 18 + g 2 - g 4 + x + y
  case' «1» => change 0 ≤ g 16 - x - y
  case' «2» => change 0 ≤ g 13 - x
  case' «3» => change 0 ≤ g 12 - g 2 - x
  case' «4» => change 0 ≤ x
  case' «5» => change 0 ≤ g 10 - y
  case' «6» => change 0 ≤ g 9
  case' «7» => change 0 ≤ -g 2 + g 4 - y
  case' «8» => change 0 ≤ y
  case' «9» => change 0 ≤ 0
  case' «10» => change 0 ≤ 0
  case' «11» => change 0 ≤ g 2
  case' «12» => change 0 ≤ 0
  all_goals linarith only [hy0, hy10, hy5, hx0, hxB, hx16, hx13, hx12, hn 2, hn 9]

private theorem t19_weights_nonneg (g : Fin 24 → ℝ) (hn : ∀ i, 0 ≤ g i)
    (hp : ∀ i, g i = t19GapProfile g i)
    (hA : 0 ≤ g 13 - g 2) (hB : 0 ≤ g 2 - g 3 + g 9 - g 12 + g 13 + g 18) :
    let y := min (g 9) (g 3 - g 2)
    let x := max 0 (g 12 - g 18 - g 2)
    ∀ j, 0 ≤ t19MinorWeights g x y j := by
  let y := min (g 9) (g 3 - g 2)
  let x := max 0 (g 12 - g 18 - g 2)
  have h5 : 0 ≤ g 3 - g 2 := by
    have h := hn 5
    rw [hp 5] at h
    change 0 ≤ -g 2 + g 3 at h
    linarith only [h]
  have h14 : 0 ≤ g 12 - g 2 := by
    have h := hn 14
    rw [hp 14] at h
    change 0 ≤ g 12 - g 2 at h
    linarith only [h]
  have h15 : 0 ≤ g 13 - g 3 + g 9 := by
    have h := hn 15
    rw [hp 15] at h
    change 0 ≤ g 13 - g 3 + g 9 at h
    linarith only [h]
  have h17 : 0 ≤ g 16 + g 2 - g 3 + g 9 := by
    have h := hn 17
    rw [hp 17] at h
    change 0 ≤ g 16 + g 2 - g 3 + g 9 at h
    linarith only [h]
  have h19 : 0 ≤ -g 12 + g 13 + g 18 := by
    have h := hn 19
    rw [hp 19] at h
    change 0 ≤ -g 12 + g 13 + g 18 at h
    linarith only [h]
  have h22 : 0 ≤ -g 12 + g 16 + g 18 + g 2 := by
    have h := hn 22
    rw [hp 22] at h
    change 0 ≤ -g 12 + g 16 + g 18 + g 2 at h
    linarith only [h]
  have h23 : 0 ≤ -g 12 + g 16 + g 18 + 2 * g 2 - g 3 + g 9 := by
    have h := hn 23
    rw [hp 23] at h
    change 0 ≤ -g 12 + g 16 + g 18 + 2 * g 2 - g 3 + g 9 at h
    linarith only [h]
  have hy0 : 0 ≤ y := le_min (hn 9) h5
  have hy9 : y ≤ g 9 := min_le_left _ _
  have hy5 : y ≤ g 3 - g 2 := min_le_right _ _
  have hx0 : 0 ≤ x := le_max_left _ _
  have hxB : g 12 - g 18 - g 2 ≤ x := le_max_right _ _
  have hx12 : x ≤ g 12 - g 2 := max_le h14 (by linarith only [hn 18])
  have hx16 : x ≤ g 16 + g 2 - g 3 + y := by
    dsimp only [y]
    rcases le_total (g 9) (g 3 - g 2) with h | h
    · rw [min_eq_left h]
      exact max_le h17 (by linarith only [h23])
    · rw [min_eq_right h]
      exact max_le (by linarith only [hn 16]) (by linarith only [h22])
  have hx13 : x ≤ g 13 - g 3 + y := by
    dsimp only [y]
    rcases le_total (g 9) (g 3 - g 2) with h | h
    · rw [min_eq_left h]
      exact max_le h15 (by linarith only [hB])
    · rw [min_eq_right h]
      exact max_le (by linarith only [hA]) (by linarith only [h19])
  change ∀ j : Fin 13, 0 ≤ t19MinorWeights g x y j
  intro j
  fin_cases j
  case' «0» => change 0 ≤ -g 12 + g 18 + g 2 + x
  case' «1» => change 0 ≤ g 16 + g 2 - g 3 - x + y
  case' «2» => change 0 ≤ g 13 - g 3 - x + y
  case' «3» => change 0 ≤ g 12 - g 2 - x
  case' «4» => change 0 ≤ x
  case' «5» => change 0 ≤ g 10
  case' «6» => change 0 ≤ g 9 - y
  case' «7» => change 0 ≤ 0
  case' «8» => change 0 ≤ 0
  case' «9» => change 0 ≤ -g 2 + g 3 - y
  case' «10» => change 0 ≤ y
  case' «11» => change 0 ≤ 0
  case' «12» => change 0 ≤ g 2
  all_goals linarith only [hy0, hy9, hy5, hx0, hxB, hx12, hx16, hx13, hn 2, hn 10]

private theorem t20_weights_nonneg (g : Fin 24 → ℝ) (hn : ∀ i, 0 ≤ g i)
    (hp : ∀ i, g i = t20GapProfile g i)
    (hA : 0 ≤ g 3 - g 2 + g 18) (hB : 0 ≤ g 13 - g 3) :
    let x := max 0 (g 12 - g 18 - g 3)
    ∀ j, 0 ≤ t20MinorWeights g x j := by
  let x := max 0 (g 12 - g 18 - g 3)
  have h4 : 0 ≤ g 2 - g 3 := by
    have h := hn 4
    rw [hp 4] at h
    change 0 ≤ g 2 - g 3 at h
    linarith only [h]
  have h14 : 0 ≤ g 12 - g 2 := by
    have h := hn 14
    rw [hp 14] at h
    change 0 ≤ g 12 - g 2 at h
    linarith only [h]
  have h19 : 0 ≤ -g 12 + g 13 + g 18 := by
    have h := hn 19
    rw [hp 19] at h
    change 0 ≤ -g 12 + g 13 + g 18 at h
    linarith only [h]
  have h22 : 0 ≤ -g 12 + g 16 + g 18 + g 3 := by
    have h := hn 22
    rw [hp 22] at h
    change 0 ≤ -g 12 + g 16 + g 18 + g 3 at h
    linarith only [h]
  have hx0 : 0 ≤ x := le_max_left _ _
  have hxB : g 12 - g 18 - g 3 ≤ x := le_max_right _ _
  have hx16 : x ≤ g 16 := max_le (hn 16) (by linarith only [h22])
  have hx13 : x ≤ g 13 - g 3 := max_le hB (by linarith only [h19])
  have hx12 : x ≤ g 12 - g 2 := max_le h14 (by linarith only [hA])
  change ∀ j : Fin 13, 0 ≤ t20MinorWeights g x j
  intro j
  fin_cases j
  case' «0» => change 0 ≤ -g 12 + g 18 + g 3 + x
  case' «1» => change 0 ≤ g 16 - x
  case' «2» => change 0 ≤ g 13 - g 3 - x
  case' «3» => change 0 ≤ g 12 - g 2 - x
  case' «4» => change 0 ≤ x
  case' «5» => change 0 ≤ g 10
  case' «6» => change 0 ≤ g 9
  case' «7» => change 0 ≤ 0
  case' «8» => change 0 ≤ 0
  case' «9» => change 0 ≤ 0
  case' «10» => change 0 ≤ 0
  case' «11» => change 0 ≤ g 2 - g 3
  case' «12» => change 0 ≤ g 3
  all_goals linarith only [h4, hx0, hxB, hx16, hx13, hx12, hn 3, hn 9, hn 10]

/-- The two additional spectral inequalities certify the support bound in case T18. -/
theorem fourT18_support_of_two_inequalities (a b : Fin 4 → ℂ) (η : ℂ) (H : ℝ)
    (hn : ∀ i, H ≤ (η * matchingProduct a b (fourPerm i).symm).re)
    (hc : ∀ i ∈ fourT18ContactIndices, (η * matchingProduct a b (fourPerm i).symm).re = H)
    (U : Matrix (Fin 4) (Fin 4) ℂ) (hU : IsUnitary U) :
    let g (i : Fin 24) := (η * matchingProduct a b (fourPerm i).symm).re - H
    0 ≤ g 18 - g 2 → 0 ≤ g 2 - g 4 + g 10 - g 12 + g 13 + g 18 →
      H ≤ (η * determinantValue a b U).re := by
  let m : Fin 14 → ℝ := fun i => (η * fourNoncrossingCoordinates (fourSpectralPoints a b) i).re
  let g (i : Fin 24) := (η * matchingProduct a b (fourPerm i).symm).re - H
  change 0 ≤ g 18 - g 2 → 0 ≤ g 2 - g 4 + g 10 - g 12 + g 13 + g 18 → _
  intro hA hB
  have hm (i : Fin 24) : fourMatchingEvaluation m i =
      (η * matchingProduct a b (fourPerm i).symm).re :=
    fourMatchingEvaluation_spectral_real_part a b η i
  have hcontact (i : Fin 24) (hi : i ∈ fourT18ContactIndices) : fourMatchingEvaluation m i = H :=
    (hm i).trans (hc i hi)
  have hp (i : Fin 24) : g i = t18GapProfile g i := by
    have h := t18_gapProfile_of_contacts m H
      (hcontact 0 (by decide)) (hcontact 1 (by decide)) (hcontact 3 (by decide))
      (hcontact 6 (by decide)) (hcontact 7 (by decide)) (hcontact 8 (by decide)) i
    simpa only [hm, g] using h
  let y := min (g 10) (min (g 4 - g 2) (g 16))
  let x := max 0 (g 12 - g 18 - g 2 + g 4 - y)
  have hw : ∀ j, 0 ≤ t18MinorWeights g x y j :=
    t18_weights_nonneg g (fun i => sub_nonneg.mpr (hn i)) hp hA hB
  apply four_support_of_minor_gap_decomposition a b η H U hU 0 (hc 0 (by decide))
    rectangleMinorRows rectangleMinorColumns (t18MinorWeights g x y) hw
  intro i
  change g i = _
  simp only [← rectangleMinorSupport_spec]
  exact (hp i).trans (t18_gapProfile_eq_minorSum g x y i)

/-- The two additional spectral inequalities certify the support bound in case T19. -/
theorem fourT19_support_of_two_inequalities (a b : Fin 4 → ℂ) (η : ℂ) (H : ℝ)
    (hn : ∀ i, H ≤ (η * matchingProduct a b (fourPerm i).symm).re)
    (hc : ∀ i ∈ fourT19ContactIndices, (η * matchingProduct a b (fourPerm i).symm).re = H)
    (U : Matrix (Fin 4) (Fin 4) ℂ) (hU : IsUnitary U) :
    let g (i : Fin 24) := (η * matchingProduct a b (fourPerm i).symm).re - H
    0 ≤ g 13 - g 2 → 0 ≤ g 2 - g 3 + g 9 - g 12 + g 13 + g 18 →
      H ≤ (η * determinantValue a b U).re := by
  let m : Fin 14 → ℝ := fun i => (η * fourNoncrossingCoordinates (fourSpectralPoints a b) i).re
  let g (i : Fin 24) := (η * matchingProduct a b (fourPerm i).symm).re - H
  change 0 ≤ g 13 - g 2 → 0 ≤ g 2 - g 3 + g 9 - g 12 + g 13 + g 18 → _
  intro hA hB
  have hm (i : Fin 24) : fourMatchingEvaluation m i =
      (η * matchingProduct a b (fourPerm i).symm).re :=
    fourMatchingEvaluation_spectral_real_part a b η i
  have hcontact (i : Fin 24) (hi : i ∈ fourT19ContactIndices) : fourMatchingEvaluation m i = H :=
    (hm i).trans (hc i hi)
  have hp (i : Fin 24) : g i = t19GapProfile g i := by
    have h := t19_gapProfile_of_contacts m H
      (hcontact 0 (by decide)) (hcontact 1 (by decide)) (hcontact 4 (by decide))
      (hcontact 6 (by decide)) (hcontact 7 (by decide)) (hcontact 8 (by decide)) i
    simpa only [hm, g] using h
  let y := min (g 9) (g 3 - g 2)
  let x := max 0 (g 12 - g 18 - g 2)
  have hw : ∀ j, 0 ≤ t19MinorWeights g x y j :=
    t19_weights_nonneg g (fun i => sub_nonneg.mpr (hn i)) hp hA hB
  apply four_support_of_minor_gap_decomposition a b η H U hU 0 (hc 0 (by decide))
    rectangleMinorRows rectangleMinorColumns (t19MinorWeights g x y) hw
  intro i
  change g i = _
  simp only [← rectangleMinorSupport_spec]
  exact (hp i).trans (t19_gapProfile_eq_minorSum g x y i)

/-- The two additional spectral inequalities certify the support bound in case T20. -/
theorem fourT20_support_of_two_inequalities (a b : Fin 4 → ℂ) (η : ℂ) (H : ℝ)
    (hn : ∀ i, H ≤ (η * matchingProduct a b (fourPerm i).symm).re)
    (hc : ∀ i ∈ fourT20ContactIndices, (η * matchingProduct a b (fourPerm i).symm).re = H)
    (U : Matrix (Fin 4) (Fin 4) ℂ) (hU : IsUnitary U) :
    let g (i : Fin 24) := (η * matchingProduct a b (fourPerm i).symm).re - H
    0 ≤ g 3 - g 2 + g 18 → 0 ≤ g 13 - g 3 →
      H ≤ (η * determinantValue a b U).re := by
  let m : Fin 14 → ℝ := fun i => (η * fourNoncrossingCoordinates (fourSpectralPoints a b) i).re
  let g (i : Fin 24) := (η * matchingProduct a b (fourPerm i).symm).re - H
  change 0 ≤ g 3 - g 2 + g 18 → 0 ≤ g 13 - g 3 → _
  intro hA hB
  have hm (i : Fin 24) : fourMatchingEvaluation m i =
      (η * matchingProduct a b (fourPerm i).symm).re :=
    fourMatchingEvaluation_spectral_real_part a b η i
  have hcontact (i : Fin 24) (hi : i ∈ fourT20ContactIndices) : fourMatchingEvaluation m i = H :=
    (hm i).trans (hc i hi)
  have hp (i : Fin 24) : g i = t20GapProfile g i := by
    have h := t20_gapProfile_of_contacts m H
      (hcontact 0 (by decide)) (hcontact 1 (by decide)) (hcontact 5 (by decide))
      (hcontact 6 (by decide)) (hcontact 7 (by decide)) (hcontact 8 (by decide)) i
    simpa only [hm, g] using h
  let x := max 0 (g 12 - g 18 - g 3)
  have hw : ∀ j, 0 ≤ t20MinorWeights g x j :=
    t20_weights_nonneg g (fun i => sub_nonneg.mpr (hn i)) hp hA hB
  apply four_support_of_minor_gap_decomposition a b η H U hU 0 (hc 0 (by decide))
    rectangleMinorRows rectangleMinorColumns (t20MinorWeights g x) hw
  intro i
  change g i = _
  simp only [← rectangleMinorSupport_spec]
  exact (hp i).trans (t20_gapProfile_eq_minorSum g x i)

end

end MOC
