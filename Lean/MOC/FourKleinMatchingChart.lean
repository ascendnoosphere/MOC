import MOC.FourMatchingRelations
import MOC.RealMatchingSquares

/-! Exact ten-dimensional chart on costs vanishing on the normal Klein four. -/

open BigOperators Matrix

namespace MOC

noncomputable section

/-- The identity and three double transpositions in the shared lexicographic table. -/
def normalKleinFourContacts : Finset (Fin 24) := {0, 7, 16, 23}

/-- Columns are the cycle difference, three indicator coordinates, and the
two triples of signed off-diagonal coordinates. -/
def kleinMatchingFeatureTable : Fin 10 → Fin 24 → ℤ :=
  ![![0, 0, 0, 1, -1, 0, 0, 0, -1, 0, 0, 1, 1, 0, 0, -1, 0, 0, 0, -1, 1, 0, 0, 0],
    ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0],
    ![0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0],
    ![0, 1, 0, 1, 0, 0, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 0, 0, 1, 0, 1, 0],
    ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0, -1, -1, 1, 1, 0, 0, 0, 0, 0, 0, -1, -1, 0, 0],
    ![0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 1, -1, 0, -1, 0, 0, 0, -1, 0, -1, 0, 0, 0],
    ![0, 1, 0, 1, 0, 0, -1, 0, 0, 0, 0, -1, -1, 0, 0, 0, 0, -1, 0, 0, 1, 0, 1, 0],
    ![0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 1, 0, 0, -1, 0, -1, 0, 0, 0, -1, 0, -1, 0, 0],
    ![0, 0, 0, 0, 1, 1, 0, 0, -1, -1, 0, 0, 0, 0, -1, -1, 0, 0, 1, 1, 0, 0, 0, 0],
    ![0, 1, 0, 0, 1, 0, -1, 0, -1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, -1, 0, 0, -1, 0]]

abbrev KleinMatchingFunction := Fin 24 → ℝ

/-- The cycle difference is +1 on the first cycle coset and −1 on the second. -/
def kleinCycle : KleinMatchingFunction :=
  fun j => kleinMatchingFeatureTable 0 j

/-- The indicator and sign functions in one three-coordinate group. -/
def kleinFaceIndicator (i : Fin 3) : KleinMatchingFunction :=
  fun j => kleinMatchingFeatureTable (Fin.castAdd 6 (i.succ)) j

def kleinFaceSignPlus (i : Fin 3) : KleinMatchingFunction :=
  fun j => kleinMatchingFeatureTable (Fin.natAdd 4 (Fin.castAdd 3 i)) j

def kleinFaceSignMinus (i : Fin 3) : KleinMatchingFunction :=
  fun j => kleinMatchingFeatureTable (Fin.natAdd 7 i) j

/-- The two sum-to-four cycles have baseline values `c₋` and
`∑ i, β i - c₋`. -/
def kleinMatchingCost (β p q : Fin 3 → ℝ) (c₋ : ℝ) : KleinMatchingFunction :=
  fun j => -c₋ * kleinCycle j +
    ∑ i : Fin 3, (β i * kleinFaceIndicator i j +
      p i * kleinFaceSignPlus i j + q i * kleinFaceSignMinus i j)

private def chartBeta (g : KleinMatchingFunction) : Fin 3 → ℝ :=
  ![(g 2 + g 10 + g 13 + g 21) / 4,
    (g 5 + g 9 + g 14 + g 18) / 4,
    (g 1 + g 6 + g 17 + g 22) / 4]

private def chartPlusSign (g : KleinMatchingFunction) : Fin 3 → ℝ :=
  ![(g 2 - g 10 + g 13 - g 21) / 4,
    (g 5 + g 9 - g 14 - g 18) / 4,
    (g 1 - g 6 - g 17 + g 22) / 4]

private def chartMinusSign (g : KleinMatchingFunction) : Fin 3 → ℝ :=
  ![(g 2 + g 10 - g 13 - g 21) / 4,
    (g 5 - g 9 - g 14 + g 18) / 4,
    (g 1 - g 6 + g 17 - g 22) / 4]

private def chartMinusBaseline (g : KleinMatchingFunction) : ℝ :=
  (g 4 + g 8 + g 15 + g 19) / 4

set_option maxHeartbeats 2000000 in
/-- A matching evaluation vanishing on the normal Klein four has the
displayed ten-coordinate form. The inverse reads the rectangle averages,
the two signed averages, and the mean on the second cycle coset. -/
theorem exists_kleinMatchingCost (m : Fin 14 → ℝ)
    (h : ∀ j ∈ normalKleinFourContacts, fourMatchingEvaluation m j = 0) :
    ∃ (β p q : Fin 3 → ℝ) (c₋ : ℝ), fourMatchingEvaluation m = kleinMatchingCost β p q c₋ := by
  let g := fourMatchingEvaluation m
  refine ⟨chartBeta g, chartPlusSign g, chartMinusSign g, chartMinusBaseline g, ?_⟩
  have h₀ := h 0 (by decide)
  have h₇ := h 7 (by decide)
  have h₁₆ := h 16 (by decide)
  have h₂₃ := h 23 (by decide)
  norm_num [fourMatchingEvaluation] at h₀ h₇ h₁₆ h₂₃
  funext j
  fin_cases j <;>
    norm_num [g, kleinMatchingCost, kleinCycle, kleinFaceIndicator, kleinFaceSignPlus,
      kleinFaceSignMinus, kleinMatchingFeatureTable, chartBeta, chartPlusSign, chartMinusSign,
      chartMinusBaseline, fourMatchingEvaluation, Fin.sum_univ_three] <;>
    linarith only [h₀, h₇, h₁₆, h₂₃]

def kleinMatchingEvaluationLinear : (Fin 14 → ℝ) →ₗ[ℝ] KleinMatchingFunction where
  toFun := fourMatchingEvaluation
  map_add' x y := by
    funext i
    fin_cases i <;> simp [fourMatchingEvaluation] <;> ring
  map_smul' r x := by
    funext i
    fin_cases i <;> simp [fourMatchingEvaluation] <;> ring

def kleinMatchingSpace : Submodule ℝ KleinMatchingFunction :=
  LinearMap.range kleinMatchingEvaluationLinear

private theorem matchingEvaluation_map_int (m : Fin 14 → ℤ) (j : Fin 24) :
    fourMatchingEvaluation (fun i => (m i : ℝ)) j = (fourMatchingEvaluation m j : ℝ) := by
  fin_cases j <;>
    push_cast [fourMatchingEvaluation] <;> rfl

private theorem feature_eval_int (i : Fin 10) (j : Fin 24) :
    fourMatchingEvaluation (fourMatchingCoordinatesOfValues (kleinMatchingFeatureTable i)) j =
      kleinMatchingFeatureTable i j := by
  revert i j
  decide +kernel

theorem kleinMatchingFeature_mem (i : Fin 10) :
    (fun j => (kleinMatchingFeatureTable i j : ℝ)) ∈ kleinMatchingSpace := by
  refine ⟨fun k => (fourMatchingCoordinatesOfValues (kleinMatchingFeatureTable i) k : ℝ), ?_⟩
  funext j
  change fourMatchingEvaluation (fun k => (fourMatchingCoordinatesOfValues
    (kleinMatchingFeatureTable i) k : ℝ)) j = _
  rw [matchingEvaluation_map_int, feature_eval_int]

theorem kleinCycle_mem : kleinCycle ∈ kleinMatchingSpace := kleinMatchingFeature_mem 0

theorem kleinFaceIndicator_mem (i : Fin 3) : kleinFaceIndicator i ∈ kleinMatchingSpace :=
  kleinMatchingFeature_mem (Fin.castAdd 6 i.succ)

theorem kleinFaceSignPlus_mem (i : Fin 3) : kleinFaceSignPlus i ∈ kleinMatchingSpace :=
  kleinMatchingFeature_mem (Fin.natAdd 4 (Fin.castAdd 3 i))

theorem kleinFaceSignMinus_mem (i : Fin 3) : kleinFaceSignMinus i ∈ kleinMatchingSpace :=
  kleinMatchingFeature_mem (Fin.natAdd 7 i)

/-- The ordinary indicator with the chosen sign in the first or second group. -/
def kleinOrdinaryPlus (i : Fin 3) (s : ℝ) : KleinMatchingFunction :=
  fun j => (kleinFaceIndicator i j + s * kleinFaceSignPlus i j) / 2

def kleinOrdinaryMinus (i : Fin 3) (s : ℝ) : KleinMatchingFunction :=
  fun j => (kleinFaceIndicator i j - kleinCycle j + s * kleinFaceSignMinus i j) / 2

theorem kleinOrdinaryPlus_mem (i : Fin 3) (s : ℝ) :
    kleinOrdinaryPlus i s ∈ kleinMatchingSpace := by
  have h := kleinMatchingSpace.smul_mem (1 / 2 : ℝ)
    (kleinMatchingSpace.add_mem (kleinFaceIndicator_mem i)
      (kleinMatchingSpace.smul_mem s (kleinFaceSignPlus_mem i)))
  convert h using 1
  funext j
  simp only [kleinOrdinaryPlus, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
  ring

theorem kleinOrdinaryMinus_mem (i : Fin 3) (s : ℝ) :
    kleinOrdinaryMinus i s ∈ kleinMatchingSpace := by
  have h := kleinMatchingSpace.smul_mem (1 / 2 : ℝ)
    (kleinMatchingSpace.add_mem (kleinMatchingSpace.sub_mem (kleinFaceIndicator_mem i) kleinCycle_mem)
      (kleinMatchingSpace.smul_mem s (kleinFaceSignMinus_mem i)))
  convert h using 1
  funext j
  simp only [kleinOrdinaryMinus, Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul]
  ring

theorem kleinOrdinaryPlus_sq (i : Fin 3) (j : Fin 24) (s : ℝ) (hs : s = 1 ∨ s = -1) :
    kleinOrdinaryPlus i s j ^ 2 = kleinOrdinaryPlus i s j := by
  rcases hs with rfl | rfl <;> fin_cases i <;> fin_cases j <;>
    norm_num [kleinOrdinaryPlus, kleinFaceIndicator, kleinFaceSignPlus, kleinMatchingFeatureTable]

theorem kleinOrdinaryMinus_sq (i : Fin 3) (j : Fin 24) (s : ℝ) (hs : s = 1 ∨ s = -1) :
    kleinOrdinaryMinus i s j ^ 2 = kleinOrdinaryMinus i s j := by
  rcases hs with rfl | rfl <;> fin_cases i <;> fin_cases j <;>
    norm_num [kleinOrdinaryMinus, kleinFaceIndicator, kleinFaceSignMinus, kleinCycle, kleinMatchingFeatureTable]

private def rectangleIndex (i : Fin 3) (s t : Bool) : Fin 24 :=
  if s then (if t then ![2, 5, 1] i else ![13, 9, 22] i)
  else (if t then ![10, 18, 17] i else ![21, 14, 6] i)

private def signOfBool (s : Bool) : ℝ := if s then 1 else -1

theorem kleinMatchingCost_rectangle (β p q : Fin 3 → ℝ) (c₋ : ℝ)
    (h : ∀ j, 0 ≤ kleinMatchingCost β p q c₋ j) (i : Fin 3) :
    |p i| + |q i| ≤ β i := by
  have he (s t : Bool) : kleinMatchingCost β p q c₋ (rectangleIndex i s t) =
      β i + signOfBool s * p i + signOfBool t * q i := by
    fin_cases i <;> cases s <;> cases t <;>
      norm_num [rectangleIndex, signOfBool, kleinMatchingCost, kleinCycle, kleinFaceIndicator,
        kleinFaceSignPlus, kleinFaceSignMinus, kleinMatchingFeatureTable, Fin.sum_univ_three] <;> ring
  by_cases hp : 0 ≤ p i <;> by_cases hq : 0 ≤ q i
  · have ha := h (rectangleIndex i false false)
    rw [he] at ha
    simp [signOfBool] at ha
    rw [abs_of_nonneg hp, abs_of_nonneg hq]
    linarith only [ha]
  · have ha := h (rectangleIndex i false true)
    rw [he] at ha
    simp [signOfBool] at ha
    rw [abs_of_nonneg hp, abs_of_neg (lt_of_not_ge hq)]
    linarith only [ha]
  · have ha := h (rectangleIndex i true false)
    rw [he] at ha
    simp [signOfBool] at ha
    rw [abs_of_neg (lt_of_not_ge hp), abs_of_nonneg hq]
    linarith only [ha]
  · have ha := h (rectangleIndex i true true)
    rw [he] at ha
    simp [signOfBool] at ha
    rw [abs_of_neg (lt_of_not_ge hp), abs_of_neg (lt_of_not_ge hq)]
    linarith only [ha]

end
end MOC
