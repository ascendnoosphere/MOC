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

/-- The two sum-to-four cycles have baseline values `cNeg` and
`∑ i, β i - cNeg`. -/
def kleinMatchingCost (β p q : Fin 3 → ℝ) (cNeg : ℝ) : KleinMatchingFunction :=
  fun j => -cNeg * kleinCycle j +
    ∑ i : Fin 3, (β i * kleinFaceIndicator i j +
      p i * kleinFaceSignPlus i j + q i * kleinFaceSignMinus i j)

private def chartEntry {R : Type*} [CommRing R] (j : Fin 24) : (Fin 24 → R) →ₗ[R] R :=
  LinearMap.proj j

private def chartBetaNumerator {R : Type*} [CommRing R] : Fin 3 → (Fin 24 → R) →ₗ[R] R :=
  ![chartEntry 2 + chartEntry 10 + chartEntry 13 + chartEntry 21,
    chartEntry 5 + chartEntry 9 + chartEntry 14 + chartEntry 18,
    chartEntry 1 + chartEntry 6 + chartEntry 17 + chartEntry 22]

private def chartPlusNumerator {R : Type*} [CommRing R] : Fin 3 → (Fin 24 → R) →ₗ[R] R :=
  ![chartEntry 2 - chartEntry 10 + chartEntry 13 - chartEntry 21,
    chartEntry 5 + chartEntry 9 - chartEntry 14 - chartEntry 18,
    chartEntry 1 - chartEntry 6 - chartEntry 17 + chartEntry 22]

private def chartMinusNumerator {R : Type*} [CommRing R] : Fin 3 → (Fin 24 → R) →ₗ[R] R :=
  ![chartEntry 2 + chartEntry 10 - chartEntry 13 - chartEntry 21,
    chartEntry 5 - chartEntry 9 - chartEntry 14 + chartEntry 18,
    chartEntry 1 - chartEntry 6 + chartEntry 17 - chartEntry 22]

private def chartBaselineNumerator {R : Type*} [CommRing R] : (Fin 24 → R) →ₗ[R] R :=
  chartEntry 4 + chartEntry 8 + chartEntry 15 + chartEntry 19

private def chartNumerator {R : Type*} [CommRing R] (j : Fin 24) : (Fin 24 → R) →ₗ[R] R :=
  -(kleinMatchingFeatureTable 0 j : R) • chartBaselineNumerator +
    ∑ i : Fin 3,
      ((kleinMatchingFeatureTable (Fin.castAdd 6 i.succ) j : R) • chartBetaNumerator i +
      (kleinMatchingFeatureTable (Fin.natAdd 4 (Fin.castAdd 3 i)) j : R) • chartPlusNumerator i +
      (kleinMatchingFeatureTable (Fin.natAdd 7 i) j : R) • chartMinusNumerator i)

private def chartContact (k : Fin 4) : Fin 24 := ![0, 7, 16, 23] k

/-- The difference between four times a matching evaluation and its chart numerator
is a linear combination of the four contact values. -/
private def chartCorrectionCoefficient : Fin 24 → Fin 4 → ℤ :=
  ![![4, 0, 0, 0], ![1, 1, -1, -1], ![1, -1, -1, 1], ![-1, -1, -1, -1],
    ![0, 0, 0, 0], ![1, -1, 1, -1], ![1, 1, -1, -1], ![0, 4, 0, 0],
    ![0, 0, 0, 0], ![-1, 1, -1, 1], ![-1, 1, 1, -1], ![-1, -1, -1, -1],
    ![-1, -1, -1, -1], ![-1, 1, 1, -1], ![1, -1, 1, -1], ![0, 0, 0, 0],
    ![0, 0, 4, 0], ![-1, -1, 1, 1], ![-1, 1, -1, 1], ![0, 0, 0, 0],
    ![-1, -1, -1, -1], ![1, -1, -1, 1], ![-1, -1, 1, 1], ![0, 0, 0, 4]]

private def chartCorrection {R : Type*} [CommRing R] (j : Fin 24) : (Fin 24 → R) →ₗ[R] R :=
  ∑ k : Fin 4, (chartCorrectionCoefficient j k : R) • chartEntry (chartContact k)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
private theorem chartBasis_identity (i : Fin 14) (j : Fin 24) :
    let g := fourMatchingEvaluation (Pi.single i (1 : ℤ))
    4 * g j = chartNumerator j g + chartCorrection j g := by
  revert i j
  decide +kernel

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
    fourMatchingEvaluation (fun i => (m i : ℝ)) j =
      (fourMatchingEvaluation (R := ℤ) m j : ℝ) := by
  fin_cases j <;> simp [fourMatchingEvaluation]

private theorem chartNumerator_map_int (g : Fin 24 → ℤ) (j : Fin 24) :
    chartNumerator j (fun k => (g k : ℝ)) = (chartNumerator (R := ℤ) j g : ℝ) := by
  have hBeta (i : Fin 3) : chartBetaNumerator i (fun k => (g k : ℝ)) =
      (chartBetaNumerator (R := ℤ) i g : ℝ) := by
    fin_cases i <;> simp [chartBetaNumerator, chartEntry, Matrix.cons_val, LinearMap.add_apply]
  have hPlus (i : Fin 3) : chartPlusNumerator i (fun k => (g k : ℝ)) =
      (chartPlusNumerator (R := ℤ) i g : ℝ) := by
    fin_cases i <;> simp [chartPlusNumerator, chartEntry, Matrix.cons_val,
      LinearMap.add_apply, LinearMap.sub_apply]
  have hMinus (i : Fin 3) : chartMinusNumerator i (fun k => (g k : ℝ)) =
      (chartMinusNumerator (R := ℤ) i g : ℝ) := by
    fin_cases i <;> simp [chartMinusNumerator, chartEntry, Matrix.cons_val,
      LinearMap.add_apply, LinearMap.sub_apply]
  simp only [chartNumerator, LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smul_apply,
    smul_eq_mul, hBeta, hPlus, hMinus, chartBaselineNumerator, chartEntry, LinearMap.proj_apply,
    Int.cast_add, Int.cast_sum, Int.cast_mul, Int.cast_neg, Int.cast_id]

private theorem chartCorrection_map_int (g : Fin 24 → ℤ) (j : Fin 24) :
    chartCorrection j (fun k => (g k : ℝ)) = (chartCorrection (R := ℤ) j g : ℝ) := by
  simp only [chartCorrection, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    chartEntry, LinearMap.proj_apply, Int.cast_sum, Int.cast_mul, Int.cast_id]
set_option maxRecDepth 4096 in
private theorem chartReconstruction (m : Fin 14 → ℝ) (j : Fin 24) :
    let g := fourMatchingEvaluation m
    4 * g j = chartNumerator j g + chartCorrection j g := by
  let lhs := ((4 : ℝ) • chartEntry j).comp kleinMatchingEvaluationLinear
  let rhs := (chartNumerator j + chartCorrection j).comp kleinMatchingEvaluationLinear
  change lhs m = rhs m
  have hm : m = ∑ i, m i • (Pi.single i (1 : ℝ) : Fin 14 → ℝ) := by
    funext k
    simp [Finset.sum_apply, Pi.single_apply, eq_comm]
  rw [hm, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul, map_smul]
  congr 1
  let u : Fin 14 → ℤ := Pi.single i 1
  have hu : (Pi.single i (1 : ℝ) : Fin 14 → ℝ) = fun k => (u k : ℝ) := by
    funext k
    by_cases h : k = i <;> simp [u, Pi.single_apply, h]
  have hg : fourMatchingEvaluation (Pi.single i (1 : ℝ)) =
      fun k => (fourMatchingEvaluation (R := ℤ) u k : ℝ) := by
    rw [hu]
    exact funext (matchingEvaluation_map_int u)
  change 4 * fourMatchingEvaluation (Pi.single i (1 : ℝ)) j =
    chartNumerator j (fourMatchingEvaluation (Pi.single i (1 : ℝ))) +
      chartCorrection j (fourMatchingEvaluation (Pi.single i (1 : ℝ)))
  rw [hg, chartNumerator_map_int, chartCorrection_map_int]
  have hInt : 4 * fourMatchingEvaluation u j =
      chartNumerator j (fourMatchingEvaluation u) + chartCorrection j (fourMatchingEvaluation u) :=
    chartBasis_identity i j
  simpa only [Int.cast_mul, Int.cast_add, Int.cast_ofNat] using congrArg (Int.cast : ℤ → ℝ) hInt

/-- A matching evaluation vanishing on the normal Klein four has the
displayed ten-coordinate form. The inverse reads the rectangle averages,
the two signed averages, and the mean on the second cycle coset. -/
theorem exists_kleinMatchingCost (m : Fin 14 → ℝ)
    (h : ∀ j ∈ normalKleinFourContacts, fourMatchingEvaluation m j = 0) :
    ∃ (β p q : Fin 3 → ℝ) (cNeg : ℝ),
      fourMatchingEvaluation m = kleinMatchingCost β p q cNeg := by
  let g := fourMatchingEvaluation m
  refine ⟨fun i => chartBetaNumerator i g / 4, fun i => chartPlusNumerator i g / 4,
    fun i => chartMinusNumerator i g / 4, chartBaselineNumerator g / 4, ?_⟩
  funext j
  have hz (k : Fin 4) : g (chartContact k) = 0 := by
    apply h
    fin_cases k <;> decide
  have hc : chartCorrection j g = 0 := by
    simp [chartCorrection, LinearMap.sum_apply, LinearMap.smul_apply, chartEntry, hz]
  have he : 4 * g j = chartNumerator j g + chartCorrection j g := chartReconstruction m j
  rw [hc, add_zero] at he
  have hvalue : g j = chartNumerator j g / 4 := by linarith only [he]
  change g j = _
  rw [hvalue]
  simp only [chartNumerator, LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smul_apply,
    smul_eq_mul, kleinMatchingCost, kleinCycle, kleinFaceIndicator, kleinFaceSignPlus,
    kleinFaceSignMinus, add_div, Finset.sum_div]
  apply congrArg₂ (· + ·)
  · ring
  · apply Finset.sum_congr rfl
    intro i _
    ring

private theorem feature_eval_int (i : Fin 10) (j : Fin 24) :
    fourMatchingEvaluation (fourMatchingCoordinatesOfValues (kleinMatchingFeatureTable i)) j =
      kleinMatchingFeatureTable i j := by
  revert i j
  decide +kernel

theorem kleinMatchingFeature_mem (i : Fin 10) :
    (fun j => (kleinMatchingFeatureTable i j : ℝ)) ∈ kleinMatchingSpace := by
  let m := fourMatchingCoordinatesOfValues (R := ℤ) (kleinMatchingFeatureTable i)
  refine ⟨fun k => (m k : ℝ), ?_⟩
  funext j
  change fourMatchingEvaluation (fun k => (m k : ℝ)) j = _
  rw [matchingEvaluation_map_int]
  exact congrArg (Int.cast : ℤ → ℝ) (feature_eval_int i j)

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

private theorem kleinSign_from_bool {s : ℝ} (hs : s = 1 ∨ s = -1) :
    ∃ positive : Bool, s = if positive then 1 else -1 := by
  rcases hs with rfl | rfl
  · exact ⟨true, rfl⟩
  · exact ⟨false, rfl⟩

private theorem halfInteger_sq {n : ℤ} (hn : n = 0 ∨ n = 2) :
    ((n : ℝ) / 2) ^ 2 = (n : ℝ) / 2 := by
  rcases hn with rfl | rfl <;> norm_num

set_option maxRecDepth 4096 in
theorem kleinOrdinaryPlus_sq (i : Fin 3) (j : Fin 24) (s : ℝ) (hs : s = 1 ∨ s = -1) :
    kleinOrdinaryPlus i s j ^ 2 = kleinOrdinaryPlus i s j := by
  let numerator (positive : Bool) (k : Fin 3) (p : Fin 24) : ℤ :=
    kleinMatchingFeatureTable (Fin.castAdd 6 k.succ) p +
      (if positive then 1 else -1) * kleinMatchingFeatureTable (Fin.natAdd 4 (Fin.castAdd 3 k)) p
  have htable : ∀ positive k p, numerator positive k p = 0 ∨ numerator positive k p = 2 := by
    intro positive k
    cases positive <;> fin_cases k <;> dsimp only [numerator] <;> decide +kernel
  obtain ⟨positive, rfl⟩ := kleinSign_from_bool hs
  have hvalue : kleinOrdinaryPlus i (if positive then 1 else -1) j =
      (numerator positive i j : ℝ) / 2 := by
    cases positive <;> simp [kleinOrdinaryPlus, kleinFaceIndicator, kleinFaceSignPlus, numerator]
  rw [hvalue]
  exact halfInteger_sq (htable positive i j)

set_option maxRecDepth 4096 in
theorem kleinOrdinaryMinus_sq (i : Fin 3) (j : Fin 24) (s : ℝ) (hs : s = 1 ∨ s = -1) :
    kleinOrdinaryMinus i s j ^ 2 = kleinOrdinaryMinus i s j := by
  let numerator (positive : Bool) (k : Fin 3) (p : Fin 24) : ℤ :=
    kleinMatchingFeatureTable (Fin.castAdd 6 k.succ) p - kleinMatchingFeatureTable 0 p +
      (if positive then 1 else -1) * kleinMatchingFeatureTable (Fin.natAdd 7 k) p
  have htable : ∀ positive k p, numerator positive k p = 0 ∨ numerator positive k p = 2 := by
    intro positive k
    cases positive <;> fin_cases k <;> dsimp only [numerator] <;> decide +kernel
  obtain ⟨positive, rfl⟩ := kleinSign_from_bool hs
  have hvalue : kleinOrdinaryMinus i (if positive then 1 else -1) j =
      (numerator positive i j : ℝ) / 2 := by
    cases positive <;>
      simp [kleinOrdinaryMinus, kleinFaceIndicator, kleinFaceSignMinus, kleinCycle, numerator]
  rw [hvalue]
  exact halfInteger_sq (htable positive i j)

private def rectangleIndex (i : Fin 3) (s t : Bool) : Fin 24 :=
  if s then (if t then ![2, 5, 1] i else ![13, 9, 22] i)
  else (if t then ![10, 18, 17] i else ![21, 14, 6] i)

private def signOfBool (s : Bool) : ℝ := if s then 1 else -1

set_option maxRecDepth 4096 in
private theorem rectangleFeature_values (i k : Fin 3) (s t : Bool) :
    let j := rectangleIndex i s t
    kleinMatchingFeatureTable 0 j = 0 ∧
      kleinMatchingFeatureTable (Fin.castAdd 6 k.succ) j = (if k = i then 1 else 0) ∧
      kleinMatchingFeatureTable (Fin.natAdd 4 (Fin.castAdd 3 k)) j =
        (if k = i then (if s then 1 else -1) else 0) ∧
      kleinMatchingFeatureTable (Fin.natAdd 7 k) j =
        (if k = i then (if t then 1 else -1) else 0) := by
  revert i k s t
  decide +kernel

theorem kleinMatchingCost_rectangle (β p q : Fin 3 → ℝ) (cNeg : ℝ)
    (h : ∀ j, 0 ≤ kleinMatchingCost β p q cNeg j) (i : Fin 3) :
    |p i| + |q i| ≤ β i := by
  have he (s t : Bool) : kleinMatchingCost β p q cNeg (rectangleIndex i s t) =
      β i + signOfBool s * p i + signOfBool t * q i := by
    have hcycle := (rectangleFeature_values i i s t).1
    simp only [kleinMatchingCost, kleinCycle, hcycle, Int.cast_zero, mul_zero, zero_add]
    calc
      _ = ∑ k : Fin 3, if k = i then β k + signOfBool s * p k + signOfBool t * q k else 0 := by
        refine Finset.sum_congr rfl fun k _ => ?_
        obtain ⟨hind, hplus, hminus⟩ := (rectangleFeature_values i k s t).2
        simp only [kleinFaceIndicator, kleinFaceSignPlus, kleinFaceSignMinus, hind, hplus, hminus]
        by_cases hk : k = i
        · cases s <;> cases t <;> simp [hk, signOfBool]
        · simp [hk]
      _ = _ := by simp
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
