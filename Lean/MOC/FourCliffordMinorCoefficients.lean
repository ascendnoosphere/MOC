import MOC.FourCliffordSubsetFrame
import MOC.SparsePolynomialCertificate

/-! The one-, two- and three-column coefficients used by the order-four moment. -/

open Matrix BigOperators

namespace MOC.FourCliffordFrame

def columnGeneratorMask (i : Fin 4) : Fin 16 := ⟨2 ^ i.val, by decide +revert⟩

theorem columnGeneratorMask_eq : ∀ i : Fin 4,
    columnGeneratorMask i = (![1,2,4,8] : Fin 4 → Fin 16) i := by decide +kernel

private theorem generator_eq_local (O : Matrix (Fin 4) (Fin 4) ℝ) (j : Fin 4) :
    generator O j = ∑ i, O i j • blade (columnGeneratorMask i) := rfl

def twoMinor (O : Matrix (Fin 4) (Fin 4) ℝ) (a b i j : Fin 4) : ℝ :=
  O a i * O b j - O b i * O a j

def twoGeneratorCoefficients (O : Matrix (Fin 4) (Fin 4) ℝ) (i j : Fin 4) : Fin 16 → ℝ :=
  ![(Oᵀ * O) i j, 0, 0, twoMinor O 0 1 i j, 0, twoMinor O 0 2 i j, twoMinor O 1 2 i j, 0,
     0, twoMinor O 0 3 i j, twoMinor O 1 3 i j, 0, twoMinor O 2 3 i j, 0, 0, 0]

private def generatorPairMask : Fin 4 → Fin 4 → Fin 16 :=
  ![![0, 3, 5, 9], ![3, 0, 6, 10], ![5, 6, 0, 12], ![9, 10, 12, 0]]

private def generatorPairSign : Fin 4 → Fin 4 → ℤ :=
  ![![1, 1, 1, 1], ![-1, 1, 1, 1], ![-1, -1, 1, 1], ![-1, -1, -1, 1]]

private theorem generatorPairMask_eq : ∀ i j, xorMask (columnGeneratorMask i) (columnGeneratorMask j) =
    generatorPairMask i j := by decide +kernel

private theorem generatorPairSign_eq : ∀ i j, sign (columnGeneratorMask i) (columnGeneratorMask j) =
    generatorPairSign i j := by decide +kernel

private def generatorTripleMask : Fin 4 → Fin 4 → Fin 4 → Fin 16 :=
  ![![![1, 2, 4, 8], ![2, 1, 7, 11], ![4, 7, 1, 13], ![8, 11, 13, 1]], ![![2, 1, 7, 11], ![1, 2, 4, 8], ![7, 4, 2, 14], ![11, 8, 14, 2]], ![![4, 7, 1, 13], ![7, 4, 2, 14], ![1, 2, 4, 8], ![13, 14, 8, 4]], ![![8, 11, 13, 1], ![11, 8, 14, 2], ![13, 14, 8, 4], ![1, 2, 4, 8]]]

private def generatorTripleSign : Fin 4 → Fin 4 → Fin 4 → ℤ :=
  ![![![1, 1, 1, 1], ![-1, 1, 1, 1], ![-1, -1, 1, 1], ![-1, -1, -1, 1]], ![![-1, 1, 1, 1], ![1, 1, 1, 1], ![1, -1, 1, 1], ![1, -1, -1, 1]], ![![-1, -1, 1, 1], ![1, -1, 1, 1], ![1, 1, 1, 1], ![1, 1, -1, 1]], ![![-1, -1, -1, 1], ![1, -1, -1, 1], ![1, 1, -1, 1], ![1, 1, 1, 1]]]

private theorem generatorTripleMask_eq : ∀ i j k, xorMask (generatorPairMask i j) (columnGeneratorMask k) =
    generatorTripleMask i j k := by decide +kernel

private theorem generatorTripleSign_eq : ∀ i j k, sign (generatorPairMask i j) (columnGeneratorMask k) =
    generatorTripleSign i j k := by decide +kernel

def threeMinor (O : Matrix (Fin 4) (Fin 4) ℝ) (a b c i j k : Fin 4) : ℝ :=
  O a i * twoMinor O b c j k - O a j * twoMinor O b c i k + O a k * twoMinor O b c i j

def threeGeneratorCoefficients (O : Matrix (Fin 4) (Fin 4) ℝ) (i j k : Fin 4) : Fin 16 → ℝ :=
  let g := Oᵀ * O
  let contraction := fun a => O a i * g j k - O a j * g i k + O a k * g i j
  ![0, contraction 0, contraction 1, 0, contraction 2, 0, 0, threeMinor O 0 1 2 i j k,
    contraction 3, 0, 0, threeMinor O 0 1 3 i j k, 0, threeMinor O 0 2 3 i j k,
      threeMinor O 1 2 3 i j k, 0]

open SparsePolynomialCertificate

private abbrev ColumnPolynomial := SparsePolynomialCertificate.Polynomial 12

private def columnVariable (k : Fin 3) (a : Fin 4) : ColumnPolynomial :=
  indeterminate (finProdFinEquiv (k,a))

private def coeffPolynomial (c : ℤ) (p : ColumnPolynomial) : ColumnPolynomial :=
  mul (constant 12 c) p

private def productPairPolynomial (a : Fin 16) : ColumnPolynomial :=
  SparsePolynomialCertificate.sum fun j : Fin 4 => SparsePolynomialCertificate.sum fun i : Fin 4 =>
    if a = generatorPairMask i j then
      coeffPolynomial (generatorPairSign i j) (mul (columnVariable 0 i) (columnVariable 1 j))
    else []

private def productTriplePolynomial (a : Fin 16) : ColumnPolynomial :=
  SparsePolynomialCertificate.sum fun k : Fin 4 => SparsePolynomialCertificate.sum fun j : Fin 4 =>
    SparsePolynomialCertificate.sum fun i : Fin 4 =>
      if a = generatorTripleMask i j k then
        coeffPolynomial (generatorPairSign i j * generatorTripleSign i j k)
          (mul (mul (columnVariable 0 i) (columnVariable 1 j)) (columnVariable 2 k))
      else []

private def polynomialContraction (k l : Fin 3) : ColumnPolynomial :=
  SparsePolynomialCertificate.sum fun a : Fin 4 => mul (columnVariable k a) (columnVariable l a)

private def polynomialMinorPair (a b : Fin 4) (k l : Fin 3) : ColumnPolynomial :=
  mul (columnVariable k a) (columnVariable l b) ++
    coeffPolynomial (-1) (mul (columnVariable k b) (columnVariable l a))

private def polynomialMinorTriple (a b c : Fin 4) : ColumnPolynomial :=
  mul (columnVariable 0 a) (polynomialMinorPair b c 1 2) ++
    coeffPolynomial (-1) (mul (columnVariable 1 a) (polynomialMinorPair b c 0 2)) ++
    mul (columnVariable 2 a) (polynomialMinorPair b c 0 1)

private def polynomialTripleContraction (a : Fin 4) : ColumnPolynomial :=
  mul (columnVariable 0 a) (polynomialContraction 1 2) ++
    coeffPolynomial (-1) (mul (columnVariable 1 a) (polynomialContraction 0 2)) ++
    mul (columnVariable 2 a) (polynomialContraction 0 1)

private def pairCoefficientsPolynomial : Fin 16 → ColumnPolynomial :=
  let m a b := polynomialMinorPair a b 0 1
  ![polynomialContraction 0 1, [], [], m 0 1, [], m 0 2, m 1 2, [],
    [], m 0 3, m 1 3, [], m 2 3, [], [], []]

private def tripleCoefficientsPolynomial : Fin 16 → ColumnPolynomial :=
  let m := polynomialMinorTriple
  let c := polynomialTripleContraction
  ![[], c 0, c 1, [], c 2, [], [], m 0 1 2, c 3, [], [], m 0 1 3, [], m 0 2 3, m 1 2 3, []]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem normalizedPair : ∀ a : Fin 16,
    (normalizedKeys (productPairPolynomial a) == normalizedKeys (pairCoefficientsPolynomial a)) = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem normalizedTriple : ∀ a : Fin 16,
    (normalizedKeys (productTriplePolynomial a) == normalizedKeys (tripleCoefficientsPolynomial a)) = true := by
  decide +kernel

private def columnPolynomialValues (O : Matrix (Fin 4) (Fin 4) ℝ) (b : Fin 3 → Fin 4) : Fin 12 → ℝ :=
  let e : Fin 3 × Fin 4 ≃ Fin 12 := finProdFinEquiv
  fun i => O (e.symm i).2 (b (e.symm i).1)

@[simp] private theorem evaluate_columnVariable (O : Matrix (Fin 4) (Fin 4) ℝ) (b : Fin 3 → Fin 4)
    (k : Fin 3) (a : Fin 4) : eval (columnPolynomialValues O b) (columnVariable k a) = O a (b k) := by
  simp [columnVariable, columnPolynomialValues]

@[simp] private theorem evaluate_contraction (O : Matrix (Fin 4) (Fin 4) ℝ) (b : Fin 3 → Fin 4)
    (k l : Fin 3) : eval (columnPolynomialValues O b) (polynomialContraction k l) =
      (Oᵀ * O) (b k) (b l) := by
  simp only [polynomialContraction, eval_sum, eval_mul, evaluate_columnVariable, Matrix.mul_apply,
    Matrix.transpose_apply]

@[simp] private theorem evaluate_polynomialMinorPair (O : Matrix (Fin 4) (Fin 4) ℝ)
    (b : Fin 3 → Fin 4) (a c : Fin 4) (k l : Fin 3) :
    eval (columnPolynomialValues O b) (polynomialMinorPair a c k l) = twoMinor O a c (b k) (b l) := by
  simp [polynomialMinorPair, coeffPolynomial, twoMinor, sub_eq_add_neg]

private theorem evaluate_pairCoefficients (O : Matrix (Fin 4) (Fin 4) ℝ) (i j : Fin 4) (a : Fin 16) :
    eval (columnPolynomialValues O ![i,j,j]) (pairCoefficientsPolynomial a) =
      twoGeneratorCoefficients O i j a := by
  fin_cases a <;> simp [pairCoefficientsPolynomial, twoGeneratorCoefficients, Matrix.cons_val]

private theorem evaluate_tripleCoefficients (O : Matrix (Fin 4) (Fin 4) ℝ) (i j k : Fin 4) (a : Fin 16) :
    eval (columnPolynomialValues O ![i,j,k]) (tripleCoefficientsPolynomial a) =
      threeGeneratorCoefficients O i j k a := by
  fin_cases a <;> simp [tripleCoefficientsPolynomial, threeGeneratorCoefficients, Matrix.cons_val,
    polynomialMinorTriple, polynomialTripleContraction, threeMinor, coeffPolynomial, sub_eq_add_neg] <;> ring

/-- The coefficients of two columns are their inner product and their two-minors. -/
theorem bladeCoefficient_generator_mul (O : Matrix (Fin 4) (Fin 4) ℝ) (i j : Fin 4)
    (a : Fin 16) : bladeCoefficient a (generator O i * generator O j) =
      twoGeneratorCoefficients O i j a := by
  rw [← evaluate_pairCoefficients O i j a,
    ← eval_eq_of_normalizedKeys_eq (columnPolynomialValues O ![i,j,j]) (normalizedPair a)]
  simp only [generator_eq_local, Matrix.sum_mul, Matrix.mul_sum, Matrix.smul_mul, Matrix.mul_smul,
    bladeCoefficient_sum, bladeCoefficient_smul, blade_mul, generatorPairMask_eq, generatorPairSign_eq,
    bladeCoefficient_blade, productPairPolynomial, eval_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro r _
  by_cases h : a = generatorPairMask r s <;>
    simp [h, coeffPolynomial, eval_mul, evaluate_columnVariable] <;> ring

/-- The coefficient of a product of three column generators is a three-minor
in grade three and a sum of contractions in grade one. -/
theorem bladeCoefficient_generator_mul_mul (O : Matrix (Fin 4) (Fin 4) ℝ) (i j k : Fin 4)
    (a : Fin 16) : bladeCoefficient a ((generator O i * generator O j) * generator O k) =
      threeGeneratorCoefficients O i j k a := by
  rw [← evaluate_tripleCoefficients O i j k a,
    ← eval_eq_of_normalizedKeys_eq (columnPolynomialValues O ![i,j,k]) (normalizedTriple a)]
  simp only [generator_eq_local, Matrix.sum_mul, Matrix.mul_sum, Matrix.smul_mul, Matrix.mul_smul,
    bladeCoefficient_sum, bladeCoefficient_smul, blade_mul, generatorPairMask_eq, generatorPairSign_eq,
    generatorTripleMask_eq, generatorTripleSign_eq, bladeCoefficient_blade, productTriplePolynomial,
    eval_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t _
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro r _
  by_cases h : a = generatorTripleMask r s t <;>
    simp [h, coeffPolynomial, eval_mul, evaluate_columnVariable] <;> ring

/-- The number of positions in a mask on the first three coordinates. -/
def smallMaskCard : Fin 8 → ℕ := ![0, 1, 1, 2, 1, 2, 2, 3]

theorem bladeCoefficient_generator (a : Fin 16) (O : Matrix (Fin 4) (Fin 4) ℝ) (j : Fin 4) :
    bladeCoefficient a (generator O j) =
      ∑ i, O i j * (if a = columnGeneratorMask i then 1 else 0) := by
  simp only [generator_eq_local, bladeCoefficient_sum, bladeCoefficient_smul, bladeCoefficient_blade]

theorem bladeCoefficient_one (a : Fin 16) :
    bladeCoefficient a 1 = if a = 0 then 1 else 0 := by
  rw [← blade_zero, bladeCoefficient_blade]

/-- For an orthonormal frame, the coefficient of a blade has the same degree
as the blade obtained from the column frame. -/
theorem smallFrame_coefficient_eq_zero_of_card_ne (O : Matrix (Fin 4) (Fin 4) ℝ)
    (hO : Oᵀ * O = 1) (a b : Fin 8) (h : smallMaskCard a ≠ smallMaskCard b) :
    bladeCoefficient (smallMask a) (smallFrame O b) = 0 := by
  fin_cases a <;> fin_cases b <;>
    simp (disch := decide) [Matrix.cons_val, smallMaskCard, smallMask, smallFrame, bladeCoefficient_one,
      bladeCoefficient_generator, bladeCoefficient_generator_mul, bladeCoefficient_generator_mul_mul,
      twoGeneratorCoefficients, threeGeneratorCoefficients, Fin.sum_univ_four, columnGeneratorMask_eq, hO] at h ⊢

end MOC.FourCliffordFrame
