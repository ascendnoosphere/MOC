import MOC.Reformulations.Common
import MOC.Normal
import Mathlib.MeasureTheory.Measure.Dirac

/-!
# Native determinant statements for the second atlas range

A native comparison below is either a proved restriction on the actual finite
spectra, or an explicitly stated proposition whose relationship to MOC is
proved. No theorem asserts unrestricted MOC. See `SecondAtlas` for the common
labelled-evaluation layer.
-/

open BigOperators Matrix MeasureTheory Filter

namespace MOC.Reformulations

noncomputable section

/-- The invalid extension of Atlas 175 to arbitrary weighted adjacency
matrices. Loops and directed edges have independent complex weights;
without normality the hull inclusion need not hold. -/
def ArbitraryAdjacencyForm : Prop :=
  ∀ (n : ℕ) (A B : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n → ℂ),
    A.charpoly.roots = (Finset.univ : Finset (Fin n)).val.map a →
    B.charpoly.roots = (Finset.univ : Finset (Fin n)).val.map b →
    (A + B).det ∈ convexHull ℝ (Set.range (matchingProduct a b))

/-- Opposite single directed edges have zero spectral lists but their
sum has determinant minus one. This is not a disproof of MOC. -/
theorem not_arbitraryAdjacencyForm : ¬ ArbitraryAdjacencyForm := by
  intro h
  let A : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 0, 0]
  let B : Matrix (Fin 2) (Fin 2) ℂ := !![0, 0; 1, 0]
  let z : Fin 2 → ℂ := fun _ => 0
  have h01 : (0 : Fin 2) ≠ 1 := by decide
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  have hA : A.charpoly = Polynomial.X ^ 2 := by
    simp [Matrix.charpoly, Matrix.det_fin_two, Matrix.charmatrix_apply_eq,
      Matrix.charmatrix_apply_ne, A, h01, h10, pow_two]
  have hB : B.charpoly = Polynomial.X ^ 2 := by
    simp [Matrix.charpoly, Matrix.det_fin_two, Matrix.charmatrix_apply_eq,
      Matrix.charmatrix_apply_ne, B, h01, h10, pow_two]
  have hroots : ((Polynomial.X : Polynomial ℂ) ^ 2).roots =
      (Finset.univ : Finset (Fin 2)).val.map z := by
    rw [Polynomial.roots_X_pow]
    simp [Finset.univ_fin2, z, two_nsmul]
  have ha : A.charpoly.roots = (Finset.univ : Finset (Fin 2)).val.map z := by rwa [hA]
  have hb : B.charpoly.roots = (Finset.univ : Finset (Fin 2)).val.map z := by rwa [hB]
  have hh := h 2 A B z z ha hb
  have hp : matchingProduct z z = fun _ => 0 := by
    funext σ
    simp [matchingProduct, Fin.prod_univ_two, z]
  have hd : (A + B).det = -1 := by simp [A, B, Matrix.det_fin_two, Matrix.add_apply]
  rw [hp, Set.range_const, convexHull_singleton, Set.mem_singleton_iff, hd] at hh
  exact neg_ne_zero.mpr one_ne_zero hh

/-- Atlas 183: a probability law on perfect matchings of the two labelled parts.
The law is allowed to depend on both spectra. -/
def BipartiteMatchingForm : Prop :=
  ∀ (n : ℕ) (a b : Fin n → ℂ) (U : Matrix (Fin n) (Fin n) ℂ), IsUnitary U →
    ∃ w : Equiv.Perm (Fin n) → ℝ,
      (∀ σ, 0 ≤ w σ) ∧ (∑ σ, w σ = 1) ∧
      (∑ σ, (w σ : ℂ) * ∏ j, (a (σ j) + b j)) =
        (diagonal a + U * diagonal b * Uᴴ).det

theorem bipartiteMatchingForm_iff : BipartiteMatchingForm ↔ MOCIsTrue := by
  classical
  constructor
  · intro h n a b U hU
    obtain ⟨w, hw, hs, hv⟩ := h n a b U hU
    exact holds_of_weights w hw hs hv
  · intro h n a b U hU
    have hv := h n a b U hU
    unfold Holds at hv
    rw [convexHull_range_eq_exists_affineCombination] at hv
    obtain ⟨s, w, hw, hs, hv⟩ := hv
    let W : Equiv.Perm (Fin n) → ℝ := fun σ => if σ ∈ s then w σ else 0
    refine ⟨W, fun σ => ?_, ?_, ?_⟩
    · by_cases hσ : σ ∈ s
      · simpa [W, hσ] using hw σ hσ
      · simp [W, hσ]
    · unfold W
      rw [← Finset.sum_filter]
      simpa using hs
    · rw [Finset.affineCombination_eq_linear_combination _ _ _ hs] at hv
      change (∑ σ ∈ s, w σ • matchingProduct a b σ) = _ at hv
      change (∑ σ, (W σ : ℂ) * matchingProduct a b σ) = determinantValue a b U
      simp only [Complex.real_smul] at hv
      simp only [W, apply_ite Complex.ofReal, Complex.ofReal_zero, ite_mul, zero_mul]
      rw [← Finset.sum_filter]
      simpa using hv

/-- The characteristic comparison at each parameter, used in Atlas 185 and 193.
This does not assert simultaneous weights on polynomial coefficients. -/
def PointwiseCharacteristicForm : Prop :=
  ∀ (n : ℕ) (a b : Fin n → ℂ) (U : Matrix (Fin n) (Fin n) ℂ) (z : ℂ),
    IsUnitary U →
    (z • (1 : Matrix (Fin n) (Fin n) ℂ) - (diagonal a + U * diagonal b * Uᴴ)).det ∈
      convexHull ℝ (Set.range (fun σ : Equiv.Perm (Fin n) =>
        ∏ j, (z - (a (σ j) + b j))))

private theorem pointwiseCharacteristic_iff_holds {n : ℕ} (a b : Fin n → ℂ)
    (U : Matrix (Fin n) (Fin n) ℂ) (z : ℂ) :
    (z • (1 : Matrix (Fin n) (Fin n) ℂ) - (diagonal a + U * diagonal b * Uᴴ)).det ∈
      convexHull ℝ (Set.range (fun σ : Equiv.Perm (Fin n) =>
        ∏ j, (z - (a (σ j) + b j)))) ↔
    Holds (fun j => z - a j) (fun j => -b j) U := by
  have hdiag : diagonal (fun j => z - a j) =
      z • (1 : Matrix (Fin n) (Fin n) ℂ) - diagonal a := by
    ext i j
    by_cases h : i = j <;> simp [Matrix.diagonal_apply, Matrix.one_apply, h]
  have hb : diagonal (fun j => -b j) = -diagonal b := by ext i j; by_cases h : i = j <;> simp [Matrix.diagonal_apply, h]
  have hp (σ : Equiv.Perm (Fin n)) :
      (∏ j, (z - (a (σ j) + b j))) = matchingProduct (fun j => z - a j) (fun j => -b j) σ := by
    unfold matchingProduct
    apply Finset.prod_congr rfl
    intro j _
    ring
  unfold Holds determinantValue
  rw [show (fun σ : Equiv.Perm (Fin n) => ∏ j, (z - (a (σ j) + b j))) =
    matchingProduct (fun j => z - a j) (fun j => -b j) by funext σ; exact hp σ]
  rw [hdiag, hb, Matrix.mul_neg, Matrix.neg_mul]
  rw [show z • (1 : Matrix (Fin n) (Fin n) ℂ) - (diagonal a + U * diagonal b * Uᴴ) =
      (z • (1 : Matrix (Fin n) (Fin n) ℂ) - diagonal a) + -(U * diagonal b * Uᴴ) by abel]

theorem pointwiseCharacteristicForm_iff : PointwiseCharacteristicForm ↔ MOCIsTrue := by
  constructor
  · intro h n a b U hU
    simpa using (pointwiseCharacteristic_iff_holds (-a) (-b) U 0).1
      (h n (-a) (-b) U 0 hU)
  · intro h n a b U z hU
    exact (pointwiseCharacteristic_iff_holds a b U z).2 (h n _ _ U hU)

/-- Atlas 190: finite reciprocal zeta determinants, with a separate comparison
at each scalar parameter. For Atlas 145 and 156 the same determinant identity
applies to an individual finite Euler factor at its specified parameter. -/
def FiniteEulerForm : Prop :=
  ∀ (n : ℕ) (a b : Fin n → ℂ) (U : Matrix (Fin n) (Fin n) ℂ) (z : ℂ),
    IsUnitary U →
    ((1 : Matrix (Fin n) (Fin n) ℂ) - z • (diagonal a + U * diagonal b * Uᴴ)).det ∈
      convexHull ℝ (Set.range (fun σ : Equiv.Perm (Fin n) =>
        ∏ j, (1 - z * (a (σ j) + b j))))

private theorem finiteEuler_iff_holds {n : ℕ} (a b : Fin n → ℂ)
    (U : Matrix (Fin n) (Fin n) ℂ) (z : ℂ) :
    ((1 : Matrix (Fin n) (Fin n) ℂ) - z • (diagonal a + U * diagonal b * Uᴴ)).det ∈
      convexHull ℝ (Set.range (fun σ : Equiv.Perm (Fin n) =>
        ∏ j, (1 - z * (a (σ j) + b j)))) ↔
    Holds (fun j => 1 - z * a j) (fun j => -(z * b j)) U := by
  have hdiag : diagonal (fun j => 1 - z * a j) =
      (1 : Matrix (Fin n) (Fin n) ℂ) - z • diagonal a := by
    ext i j
    by_cases h : i = j <;> simp [Matrix.diagonal_apply, Matrix.one_apply, h, smul_eq_mul]
  have hb : diagonal (fun j => -(z * b j)) = -(z • diagonal b) := by
    ext i j
    by_cases h : i = j <;> simp [Matrix.diagonal_apply, h, smul_eq_mul]
  have hp : (fun σ : Equiv.Perm (Fin n) => ∏ j, (1 - z * (a (σ j) + b j))) =
      matchingProduct (fun j => 1 - z * a j) (fun j => -(z * b j)) := by
    funext σ
    unfold matchingProduct
    apply Finset.prod_congr rfl
    intro j _
    ring
  have hm : (1 : Matrix (Fin n) (Fin n) ℂ) - z • (diagonal a + U * diagonal b * Uᴴ) =
      (1 - z • diagonal a) + -(z • (U * diagonal b * Uᴴ)) := by rw [smul_add]; abel
  unfold Holds determinantValue
  rw [hp, hdiag, hb, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_smul, Matrix.smul_mul, hm]

theorem finiteEulerForm_iff : FiniteEulerForm ↔ MOCIsTrue := by
  constructor
  · intro h n a b U hU
    have hs := h n (fun j => 1 - a j) (fun j => -b j) U 1 hU
    have hr := (finiteEuler_iff_holds (fun j => 1 - a j) (fun j => -b j) U 1).1 hs
    have ha : (fun j => 1 - 1 * (1 - a j)) = a := by funext j; ring
    have hb : (fun j => -(1 * -b j)) = b := by funext j; ring
    rwa [ha, hb] at hr
  · intro h n a b U z hU
    exact (finiteEuler_iff_holds a b U z).2 (h n _ _ U hU)

/-- The finite Euler determinant at a fixed parameter on nonzero spectral
lists, as in the diagonal realization of Atlas 145 and 156. -/
def FixedEulerParameterForm (z : ℂ) : Prop :=
  ∀ (n : ℕ) (a b : Fin n → ℂ) (U : Matrix (Fin n) (Fin n) ℂ),
    IsUnitary U → (∀ i, a i ≠ 0) → (∀ j, b j ≠ 0) →
    ((1 : Matrix (Fin n) (Fin n) ℂ) - z • (diagonal a + U * diagonal b * Uᴴ)).det ∈
      convexHull ℝ (Set.range (fun σ : Equiv.Perm (Fin n) =>
        ∏ j, (1 - z * (a (σ j) + b j))))

/-- Even one fixed nonzero characteristic parameter suffices. Opposite
spectral shifts avoid the finitely many zero coordinates exactly. -/
theorem fixedEulerParameterForm_iff {z : ℂ} (hz : z ≠ 0) :
    FixedEulerParameterForm z ↔ MOCIsTrue := by
  constructor
  · intro h n x y U hU
    have hf : (Set.range (fun i => 1 - x i) ∪ Set.range y).Finite :=
      (Set.finite_range _).union (Set.finite_range _)
    obtain ⟨t, _, ht⟩ := Set.infinite_univ.exists_not_mem_finite hf
    let a (i : Fin n) := (1 - (x i + t)) / z
    let b (j : Fin n) := -(y j - t) / z
    have ha : ∀ i, a i ≠ 0 := by
      intro i hi
      have hi' : 1 - (x i + t) = 0 := (div_eq_zero_iff.mp hi).resolve_right hz
      have he : 1 - x i = t := calc
        1 - x i = (1 - (x i + t)) + t := by ring
        _ = t := by rw [hi', zero_add]
      exact ht (Or.inl ⟨i, he⟩)
    have hb : ∀ j, b j ≠ 0 := by
      intro j hj
      have hj' : -(y j - t) = 0 := (div_eq_zero_iff.mp hj).resolve_right hz
      exact ht (Or.inr ⟨j, sub_eq_zero.mp (neg_eq_zero.mp hj')⟩)
    have hfa : (fun i => 1 - z * a i) = fun i => x i + t := by
      funext i
      dsimp [a]
      field_simp [hz]
    have hfb : (fun i => -(z * b i)) = fun i => y i - t := by
      funext i
      dsimp [b]
      field_simp [hz]
    have hh := (finiteEuler_iff_holds a b U z).1 (h n a b U hU ha hb)
    rw [hfa, hfb] at hh
    exact (holds_shift_iff x y hU t).mp hh
  · intro h n a b U hU _ _
    exact (finiteEuler_iff_holds a b U z).2 (h n _ _ U hU)

/-- Atlas 195: products of arbitrary finite words whose products are normal.
The root lists count algebraic multiplicity. -/
def NormalWordProductForm : Prop :=
  ∀ (n : ℕ) (xs ys : List (Matrix (Fin n) (Fin n) ℂ)) (a b : Fin n → ℂ),
    IsStarNormal xs.prod → IsStarNormal ys.prod →
    xs.prod.charpoly.roots = (Finset.univ : Finset (Fin n)).val.map a →
    ys.prod.charpoly.roots = (Finset.univ : Finset (Fin n)).val.map b →
    (xs.prod + ys.prod).det ∈ convexHull ℝ (Set.range (matchingProduct a b))

theorem normalWordProductForm_iff : NormalWordProductForm ↔ MOCIsTrue := by
  constructor
  · intro h n
    apply conjecture_iff_normalConjecture.mpr
    intro A B a b hA hB ha hb
    have hr := h n [A] [B] a b (by simpa using hA) (by simpa using hB)
      (by simpa using ha) (by simpa using hb)
    simpa using hr
  · intro h n xs ys a b hx hy ha hb
    exact conjecture_iff_normalConjecture.mp (h n) xs.prod ys.prod a b hx hy ha hb

/-- Atlas 206, with samples expressed in normal spectral coordinates. No independence
condition on the two spectra or the mixer is necessary. -/
def AlmostSureSpectralForm : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (n : ℕ) (a b : Ω → Fin n → ℂ) (U : Ω → Matrix (Fin n) (Fin n) ℂ),
    (∀ᵐ x ∂μ, IsUnitary (U x)) → ∀ᵐ x ∂μ, Holds (a x) (b x) (U x)

theorem almostSureSpectralForm_iff : AlmostSureSpectralForm ↔ MOCIsTrue := by
  constructor
  · intro h n a b U hU
    letI : MeasurableSpace Unit := ⊤
    letI : MeasurableSingletonClass Unit := ⟨fun _ => trivial⟩
    have hh := h Unit (Measure.dirac ()) n (fun _ => a) (fun _ => b) (fun _ => U)
      (Filter.Eventually.of_forall fun _ => hU)
    rwa [ae_dirac_eq, Filter.eventually_pure] at hh
  · intro h Ω _ μ _ n a b U hU
    exact hU.mono fun x hx => h n (a x) (b x) (U x) hx

/-- Atlas 243: the determinant of each scalar projection of two jointly
diagonalized normal tuples. No shared probability law across projections is required. -/
def JointTupleProjectionForm : Prop :=
  ∀ (n r : ℕ) (a b : Fin n → Fin r → ℂ) (c : Fin r → ℂ)
    (U : Matrix (Fin n) (Fin n) ℂ), IsUnitary U →
    Holds (fun j => ∑ k, c k * a j k) (fun j => ∑ k, c k * b j k) U

theorem jointTupleProjectionForm_iff : JointTupleProjectionForm ↔ MOCIsTrue := by
  constructor
  · intro h n a b U hU
    simpa [Fin.sum_univ_one] using h n 1 (fun j _ => a j) (fun j _ => b j)
      (fun _ => 1) U hU
  · intro h n r a b c U hU
    exact h n _ _ U hU

end

end MOC.Reformulations
