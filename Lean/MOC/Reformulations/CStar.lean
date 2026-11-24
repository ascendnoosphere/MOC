import MOC.Reformulations.Common
import MOC.Normal

open BigOperators Matrix

namespace MOC.Reformulations.CStar

/-- C★ 1, stated for arbitrary normal matrices and their characteristic roots. -/
def MatrixForm : Prop := ∀ n, NormalConjecture (Fin n)

theorem matrixForm_iff : MatrixForm ↔ MOCIsTrue :=
  ⟨fun h n => conjecture_iff_normalConjecture.mpr (h n),
    fun h n => conjecture_iff_normalConjecture.mp (h n)⟩

/-- C★ 2: the target matrix may be any normal matrix with the prescribed
characteristic roots, without supplying a conjugating unitary. -/
def OrbitForm : Prop :=
  ∀ (n : ℕ) (A B Y : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n → ℂ),
    IsStarNormal A → IsStarNormal B → IsStarNormal Y →
    A.charpoly.roots = (Finset.univ : Finset (Fin n)).val.map a →
    B.charpoly.roots = (Finset.univ : Finset (Fin n)).val.map b →
    Y.charpoly.roots = B.charpoly.roots →
    (A + Y).det ∈ convexHull ℝ (Set.range (matchingProduct a b))

theorem orbitForm_iff : OrbitForm ↔ MOCIsTrue := by
  rw [← matrixForm_iff]
  constructor
  · intro h n A B a b hA hB ha hb
    exact h n A B B a b hA hB hB ha hb rfl
  · intro h n A B Y a b hA _ hY ha hb hYB
    exact h n A Y a b hA hY ha (hYB.trans hb)

/-- C★ 5 in the joint eigenbases of the two self-adjoint pairs. The four
lists are real; the two parts of each pair use the same spectral labels. -/
def CartesianForm : Prop :=
  ∀ (n : ℕ) (a₁ a₂ b₁ b₂ : Fin n → ℝ) (U : Matrix (Fin n) (Fin n) ℂ),
    IsUnitary U →
    Holds (fun i => (a₁ i : ℂ) + (a₂ i : ℂ) * Complex.I)
      (fun i => (b₁ i : ℂ) + (b₂ i : ℂ) * Complex.I) U

theorem cartesianForm_iff : CartesianForm ↔ MOCIsTrue := by
  constructor
  · intro h n a b U hU
    simpa only [Complex.re_add_im] using h n
      (fun i => (a i).re) (fun i => (a i).im)
      (fun i => (b i).re) (fun i => (b i).im) U hU
  · intro h n a₁ a₂ b₁ b₂ U hU
    exact h n _ _ U hU

theorem determinantValue_affine {n : ℕ} (a b : Fin n → ℂ) (s t z : ℂ)
    (U : Matrix (Fin n) (Fin n) ℂ) :
    determinantValue (fun i => s * a i + z) (fun i => t * b i) U =
      (s • diagonal a + t • (U * diagonal b * Uᴴ) + z • 1).det := by
  have h₁ : diagonal (fun i => s * a i + z) =
      s • diagonal a + z • (1 : Matrix (Fin n) (Fin n) ℂ) := by
    ext i j
    by_cases h : i = j
    · subst j
      simp [smul_eq_mul]
    · simp [Matrix.diagonal_apply_ne _ h, Matrix.one_apply_ne h]
  have h₂ : diagonal (fun i => t * b i) = t • diagonal b :=
    Matrix.diagonal_smul t b
  unfold determinantValue
  rw [h₁, h₂, Matrix.mul_smul, Matrix.smul_mul]
  abel_nf

/-- C★ 6: genuine functions on spectral values, not on occurrence labels. -/
def FunctionalCalculusForm : Prop :=
  ∀ (n : ℕ) (a b : Fin n → ℂ) (f g : ℂ → ℂ)
    (U : Matrix (Fin n) (Fin n) ℂ), IsUnitary U → Holds (f ∘ a) (g ∘ b) U

theorem functionalCalculusForm_iff : FunctionalCalculusForm ↔ MOCIsTrue :=
  ⟨fun h n a b U hU => h n a b id id U hU,
    fun h n a b f g U hU => h n (f ∘ a) (g ∘ b) U hU⟩

/-- C★ 7: the hull is pointwise in the scalar parameters. -/
def AffineForm : Prop :=
  ∀ (n : ℕ) (a b : Fin n → ℂ) (s t z : ℂ)
    (U : Matrix (Fin n) (Fin n) ℂ), IsUnitary U →
    Holds (fun i => s * a i + z) (fun i => t * b i) U

theorem affineForm_iff : AffineForm ↔ MOCIsTrue := by
  constructor
  · intro h n a b U hU
    simpa only [one_mul, add_zero] using h n a b 1 1 0 U hU
  · intro h n a b s t z U hU
    exact h n _ _ U hU

/-- A pointwise characteristic determinant. This does not assert one law for
all coefficients or all values of the scalar parameter. -/
def PointwiseCharacteristicForm : Prop :=
  ∀ (n : ℕ) (a b : Fin n → ℂ) (z : ℂ) (U : Matrix (Fin n) (Fin n) ℂ),
    IsUnitary U → Holds (fun i => z - a i) (fun i => -b i) U

theorem pointwiseCharacteristicForm_iff : PointwiseCharacteristicForm ↔ MOCIsTrue := by
  constructor
  · intro h n a b U hU
    simpa only [zero_sub, neg_neg] using h n (fun i => -a i) (fun i => -b i) 0 U hU
  · intro h n a b z U hU
    exact h n _ _ U hU

/-- Comparison with the laws of nonnegative weights for a fixed spectral
instance. Weights are allowed to depend on both spectra and the mixer. -/
def ScalarWeightForm : Prop :=
  ∀ (n : ℕ) (a b : Fin n → ℂ) (U : Matrix (Fin n) (Fin n) ℂ), IsUnitary U →
    ∃ w : Equiv.Perm (Fin n) → ℝ, (∀ p, 0 ≤ w p) ∧
      (∑ p, w p) = 1 ∧
      (∑ p, (w p : ℂ) * matchingProduct a b p) = determinantValue a b U

theorem scalarWeightForm_iff : ScalarWeightForm ↔ MOCIsTrue := by
  classical
  constructor
  · intro h n a b U hU
    obtain ⟨w, hw, hs, hv⟩ := h n a b U hU
    exact holds_of_weights w hw hs hv
  · intro h n a b U hU
    obtain ⟨κ, _, v, q, hv, hvsum, hq, hsum⟩ :=
      mem_convexHull_iff_exists_fintype.mp (h n a b U hU)
    choose p hp using hq
    let w (σ : Equiv.Perm (Fin n)) : ℝ := ∑ j : κ, if p j = σ then v j else 0
    have hw (σ : Equiv.Perm (Fin n)) : 0 ≤ w σ :=
      Finset.sum_nonneg (fun j _ => by split <;> simp [hv j])
    have hs : (∑ σ, w σ) = 1 := by
      simp only [w]
      rw [Finset.sum_comm]
      rw [← hvsum]
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.sum_eq_single (p j)]
      · simp
      · intro σ _ hσ
        simp [Ne.symm hσ]
      · simp
    refine ⟨w, hw, hs, ?_⟩
    simp only [w, Complex.ofReal_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    convert hsum using 1
    apply Finset.sum_congr rfl
    intro j _
    simp only [apply_ite Complex.ofReal, Complex.ofReal_zero, ite_mul, zero_mul,
      Complex.real_smul]
    rw [Finset.sum_eq_single (p j)]
    · simp [hp j]
    · intro σ _ hσ
      simp [Ne.symm hσ]
    · simp

theorem not_moc_of_not_scalarWeightForm (h : ¬ ScalarWeightForm) : ¬ MOCIsTrue :=
  fun hMOC => h (scalarWeightForm_iff.mpr hMOC)

end MOC.Reformulations.CStar
