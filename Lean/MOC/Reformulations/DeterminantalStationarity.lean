import MOC.ComplexTiedSwap
import MOC.OrderFourSecondVariation
import MOC.Singular

/-! First and second variation tests for the support maximum of a
unitary determinant orbit in each finite order. -/

open Matrix

namespace MOC.Reformulations

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The determinant-scaled adjugate commutator is Hermitian at a
stationary candidate. This expression is defined for singular sums. -/
def DeterminantAdjugateStationary (A B : Matrix ι ι ℂ) (η : ℂ) : Prop :=
  let C := A + B
  (η • (B * C.adjugate - C.adjugate * B)).IsHermitian

private theorem adjugate_stationary_of_maximum (a : ι → ℂ) (B : Matrix ι ι ℂ) (η : ℂ)
    (hmax : ∀ R : Matrix ι ι ℂ, IsUnitary R →
      (η * (R * diagonal a * Rᴴ + B).det).re ≤ (η * (diagonal a + B).det).re) :
    DeterminantAdjugateStationary (diagonal a) B η := by
  let A := diagonal a
  let C := A + B
  let T := η • (A * C.adjugate - C.adjugate * A)
  have hentry (i j : ι) : T i j = (η * (a i - a j)) * C.adjugate i j := by
    simp only [T, A, Matrix.smul_apply, smul_eq_mul, Matrix.sub_apply,
      Matrix.diagonal_mul, Matrix.mul_diagonal]
    ring
  have hT : Tᴴ = T := by
    ext i j : 1
    rw [Matrix.conjTranspose_apply, hentry, hentry]
    by_cases hij : i = j
    · subst j
      simp
    · have he := adjugate_cross_of_complex_diagonal_support_max a B η hij hmax
      change (η * (a i - a j)) * C.adjugate i j +
        star ((η * (a i - a j)) * C.adjugate j i) = 0 at he
      rw [show a j - a i = -(a i - a j) by ring, mul_neg, neg_mul, star_neg]
      linear_combination -he
  have he : η • (B * C.adjugate - C.adjugate * B) = -T := by
    change _ = -(η • (A * C.adjugate - C.adjugate * A))
    rw [← smul_neg, neg_sub]
    have hB : B = C - A := by dsimp [C]; abel
    rw [hB, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_adjugate, Matrix.adjugate_mul]
    congr 1
    abel
  change (η • (B * C.adjugate - C.adjugate * B))ᴴ = _
  rw [he, Matrix.conjTranspose_neg, hT]

private theorem adjugate_stationary_of_spectral_maximum (a b : ι → ℂ)
    (U : Matrix ι ι ℂ) (hU : IsUnitary U) (η : ℂ)
    (hmax : ∀ V : Matrix ι ι ℂ, IsUnitary V →
      (η * determinantValue a b V).re ≤ (η * determinantValue a b U).re) :
    DeterminantAdjugateStationary (diagonal a) (U * diagonal b * Uᴴ) η := by
  apply adjugate_stationary_of_maximum
  intro R hR
  rw [determinantValue_relative a b R U hR]
  exact hmax _ (relative_unitary R U hR hU)

/-- It suffices to compare the support value at every stationary unitary
candidate with the largest permutation projection. -/
theorem conjecture_iff_adjugate_stationary_bound : Conjecture ι ↔
    ∀ (a b : ι → ℂ) (U : Matrix ι ι ℂ) (η : ℂ), IsUnitary U →
      DeterminantAdjugateStationary (diagonal a) (U * diagonal b * Uᴴ) η →
      ∃ p : Equiv.Perm ι, (η * determinantValue a b U).re ≤ (η * matchingProduct a b p).re := by
  constructor
  · intro h a b U η hU _
    exact (holds_iff_directional a b U).mp (h a b U hU) η
  · intro h a b U hU
    apply (holds_iff_directional a b U).mpr
    intro η
    obtain ⟨V, hV, hmax⟩ := exists_support_maximizer a b η
    obtain ⟨p, hp⟩ := h a b V η hV (adjugate_stationary_of_spectral_maximum a b V hV η hmax)
    exact ⟨p, (hmax U hU).trans hp⟩

/-- The second derivative of the support at a nonsingular candidate in a
skew-Hermitian conjugation direction. -/
def DeterminantOrbitHessianNonpositive (A B : Matrix ι ι ℂ) (η : ℂ) : Prop :=
  ∀ K : Matrix ι ι ℂ, Kᴴ = -K →
    let C := A + B
    let L := K * B - B * K
    let D := C⁻¹ * L
    (η * C.det *
      ((C⁻¹ * (K * L - L * K)).trace + D.trace ^ 2 - (D * D).trace)).re ≤ 0

private theorem hessian_nonpositive_of_spectral_maximum (a b : ι → ℂ)
    (U : Matrix ι ι ℂ) (hU : IsUnitary U) (η : ℂ) (hdet : determinantValue a b U ≠ 0)
    (hmax : ∀ V : Matrix ι ι ℂ, IsUnitary V →
      (η * determinantValue a b V).re ≤ (η * determinantValue a b U).re) :
    DeterminantOrbitHessianNonpositive (diagonal a) (U * diagonal b * Uᴴ) η := by
  intro K hK
  refine determinant_orbit_hessian_nonpos _ _ η hdet ?_ K hK
  intro R hR
  have hR' : IsUnitary Rᴴ := by
    simpa only [IsUnitary, Matrix.conjTranspose_conjTranspose] using And.intro hR.2 hR.1
  have hu : IsUnitary (R * U) := by
    simpa only [Matrix.conjTranspose_conjTranspose] using relative_unitary Rᴴ U hR' hU
  simpa only [determinantValue, Matrix.conjTranspose_mul, Matrix.mul_assoc] using hmax (R * U) hu

/-- Nonsingular stationary candidates with nonpositive second variation
suffice for the conjecture. Singular sums satisfy the inclusion directly. -/
theorem conjecture_iff_second_order_stationary_bound : Conjecture ι ↔
    ∀ (a b : ι → ℂ) (U : Matrix ι ι ℂ) (η : ℂ), IsUnitary U →
      determinantValue a b U ≠ 0 →
      DeterminantAdjugateStationary (diagonal a) (U * diagonal b * Uᴴ) η →
      DeterminantOrbitHessianNonpositive (diagonal a) (U * diagonal b * Uᴴ) η →
      ∃ p : Equiv.Perm ι, (η * determinantValue a b U).re ≤ (η * matchingProduct a b p).re := by
  constructor
  · intro h a b U η hU _ _ _
    exact (holds_iff_directional a b U).mp (h a b U hU) η
  · intro h a b U hU
    apply (holds_iff_directional a b U).mpr
    intro η
    obtain ⟨V, hV, hmax⟩ := exists_support_maximizer a b η
    have hbound : ∃ p : Equiv.Perm ι,
        (η * determinantValue a b V).re ≤ (η * matchingProduct a b p).re := by
      by_cases hv : determinantValue a b V = 0
      · exact (holds_iff_directional a b V).mp (holds_of_singular a b hV hv) η
      · exact h a b V η hV hv (adjugate_stationary_of_spectral_maximum a b V hV η hmax)
          (hessian_nonpositive_of_spectral_maximum a b V hV η hv hmax)
    obtain ⟨p, hp⟩ := hbound
    exact ⟨p, (hmax U hU).trans hp⟩

end
end MOC.Reformulations
