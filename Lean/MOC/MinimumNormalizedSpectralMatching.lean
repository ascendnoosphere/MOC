import MOC.SpectralDeterminantStability
import MOC.SpectralPolynomialTranslation

/-! Minimum-normalized stable squarefree polynomials and their matching test. -/

open BigOperators Finset

namespace MOC

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The value is nonzero when all entries of both spectra have positive
imaginary part. -/
def IsStableSpectralValue (c : SquarefreeClass ι) : Prop :=
  ∀ a b : ι → ℂ, (∀ i, 0 < (a i).im) → (∀ j, 0 < (b j).im) →
    squarefreeSpectralValue c a b ≠ 0

/-- The degree, multiaffinity and two lists are part of the evaluation.
Only coefficients in that degree enter the definition. -/
structure IsMinimumNormalizedSpectralValue (c : SquarefreeClass ι) : Prop where
  stable : IsStableSpectralValue c
  nonnegative : ∀ I J : Finset ι, Iᶜ.card = J.card →
    (c I J).im = 0 ∧ 0 ≤ (c I J).re
  leftEndpoint : c univ ∅ = 1
  rightEndpoint : c ∅ univ = 1
  normalized : squarefreeSpectralValue c (fun _ => 1) (fun _ => 1) = 2 ^ Fintype.card ι

/-- The squared-minor coefficient of the product on left indices `I`
and right indices `J`. The minor uses the complementary left index set. -/
def spectralMinorCoefficients (U : Matrix ι ι ℂ) : SquarefreeClass ι :=
  fun I J => subsetMinorSq U Iᶜ J

/-- Evaluation of the squared-minor coefficients gives the spectral determinant. -/
theorem squarefreeSpectralValue_spectralMinorCoefficients (U : Matrix ι ι ℂ)
    (hU : IsUnitary U) (a b : ι → ℂ) :
    squarefreeSpectralValue (spectralMinorCoefficients U) a b = determinantValue a b U := by
  classical
  let e : Equiv.Perm (Finset ι) :=
    ⟨(·ᶜ), (·ᶜ), compl_compl, compl_compl⟩
  rw [squarefreeSpectralValue, Finset.sum_comm, determinantValue_eq_sum_subsetMinors a b U hU]
  apply Finset.sum_congr rfl
  intro J _
  rw [← Equiv.sum_comp e
    (fun I => spectralMinorCoefficients U I J * squarefreeDividedDivisor a b I J)]
  apply Finset.sum_congr rfl
  intro I _
  change spectralMinorCoefficients U Iᶜ J * squarefreeDividedDivisor a b Iᶜ J = _
  by_cases hIJ : I.card = J.card
  · simp only [spectralMinorCoefficients, squarefreeDividedDivisor, compl_compl, if_pos hIJ]
  · simp only [spectralMinorCoefficients, squarefreeDividedDivisor, compl_compl,
      if_neg hIJ, subsetMinorSq, dif_neg hIJ, Complex.ofReal_zero, zero_mul]

private theorem subsetMinorSq_endpoints (U : Matrix ι ι ℂ) (hU : IsUnitary U) :
    (subsetMinorSq U ∅ ∅ : ℂ) = 1 ∧ (subsetMinorSq U univ univ : ℂ) = 1 := by
  classical
  have hmass := sum_signedWeight U (det_ne_zero_of_unitary hU)
  constructor
  · rw [← sum_signedWeight_image_eq_subsetMinorSq U hU,
      Finset.filter_true_of_mem (by intro σ _; simp)]
    exact hmass
  · rw [← sum_signedWeight_image_eq_subsetMinorSq U hU,
      Finset.filter_true_of_mem (fun σ _ => Finset.map_univ_equiv σ)]
    exact hmass

/-- Every unitary determinant belongs to the minimum-normalized stable class. -/
theorem spectralMinorCoefficients_isMinimumNormalized (U : Matrix ι ι ℂ)
    (hU : IsUnitary U) : IsMinimumNormalizedSpectralValue (spectralMinorCoefficients U) := by
  obtain ⟨hleft, hright⟩ := subsetMinorSq_endpoints U hU
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro a b ha hb
    rw [squarefreeSpectralValue_spectralMinorCoefficients U hU]
    exact determinantValue_ne_zero_of_im_pos a b U ha (fun j => (hb j).le)
  · intro I J _
    exact ⟨Complex.ofReal_im _, by
      simpa only [spectralMinorCoefficients, Complex.ofReal_re] using subsetMinorSq_nonneg U Iᶜ J⟩
  · simpa only [spectralMinorCoefficients, compl_univ] using hleft
  · simpa only [spectralMinorCoefficients, compl_empty] using hright
  · rw [squarefreeSpectralValue_spectralMinorCoefficients U hU, ← signed_determinant _ _ U hU]
    simp only [matchingProduct, Finset.prod_const, Finset.card_univ, one_add_one_eq_two,
      ← Finset.sum_mul, sum_signedWeight U (det_ne_zero_of_unitary hU), one_mul]

/-- The proposed hull inclusion for the entire minimum-normalized stable class. -/
def MinimumNormalizedSpectralMatching (ι : Type*) [Fintype ι] [DecidableEq ι] : Prop :=
  ∀ c : SquarefreeClass ι, IsMinimumNormalizedSpectralValue c →
    ∀ a b : ι → ℂ, squarefreeSpectralValue c a b ∈
      convexHull ℝ (Set.range (matchingProduct a b))

/-- The proposed inclusion for stable polynomials implies MOC in the same order. -/
theorem conjecture_of_minimumNormalizedSpectralMatching
    (h : MinimumNormalizedSpectralMatching ι) : Conjecture ι := by
  intro a b U hU
  have hmem := h (spectralMinorCoefficients U)
    (spectralMinorCoefficients_isMinimumNormalized U hU) a b
  rwa [squarefreeSpectralValue_spectralMinorCoefficients U hU] at hmem

/-! Remaining goal.
Prove `MinimumNormalizedSpectralMatching` for an arbitrary finite index
type. The construction above gives the implication to the determinant
conjecture in the same order.
-/

end

end MOC
