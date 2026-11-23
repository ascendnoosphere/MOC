import MOC.CommonWeights
import MOC.FiniteMinorLaw

/-! A finite test for one weight vector that must represent every spectral pair. -/

open BigOperators Finset Matrix

namespace MOC

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Complementary zero-one spectra evaluate a fixed real weight vector on one subset image. -/
theorem weightedMatchingValue_subset_marker (w : Equiv.Perm ι → ℝ)
    (I J : Finset ι) (hc : I.card = J.card) :
    weightedMatchingValue (fun i => if i ∈ I then 0 else 1)
        (fun j => if j ∈ J then 1 else 0) w =
      ((∑ σ ∈ univ.filter (fun σ : Equiv.Perm ι => J.map σ.toEmbedding = I), w σ : ℝ) : ℂ) := by
  classical
  rw [weightedMatchingValue, Complex.ofReal_sum, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro σ _
  rw [matchingProduct_subset_marker I J hc σ]
  split_ifs <;> simp

/-- The determinant at a complementary zero-one spectral pair is a squared minor. -/
theorem determinantValue_subset_marker (U : Matrix ι ι ℂ) (hU : IsUnitary U)
    (I J : Finset ι) (hc : I.card = J.card) :
    determinantValue (fun i => if i ∈ I then 0 else 1)
      (fun j => if j ∈ J then 1 else 0) U = (subsetMinorSq U I J : ℂ) := by
  classical
  rw [← signed_determinant _ _ U hU, ← sum_signedWeight_image_eq_subsetMinorSq U hU I J,
    Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro σ _
  rw [matchingProduct_subset_marker I J hc σ]
  split_ifs <;> simp

/-- A fixed weight vector represents the determinant for all complex spectra
if and only if it represents the complementary zero-one pairs indexed by two
sets of equal size at most half the matrix order. -/
theorem weightedMatchingValue_eq_all_iff_subset_markers (U : Matrix ι ι ℂ)
    (hU : IsUnitary U) (w : Equiv.Perm ι → ℝ) :
    (∀ a b : ι → ℂ, weightedMatchingValue a b w = determinantValue a b U) ↔
    ∀ I J : Finset ι, I.card = J.card → I.card ≤ Fintype.card ι / 2 →
      weightedMatchingValue (fun i => if i ∈ I then 0 else 1)
          (fun j => if j ∈ J then 1 else 0) w =
        determinantValue (fun i => if i ∈ I then 0 else 1)
          (fun j => if j ∈ J then 1 else 0) U := by
  constructor
  · exact fun h _ _ _ _ => h _ _
  · intro h a b
    apply determinantValue_eq_sum_of_indexed_minor_law a b U hU id w
    apply indexed_minor_law_of_small U hU id w
    intro I J hc hn
    have he := h I J hc hn
    rw [weightedMatchingValue_subset_marker w I J hc,
      determinantValue_subset_marker U hU I J hc] at he
    exact (Complex.ofReal_injective he).symm

end

end MOC
