import MOC.UniversalMatchingWeights
import MOC.SubsetMarkerTest
import MOC.FiniteMinorLaw
import Mathlib.Tactic.FinCases

/-! Four subset-image events obstruct the squared-minor law for a rational
orthogonal matrix. A fifth fixed coordinate gives the order-five example. -/

open BigOperators Matrix Finset

namespace MOC.RationalMinorCover

noncomputable section

private def marker {n : ℕ} (I J : Finset (Fin n)) (p : Equiv.Perm (Fin n)) : ℕ :=
  if J.map p.toEmbedding = I then 1 else 0

private theorem weighted_marker {n : ℕ} (I J : Finset (Fin n))
    (w : Equiv.Perm (Fin n) → ℝ) :
    (∑ p, w p * (marker I J p : ℝ)) =
      ∑ p ∈ univ.filter (fun p : Equiv.Perm (Fin n) => J.map p.toEmbedding = I), w p := by
  classical
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p _
  by_cases h : J.map p.toEmbedding = I <;> simp [marker, h]

private def numeratorFour : Matrix (Fin 4) (Fin 4) ℤ :=
  !![80, -10, 115, -94; 134, -59, -82, 20; 61, 98, 56, 110; -22, -124, 74, 85]

def mixerFour : Matrix (Fin 4) (Fin 4) ℂ := fun i j =>
  (((numeratorFour i j : ℝ) / 169 : ℝ) : ℂ)

theorem mixerFour_unitary : IsUnitary mixerFour := by
  have h : mixerFour * mixerFourᴴ = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [mixerFour, numeratorFour, Matrix.mul_apply, Fin.sum_univ_succ,
        Matrix.conjTranspose_apply, Matrix.one_apply, Matrix.cons_val_two, Matrix.cons_val_three,
        Matrix.vecHead, Matrix.vecTail, ← Complex.ofReal_mul, ← Complex.ofReal_add]
  exact ⟨h, Matrix.mul_eq_one_comm.mp h⟩

set_option maxRecDepth 12000 in
set_option maxHeartbeats 3000000 in
private theorem coverFour : ∀ p : Equiv.Perm (Fin 4),
    marker {0,3} {0,2} p ≤ marker {1} {3} p + marker {3} {0} p + marker {0,1} {0,1} p := by
  decide +kernel

theorem mixerFour_no_minor_law :
    ¬ ∃ w : Equiv.Perm (Fin 4) → ℝ, (∀ p, 0 ≤ w p) ∧
      ∀ I J : Finset (Fin 4), (∑ p ∈ univ.filter (fun p : Equiv.Perm (Fin 4) =>
        J.map p.toEmbedding = I), w p) = subsetMinorSq mixerFour I J := by
  classical
  rintro ⟨w, hw, hm⟩
  have hweight (I J : Finset (Fin 4)) :
      (∑ p, w p * (marker I J p : ℝ)) = subsetMinorSq mixerFour I J :=
    (weighted_marker I J w).trans (hm I J)
  have h0 : subsetMinorSq mixerFour {1} {3} = 400/28561 := by
    rw [subsetMinorSq_singleton _ mixerFour_unitary]
    norm_num [mixerFour, numeratorFour, ← Complex.ofReal_mul, ← Complex.ofReal_sub,
      Complex.normSq_ofReal, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail]
  have h1 : subsetMinorSq mixerFour {3} {0} = 484/28561 := by
    rw [subsetMinorSq_singleton _ mixerFour_unitary]
    norm_num [mixerFour, numeratorFour, ← Complex.ofReal_mul, ← Complex.ofReal_sub,
      Complex.normSq_ofReal, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail]
  have h2 : subsetMinorSq mixerFour {0,1} {0,1} = 400/28561 := by
    rw [subsetMinorSq_pair _ mixerFour_unitary (by decide) (by decide)]
    norm_num [mixerFour, numeratorFour, ← Complex.ofReal_mul, ← Complex.ofReal_sub,
      Complex.normSq_ofReal, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail]
  have h3 : subsetMinorSq mixerFour {0,3} {0,2} = 2500/28561 := by
    rw [subsetMinorSq_pair _ mixerFour_unitary (by decide) (by decide)]
    norm_num [mixerFour, numeratorFour, ← Complex.ofReal_mul, ← Complex.ofReal_sub,
      Complex.normSq_ofReal, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail]
  have hp (p : Equiv.Perm (Fin 4)) :
      (marker {0,3} {0,2} p : ℝ) ≤ (marker {1} {3} p : ℝ) + (marker {3} {0} p : ℝ) + (marker {0,1} {0,1} p : ℝ) := by
    exact_mod_cast coverFour p
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun p _ =>
    mul_le_mul_of_nonneg_left (hp p) (hw p))
  simp only [mul_add, Finset.sum_add_distrib, hweight, h0, h1, h2, h3] at hs
  norm_num at hs

private def numeratorFive : Matrix (Fin 5) (Fin 5) ℤ :=
  !![80, -10, 115, -94, 0; 134, -59, -82, 20, 0; 61, 98, 56, 110, 0; -22, -124, 74, 85, 0; 0, 0, 0, 0, 169]

def mixerFive : Matrix (Fin 5) (Fin 5) ℂ := fun i j =>
  (((numeratorFive i j : ℝ) / 169 : ℝ) : ℂ)

theorem mixerFive_unitary : IsUnitary mixerFive := by
  have h : mixerFive * mixerFiveᴴ = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [mixerFive, numeratorFive, Matrix.mul_apply, Fin.sum_univ_succ,
        Matrix.conjTranspose_apply, Matrix.one_apply, Matrix.cons_val_two, Matrix.cons_val_three,
        Matrix.vecHead, Matrix.vecTail, ← Complex.ofReal_mul, ← Complex.ofReal_add]
  exact ⟨h, Matrix.mul_eq_one_comm.mp h⟩

set_option maxRecDepth 12000 in
set_option maxHeartbeats 3000000 in
private theorem coverFive : ∀ p : Equiv.Perm (Fin 5),
    marker {0,3} {0,2} p ≤ marker {1} {3} p + marker {3} {0} p + marker {0,1} {0,1} p + marker {1} {4} p := by
  decide +kernel

theorem mixerFive_no_minor_law :
    ¬ ∃ w : Equiv.Perm (Fin 5) → ℝ, (∀ p, 0 ≤ w p) ∧
      ∀ I J : Finset (Fin 5), (∑ p ∈ univ.filter (fun p : Equiv.Perm (Fin 5) =>
        J.map p.toEmbedding = I), w p) = subsetMinorSq mixerFive I J := by
  classical
  rintro ⟨w, hw, hm⟩
  have hweight (I J : Finset (Fin 5)) :
      (∑ p, w p * (marker I J p : ℝ)) = subsetMinorSq mixerFive I J :=
    (weighted_marker I J w).trans (hm I J)
  have h0 : subsetMinorSq mixerFive {1} {3} = 400/28561 := by
    rw [subsetMinorSq_singleton _ mixerFive_unitary]
    norm_num [mixerFive, numeratorFive, ← Complex.ofReal_mul, ← Complex.ofReal_sub,
      Complex.normSq_ofReal, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail]
  have h1 : subsetMinorSq mixerFive {3} {0} = 484/28561 := by
    rw [subsetMinorSq_singleton _ mixerFive_unitary]
    norm_num [mixerFive, numeratorFive, ← Complex.ofReal_mul, ← Complex.ofReal_sub,
      Complex.normSq_ofReal, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail]
  have h2 : subsetMinorSq mixerFive {0,1} {0,1} = 400/28561 := by
    rw [subsetMinorSq_pair _ mixerFive_unitary (by decide) (by decide)]
    norm_num [mixerFive, numeratorFive, ← Complex.ofReal_mul, ← Complex.ofReal_sub,
      Complex.normSq_ofReal, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail]
  have h3 : subsetMinorSq mixerFive {0,3} {0,2} = 2500/28561 := by
    rw [subsetMinorSq_pair _ mixerFive_unitary (by decide) (by decide)]
    norm_num [mixerFive, numeratorFive, ← Complex.ofReal_mul, ← Complex.ofReal_sub,
      Complex.normSq_ofReal, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail]
  have h4 : subsetMinorSq mixerFive {1} {4} = 0/28561 := by
    rw [subsetMinorSq_singleton _ mixerFive_unitary]
    norm_num [mixerFive, numeratorFive, ← Complex.ofReal_mul, ← Complex.ofReal_sub,
      Complex.normSq_ofReal, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail]
  have hp (p : Equiv.Perm (Fin 5)) :
      (marker {0,3} {0,2} p : ℝ) ≤ (marker {1} {3} p : ℝ) + (marker {3} {0} p : ℝ) + (marker {0,1} {0,1} p : ℝ) + (marker {1} {4} p : ℝ) := by
    exact_mod_cast coverFive p
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun p _ =>
    mul_le_mul_of_nonneg_left (hp p) (hw p))
  simp only [mul_add, Finset.sum_add_distrib, hweight, h0, h1, h2, h3, h4] at hs
  norm_num at hs

private theorem no_spectrum_independent_law {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix ι ι ℂ) (hU : IsUnitary U)
    (hn : ¬ ∃ w : Equiv.Perm ι → ℝ, (∀ p, 0 ≤ w p) ∧
      ∀ I J : Finset ι, (∑ p ∈ univ.filter (fun p : Equiv.Perm ι =>
        J.map p.toEmbedding = I), w p) = subsetMinorSq U I J) :
    ¬ HasUniversalMatchingWeights U := by
  rintro ⟨w,hw,_,he⟩
  apply hn
  refine ⟨w,hw,?_⟩
  have hmarkers := (weightedMatchingValue_eq_all_iff_subset_markers U hU w).mp (fun a b => (he a b).symm)
  have hall := indexed_minor_law_of_small U hU id w (fun I J hc hsmall => by
    have h := hmarkers I J hc hsmall
    rw [weightedMatchingValue_subset_marker w I J hc, determinantValue_subset_marker U hU I J hc] at h
    exact (Complex.ofReal_injective h).symm)
  exact fun I J => (hall I J).symm

theorem no_universal_weights_four : ¬ HasUniversalMatchingWeights mixerFour :=
  no_spectrum_independent_law _ mixerFour_unitary mixerFour_no_minor_law

theorem no_universal_weights_five : ¬ HasUniversalMatchingWeights mixerFive :=
  no_spectrum_independent_law _ mixerFive_unitary mixerFive_no_minor_law

end

end MOC.RationalMinorCover
