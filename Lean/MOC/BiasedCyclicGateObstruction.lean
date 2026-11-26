import MOC.SubsetMarkerTest
import MOC.UniversalMatchingWeights

/-! Two layers of nonbalanced gates on an alternating cycle can fail to have common weights. -/

open BigOperators Finset Matrix

namespace MOC

noncomputable section

private def scaledRealMatrix (d : ℝ) (A : Matrix (Fin 4) (Fin 4) ℝ) :
    Matrix (Fin 4) (Fin 4) ℂ :=
  Complex.ofRealHom.mapMatrix (d • A)

/-- The first layer rotates the ordered pairs `(0,1)` and `(2,3)`. -/
def biasedCyclicLeftLayer : Matrix (Fin 4) (Fin 4) ℂ :=
  scaledRealMatrix (1/13) !![12, -5, 0, 0; 5, 12, 0, 0; 0, 0, 12, -5; 0, 0, 5, 12]

/-- The second layer rotates the ordered pairs `(1,2)` and `(3,0)`, with opposite signs. -/
def biasedCyclicRightLayer : Matrix (Fin 4) (Fin 4) ℂ :=
  scaledRealMatrix (1/13) !![12, 0, 0, 5; 0, 12, 5, 0; 0, -5, 12, 0; -5, 0, 0, 12]

/-- The two layers of biased cyclic gates. -/
def biasedCyclicMixer : Matrix (Fin 4) (Fin 4) ℂ :=
  scaledRealMatrix (1/169)
    !![144, -60, -25, 60; 60, 144, 60, 25; 25, -60, 144, -60; -60, -25, 60, 144]

theorem biasedCyclicMixer_eq_gateProduct :
    biasedCyclicMixer = biasedCyclicLeftLayer * biasedCyclicRightLayer := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [biasedCyclicMixer, biasedCyclicLeftLayer, biasedCyclicRightLayer, scaledRealMatrix,
      Matrix.mul_apply, Fin.sum_univ_four, ← Complex.ofReal_mul, ← Complex.ofReal_add,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail]

theorem biasedCyclicLeftLayer_unitary : IsUnitary biasedCyclicLeftLayer := by
  have h : biasedCyclicLeftLayer * biasedCyclicLeftLayerᴴ = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [biasedCyclicLeftLayer, scaledRealMatrix, Matrix.mul_apply, Fin.sum_univ_four,
        Matrix.conjTranspose_apply, Matrix.one_apply, Complex.star_def, ← Complex.ofReal_mul,
        ← Complex.ofReal_add, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead,
        Matrix.vecTail]
  exact ⟨h, mul_eq_one_comm.mp h⟩

theorem biasedCyclicRightLayer_unitary : IsUnitary biasedCyclicRightLayer := by
  have h : biasedCyclicRightLayer * biasedCyclicRightLayerᴴ = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [biasedCyclicRightLayer, scaledRealMatrix, Matrix.mul_apply, Fin.sum_univ_four,
        Matrix.conjTranspose_apply, Matrix.one_apply, Complex.star_def, ← Complex.ofReal_mul,
        ← Complex.ofReal_add, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead,
        Matrix.vecTail]
  exact ⟨h, mul_eq_one_comm.mp h⟩

theorem biasedCyclicMixer_unitary : IsUnitary biasedCyclicMixer := by
  have h : biasedCyclicMixer * biasedCyclicMixerᴴ = 1 := by
    rw [biasedCyclicMixer_eq_gateProduct, Matrix.conjTranspose_mul, Matrix.mul_assoc,
      ← Matrix.mul_assoc biasedCyclicRightLayer, biasedCyclicRightLayer_unitary.1,
      Matrix.one_mul, biasedCyclicLeftLayer_unitary.1]
  exact ⟨h, mul_eq_one_comm.mp h⟩

private def imageIndicator (σ : Equiv.Perm (Fin 4)) (I J : Finset (Fin 4)) : ℤ :=
  if J.map σ.toEmbedding = I then 1 else 0

private def permutationScore (σ : Equiv.Perm (Fin 4)) : ℤ :=
  imageIndicator σ {0, 1} {0, 1} + imageIndicator σ {0, 1} {0, 2} +
  imageIndicator σ {1, 3} {0, 2} + imageIndicator σ {2, 3} {0, 2} -
    imageIndicator σ {1, 2} {0, 3}

private theorem permutationScore_le : ∀ σ : Equiv.Perm (Fin 4), permutationScore σ ≤ 1 := by
  decide +kernel

private theorem biasedCyclicMixer_score :
    subsetMinorSq biasedCyclicMixer {0, 1} {0, 1} +
    subsetMinorSq biasedCyclicMixer {0, 1} {0, 2} +
    subsetMinorSq biasedCyclicMixer {1, 3} {0, 2} +
    subsetMinorSq biasedCyclicMixer {2, 3} {0, 2} -
    subsetMinorSq biasedCyclicMixer {1, 2} {0, 3} = 831869471 / 815730721 := by
  have h := biasedCyclicMixer_unitary
  rw [subsetMinorSq_pair _ h (i := 0) (k := 1) (j := 0) (l := 1) (by decide) (by decide),
    subsetMinorSq_pair _ h (i := 0) (k := 1) (j := 0) (l := 2) (by decide) (by decide),
    subsetMinorSq_pair _ h (i := 1) (k := 3) (j := 0) (l := 2) (by decide) (by decide),
    subsetMinorSq_pair _ h (i := 2) (k := 3) (j := 0) (l := 2) (by decide) (by decide),
    subsetMinorSq_pair _ h (i := 1) (k := 2) (j := 0) (l := 3) (by decide) (by decide)]
  norm_num [biasedCyclicMixer, scaledRealMatrix, ← Complex.ofReal_mul, ← Complex.ofReal_sub,
    Complex.normSq_ofReal, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead,
    Matrix.vecTail]

/-- One nonnegative permutation law cannot represent the cyclic mixer for every spectral pair. -/
theorem biasedCyclicMixer_no_universalMatchingWeights :
    ¬ HasUniversalMatchingWeights biasedCyclicMixer := by
  classical
  rintro ⟨w, hw, hs, hd⟩
  have hm (I J : Finset (Fin 4)) (hc : I.card = J.card) :
      ∑ σ, w σ * (imageIndicator σ I J : ℝ) = subsetMinorSq biasedCyclicMixer I J := by
    have h := hd (fun i => if i ∈ I then 0 else 1) (fun j => if j ∈ J then 1 else 0)
    rw [determinantValue_subset_marker _ biasedCyclicMixer_unitary I J hc,
      weightedMatchingValue_subset_marker w I J hc] at h
    rw [Complex.ofReal_injective h, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro σ _
    by_cases he : J.map σ.toEmbedding = I <;> simp [imageIndicator, he]
  have hupper : ∑ σ, w σ * (permutationScore σ : ℝ) ≤ 1 := calc
    _ ≤ ∑ σ, w σ * 1 := by
      apply Finset.sum_le_sum
      intro σ _
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast permutationScore_le σ) (hw σ)
    _ = 1 := by simpa only [mul_one] using hs
  have he : ∑ σ, w σ * (permutationScore σ : ℝ) = 831869471 / 815730721 := by
    simp only [permutationScore, Int.cast_add, Int.cast_sub, mul_add, mul_sub,
      Finset.sum_add_distrib, Finset.sum_sub_distrib]
    rw [hm _ _ (by decide), hm _ _ (by decide), hm _ _ (by decide), hm _ _ (by decide),
      hm _ _ (by decide)]
    exact biasedCyclicMixer_score
  rw [he] at hupper
  norm_num at hupper

end

end MOC
