import MOC.SubsetMarkerTest
import MOC.UniversalMatchingWeights
import MOC.CyclicSwitchMatrices

/-! Three biased gates on an alternating cycle can prevent common weights. -/

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

private theorem cyclic_five_minor_score_le_of_universal (U : Matrix (Fin 4) (Fin 4) ℂ)
    (hU : IsUnitary U) : HasUniversalMatchingWeights U →
    subsetMinorSq U {0, 1} {0, 1} +
    subsetMinorSq U {0, 1} {0, 2} +
    subsetMinorSq U {1, 3} {0, 2} +
    subsetMinorSq U {2, 3} {0, 2} -
    subsetMinorSq U {1, 2} {0, 3} ≤ 1 := by
  classical
  rintro ⟨w, hw, hs, hd⟩
  have hm (I J : Finset (Fin 4)) (hc : I.card = J.card) :
      ∑ σ, w σ * (imageIndicator σ I J : ℝ) = subsetMinorSq U I J := by
    have h := hd (fun i => if i ∈ I then 0 else 1) (fun j => if j ∈ J then 1 else 0)
    rw [determinantValue_subset_marker _ hU I J hc,
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
  have he : ∑ σ, w σ * (permutationScore σ : ℝ) =
      subsetMinorSq U {0, 1} {0, 1} +
      subsetMinorSq U {0, 1} {0, 2} +
      subsetMinorSq U {1, 3} {0, 2} +
      subsetMinorSq U {2, 3} {0, 2} -
      subsetMinorSq U {1, 2} {0, 3} := by
    simp only [permutationScore, Int.cast_add, Int.cast_sub, mul_add, mul_sub,
      Finset.sum_add_distrib, Finset.sum_sub_distrib]
    rw [hm _ _ (by decide), hm _ _ (by decide), hm _ _ (by decide), hm _ _ (by decide),
      hm _ _ (by decide)]
  rw [he] at hupper
  exact hupper

/-- One nonnegative permutation law cannot represent the cyclic mixer for every spectral pair. -/
theorem biasedCyclicMixer_no_universalMatchingWeights :
    ¬ HasUniversalMatchingWeights biasedCyclicMixer := by
  intro h
  have hs := cyclic_five_minor_score_le_of_universal _ biasedCyclicMixer_unitary h
  rw [biasedCyclicMixer_score] at hs
  norm_num at hs

private def fairCycleScalar : ℂ := ⟨1 / 2, 1 / 2⟩

private def sharpCycleRotation (a b : ℂ) : Matrix Bool Bool ℂ :=
  Matrix.of fun i j => if i = j then a else if i then b else -b

private def sharpCycleLeft (k : Fin 2) : Matrix Bool Bool ℂ :=
  if k = 0 then sharpCycleRotation fairCycleScalar fairCycleScalar else sharpCycleRotation (12/13) (5/13)

private def sharpCycleRight (k : Fin 2) : Matrix Bool Bool ℂ :=
  sharpCycleRotation (12/13) (if k = 0 then -5/13 else 5/13)

private def sharpCycleChart : Fin 2 × Bool ≃ Fin 4 :=
  (Equiv.prodCongr (Equiv.refl (Fin 2)) finTwoEquiv.symm).trans finProdFinEquiv

private def sharpCycleOrder : Equiv.Perm (Fin 2) := Equiv.swap 0 1

/-- An alternating cycle with one fair gate and three biased gates. -/
def threeBiasedCycle : Matrix (Fin 4) (Fin 4) ℂ :=
  (1 / 169 : ℂ) •
    !![156*fairCycleScalar, -156*fairCycleScalar, -65*fairCycleScalar, 65*fairCycleScalar;
       156*fairCycleScalar, 156*fairCycleScalar, 65*fairCycleScalar, 65*fairCycleScalar;
       25, -60, 144, -60;
       -60, -25, 60, 144]

private theorem fairCycleRotation_unitary :
    IsUnitary (sharpCycleRotation fairCycleScalar fairCycleScalar) := by
  have h : sharpCycleRotation fairCycleScalar fairCycleScalar *
      (sharpCycleRotation fairCycleScalar fairCycleScalar)ᴴ = 1 := by
    ext i j
    cases i <;> cases j <;>
      simp [sharpCycleRotation, Matrix.mul_apply, Matrix.conjTranspose_apply,
        Matrix.one_apply, Complex.star_def, Fintype.sum_bool, Complex.ext_iff,
        Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, fairCycleScalar] <;> norm_num
  exact ⟨h, mul_eq_one_comm.mp h⟩

private theorem rationalCycleRotation_unitary (b : ℝ) (hb : b^2 = (5/13 : ℝ)^2) :
    IsUnitary (sharpCycleRotation (12/13) b) := by
  have hb' := congrArg Complex.ofReal hb
  rw [Complex.ofReal_pow, Complex.ofReal_pow, Complex.ofReal_div,
    Complex.ofReal_ofNat, Complex.ofReal_ofNat] at hb'
  have h : sharpCycleRotation (12 / 13) b * (sharpCycleRotation (12 / 13) b)ᴴ = 1 := by
    ext i j
    cases i <;> cases j <;>
      simp [sharpCycleRotation, Matrix.mul_apply, Matrix.conjTranspose_apply,
        Matrix.one_apply, Fintype.sum_bool, Complex.star_def, Complex.conj_ofNat,
        ← pow_two, hb'] <;> ring
  exact ⟨h, mul_eq_one_comm.mp h⟩

private theorem sharpCycleLeft_unitary (k : Fin 2) : IsUnitary (sharpCycleLeft k) := by
  fin_cases k
  · exact fairCycleRotation_unitary
  · simpa [sharpCycleLeft] using rationalCycleRotation_unitary (5/13) rfl

private theorem sharpCycleRight_unitary (k : Fin 2) : IsUnitary (sharpCycleRight k) := by
  fin_cases k
  · simpa [sharpCycleRight] using rationalCycleRotation_unitary (-5/13) (by norm_num)
  · simpa [sharpCycleRight] using rationalCycleRotation_unitary (5/13) rfl

private theorem sharpCycle_submatrix_factorization :
    threeBiasedCycle.submatrix sharpCycleChart sharpCycleChart =
      cyclicGateMixer sharpCycleOrder sharpCycleLeft sharpCycleRight := by
  ext i j
  obtain ⟨⟨k,b⟩,rfl⟩ := (Equiv.refl (Fin 2 × Bool)).surjective i
  obtain ⟨⟨l,c⟩,rfl⟩ := (cyclicRightChart sharpCycleOrder).surjective j
  rw [cyclicGateMixer, blockGateMatrix_mul_entry]
  fin_cases k <;> cases b <;> fin_cases l <;> cases c <;>
    norm_num [threeBiasedCycle, sharpCycleChart, finProdFinEquiv, finTwoEquiv, Matrix.smul_apply,
      sharpCycleOrder, cyclicRightChart, sharpCycleRotation, sharpCycleLeft, sharpCycleRight,
      Matrix.submatrix_apply, Fintype.sum_bool, Equiv.swap_apply_def,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail] <;> ring

private theorem threeBiasedCycle_unitary : IsUnitary threeBiasedCycle := by
  have h := blockGateMatrix_mul_unitary (Equiv.refl _) (cyclicRightChart sharpCycleOrder)
    sharpCycleLeft sharpCycleRight sharpCycleLeft_unitary sharpCycleRight_unitary
  change IsUnitary (cyclicGateMixer sharpCycleOrder sharpCycleLeft sharpCycleRight) at h
  rw [← sharpCycle_submatrix_factorization] at h
  have h' := unitary_reindex sharpCycleChart.symm sharpCycleChart.symm h
  simpa [Matrix.submatrix_apply] using h'

private theorem threeBiasedCycle_score :
    subsetMinorSq threeBiasedCycle {0, 1} {0, 1} +
    subsetMinorSq threeBiasedCycle {0, 1} {0, 2} +
    subsetMinorSq threeBiasedCycle {1, 3} {0, 2} +
    subsetMinorSq threeBiasedCycle {2, 3} {0, 2} -
    subsetMinorSq threeBiasedCycle {1, 2} {0, 3} = 9768743 / 9653618 := by
  have h := threeBiasedCycle_unitary
  rw [subsetMinorSq_pair _ h (i := 0) (k := 1) (j := 0) (l := 1) (by decide) (by decide),
    subsetMinorSq_pair _ h (i := 0) (k := 1) (j := 0) (l := 2) (by decide) (by decide),
    subsetMinorSq_pair _ h (i := 1) (k := 3) (j := 0) (l := 2) (by decide) (by decide),
    subsetMinorSq_pair _ h (i := 2) (k := 3) (j := 0) (l := 2) (by decide) (by decide),
    subsetMinorSq_pair _ h (i := 1) (k := 2) (j := 0) (l := 3) (by decide) (by decide)]
  norm_num [threeBiasedCycle, Matrix.smul_apply, fairCycleScalar, Complex.normSq_apply,
    Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.div_re, Complex.div_im, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead,
    Matrix.vecTail]

/-- The alternating cycle with three biased gates has no common matching law. -/
theorem threeBiasedCycle_no_universalMatchingWeights :
    ¬ HasUniversalMatchingWeights threeBiasedCycle := by
  intro h
  have hs := cyclic_five_minor_score_le_of_universal _ threeBiasedCycle_unitary h
  rw [threeBiasedCycle_score] at hs
  norm_num at hs

/-- Three arbitrary gates can fail to have a common law even when the
remaining gate is balanced. -/
theorem exists_three_biased_cyclic_gate_obstruction :
    ∃ (s : Equiv.Perm (Fin 2)) (L R : Fin 2 → Matrix Bool Bool ℂ),
      TraversesAllIndices s ∧ s ≠ 1 ∧ (∀ k, IsUnitary (L k)) ∧ (∀ k, IsUnitary (R k)) ∧
      BalancedGate (L 0) ∧ ¬ HasUniversalMatchingWeights (cyclicGateMixer s L R) := by
  refine ⟨sharpCycleOrder, sharpCycleLeft, sharpCycleRight, ?_, ?_,
    sharpCycleLeft_unitary, sharpCycleRight_unitary, ?_, ?_⟩
  · intro i j
    fin_cases i <;> fin_cases j
    · exact ⟨0, rfl⟩
    · exact ⟨1, by decide⟩
    · exact ⟨1, by decide⟩
    · exact ⟨0, rfl⟩
  · decide
  · refine ⟨sharpCycleLeft_unitary 0, ?_⟩
    intro i j
    cases i <;> cases j <;>
      norm_num [sharpCycleLeft, sharpCycleRotation, Complex.normSq_apply, fairCycleScalar]
  · rw [← sharpCycle_submatrix_factorization,
      hasUniversalMatchingWeights_reindex_iff sharpCycleChart sharpCycleChart]
    exact threeBiasedCycle_no_universalMatchingWeights

end

end MOC
