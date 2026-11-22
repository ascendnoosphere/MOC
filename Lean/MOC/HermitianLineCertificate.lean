import MOC.CommonWeights
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.Topology.Instances.Matrix

/-! An exact all-partner law from the order-five rational replay. -/

open BigOperators Filter Matrix
open scoped Topology

namespace MOC

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem conjugateTranspose_mapRat (Q : Matrix ι ι ℚ) :
    (Q.map (Rat.castHom ℂ))ᴴ = Qᵀ.map (Rat.castHom ℂ) := by
  ext i j : 1
  simp [Matrix.conjTranspose_apply]

private theorem unitary_mapRat (Q : Matrix ι ι ℚ) (hQ : Q * Qᵀ = 1) :
    IsUnitary (Q.map (Rat.castHom ℂ)) := by
  have h : Q.map (Rat.castHom ℂ) * (Q.map (Rat.castHom ℂ))ᴴ = 1 := by
    rw [conjugateTranspose_mapRat, ← Matrix.map_mul, hQ]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  exact ⟨h, Matrix.mul_eq_one_comm.mp h⟩

/-- A common law with positive weights on every assignment gives a common law
for every unitary in a neighborhood of the original relative unitary. -/
theorem eventually_common_weights_of_positive (a : ι → ℂ) (U : Matrix ι ι ℂ)
    (hU : IsUnitary U) (w : Equiv.Perm ι → ℝ) (hw : ∀ σ, 0 < w σ)
    (hmass : ∑ σ, w σ = 1)
    (heq : ∀ b, weightedMatchingValue a b w = determinantValue a b U) :
    ∀ᶠ V in 𝓝 U, IsUnitary V → HasCommonWeights a V := by
  let w' (V : Matrix ι ι ℂ) (σ : Equiv.Perm ι) :=
    w σ + realSignedWeight V σ - realSignedWeight U σ
  have hnear : ∀ᶠ V in 𝓝 U, ∀ σ, 0 < w' V σ := by
    apply Filter.eventually_all.mpr
    intro σ
    have hp : Continuous (fun V : Matrix ι ι ℂ => ∏ i, V (σ i) i) :=
      continuous_finset_prod _ fun i _ => continuous_id.matrix_elem (σ i) i
    have hnum : Continuous (fun V : Matrix ι ι ℂ => leibnizTerm V σ) :=
      continuous_const.mul hp
    have hdiv : ContinuousAt (fun V : Matrix ι ι ℂ => signedWeight V σ) U :=
      hnum.continuousAt.div continuous_id.matrix_det.continuousAt (det_ne_zero_of_unitary hU)
    have hwc : ContinuousAt (fun V : Matrix ι ι ℂ => realSignedWeight V σ) U :=
      Complex.continuous_re.continuousAt.comp hdiv
    have hcont : ContinuousAt (fun V => w' V σ) U :=
      (continuousAt_const.add hwc).sub continuousAt_const
    exact hcont.eventually_mem (Ioi_mem_nhds (by simpa [w'] using hw σ))
  filter_upwards [hnear] with V hV
  intro hVu
  refine ⟨w' V, fun σ => (hV σ).le, ?_, ?_⟩
  · simp only [w', Finset.sum_sub_distrib, Finset.sum_add_distrib, hmass,
      sum_realSignedWeight U hU, sum_realSignedWeight V hVu]
    ring
  · intro b
    unfold weightedMatchingValue at heq ⊢
    simp only [w', Complex.ofReal_add, Complex.ofReal_sub, add_mul, sub_mul,
      Finset.sum_add_distrib, Finset.sum_sub_distrib, heq b,
      real_signed_determinant _ _ U hU, real_signed_determinant _ _ V hVu]
    ring

private def witnessSpectrumInt : Fin 5 → ℤ := ![-9, -8, -6, -2, 8]

private def witnessMixerInt : Matrix (Fin 5) (Fin 5) ℤ :=
  !![33, 22, 53, 19, -21;
    33, 22, -19, -53, -21;
    -9, -54, 27, -27, -27;
    -3, -2, -31, 31, -57;
    -54, 36, 18, -18, -18]

private def witnessMixerRat : Matrix (Fin 5) (Fin 5) ℚ :=
  (1 / 72 : ℚ) • witnessMixerInt.map (Int.castRingHom ℚ)

private def witnessRank (σ : Equiv.Perm (Fin 5)) : ℕ :=
  let a := (σ 0).val
  let b := (σ 1).val
  let c := (σ 2).val
  let d := (σ 3).val
  24 * a + 6 * (b - (if a < b then 1 else 0)) +
    2 * (c - (if a < c then 1 else 0) - (if b < c then 1 else 0)) +
    (d - (if a < d then 1 else 0) - (if b < d then 1 else 0) - (if c < d then 1 else 0))

private def witnessExtra (r : ℕ) : ℕ :=
  match r with
  | 10 => 4083811112780668708992
  | 18 => 4714860184907946635520
  | 20 => 5381341133310177255360
  | 22 => 86025753909154035648
  | 26 => 646204624542077636784
  | 30 => 1982772190097854610400
  | 31 => 4229429434907946635520
  | 32 => 1600452620268014388336
  | 34 => 111178978369381786248
  | 42 => 111885521330450253960
  | 43 => 2897268363284049906885
  | 46 => 2277826261377270387771
  | 47 => 409020190730901029616
  | 66 => 1041330184907946635520
  | 82 => 34439343757896140280
  | 90 => 62268841150050495240
  | 98 => 3968541618093557681365
  | 100 => 1691317877525262887936
  | 101 => 22525314747048429435
  | 102 => 3607322913741576014685
  | 103 => 2493781743904262781760
  | 105 => 193045433504211698795
  | 108 => 15354997102558295028350
  | 109 => 5019842454117567637680
  | 112 => 690962981135383932885
  | 113 => 5162374560672833907109
  | 115 => 31109434907946635520
  | _ => 0

private def witnessWeightInt (σ : Equiv.Perm (Fin 5)) : ℤ :=
  ((890398545502223520 + witnessExtra (witnessRank σ) : ℕ) : ℤ)

private def witnessSignedInt (σ : Equiv.Perm (Fin 5)) : ℤ :=
  (Equiv.Perm.sign σ : ℤ) * ∏ i, witnessMixerInt (σ i) i

/-- Use the constructive permutation enumeration for the integer checks. -/
private def witnessPermutations : Finset (Equiv.Perm (Fin 5)) :=
  @Finset.univ _ (fintypePerm (α := Fin 5))

private theorem witnessPermutations_eq_univ : witnessPermutations = Finset.univ :=
  congrArg (fun k : Fintype (Equiv.Perm (Fin 5)) => @Finset.univ _ k) (Subsingleton.elim _ _)

private theorem witnessOrthogonal : witnessMixerRat * witnessMixerRatᵀ = 1 := by
  ext i j : 1
  exact (by decide +kernel : ∀ i j : Fin 5,
    (witnessMixerRat * witnessMixerRatᵀ) i j = (1 : Matrix (Fin 5) (Fin 5) ℚ) i j) i j

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
private theorem witnessMassCheck :
    (∑ σ ∈ witnessPermutations, witnessWeightInt σ) = 68012784000000000000000 := by
  decide +kernel

private theorem witnessMass : (∑ σ, witnessWeightInt σ) = 68012784000000000000000 := by
  simpa only [witnessPermutations_eq_univ] using witnessMassCheck

set_option maxRecDepth 10000 in
set_option maxHeartbeats 16000000 in
private theorem witnessMomentCheck :
    ∀ S : Finset (Fin 5),
      (72 : ℤ)^5 * (∑ σ ∈ witnessPermutations,
        witnessWeightInt σ * ∏ i ∈ S, witnessSpectrumInt (σ i)) =
      68012784000000000000000 * (∑ σ ∈ witnessPermutations,
        witnessSignedInt σ * ∏ i ∈ S, witnessSpectrumInt (σ i)) := by
  decide +kernel

private theorem witnessDetInt : witnessMixerInt.det = (72 : ℤ)^5 := by
  rw [Matrix.det_apply']
  have h := (witnessMomentCheck ∅).symm
  simp only [Finset.prod_empty, mul_one, witnessPermutations_eq_univ, witnessMass,
    witnessSignedInt] at h
  rw [mul_comm ((72 : ℤ)^5)] at h
  exact mul_left_cancel₀ (by decide) h

/-- The Hermitian spectrum of sample 104 in the rational replay archive. -/
def orderFiveWitnessSpectrum : Fin 5 → ℂ := fun i => witnessSpectrumInt i

/-- The relative unitary of sample 104. The archive uses the transpose because
it conjugates the Hermitian term. -/
def orderFiveWitnessUnitary : Matrix (Fin 5) (Fin 5) ℂ :=
  (1 / 72 : ℂ) • witnessMixerInt.map (Int.castRingHom ℂ)

theorem orderFiveWitness_isUnitary : IsUnitary orderFiveWitnessUnitary := by
  have h : orderFiveWitnessUnitary = witnessMixerRat.map (Rat.castHom ℂ) := by
    ext i j : 1
    simp [orderFiveWitnessUnitary, witnessMixerRat, Matrix.smul_apply, smul_eq_mul]
  rw [h]
  exact unitary_mapRat _ witnessOrthogonal

private theorem witnessDet : orderFiveWitnessUnitary.det = 1 := by
  have h := (Int.castRingHom ℂ).map_det witnessMixerInt
  simp only [RingHom.mapMatrix_apply] at h
  rw [orderFiveWitnessUnitary, Matrix.det_smul, Fintype.card_fin, ← h, witnessDetInt]
  norm_num

private theorem witnessSignedWeight (σ : Equiv.Perm (Fin 5)) :
    signedWeight orderFiveWitnessUnitary σ = (witnessSignedInt σ : ℂ) / (72 : ℂ)^5 := by
  rw [signedWeight, witnessDet, div_one]
  simp only [leibnizTerm, orderFiveWitnessUnitary, Matrix.smul_apply, Matrix.map_apply,
    smul_eq_mul, Int.coe_castRingHom, witnessSignedInt, Int.cast_mul, Int.cast_prod,
    Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  ring

private def witnessWeight (σ : Equiv.Perm (Fin 5)) : ℝ :=
  (witnessWeightInt σ : ℝ) / 68012784000000000000000

private theorem witnessMoment (S : Finset (Fin 5)) :
    (∑ σ, (witnessWeight σ : ℂ) * ∏ i ∈ S, orderFiveWitnessSpectrum (σ i)) =
      ∑ σ, signedWeight orderFiveWitnessUnitary σ * ∏ i ∈ S, orderFiveWitnessSpectrum (σ i) := by
  simp_rw [witnessWeight, Complex.ofReal_div, Complex.ofReal_intCast, Complex.ofReal_ofNat,
    witnessSignedWeight, div_mul_eq_mul_div, ← Finset.sum_div]
  rw [div_eq_div_iff (by norm_num) (by norm_num)]
  have h := congrArg (fun x : ℤ => (x : ℂ)) (witnessMomentCheck S)
  simp only [Int.cast_mul, Int.cast_sum, Int.cast_prod, Int.cast_ofNat, Int.cast_pow,
    witnessPermutations_eq_univ] at h
  exact (mul_comm _ _).trans (h.trans (mul_comm _ _))

/-- The exact sample admits a positive law for all complex partner spectra. -/
theorem orderFiveWitness_positive_common_weights :
    ∃ w : Equiv.Perm (Fin 5) → ℝ, (∀ σ, 0 < w σ) ∧ (∑ σ, w σ = 1) ∧
      ∀ b, weightedMatchingValue orderFiveWitnessSpectrum b w =
        determinantValue orderFiveWitnessSpectrum b orderFiveWitnessUnitary := by
  refine ⟨witnessWeight, ?_, ?_, ?_⟩
  · intro σ
    have hp : 0 < witnessWeightInt σ := by
      unfold witnessWeightInt
      omega
    exact div_pos (Int.cast_pos.mpr hp) (by norm_num)
  · simp only [witnessWeight, ← Finset.sum_div, ← Int.cast_sum, witnessMass]
    norm_num
  · intro b
    rw [← signed_determinant _ _ _ orderFiveWitness_isUnitary]
    simp_rw [weightedMatchingValue, matchingProduct, Fintype.prod_add, Finset.mul_sum, ← mul_assoc]
    rw [Finset.sum_comm]
    conv_rhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro S _
    rw [← Finset.sum_mul, ← Finset.sum_mul, witnessMoment]

theorem orderFiveWitness_common_weights :
    HasCommonWeights orderFiveWitnessSpectrum orderFiveWitnessUnitary := by
  obtain ⟨w, hpos, hsum, heq⟩ := orderFiveWitness_positive_common_weights
  exact ⟨w, fun σ => (hpos σ).le, hsum, heq⟩

/-- All nearby relative unitaries admit a common law for the fixed spectrum. -/
theorem eventually_orderFiveWitness_common_weights :
    ∀ᶠ V in 𝓝 orderFiveWitnessUnitary,
      IsUnitary V → HasCommonWeights orderFiveWitnessSpectrum V := by
  obtain ⟨w, hpos, hsum, heq⟩ := orderFiveWitness_positive_common_weights
  exact eventually_common_weights_of_positive _ _ orderFiveWitness_isUnitary w hpos hsum heq

end

end MOC
