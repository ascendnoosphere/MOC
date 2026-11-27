import MOC.FourKleinMatchingChart
import MOC.FourKleinPrism
import Mathlib.Data.Real.Sqrt

/-! Ordinary and mixed sum-of-squares certificates on the normal Klein-four chart. -/

open BigOperators Matrix

namespace MOC

noncomputable section

private theorem klein_sos_add {g h : KleinMatchingFunction}
    (hg : IsRealMatchingSOS g) (hh : IsRealMatchingSOS h) : IsRealMatchingSOS (g + h) := by
  obtain ⟨n, f, hf⟩ := hg
  obtain ⟨m, r, hr⟩ := hh
  refine ⟨n + m, Fin.addCases f r, fun j => ?_⟩
  rw [Pi.add_apply, hf j, hr j, Fin.sum_univ_add]
  simp only [Fin.addCases_left, Fin.addCases_right]

private theorem klein_weighted_squares {n : ℕ} (w : Fin n → ℝ)
    (f : Fin n → KleinMatchingFunction) (hw : ∀ i, 0 ≤ w i)
    (hf : ∀ i, f i ∈ kleinMatchingSpace) :
    IsRealMatchingSOS (fun j => ∑ i, w i * f i j ^ 2) := by
  have hx (i : Fin n) : ∃ x : Fin 14 → ℝ, kleinMatchingEvaluationLinear x = f i := hf i
  choose x hxe using hx
  refine ⟨n, fun i => Real.sqrt (w i) • x i, fun j => ?_⟩
  apply Finset.sum_congr rfl
  intro i _
  have he :
      fourMatchingEvaluation (Real.sqrt (w i) • x i) j = Real.sqrt (w i) * f i j := by
    change (kleinMatchingEvaluationLinear (Real.sqrt (w i) • x i)) j = _
    rw [map_smul, hxe i, Pi.smul_apply, smul_eq_mul]
  rw [he, mul_pow, Real.sq_sqrt (hw i)]

private theorem klein_one_square (w : ℝ) (f : KleinMatchingFunction)
    (hw : 0 ≤ w) (hf : f ∈ kleinMatchingSpace) :
    IsRealMatchingSOS (fun j => w * f j ^ 2) := by
  simpa only [Fin.sum_univ_one] using
    (klein_weighted_squares (n := 1) (fun _ => w) (fun _ => f) (fun _ => hw) (fun _ => hf))

private theorem klein_split_ordinary_bounds (β p q : Fin 3 → ℝ) (cNeg : ℝ)
    (hbox : ∀ i, |p i| + |q i| ≤ β i) (hPos : ∑ i, |p i| ≤ (∑ i, β i) - cNeg)
    (hNeg : ∑ i, |q i| ≤ cNeg) :
    ∃ a : Fin 3 → ℝ, (∀ i, |p i| ≤ a i ∧ a i ≤ β i - |q i|) ∧
      (∑ i, a i) = (∑ i, β i) - cNeg := by
  let L := ∑ i, |p i|
  let R := ∑ i, (β i - |q i|)
  let c := (∑ i, β i) - cNeg
  have hLR (i : Fin 3) : |p i| ≤ β i - |q i| := by linarith only [hbox i]
  have hLc : L ≤ c := hPos
  have hcR : c ≤ R := by
    dsimp only [c, R]
    rw [Finset.sum_sub_distrib]
    linarith only [hNeg]
  by_cases hRL : R = L
  · refine ⟨fun i => |p i|, fun i => ⟨le_rfl, hLR i⟩, ?_⟩
    exact le_antisymm hLc (hcR.trans_eq hRL)
  · have hden : 0 < R - L := sub_pos.mpr
      (lt_of_le_of_ne (hLc.trans hcR) (Ne.symm hRL))
    let t := (c - L) / (R - L)
    have ht₀ : 0 ≤ t := div_nonneg (sub_nonneg.mpr hLc) hden.le
    have ht₁ : t ≤ 1 := (div_le_one hden).2 (sub_le_sub_right hcR L)
    let a (i : Fin 3) := |p i| + t * (β i - |q i| - |p i|)
    refine ⟨a, fun i => ⟨?_, ?_⟩, ?_⟩
    · exact le_add_of_nonneg_right (mul_nonneg ht₀ (sub_nonneg.mpr (hLR i)))
    · dsimp only [a]
      have h := mul_le_mul_of_nonneg_right ht₁ (sub_nonneg.mpr (hLR i))
      linarith only [h]
    · change (∑ i, (|p i| + t * (β i - |q i| - |p i|))) = c
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib]
      change L + t * (R - L) = c
      have ht : t * (R - L) = c - L := div_mul_cancel₀ _ hden.ne'
      rw [ht]
      ring

/-- The two absolute-sum bounds certify the cost with ordinary squares.
This includes all zero and equality cases of the split. -/
theorem klein_matching_sos_of_absolute_bounds (β p q : Fin 3 → ℝ) (cNeg : ℝ)
    (hbox : ∀ i, |p i| + |q i| ≤ β i) (hPos : ∑ i, |p i| ≤ (∑ i, β i) - cNeg)
    (hNeg : ∑ i, |q i| ≤ cNeg) : IsRealMatchingSOS (kleinMatchingCost β p q cNeg) := by
  obtain ⟨a, ha, hsum⟩ := klein_split_ordinary_bounds β p q cNeg hbox hPos hNeg
  let b := fun i => β i - a i
  have hb (i : Fin 3) : |q i| ≤ b i := by
    dsimp only [b]
    linarith only [(ha i).2]
  have hbsum : ∑ i, b i = cNeg := by
    change (∑ i, (β i - a i)) = cNeg
    rw [Finset.sum_sub_distrib, hsum, sub_sub_cancel]
  have h1 (i : Fin 3) : 0 ≤ a i + p i := by linarith only [(ha i).1, neg_abs_le (p i)]
  have h2 (i : Fin 3) : 0 ≤ a i - p i := sub_nonneg.mpr ((le_abs_self (p i)).trans (ha i).1)
  have h3 (i : Fin 3) : 0 ≤ b i + q i := by linarith only [hb i, neg_abs_le (q i)]
  have h4 (i : Fin 3) : 0 ≤ b i - q i := sub_nonneg.mpr ((le_abs_self (q i)).trans (hb i))
  have hc1 := klein_weighted_squares (fun i => a i + p i) (fun i => kleinOrdinaryPlus i 1)
    h1 (fun i => kleinOrdinaryPlus_mem i 1)
  have hc2 := klein_weighted_squares (fun i => a i - p i) (fun i => kleinOrdinaryPlus i (-1))
    h2 (fun i => kleinOrdinaryPlus_mem i (-1))
  have hc3 := klein_weighted_squares (fun i => b i + q i) (fun i => kleinOrdinaryMinus i 1)
    h3 (fun i => kleinOrdinaryMinus_mem i 1)
  have hc4 := klein_weighted_squares (fun i => b i - q i) (fun i => kleinOrdinaryMinus i (-1))
    h4 (fun i => kleinOrdinaryMinus_mem i (-1))
  have sos := klein_sos_add (klein_sos_add (klein_sos_add hc1 hc2) hc3) hc4
  convert sos using 1
  funext j
  simp only [Pi.add_apply,
    fun i => kleinOrdinaryPlus_sq i j 1 (Or.inl rfl),
    fun i => kleinOrdinaryPlus_sq i j (-1) (Or.inr rfl),
    fun i => kleinOrdinaryMinus_sq i j 1 (Or.inl rfl),
    fun i => kleinOrdinaryMinus_sq i j (-1) (Or.inr rfl)]
  have hbj := congrArg (fun c : ℝ => c * kleinCycle j) hbsum
  simp only [b, Fin.sum_univ_three] at hbj
  simp only [kleinMatchingCost, kleinOrdinaryPlus, kleinOrdinaryMinus, b, Fin.sum_univ_three]
  linear_combination hbj

private def kleinMixedSquareLead : KleinMatchingFunction :=
  fun j => -kleinCycle j + ∑ i : Fin 3, kleinOrdinaryPlus i 1 j

private theorem kleinMixedSquareLead_mem : kleinMixedSquareLead ∈ kleinMatchingSpace := by
  have heq : kleinMixedSquareLead = -kleinCycle + ∑ i : Fin 3, kleinOrdinaryPlus i 1 := by
    funext j
    simp only [kleinMixedSquareLead, Pi.add_apply, Pi.neg_apply, Finset.sum_apply]
  rw [heq]
  exact kleinMatchingSpace.add_mem (kleinMatchingSpace.neg_mem kleinCycle_mem)
    (kleinMatchingSpace.sum_mem fun i _ => kleinOrdinaryPlus_mem i 1)

private def kleinMixedRay : KleinMatchingFunction :=
  fun j => kleinMixedSquareLead j ^ 2 - 2 * kleinOrdinaryPlus 0 1 j * kleinOrdinaryPlus 1 1 j

private def kleinPlusNumerator (i : Fin 3) (j : Fin 24) : ℤ :=
  kleinMatchingFeatureTable (Fin.castAdd 6 i.succ) j +
    kleinMatchingFeatureTable (Fin.natAdd 4 (Fin.castAdd 3 i)) j

private def kleinLeadNumerator (j : Fin 24) : ℤ :=
  -2 * kleinMatchingFeatureTable 0 j + ∑ i : Fin 3, kleinPlusNumerator i j

private theorem kleinOrdinaryPlus_eq_half (i : Fin 3) (j : Fin 24) :
    kleinOrdinaryPlus i 1 j = (kleinPlusNumerator i j : ℝ) / 2 := by
  simp [kleinOrdinaryPlus, kleinFaceIndicator, kleinFaceSignPlus, kleinPlusNumerator]

private theorem kleinMixedSquareLead_eq_half (j : Fin 24) :
    kleinMixedSquareLead j = (kleinLeadNumerator j : ℝ) / 2 := by
  simp only [kleinMixedSquareLead, kleinCycle, kleinOrdinaryPlus_eq_half, kleinLeadNumerator,
    Int.cast_add, Int.cast_mul, Int.cast_neg, Int.cast_ofNat, Int.cast_sum, add_div, Finset.sum_div]
  ring

set_option maxRecDepth 4096 in
private theorem kleinPlus_numerator_identities (j : Fin 24) :
    kleinPlusNumerator 0 j * kleinPlusNumerator 2 j =
        kleinPlusNumerator 0 j * kleinPlusNumerator 1 j ∧
      kleinPlusNumerator 1 j * kleinPlusNumerator 2 j =
        kleinPlusNumerator 0 j * kleinPlusNumerator 1 j ∧
      kleinLeadNumerator j ^ 2 - 2 * kleinPlusNumerator 0 j * kleinPlusNumerator 1 j =
        2 * kleinLeadNumerator j := by
  revert j
  decide +kernel

private theorem klein_plus_pair_products (j : Fin 24) :
    kleinOrdinaryPlus 0 1 j * kleinOrdinaryPlus 2 1 j =
        kleinOrdinaryPlus 0 1 j * kleinOrdinaryPlus 1 1 j ∧
      kleinOrdinaryPlus 1 1 j * kleinOrdinaryPlus 2 1 j =
        kleinOrdinaryPlus 0 1 j * kleinOrdinaryPlus 1 1 j := by
  obtain ⟨h02, h12, _⟩ := kleinPlus_numerator_identities j
  have h02' := congrArg (Int.cast : ℤ → ℝ) h02
  have h12' := congrArg (Int.cast : ℤ → ℝ) h12
  simp only [Int.cast_mul] at h02' h12'
  simp only [kleinOrdinaryPlus_eq_half]
  exact ⟨by nlinarith only [h02'], by nlinarith only [h12']⟩

private theorem kleinMixedRay_eq_lead (j : Fin 24) : kleinMixedRay j = kleinMixedSquareLead j := by
  have h := congrArg (Int.cast : ℤ → ℝ) (kleinPlus_numerator_identities j).2.2
  simp only [Int.cast_sub, Int.cast_mul, Int.cast_pow, Int.cast_ofNat] at h
  simp only [kleinMixedRay, kleinMixedSquareLead_eq_half, kleinOrdinaryPlus_eq_half]
  nlinarith only [h]

private theorem klein_cap_cost_decomposition (u vPos vNeg : Fin 3 → ℝ) (t : ℝ) (j : Fin 24) :
    let p := fun i => (t + u i) / 2
    let β := fun i => p i + (vPos i + vNeg i) / 2
    let q := fun i => (vPos i - vNeg i) / 2
    let cNeg := (∑ i, β i) - (t + ∑ i, u i) / 2
    kleinMatchingCost β p q cNeg j =
      t * kleinMixedRay j + ∑ i, (u i * kleinOrdinaryPlus i 1 j +
        vPos i * kleinOrdinaryMinus i 1 j + vNeg i * kleinOrdinaryMinus i (-1) j) := by
  dsimp only
  simp only [kleinMatchingCost, kleinMixedRay_eq_lead, kleinMixedSquareLead, kleinOrdinaryPlus,
    kleinOrdinaryMinus, Fin.sum_univ_three]
  ring

/-- The mixed cap has an explicit sum of squares below the strong threshold.
The construction uses one rank-one contribution and diagonal squares. -/
theorem klein_mixed_cap_sos (a b c t : ℝ) (vPos vNeg : Fin 3 → ℝ)
    (ht : 0 < t) (hthreshold : t ≤ a * (b + c) - b * c)
    (hPos : ∀ i, 0 ≤ vPos i) (hNeg : ∀ i, 0 ≤ vNeg i) :
    let u : Fin 3 → ℝ := ![a ^ 2, b ^ 2, c ^ 2]
    let p := fun i => (t + u i) / 2
    let β := fun i => p i + (vPos i + vNeg i) / 2
    let q := fun i => (vPos i - vNeg i) / 2
    let cNeg := (∑ i, β i) - (t + ∑ i, u i) / 2
    IsRealMatchingSOS (kleinMatchingCost β p q cNeg) := by
  let T := a * (b + c) - b * c
  let θ := t / T
  have hT : 0 < T := ht.trans_le hthreshold
  have hθ₀ : 0 ≤ θ := div_nonneg ht.le hT.le
  have hθ₁ : θ ≤ 1 := (div_le_one hT).2 hthreshold
  have hθT : θ * T = t := div_mul_cancel₀ _ hT.ne'
  let u : Fin 3 → ℝ := ![a ^ 2, b ^ 2, c ^ 2]
  let v : Fin 3 → ℝ := ![a, -b, -c]
  let p := fun i => (t + u i) / 2
  let β := fun i => p i + (vPos i + vNeg i) / 2
  let q := fun i => (vPos i - vNeg i) / 2
  let cNeg := (∑ i, β i) - (t + ∑ i, u i) / 2
  let f : KleinMatchingFunction := ∑ i : Fin 3, v i • kleinOrdinaryPlus i 1
  have hf : f ∈ kleinMatchingSpace :=
    kleinMatchingSpace.sum_mem fun i _ =>
      kleinMatchingSpace.smul_mem (v i) (kleinOrdinaryPlus_mem i 1)
  have hu (i : Fin 3) : 0 ≤ u i := by fin_cases i <;> exact sq_nonneg _
  have hc0 := klein_one_square t kleinMixedSquareLead ht.le kleinMixedSquareLead_mem
  have hc1 := klein_weighted_squares (fun i => (1 - θ) * u i) (fun i => kleinOrdinaryPlus i 1)
    (fun i => mul_nonneg (sub_nonneg.mpr hθ₁) (hu i)) (fun i => kleinOrdinaryPlus_mem i 1)
  have hc2 := klein_one_square θ f hθ₀ hf
  have hc3 := klein_weighted_squares vPos (fun i => kleinOrdinaryMinus i 1)
    hPos (fun i => kleinOrdinaryMinus_mem i 1)
  have hc4 := klein_weighted_squares vNeg (fun i => kleinOrdinaryMinus i (-1))
    hNeg (fun i => kleinOrdinaryMinus_mem i (-1))
  have sos := klein_sos_add (klein_sos_add (klein_sos_add (klein_sos_add hc0 hc1) hc2) hc3) hc4
  change IsRealMatchingSOS (kleinMatchingCost β p q cNeg)
  convert sos using 1
  funext j
  have hd := klein_cap_cost_decomposition u vPos vNeg t j
  change kleinMatchingCost β p q cNeg j = _ at hd
  rw [hd]
  obtain ⟨h02, h12⟩ := klein_plus_pair_products j
  have hA_sq (i : Fin 3) := kleinOrdinaryPlus_sq i j 1 (Or.inl rfl)
  have hf_sq : f j ^ 2 =
      (∑ i, u i * kleinOrdinaryPlus i 1 j) -
        2 * T * (kleinOrdinaryPlus 0 1 j * kleinOrdinaryPlus 1 1 j) := by
    have hv : v 0 = a ∧ v 1 = -b ∧ v 2 = -c := ⟨rfl, rfl, rfl⟩
    have hu : u 0 = a ^ 2 ∧ u 1 = b ^ 2 ∧ u 2 = c ^ 2 := ⟨rfl, rfl, rfl⟩
    simp only [f, Finset.sum_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Fin.sum_univ_three, T,
      hv.1, hv.2.1, hv.2.2, hu.1, hu.2.1, hu.2.2]
    linear_combination a ^ 2 * hA_sq 0 + b ^ 2 * hA_sq 1 + c ^ 2 * hA_sq 2
      - 2 * a * c * h02 + 2 * b * c * h12
  simp only [Pi.add_apply, hf_sq, hA_sq,
    fun i => kleinOrdinaryMinus_sq i j 1 (Or.inl rfl),
    fun i => kleinOrdinaryMinus_sq i j (-1) (Or.inr rfl)]
  simp only [kleinMixedRay, Fin.sum_univ_three]
  linear_combination
    (2 * kleinOrdinaryPlus 0 1 j * kleinOrdinaryPlus 1 1 j) * hθT

/-- A prism with no strictly negative five-dimensional real compression
has a sum of squares on the normalized mixed cap. -/
theorem klein_mixed_cap_sos_of_no_negative_five (a b c t : ℝ) (vPos vNeg : Fin 3 → ℝ)
    (hb : 0 ≤ b) (hc : 0 ≤ c) (hab : b ≤ a) (hac : c ≤ a) (ht : 0 < t)
    (hPos : ∀ i, 0 ≤ vPos i) (hNeg : ∀ i, 0 ≤ vNeg i)
    (hcompress :
      let u : Fin 3 → ℝ := ![a ^ 2, b ^ 2, c ^ 2]
      let p := fun i => (t + u i) / 2
      let β := fun i => p i + (vPos i + vNeg i) / 2
      let q := fun i => (vPos i - vNeg i) / 2
      let cNeg := (∑ i, β i) - (t + ∑ i, u i) / 2
      ∀ L : (Fin 5 → ℝ) →ₗ[ℝ] KleinPrismSpace,
        ∃ x ≠ 0, 0 ≤ kleinPrismForm β p q cNeg (L x)) :
    let u : Fin 3 → ℝ := ![a ^ 2, b ^ 2, c ^ 2]
    let p := fun i => (t + u i) / 2
    let β := fun i => p i + (vPos i + vNeg i) / 2
    let q := fun i => (vPos i - vNeg i) / 2
    let cNeg := (∑ i, β i) - (t + ∑ i, u i) / 2
    IsRealMatchingSOS (kleinMatchingCost β p q cNeg) := by
  let u : Fin 3 → ℝ := ![a ^ 2, b ^ 2, c ^ 2]
  let p := fun i => (t + u i) / 2
  let β := fun i => p i + (vPos i + vNeg i) / 2
  let q := fun i => (vPos i - vNeg i) / 2
  have hbox (i : Fin 3) : p i + |q i| ≤ β i := by
    have hi := abs_le.mpr (show -((vPos i + vNeg i) / 2) ≤ q i ∧
        q i ≤ (vPos i + vNeg i) / 2 from by
      dsimp only [q]
      constructor <;> linarith only [hPos i, hNeg i])
    dsimp only [β]
    linarith only [hi]
  have hthreshold : t ≤ a * (b + c) - b * c := by
    by_contra! h
    obtain ⟨L, hL⟩ := kleinPrism_negative_five a b c t β q hb hc hab hac ht h hbox
    obtain ⟨x, hx, hnonneg⟩ := hcompress L
    exact not_lt_of_ge hnonneg (hL x hx)
  exact klein_mixed_cap_sos a b c t vPos vNeg ht hthreshold hPos hNeg

end
end MOC
