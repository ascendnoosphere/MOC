import MOC.SecularCauchyMinorCharts
import MOC.InverseBasisDeterminantExpansion
import MOC.SecularQuadraticRealRootInclusion
import Mathlib.Topology.Algebra.Polynomial

/-! Every spectral polynomial determinant objective is weighted harmonic
and bounded on the fixed simple secular chamber. -/

open BigOperators Filter Finset Matrix Polynomial Set
open scoped Topology

namespace MOC

noncomputable section

variable {n : ℕ}

/-- The determinant of a polynomial spectral evaluation plus a diagonal partner. -/
def secularEvaluationDet (d r : Fin n → ℝ) (p : ℝ[X]) (a : Fin n → ℝ) : ℝ :=
  (diagonal a + Polynomial.aeval (secularColumnModel d r) p).det

theorem polynomial_aeval_intertwines {K : Type*} [CommSemiring K]
    {A B S : Matrix (Fin n) (Fin n) K}
    (h : A*S=S*B) (p : K[X]) : Polynomial.aeval A p * S = S * Polynomial.aeval B p := by
  have hp (m : ℕ) : A^m*S=S*B^m := by
    induction m with
    | zero => simp
    | succ m ih =>
        rw [pow_succ, Matrix.mul_assoc, h, ← Matrix.mul_assoc, ih, Matrix.mul_assoc, pow_succ]
  rw [Polynomial.aeval_eq_sum_range, Polynomial.aeval_eq_sum_range, Matrix.sum_mul, Matrix.mul_sum]
  simp_rw [Matrix.smul_mul, Matrix.mul_smul, hp]

theorem secularEvaluationDet_eq_update_of_pos (d r : Fin n → ℝ)
    (hr : ∀ i, 0 < r i) (p : ℝ[X]) (a : Fin n → ℝ) :
    secularEvaluationDet d r p a =
      (diagonal a + Polynomial.aeval (diagonal d +
        vecMulVec (fun i => Real.sqrt (r i)) (fun i => Real.sqrt (r i))) p).det := by
  let x (i : Fin n) := Real.sqrt (r i)
  let S := diagonal x
  let K := secularColumnModel d r
  let H := diagonal d + vecMulVec x x
  have hS : S.det ≠ 0 := by
    change (diagonal x).det ≠ 0
    rw [Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => (Real.sqrt_pos.2 (hr i)).ne')
  have hKS : H*S=S*K := by
    ext i j : 1
    simp only [H, S, K, secularColumnModel,
      Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.add_apply, Matrix.of_apply,
      Matrix.vecMulVec_apply, x]
    by_cases hij : i = j
    · subst j
      simp only [Matrix.diagonal_apply_eq]
      have hxi := Real.mul_self_sqrt (hr i).le
      linear_combination (Real.sqrt (r i)) * hxi
    · rw [Matrix.diagonal_apply_ne _ hij, zero_add, zero_add, mul_assoc,
        Real.mul_self_sqrt (hr j).le]
  have hdiag : diagonal a * S = S * diagonal a := by
    simp only [S, Matrix.diagonal_mul_diagonal, mul_comm]
  have he : (diagonal a + Polynomial.aeval H p)*S = S*(diagonal a + Polynomial.aeval K p) := by
    rw [Matrix.add_mul, Matrix.mul_add, hdiag, polynomial_aeval_intertwines hKS p]
  have he' := congrArg Matrix.det he
  simp only [Matrix.det_mul] at he'
  unfold secularEvaluationDet
  exact (mul_right_cancel₀ hS (he'.trans (mul_comm _ _))).symm

private theorem secularEvaluationDet_eq_symmetric (h d : Fin n → ℝ)
    (hd : d ∈ secularChamber h) (p : ℝ[X]) (a : Fin n → ℝ) :
    secularEvaluationDet d (secularResidue h d) p a =
      (diagonal a + Polynomial.aeval (secularChamberMatrix h d) p).det :=
  secularEvaluationDet_eq_update_of_pos d (secularResidue h d) hd.2 p a

private theorem secularEvaluationDet_expansion (h d : Fin n → ℝ)
    (hh : Function.Injective h) (hd : d ∈ secularChamber h) (p : ℝ[X]) (a : Fin n → ℝ) :
    secularEvaluationDet d (secularResidue h d) p a =
      ∑ J : Finset (Fin n), ∑ I : Finset (Fin n), secularProjectionMinor d (secularResidue h d) h I J *
        ((∏ i ∈ Iᶜ, a i) * ∏ j ∈ J, p.eval (h j)) := by
  let X := cauchyMatrix d h
  have hsep := chamber_nodes_avoid_spectrum h d hd
  have hX := cauchyMatrix_isUnit_det d h hd.1 hh hsep
  rw [secularEvaluationDet, secularEvaluation_columnModel_eq_cauchy d h hd.1 hh hsep,
    det_inverse_basis_eq_sum_principal X X⁻¹ (Matrix.nonsing_inv_mul X hX)
      (isUnit_iff_ne_zero.mp hX)]
  apply Finset.sum_congr rfl
  intro J _
  apply Finset.sum_congr rfl
  intro I _
  simp only [X, secularProjectionMinor, secularProjector_columnModel_eq_cauchy d h hd.1 hh hsep J]

/-- A real linear combination of any finite family of polynomial determinant
evaluations has the continuity, boundedness, and harmonic hypotheses of the chamber theorem. -/
theorem secularEvaluation_objective {κ : Type*} [Fintype κ]
    (h : Fin n → ℝ) (hh : Function.Injective h) (p : κ → ℝ[X])
    (a : κ → Fin n → ℝ) (c : κ → ℝ) :
    SecularObjectiveProperties h (fun q => ∑ k, c k * secularEvaluationDet q.1 q.2 (p k) (a k)) := by
  let F (q : (Fin n → ℝ) × (Fin n → ℝ)) := ∑ k, c k * secularEvaluationDet q.1 q.2 (p k) (a k)
  let U := 1 + ∑ i, |h i|
  have hU (i : Fin n) : h i < U := by
    have hi : |h i| ≤ ∑ j, |h j| := Finset.single_le_sum (fun j _ => abs_nonneg (h j)) (mem_univ i)
    dsimp only [U]
    linarith only [hi, le_abs_self (h i)]
  have hKc : Continuous (fun q : (Fin n → ℝ) × (Fin n → ℝ) => secularColumnModel q.1 q.2) := by
    apply continuous_matrix
    intro i j
    simp only [secularColumnModel, Matrix.add_apply, Matrix.diagonal_apply, Matrix.of_apply]
    split_ifs <;> fun_prop
  have hF : Continuous F := by
    apply continuous_finset_sum
    intro k _
    exact continuous_const.mul ((continuous_const.add ((p k).continuous_aeval.comp hKc)).matrix_det)
  let M := |U| + ∑ i, (U-h i)
  let K := Set.pi Set.univ (fun _ : Fin n => Set.pi Set.univ (fun _ : Fin n => Icc (-M) M))
  have hK : IsCompact K := isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_Icc
  let G (A : Matrix (Fin n) (Fin n) ℝ) := ∑ k, c k * (diagonal (a k) + Polynomial.aeval A (p k)).det
  have hG : Continuous G := by
    apply continuous_finset_sum
    intro k _
    exact continuous_const.mul ((continuous_const.add (p k).continuous_aeval).matrix_det)
  obtain ⟨B,hB⟩ := (hK.image hG).bddAbove
  have hb : ∀ d ∈ secularChamber h, F (d,secularResidue h d) ≤ B := by
    intro d hd
    have hm : secularChamberMatrix h d ∈ K := by
      intro i _ j _
      exact abs_le.mp (abs_secularChamberMatrix_entry_le h d hd.1 (fun k => (hd.2 k).le) U hU i j)
    have hle : G (secularChamberMatrix h d) ≤ B := hB ⟨secularChamberMatrix h d,hm,rfl⟩
    simpa only [F, G, secularEvaluationDet_eq_symmetric h d hd] using hle
  let α := κ × Finset (Fin n) × Finset (Fin n)
  let w (k : α) := c k.1 * ((∏ i ∈ k.2.2ᶜ, a k.1 i) * ∏ j ∈ k.2.1, (p k.1).eval (h j))
  let V (k : α) (d : Fin n → ℝ) := secularProjectionMinor d (secularResidue h d) h k.2.2 k.2.1
  let W (d : Fin n → ℝ) := ∑ k : α, w k * V k d
  have hFW (d : Fin n → ℝ) (hd : d ∈ secularChamber h) : F (d,secularResidue h d) = W d := by
    change (∑ k : κ, c k * secularEvaluationDet d (secularResidue h d) (p k) (a k)) =
      ∑ k : κ × Finset (Fin n) × Finset (Fin n), w k * V k d
    simp only [Fintype.sum_prod_type, V, w, secularEvaluationDet_expansion h d hh hd]
    apply Finset.sum_congr rfl
    intro k _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro J _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro I _
    ring
  have hrel (d : Fin n → ℝ) (hd : d ∈ secularChamber h) (i : Fin n) :
      (fun t => F (Function.update d i t, secularResidue h (Function.update d i t))) =ᶠ[𝓝 (d i)]
        (fun t => W (Function.update d i t)) := by
    have hC : Continuous (fun t : ℝ => Function.update d i t) := continuous_const.update i continuous_id
    have ht : Tendsto (fun t : ℝ => Function.update d i t) (𝓝 (d i)) (𝓝 d) := by
      have hc0 : ContinuousAt (fun t : ℝ => Function.update d i t) (d i) := hC.continuousAt
      simpa only [Function.update_eq_self] using hc0.tendsto
    exact (ht.eventually ((isOpen_secularChamber h).mem_nhds hd)).mono (fun t ht => hFW _ ht)
  have hn (d : Fin n → ℝ) (hd : d ∈ secularChamber h) (i : Fin n) :
      ∀ᶠ t in 𝓝 (d i), ∀ k : α, DifferentiableAt ℝ (fun t => V k (Function.update d i t)) t :=
    Filter.eventually_all.mpr fun k => (secularProjectionMinor_coordinate_regular d h hh hd k.2.2 k.2.1 i).1
  have hs (d : Fin n → ℝ) (hd : d ∈ secularChamber h) (i : Fin n) (k : α) :
      HasDerivAt (deriv (fun t => w k * V k (Function.update d i t)))
        (w k * deriv (deriv (fun t => V k (Function.update d i t))) (d i)) (d i) := by
    have hh' := ((secularProjectionMinor_coordinate_regular d h hh hd k.2.2 k.2.1 i).2.hasDerivAt).const_mul (w k)
    apply hh'.congr_of_eventuallyEq
    filter_upwards [hn d hd i] with t ht
    exact ((ht k).hasDerivAt.const_mul (w k)).deriv
  have hsW (d : Fin n → ℝ) (hd : d ∈ secularChamber h) (i : Fin n) :
      HasDerivAt (deriv (fun t => W (Function.update d i t)))
        (∑ k : α, w k * deriv (deriv (fun t => V k (Function.update d i t))) (d i)) (d i) := by
    have he := HasDerivAt.sum (u := (univ : Finset α)) fun k _ => hs d hd i k
    apply he.congr_of_eventuallyEq
    filter_upwards [hn d hd i] with t ht
    exact deriv_sum fun k _ => (ht k).const_mul (w k)
  refine ⟨hF, ⟨B,hb⟩, ?_, ?_, ?_⟩
  · intro d hd i
    filter_upwards [hn d hd i, (hrel d hd i).eventuallyEq_nhds] with t ht he
    exact (DifferentiableAt.sum fun k _ => (ht k).const_mul (w k)).congr_of_eventuallyEq he
  · intro d hd i
    exact ((hsW d hd i).congr_of_eventuallyEq (hrel d hd i).deriv).differentiableAt
  · intro d hd
    change (∑ i, secularResidue h d i * deriv (deriv (fun t =>
      F (Function.update d i t, secularResidue h (Function.update d i t)))) (d i)) = 0
    simp_rw [(hrel d hd _).deriv.deriv_eq, (hsW d hd _).deriv, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro k _
    simp_rw [mul_left_comm _ (w k), ← Finset.mul_sum]
    by_cases hk : k.2.2.card = k.2.1.card
    · rw [show (∑ i, secularResidue h d i * deriv (deriv (fun t => V k (Function.update d i t))) (d i)) = 0 from
        secularProjectionMinor_weighted_second_sum d h hh hd k.2.2 k.2.1 hk, mul_zero]
    · simp [V, secularProjectionMinor, hk]


end

end MOC
