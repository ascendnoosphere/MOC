import MOC.Small
import MOC.Geometry
import MOC.Support
import MOC.SupportedWeights
import MOC.TwoSpectralCircles
import MOC.TwoValues
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Tactic.LinearCombination
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.Order.Lattice

/-! Arbitrary finite block decompositions and large shifts in every order. -/

open BigOperators Filter Matrix Polynomial
open scoped Topology

namespace MOC

noncomputable section

private def splitFirstBlock {k : ℕ} (m : Fin (k + 1) → ℕ) :
    Fin (m 0) ⊕ (Σ j : Fin k, Fin (m j.succ)) ≃ Σ j, Fin (m j) where
  toFun
    | .inl i => ⟨0, i⟩
    | .inr ⟨j, v⟩ => ⟨j.succ, v⟩
  invFun := fun x => Fin.cases (motive := fun j => Fin (m j) → _) Sum.inl
    (fun j v => Sum.inr ⟨j, v⟩) x.1 x.2
  left_inv := by rintro (i | ⟨j, v⟩) <;> simp
  right_inv := by
    rintro ⟨j, v⟩
    cases j using Fin.cases <;> simp

/-- A block diagonal sum of any finite number of covered instances is covered. -/
private theorem holds_blockDiagonal' {k : ℕ} (m : Fin k → ℕ)
    (a b : (j : Fin k) → Fin (m j) → ℂ)
    (V : (j : Fin k) → Matrix (Fin (m j)) (Fin (m j)) ℂ)
    (hV : ∀ j, Holds (a j) (b j) (V j)) :
    Holds (fun i => a i.1 i.2) (fun i => b i.1 i.2) (Matrix.blockDiagonal' V) := by
  induction k with
  | zero =>
    have h : Matrix.blockDiagonal' V = 1 := by
      ext i j : 1
      exact Fin.elim0 i.1
    rw [h]
    exact holds_identity _ _
  | succ k ih =>
    let e := splitFirstBlock m
    have hBlocks : (Matrix.blockDiagonal' V).submatrix e e =
        Matrix.fromBlocks (V 0) 0 0 (Matrix.blockDiagonal' (fun j : Fin k => V j.succ)) := by
      ext i j : 1
      rcases i with i | ⟨i, x⟩ <;> rcases j with j | ⟨j, y⟩
      · change Matrix.blockDiagonal' V ⟨0, i⟩ ⟨0, j⟩ = V 0 i j
        exact Matrix.blockDiagonal'_apply_eq V 0 i j
      · change Matrix.blockDiagonal' V ⟨0, i⟩ ⟨j.succ, y⟩ = 0
        exact Matrix.blockDiagonal'_apply_ne V i y (Fin.succ_ne_zero j).symm
      · change Matrix.blockDiagonal' V ⟨i.succ, x⟩ ⟨0, j⟩ = 0
        exact Matrix.blockDiagonal'_apply_ne V x j (Fin.succ_ne_zero i)
      · change Matrix.blockDiagonal' V ⟨i.succ, x⟩ ⟨j.succ, y⟩ =
          Matrix.blockDiagonal' (fun l : Fin k => V l.succ) ⟨i, x⟩ ⟨j, y⟩
        by_cases hij : i = j
        · subst j
          simp only [Matrix.blockDiagonal'_apply_eq]
        · exact (Matrix.blockDiagonal'_apply_ne V x y ((Fin.succ_injective k).ne hij)).trans
            (Matrix.blockDiagonal'_apply_ne _ _ _ hij).symm
    have hs (f : (j : Fin (k + 1)) → Fin (m j) → ℂ) :
        (fun (i : Σ j, Fin (m j)) => f i.1 i.2) ∘ e =
          Sum.elim (f 0) (fun i => f i.1.succ i.2) := by
      funext i
      cases i <;> rfl
    apply (holds_reindex_iff e e _ _ _).mp
    rw [hBlocks, hs a, hs b]
    exact holds_directSum _ _ _ _ _ _ (hV 0)
      (ih (fun j => m j.succ) (fun j => a j.succ) (fun j => b j.succ)
        (fun j => V j.succ) (fun j => hV j.succ))

/-- Independent relabelings of the rows and columns can expose any finite number
of paired blocks. It suffices that the determinant inclusion holds on each block. -/
theorem holds_of_finite_paired_blocks {ι : Type*} [Fintype ι] [DecidableEq ι]
    {k : ℕ} (m : Fin k → ℕ) (eRow eCol : (Σ j, Fin (m j)) ≃ ι)
    (a b : ι → ℂ) (U : Matrix ι ι ℂ)
    (V : (j : Fin k) → Matrix (Fin (m j)) (Fin (m j)) ℂ)
    (hBlocks : U.submatrix eRow eCol = Matrix.blockDiagonal' V)
    (hV : ∀ j, Holds (fun i => a (eRow ⟨j, i⟩)) (fun i => b (eCol ⟨j, i⟩)) (V j)) :
    Holds a b U := by
  have h : Holds (a ∘ eRow) (b ∘ eCol) (Matrix.blockDiagonal' V) :=
    holds_blockDiagonal' m (fun j i => a (eRow ⟨j, i⟩)) (fun j i => b (eCol ⟨j, i⟩)) V hV
  exact (holds_reindex_iff eRow eCol a b U).mp (hBlocks.symm ▸ h)

/-- A relative unitary with any finite number of paired blocks of order at most
three satisfies the determinant inclusion for arbitrary complex spectra. -/
theorem holds_of_finite_paired_blocks_le_three {ι : Type*} [Fintype ι] [DecidableEq ι]
    {k : ℕ} (m : Fin k → ℕ) (hm : ∀ j, m j ≤ 3)
    (eRow eCol : (Σ j, Fin (m j)) ≃ ι) (a b : ι → ℂ) (U : Matrix ι ι ℂ)
    (hU : IsUnitary U) (V : (j : Fin k) → Matrix (Fin (m j)) (Fin (m j)) ℂ)
    (hBlocks : U.submatrix eRow eCol = Matrix.blockDiagonal' V) : Holds a b U := by
  have h := unitary_reindex eRow eCol hU
  rw [hBlocks] at h
  obtain ⟨h₁, h₂⟩ := h
  rw [Matrix.blockDiagonal'_conjTranspose, ← Matrix.blockDiagonal'_mul,
    ← Matrix.blockDiagonal'_one, Matrix.blockDiagonal'_inj] at h₁ h₂
  exact holds_of_finite_paired_blocks m eRow eCol a b U V hBlocks fun j =>
    conjecture_le_three (hm j) _ _ _ ⟨congrFun h₁ j, congrFun h₂ j⟩

section CommonShift

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
private theorem shiftProduct_coeffs (x : ι → ℂ) (s : Finset ι) :
    let p : ℂ[X] := ∏ j ∈ s, (1 + C (x j) * X)
    p.coeff 0 = 1 ∧ p.coeff 1 = ∑ j ∈ s, x j ∧
      2 * p.coeff 2 = (∑ j ∈ s, x j) ^ 2 - ∑ j ∈ s, x j ^ 2 := by
  classical
  have hmul (P Q : ℂ[X]) :
      (P * Q).coeff 2 = P.coeff 0 * Q.coeff 2 + P.coeff 1 * Q.coeff 1 +
        P.coeff 2 * Q.coeff 0 := by
    norm_num [Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
      Finset.sum_range_succ]
  have hlinear₀ (z : ℂ) : (1 + C z * X).coeff 0 = 1 := by
    norm_num [coeff_add, coeff_one, coeff_C_mul_X]
  have hlinear₁ (z : ℂ) : (1 + C z * X).coeff 1 = z := by
    norm_num [coeff_add, coeff_one, coeff_C_mul_X]
  have hlinear₂ (z : ℂ) : (1 + C z * X).coeff 2 = 0 := by
    norm_num [coeff_add, coeff_one, coeff_C_mul_X]
  induction s using Finset.induction_on with
  | empty => norm_num [coeff_one]
  | @insert j s hj ih =>
    rcases ih with ⟨h0, h1, h2⟩
    simp only [Finset.prod_insert hj, Finset.sum_insert hj, mul_coeff_zero, mul_coeff_one,
      hmul, hlinear₀, hlinear₁, hlinear₂, h0, h1, one_mul, mul_one, add_zero, zero_add, zero_mul]
    exact ⟨trivial, add_comm _ _, by linear_combination h2⟩

private theorem trace_eq_weighted_assignment (a b : ι → ℂ) (U : Matrix ι ι ℂ)
    (w : Equiv.Perm ι → ℂ)
    (hw : ∀ i j, marginal w i j = (Complex.normSq (U i j) : ℂ)) :
    (∑ σ, w σ * ∑ j, a (σ j) * b j) = (diagonal a * (U * diagonal b * Uᴴ)).trace := by
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  have hj (j : ι) : (∑ σ, w σ * (a (σ j) * b j)) =
      ∑ i, (Complex.normSq (U i j) : ℂ) * (a i * b j) := by
    rw [sum_weighted_evaluation w j (fun i => a i * b j)]
    simp only [hw]
  simp only [hj]
  rw [Finset.sum_comm]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.diagonal_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.conjTranspose_apply,
    Complex.normSq_eq_conj_mul_self, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [starRingEnd_apply]
  ring

private theorem shiftGap_factor (a b : ι → ℂ) (U : Matrix ι ι ℂ) (hU : IsUnitary U) :
    ∃ Q : Equiv.Perm ι → ℂ[X], ∀ σ,
      (Q σ).eval 0 = (diagonal a * (U * diagonal b * Uᴴ)).trace - ∑ j, a (σ j) * b j ∧
      ∀ t : ℂ,
        matchingProduct (fun j => 1 + t * a j) (fun j => t * b j) σ -
          determinantValue (fun j => 1 + t * a j) (fun j => t * b j) U = t ^ 2 * (Q σ).eval t := by
  let x (σ : Equiv.Perm ι) (j : ι) := a (σ j) + b j
  let cost (σ : Equiv.Perm ι) := ∑ j, a (σ j) * b j
  let S := (∑ j, a j) + ∑ j, b j
  let K := (S ^ 2 - ((∑ j, a j ^ 2) + ∑ j, b j ^ 2)) / 2
  let T := (diagonal a * (U * diagonal b * Uᴴ)).trace
  let P (σ : Equiv.Perm ι) : ℂ[X] := ∏ j, (1 + C (x σ j) * X)
  let w := signedWeight U
  let D := ∑ σ, C (w σ) * P σ
  have hx (σ : Equiv.Perm ι) : ∑ j, x σ j = S := by
    simp only [x, S, Finset.sum_add_distrib, Equiv.sum_comp σ a]
  have hx₂ (σ : Equiv.Perm ι) :
      ∑ j, x σ j ^ 2 = ((∑ j, a j ^ 2) + ∑ j, b j ^ 2) + 2 * cost σ := by
    calc
      _ = ∑ j, (a (σ j) ^ 2 + b j ^ 2 + 2 * (a (σ j) * b j)) := by
        apply Finset.sum_congr rfl
        intro j _
        dsimp only [x]
        ring
      _ = _ := by
        simp only [cost, Finset.sum_add_distrib, ← Finset.mul_sum,
          Equiv.sum_comp σ (fun i => a i ^ 2)]
  have hP0 (σ : Equiv.Perm ι) : (P σ).coeff 0 = 1 :=
    (shiftProduct_coeffs (x σ) Finset.univ).1
  have hP1 (σ : Equiv.Perm ι) : (P σ).coeff 1 = S :=
    (shiftProduct_coeffs (x σ) Finset.univ).2.1.trans (hx σ)
  have hP2 (σ : Equiv.Perm ι) : (P σ).coeff 2 = K - cost σ := by
    have h := (shiftProduct_coeffs (x σ) Finset.univ).2.2
    change 2 * (P σ).coeff 2 = (∑ j, x σ j) ^ 2 - ∑ j, x σ j ^ 2 at h
    rw [hx, hx₂] at h
    dsimp only [K]
    linear_combination h / 2
  have hw : ∑ σ, w σ = 1 := sum_signedWeight U (det_ne_zero_of_unitary hU)
  have hT : (∑ σ, w σ * cost σ) = T :=
    trace_eq_weighted_assignment a b U w (marginal_signedWeight U hU)
  have hD0 : D.coeff 0 = 1 := by
    simp only [D, finset_sum_coeff, coeff_C_mul, hP0, mul_one, hw]
  have hD1 : D.coeff 1 = S := by
    simp only [D, finset_sum_coeff, coeff_C_mul, hP1, ← Finset.sum_mul, hw, one_mul]
  have hD2 : D.coeff 2 = K - T := by
    simp only [D, finset_sum_coeff, coeff_C_mul, hP2, mul_sub, Finset.sum_sub_distrib,
      ← Finset.sum_mul, hw, hT, one_mul]
  have hdiv (σ : Equiv.Perm ι) : X ^ 2 ∣ P σ - D := by
    apply X_pow_dvd_iff.mpr
    intro d hd
    have hf : d = 0 ∨ d = 1 := by omega
    rcases hf with rfl | rfl
    · simp only [coeff_sub, hP0, hD0, sub_self]
    · simp only [coeff_sub, hP1, hD1, sub_self]
  choose Q hQ using hdiv
  have hPEval (σ : Equiv.Perm ι) (t : ℂ) : (P σ).eval t =
      matchingProduct (fun j => 1 + t * a j) (fun j => t * b j) σ := by
    simp only [P, eval_prod, eval_add, eval_one, eval_mul, eval_C, eval_X, matchingProduct]
    apply Finset.prod_congr rfl
    intro j _
    dsimp only [x]
    ring
  have hDEval (t : ℂ) : D.eval t =
      determinantValue (fun j => 1 + t * a j) (fun j => t * b j) U := by
    simp only [D, eval_finset_sum, eval_mul, eval_C, hPEval]
    exact signed_determinant _ _ U hU
  refine ⟨Q, fun σ => ⟨?_, fun t => ?_⟩⟩
  · calc
      (Q σ).eval 0 = (Q σ).coeff 0 := (coeff_zero_eq_eval_zero _).symm
      _ = (X ^ 2 * Q σ).coeff 2 := (coeff_X_pow_mul (Q σ) 2 0).symm
      _ = (P σ - D).coeff 2 := by rw [← hQ σ]
      _ = T - cost σ := by rw [coeff_sub, hP2, hD2]; ring
  · rw [← hPEval, ← hDEval, ← eval_sub, hQ σ, eval_mul, eval_pow, eval_X]

/-- A positive trace-of-product margin in all unit directions gives determinant
inclusion for sufficiently large shifts, in every finite order. -/
theorem holds_common_shift_outside (a b : ι → ℂ) (U : Matrix ι ι ℂ) (hU : IsUnitary U)
    (δ : ℝ) (hδ : 0 < δ)
    (hmargin : ∀ η : ℂ, ‖η‖ = 1 → ∃ σ : Equiv.Perm ι,
      δ ≤ (η * ((diagonal a * (U * diagonal b * Uᴴ)).trace - ∑ j, a (σ j) * b j)).re) :
    ∃ R : ℝ, ∀ z : ℂ, R ≤ ‖z‖ → Holds (fun i => a i - z) b U := by
  obtain ⟨Q, hQ⟩ := shiftGap_factor a b U hU
  let L (σ : Equiv.Perm ι) := (diagonal a * (U * diagonal b * Uᴴ)).trace - ∑ j, a (σ j) * b j
  have hQL (σ : Equiv.Perm ι) : (Q σ).eval 0 = L σ := (hQ σ).1
  have hnear : ∀ᶠ t : ℂ in 𝓝 0, ∀ σ, ‖(Q σ).eval t - L σ‖ < δ := by
    apply Filter.eventually_all.mpr
    intro σ
    obtain ⟨r, hr, he⟩ := Metric.continuousAt_iff.mp (Q σ).continuousAt δ hδ
    apply Metric.eventually_nhds_iff.mpr
    refine ⟨r, hr, fun t ht => ?_⟩
    rw [← hQL σ, ← dist_eq_norm]
    exact he ht
  obtain ⟨ρ, hρ, herr⟩ := Metric.eventually_nhds_iff.mp hnear
  have hsmall (t : ℂ) (ht : ‖t‖ < ρ) (ht₀ : t ≠ 0) :
      Holds (fun j => 1 + t * a j) (fun j => t * b j) U := by
    have hs := herr (show dist t 0 < ρ by simpa only [dist_zero_right] using ht)
    apply (holds_iff_directional _ _ _).mpr
    intro k
    by_cases hk : k = 0
    · exact ⟨1, by simp [hk]⟩
    let v := k * t ^ 2
    have hv : v ≠ 0 := mul_ne_zero hk (pow_ne_zero 2 ht₀)
    have hvnorm : ‖v‖ ≠ 0 := (norm_pos_iff.mpr hv).ne'
    let η := v / (‖v‖ : ℂ)
    have hη : ‖η‖ = 1 := by
      dsimp only [η]
      rw [norm_div, Complex.norm_of_nonneg (norm_nonneg v), div_self hvnorm]
    obtain ⟨σ, hσ⟩ := hmargin η hη
    change δ ≤ (η * L σ).re at hσ
    have he : -(η * ((Q σ).eval t - L σ)).re < δ := calc
      _ ≤ ‖-(η * ((Q σ).eval t - L σ))‖ := by
        simpa only [Complex.neg_re] using Complex.re_le_norm (-(η * ((Q σ).eval t - L σ)))
      _ = ‖(Q σ).eval t - L σ‖ := by rw [norm_neg, norm_mul, hη, one_mul]
      _ < δ := hs σ
    have hpos : 0 ≤ (η * (Q σ).eval t).re := by
      rw [show η * (Q σ).eval t = η * L σ + η * ((Q σ).eval t - L σ) by ring, Complex.add_re]
      linarith only [he, hσ]
    have hscale : v = (‖v‖ : ℂ) * η := by
      exact (mul_div_cancel₀ v (Complex.ofReal_ne_zero.mpr hvnorm)).symm
    refine ⟨σ, sub_nonneg.mp ?_⟩
    rw [← Complex.sub_re, ← mul_sub, (hQ σ).2 t, ← mul_assoc]
    change 0 ≤ (v * (Q σ).eval t).re
    rw [hscale, mul_assoc, Complex.re_ofReal_mul]
    exact mul_nonneg (norm_nonneg v) hpos
  refine ⟨ρ⁻¹ + 1, fun z hz => ?_⟩
  have hz' : ρ⁻¹ < ‖z‖ := by linarith only [hz]
  have hzpos : 0 < ‖z‖ := (inv_pos.mpr hρ).trans hz'
  have hz₀ : z ≠ 0 := norm_pos_iff.mp hzpos
  let t := (-z)⁻¹
  have ht : ‖t‖ < ρ := by
    dsimp only [t]
    rw [norm_inv, norm_neg]
    simpa only [inv_inv] using (inv_lt_inv₀ hzpos (inv_pos.mpr hρ)).mpr hz'
  have h := hsmall t ht (inv_ne_zero (neg_ne_zero.mpr hz₀))
  have hA : (fun j => -z * (1 + t * a j)) = fun j => a j - z := by
    funext j
    dsimp only [t]
    rw [mul_add, mul_one, ← mul_assoc, mul_inv_cancel₀ (neg_ne_zero.mpr hz₀), one_mul]
    ring
  have hB : (fun j => -z * (t * b j)) = b := by
    funext j
    dsimp only [t]
    rw [← mul_assoc, mul_inv_cancel₀ (neg_ne_zero.mpr hz₀), one_mul]
  have hscaled : Holds (fun j => -z * (1 + t * a j)) (fun j => -z * (t * b j)) U :=
    hull_of_common_factor (determinantValue_scale _ _ U (-z)) (matchingProduct_scale _ _ (-z)) h
  rwa [hA, hB] at hscaled

/-- If the assignment costs of permutations supported by `U` do not lie on
one affine line, the trace of the product has a positive support margin. -/
theorem trace_margin_of_supported_assignments [Nonempty ι] (a b : ι → ℂ)
    (U : Matrix ι ι ℂ) (hU : IsUnitary U)
    (hspan : ∀ η : ℂ, η ≠ 0 → ∃ σ τ : Equiv.Perm ι,
      (∀ j, U (σ j) j ≠ 0) ∧ (∀ j, U (τ j) j ≠ 0) ∧
      (η * ∑ j, a (σ j) * b j).re ≠ (η * ∑ j, a (τ j) * b j).re) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ η : ℂ, ‖η‖ = 1 → ∃ σ : Equiv.Perm ι,
      δ ≤ (η * ((diagonal a * (U * diagonal b * Uᴴ)).trace - ∑ j, a (σ j) * b j)).re := by
  classical
  let T := (diagonal a * (U * diagonal b * Uᴴ)).trace
  let cost (σ : Equiv.Perm ι) := ∑ j, a (σ j) * b j
  let c (η : ℂ) (i j : ι) := (η * (a i * b j)).re
  let D : Matrix ι ι ℝ := Matrix.of (fun j i => Complex.normSq (U i j))
  let F (η : ℂ) : Matrix ι ι ℝ →ₗ[ℝ] ℝ :=
    ∑ j : ι, ∑ i : ι, c η i j • Matrix.entryLinearMap ℝ ℝ j i
  have hD : D ∈ doublyStochastic ℝ ι := normSq_transpose_doublyStochastic U hU
  have hF (η : ℂ) (M : Matrix ι ι ℝ) : F η M = ∑ j, ∑ i, c η i j * M j i := by
    simp only [F, LinearMap.sum_apply, LinearMap.smul_apply, Matrix.entryLinearMap_apply, smul_eq_mul]
  have hperm (σ : Equiv.Perm ι) (j i : ι) :
      σ.permMatrix ℝ j i = (if σ j = i then 1 else 0) := by
    simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, eq_comm]
  have hFp (η : ℂ) (σ : Equiv.Perm ι) : F η (σ.permMatrix ℝ) = (η * cost σ).re := by
    rw [hF]
    simp only [hperm, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true,
      cost, c, Finset.mul_sum, Complex.re_sum]
  have hFD (η : ℂ) : F η D = (η * T).re := by
    rw [hF, Finset.sum_comm]
    simp only [T, Matrix.trace, Matrix.diag_apply, Matrix.diagonal_mul, Finset.mul_sum, Complex.re_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Matrix.mul_apply]
    simp only [D, Matrix.of_apply, Matrix.mul_diagonal, Matrix.conjTranspose_apply,
      Finset.mul_sum, Complex.re_sum]
    apply Finset.sum_congr rfl
    intro j _
    dsimp only [c]
    rw [mul_comm, ← Complex.re_ofReal_mul]
    congr 1
    rw [Complex.normSq_eq_conj_mul_self, starRingEnd_apply]
    ring
  let f (σ : Equiv.Perm ι) (η : ℂ) := (η * (T - cost σ)).re
  have hpos (η : ℂ) (hη : η ≠ 0) : ∃ σ : Equiv.Perm ι, 0 < f σ η := by
    by_contra! h
    have hmin (σ : Equiv.Perm ι) : F η D ≤ F η (σ.permMatrix ℝ) := by
      rw [hFD, hFp]
      simpa only [f, mul_sub, Complex.sub_re, sub_nonpos] using h σ
    have heq (σ : Equiv.Perm ι) (hσ : ∀ j, U (σ j) j ≠ 0) :
        (η * cost σ).re = (η * T).re := by
      simpa only [hFp, hFD] using linearMap_eq_of_birkhoff_min hD (F η) hmin σ
        (fun j => Complex.normSq_pos.mpr (hσ j))
    obtain ⟨σ, τ, hσ, hτ, hne⟩ := hspan η hη
    exact hne ((heq σ hσ).trans (heq τ hτ).symm)
  let G (η : ℂ) : ℝ := Finset.univ.sup' Finset.univ_nonempty (fun σ => f σ η)
  have hG : Continuous G := Continuous.finset_sup'_apply Finset.univ_nonempty
    (fun σ _ => Complex.continuous_re.comp (continuous_id.mul continuous_const))
  have hS : (Metric.sphere (0 : ℂ) 1).Nonempty := ⟨1, by simp [Metric.mem_sphere, dist_zero_right]⟩
  obtain ⟨η₀, hη₀, hmin⟩ := (isCompact_sphere (0 : ℂ) 1).exists_isMinOn hS hG.continuousOn
  have hη₀ne : η₀ ≠ 0 := by rintro rfl; simp [Metric.mem_sphere] at hη₀
  obtain ⟨σ₀, hσ₀⟩ := hpos η₀ hη₀ne
  have hGpos : 0 < G η₀ := hσ₀.trans_le (Finset.le_sup' (fun σ => f σ η₀) (Finset.mem_univ σ₀))
  refine ⟨G η₀, hGpos, fun η hη => ?_⟩
  have hSη : η ∈ Metric.sphere (0 : ℂ) 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using hη
  have hle : G η₀ ≤ G η := hmin hSη
  obtain ⟨σ, _, he⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun σ => f σ η)
  change G η = f σ η at he
  rw [he] at hle
  exact ⟨σ, hle⟩

/-- Large shifts satisfy the inclusion when the relative unitary has full
support, the first spectrum is nonconstant, and the second is noncollinear. -/
private theorem holds_common_shift_outside_of_noncollinear (a b : ι → ℂ) (U : Matrix ι ι ℂ)
    (hU : IsUnitary U) (hfull : ∀ i j, U i j ≠ 0)
    (ha : ∃ i i', a i ≠ a i')
    (hb : ∀ κ : ℂ, κ ≠ 0 → ¬ ∃ t : ℝ, ∀ j, (κ * b j).re = t) :
    ∃ R : ℝ, ∀ z : ℂ, R ≤ ‖z‖ → Holds (fun i => a i - z) b U := by
  obtain ⟨i, i', hia⟩ := ha
  letI : Nonempty ι := ⟨i⟩
  suffices hspan : ∀ η : ℂ, η ≠ 0 → ∃ σ τ : Equiv.Perm ι,
      (∀ j, U (σ j) j ≠ 0) ∧ (∀ j, U (τ j) j ≠ 0) ∧
      (η * ∑ j, a (σ j) * b j).re ≠ (η * ∑ j, a (τ j) * b j).re by
    obtain ⟨δ, hδ, hmargin⟩ := trace_margin_of_supported_assignments a b U hU hspan
    exact holds_common_shift_outside a b U hU δ hδ hmargin
  intro η hη
  let κ := η * (a i - a i')
  have hκ : κ ≠ 0 := mul_ne_zero hη (sub_ne_zero.mpr hia)
  obtain ⟨j, hj⟩ : ∃ j, (κ * b j).re ≠ (κ * b i).re := by
    by_contra! h
    exact hb κ hκ ⟨_, h⟩
  have hji : j ≠ i := fun h => hj (congrArg (fun j => (κ * b j).re) h)
  let τ₀ := Equiv.swap j i'
  have hτ₀i : τ₀ i = i := Equiv.swap_apply_of_ne_of_ne hji.symm (fun h => hia (congrArg a h))
  have hτ₀j : τ₀ j = i' := Equiv.swap_apply_left _ _
  let τ := (Equiv.swap i j).trans τ₀
  refine ⟨τ₀, τ, fun k => hfull _ _, fun k => hfull _ _, ?_⟩
  have hdiff : (∑ k, a (τ₀ k) * b k) - (∑ k, a (τ k) * b k) =
      (a i - a i') * (b i - b j) := by
    rw [← Finset.sum_sub_distrib]
    have hsum : (∑ k ∈ ({i, j} : Finset ι), (a (τ₀ k) * b k - a (τ k) * b k)) =
        ∑ k, (a (τ₀ k) * b k - a (τ k) * b k) := by
      apply Finset.sum_subset (Finset.subset_univ _)
      intro k _ hk
      have hout : k ≠ i ∧ k ≠ j := by simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using hk
      rw [show τ k = τ₀ k by simp only [τ, Equiv.trans_apply, Equiv.swap_apply_of_ne_of_ne hout.1 hout.2], sub_self]
    rw [← hsum, Finset.sum_pair hji.symm]
    simp only [τ, Equiv.trans_apply, Equiv.swap_apply_left, Equiv.swap_apply_right, hτ₀i, hτ₀j]
    ring
  intro he
  apply hj
  have hzero : (η * ((∑ k, a (τ₀ k) * b k) - (∑ k, a (τ k) * b k))).re = 0 := by
    rw [mul_sub, Complex.sub_re, he, sub_self]
  rwa [hdiff, ← mul_assoc, show η * (a i - a i') = κ from rfl, mul_sub, Complex.sub_re,
    sub_eq_zero, eq_comm] at hzero

omit [Fintype ι] [DecidableEq ι] in
private theorem spectrumOnGeneralizedCircle_of_projection (a : ι → ℂ) {κ : ℂ} (hκ : κ ≠ 0)
    {t : ℝ} (ha : ∀ i, (κ * a i).re = t) : SpectrumOnGeneralizedCircle a := by
  refine spectrumOnGeneralizedCircle_of_line a κ.re (-κ.im) t ?_ (fun i => ?_)
  · by_contra! h
    exact hκ (Complex.ext (by simpa only [Complex.zero_re] using h.1)
      (by simpa only [Complex.zero_im, neg_eq_zero] using h.2))
  · simpa only [Complex.mul_re, sub_eq_add_neg, neg_mul] using ha i

/-- For arbitrary spectra and a relative unitary with full support, the
determinant inclusion holds for every sufficiently large shift. -/
theorem holds_common_shift_outside_of_full_support {n : ℕ} (a b : Fin n → ℂ)
    (U : Matrix (Fin n) (Fin n) ℂ) (hU : IsUnitary U) (hfull : ∀ i j, U i j ≠ 0) :
    ∃ R : ℝ, ∀ z : ℂ, R ≤ ‖z‖ → Holds (fun i => a i - z) b U := by
  classical
  cases n with
  | zero => exact ⟨0, fun _ _ => conjecture_zero _ _ _ hU⟩
  | succ n =>
    by_cases hA : ∀ i, a i = a 0
    · exact ⟨0, fun z _ => holds_of_two_values_left _ _ U hU (a 0 - z) (a 0 - z)
        (fun i => Or.inl (congrArg (fun x => x - z) (hA i)))⟩
    by_cases hB : ∀ j, b j = b 0
    · exact ⟨0, fun _ _ => holds_of_two_values _ _ U hU (b 0) (b 0) (fun j => Or.inl (hB j))⟩
    obtain ⟨i, hi⟩ : ∃ i, a i ≠ a 0 := not_forall.mp hA
    obtain ⟨j, hj⟩ : ∃ j, b j ≠ b 0 := not_forall.mp hB
    by_cases hBL : ∃ κ : ℂ, κ ≠ 0 ∧ ∃ t : ℝ, ∀ j, (κ * b j).re = t
    · by_cases hAL : ∃ κ : ℂ, κ ≠ 0 ∧ ∃ t : ℝ, ∀ i, (κ * a i).re = t
      · obtain ⟨κa, hκa, ta, hta⟩ := hAL
        obtain ⟨κb, hκb, tb, htb⟩ := hBL
        refine ⟨0, fun z _ => holds_of_generalized_circular_spectra _ _ ?_ ?_ U hU⟩
        · exact spectrumOnGeneralizedCircle_of_projection (fun i => a i - z) hκa
            (t := ta - (κa * z).re) (fun i => by rw [mul_sub, Complex.sub_re, hta])
        · exact spectrumOnGeneralizedCircle_neg (spectrumOnGeneralizedCircle_of_projection b hκb htb)
      · have hU' : IsUnitary Uᴴ := ⟨by simpa using hU.2, by simpa using hU.1⟩
        have hfull' (i j : Fin (n + 1)) : Uᴴ i j ≠ 0 := star_ne_zero.mpr (hfull j i)
        obtain ⟨R, hR⟩ := holds_common_shift_outside_of_noncollinear b a Uᴴ hU' hfull'
          ⟨j, 0, hj⟩ (fun κ hκ ht => hAL ⟨κ, hκ, ht⟩)
        refine ⟨R, fun z hz => (holds_swap_iff _ _ hU).mp ?_⟩
        simpa only [sub_add_cancel] using
          (holds_shift_iff (fun i => b i - z) a hU' z).mpr (hR z hz)
    · exact holds_common_shift_outside_of_noncollinear a b U hU hfull ⟨i, 0, hi⟩
        (fun κ hκ ht => hBL ⟨κ, hκ, ht⟩)

end CommonShift

end

end MOC
