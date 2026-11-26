import MOC.DeterminantModulusBound
import MOC.FiniteEntropyDuality
import Mathlib.Analysis.SpecialFunctions.Log.ERealExp

/-! Entropic transport for determinants of matrices with a finite
spectral kernel. The matrix entry basis keeps the actual overlaps. -/

open BigOperators Matrix

namespace MOC

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- The normalized logarithm of the matrix determinant modulus. -/
def matrixLogDet (W : Matrix ι ι ℂ) : EReal :=
  if W.det = 0 then ⊥ else (Real.log ‖W.det‖ / (Fintype.card ι : ℝ) : ℝ)

private theorem log_det_le_log_mean_normSq (W : Matrix ι ι ℂ) (hW : W.det ≠ 0) :
    2 * Real.log ‖W.det‖ / Fintype.card ι ≤
      Real.log ((∑ i, ∑ j, Complex.normSq (W i j)) / Fintype.card ι) := by
  let A := W * Wᴴ
  have hA := Matrix.posSemidef_self_mul_conjTranspose W
  let eig := hA.1.eigenvalues
  have hnon (i : ι) : 0 ≤ eig i := hA.eigenvalues_nonneg i
  have htrace : ∑ i, eig i = A.trace.re := by
    have he : (↑(∑ i, eig i) : ℂ) = A.trace := by
      rw [Complex.ofReal_sum]
      conv_rhs => rw [hA.1.spectral_theorem]
      rw [Matrix.trace_mul_cycle, unitary.coe_star_mul_self, Matrix.one_mul, Matrix.trace_diagonal]
      rfl
    simpa only [Complex.ofReal_re] using congrArg Complex.re he
  have hentries : A.trace.re = ∑ i, ∑ j, Complex.normSq (W i j) := by
    simp only [A, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Complex.re_sum, Complex.star_def, Complex.mul_conj, Complex.ofReal_re]
  have hprod : ∏ i, eig i = Complex.normSq W.det := by
    have he : (↑(∏ i, eig i) : ℂ) = A.det := by
      rw [hA.1.det_eq_prod_eigenvalues, Complex.ofReal_prod]
    rw [A, Matrix.det_mul, Matrix.det_conjTranspose, Complex.star_def,
      Complex.mul_conj] at he
    exact Complex.ofReal_injective he
  have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hgm := Real.geom_mean_le_arith_mean (Finset.univ : Finset ι)
    (fun _ => (1 : ℝ)) eig (by simp) (by simpa using hn) (fun i _ => hnon i)
  have hbound : (Complex.normSq W.det) ^ ((Fintype.card ι : ℝ)⁻¹) ≤
      (∑ i, ∑ j, Complex.normSq (W i j)) / Fintype.card ι := by
    simpa only [Real.rpow_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
      one_mul, hprod, htrace, hentries] using hgm
  have hpos := Complex.normSq_pos.mpr hW
  have hleft := Real.rpow_pos_of_pos hpos ((Fintype.card ι : ℝ)⁻¹)
  have hlog := Real.log_le_log hleft hbound
  rw [Real.log_rpow hpos, Complex.normSq_eq_norm_sq, Real.log_pow] at hlog
  convert hlog using 1 <;> push_cast <;> ring

/-- Exponential row and column scaling bounds twice the normalized log
determinant by the corresponding logarithmic partition function. -/
theorem matrix_logDet_potential_bound
    (W : Matrix ι ι ℂ) (hW : W.det ≠ 0) (u v : ι → ℝ) :
    2 * Real.log ‖W.det‖ / Fintype.card ι ≤
      ((∑ i, u i) + ∑ j, v j) / Fintype.card ι +
        Real.log (∑ i, ∑ j, (Complex.normSq (W i j) / Fintype.card ι) *
          Real.exp (-(u i + v j))) := by
  let D (x : ι → ℝ) : Matrix ι ι ℂ :=
    Matrix.diagonal fun i => (Real.exp (-x i / 2) : ℂ)
  let S := D u * W * D v
  have hdiag (x : ι → ℝ) :
      ‖(D x).det‖ = Real.exp (-(∑ i, x i) / 2) := by
    simp only [D, Matrix.det_diagonal, norm_prod, Complex.norm_real]
    simp_rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    rw [← Real.exp_sum]
    simp only [← Finset.sum_div, Finset.sum_neg_distrib]
  have hs : ‖S.det‖ = Real.exp (-(∑ i, u i) / 2) * ‖W.det‖ *
      Real.exp (-(∑ i, v i) / 2) := by
    simp only [S, Matrix.det_mul, norm_mul, hdiag]
  have hnormW : 0 < ‖W.det‖ := norm_pos_iff.mpr hW
  have hnormS : 0 < ‖S.det‖ := by
    rw [hs]
    exact mul_pos (mul_pos (Real.exp_pos _) hnormW) (Real.exp_pos _)
  have hl : Real.log ‖S.det‖ = -(∑ i, u i) / 2 + Real.log ‖W.det‖ - (∑ i, v i) / 2 := by
    rw [hs, Real.log_mul (mul_pos (Real.exp_pos _) hnormW).ne' (Real.exp_pos _).ne',
      Real.log_mul (Real.exp_pos _).ne' hnormW.ne', Real.log_exp, Real.log_exp]
    ring
  have hent (i j : ι) :
      Complex.normSq (S i j) = Complex.normSq (W i j) * Real.exp (-(u i + v j)) := by
    simp only [S, D, Matrix.mul_diagonal, Matrix.diagonal_mul, map_mul,
      Complex.normSq_ofReal]
    rw [show Real.exp (-u i / 2) * Real.exp (-u i / 2) = Real.exp (-u i) by
      rw [← Real.exp_add]; congr 1; ring,
      show Real.exp (-v j / 2) * Real.exp (-v j / 2) = Real.exp (-v j) by
        rw [← Real.exp_add]; congr 1; ring]
    rw [neg_add, Real.exp_add]
    ring
  have hmean :
      (∑ i, ∑ j, Complex.normSq (S i j)) / Fintype.card ι =
        ∑ i, ∑ j, (Complex.normSq (W i j) / Fintype.card ι) *
          Real.exp (-(u i + v j)) := by
    simp only [hent, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have h := log_det_le_log_mean_normSq S (norm_pos_iff.mp hnormS)
  rw [hl, hmean] at h
  linarith only [h]

/-- The pairs on which the entry kernel and the overlap are both nonzero. -/
abbrev MatrixKernelSupport (W : Matrix ι ι ℂ) :=
  {e : ι × ι // W e.1 e.2 ≠ 0}

private theorem sum_matrixKernelSupport (W : Matrix ι ι ℂ) (F : ι × ι → ℝ)
    (hF : ∀ e, W e.1 e.2 = 0 → F e = 0) :
    (∑ e : MatrixKernelSupport W, F e.val) = ∑ i, ∑ j, F (i, j) := by
  classical
  rw [← Fintype.sum_prod_type]
  rw [← Finset.subtype_univ (fun e : ι × ι => W e.1 e.2 ≠ 0),
    Finset.sum_subtype_eq_sum_filter, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro e _
  by_cases he : W e.1 e.2 = 0 <;> simp [he, hF]

/-- For a nonsingular matrix there is a coupling on its nonzero entries
with uniform row and column marginals whose entropy score bounds twice
the normalized log determinant. -/
theorem exists_matrix_entropic_transport (W : Matrix ι ι ℂ) (hW : W.det ≠ 0) :
    ∃ q ∈ stdSimplex ℝ (MatrixKernelSupport W),
      (∀ i, (∑ e : MatrixKernelSupport W, if e.val.1 = i then q e else 0) =
        (Fintype.card ι : ℝ)⁻¹) ∧
      (∀ j, (∑ e : MatrixKernelSupport W, if e.val.2 = j then q e else 0) =
        (Fintype.card ι : ℝ)⁻¹) ∧
      2 * Real.log ‖W.det‖ / Fintype.card ι ≤
        finiteEntropyScore (fun e : MatrixKernelSupport W =>
          Complex.normSq (W e.val.1 e.val.2) / Fintype.card ι) q := by
  classical
  let n : ℝ := Fintype.card ι
  have hn : 0 < n := by exact_mod_cast Fintype.card_pos
  let κ := MatrixKernelSupport W
  let E := ι ⊕ ι → ℝ
  let L (i : ι) : E := Pi.single (Sum.inl i) 1
  let R (j : ι) : E := Pi.single (Sum.inr j) 1
  let g (e : κ) := L e.val.1 + R e.val.2
  let w (e : κ) := Complex.normSq (W e.val.1 e.val.2) / n
  let m : E := fun _ => n⁻¹
  have hgL (e : κ) (i : ι) : g e (Sum.inl i) = if e.val.1 = i then 1 else 0 := by
    simp [g, L, R, Pi.single_apply, eq_comm]
  have hgR (e : κ) (j : ι) : g e (Sum.inr j) = if e.val.2 = j then 1 else 0 := by
    simp [g, L, R, Pi.single_apply, eq_comm]
  have hw (e : κ) : 0 < w e := div_pos (Complex.normSq_pos.mpr e.property) hn
  obtain ⟨σ, hσ⟩ : ∃ σ : Equiv.Perm ι, ∀ j, W (σ j) j ≠ 0 := by
    by_contra! h
    apply hW
    rw [Matrix.det_apply']
    apply Finset.sum_eq_zero
    intro σ _
    obtain ⟨j, hj⟩ := h σ
    rw [Finset.prod_eq_zero (Finset.mem_univ j) hj, mul_zero]
  let e (j : ι) : κ := ⟨(σ j, j), hσ j⟩
  haveI : Nonempty κ := ⟨e (Classical.choice ‹Nonempty ι›)⟩
  let q₀ (x : κ) : ℝ := ∑ j, if x = e j then n⁻¹ else 0
  have hs (F : κ → ℝ) : (∑ x, q₀ x * F x) = ∑ j, n⁻¹ * F (e j) := by
    simp only [q₀, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    simp [ite_mul]
  have hq₀ : q₀ ∈ stdSimplex ℝ κ := by
    refine ⟨fun x => Finset.sum_nonneg (fun j _ => ?_), ?_⟩
    · split <;> positivity
    · have ht := hs (fun _ => 1)
      simp only [mul_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at ht
      exact ht.trans (mul_inv_cancel₀ hn.ne')
  have hm₀ : (∑ x, q₀ x • g x) = m := by
    funext k
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hs]
    cases k with
    | inl i =>
      simp only [hgL, e, m]
      rw [Equiv.sum_comp σ (fun l => n⁻¹ * (if l = i then 1 else 0))]
      simp [mul_ite]
    | inr j =>
      simp [hgR, e, m, mul_ite]
  have hbound (f : E →L[ℝ] ℝ) :
      2 * Real.log ‖W.det‖ / n ≤ f m + Real.log (∑ x, w x * Real.exp (-f (g x))) := by
    let u (i : ι) := f (L i)
    let v (j : ι) := f (R j)
    have hm : m = n⁻¹ • ((∑ i, L i) + ∑ j, R j) := by
      funext k
      cases k <;> simp [m, L, R, Pi.single_apply]
    have hf : f m = ((∑ i, u i) + ∑ j, v j) / n := by
      rw [hm, map_smul, map_add, map_sum, map_sum]
      simp [u, v, smul_eq_mul, div_eq_mul_inv, mul_comm]
    have hterm (x : κ) : f (g x) = u x.val.1 + v x.val.2 := map_add f _ _
    have hpart : (∑ x, w x * Real.exp (-f (g x))) =
        ∑ i, ∑ j, (Complex.normSq (W i j) / n) * Real.exp (-(u i + v j)) := by
      simp only [w, hterm]
      exact sum_matrixKernelSupport W
        (fun p => (Complex.normSq (W p.1 p.2) / n) * Real.exp (-(u p.1 + v p.2)))
        (fun p hp => by simp [hp])
    rw [hf, hpart]
    exact matrix_logDet_potential_bound W hW u v
  obtain ⟨q, hq, hm, hscore⟩ := exists_finiteEntropyScore_of_potential_bounds
    g w hw m _ ⟨q₀, hq₀, hm₀⟩ hbound
  refine ⟨q, hq, fun i => ?_, fun j => ?_, hscore⟩
  · have hi := congrFun hm (Sum.inl i)
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hgL, mul_ite, mul_one,
      mul_zero, m] using hi
  · have hj := congrFun hm (Sum.inr j)
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hgR, mul_ite, mul_one,
      mul_zero, m] using hj

/-- A coupling is a probability vector on the nonzero entries with each
row and column marginal equal to the reciprocal of the order. -/
def IsMatrixKernelCoupling (W : Matrix ι ι ℂ) (q : MatrixKernelSupport W → ℝ) : Prop :=
  q ∈ stdSimplex ℝ (MatrixKernelSupport W) ∧
    (∀ i, (∑ e : MatrixKernelSupport W, if e.val.1 = i then q e else 0) =
      (Fintype.card ι : ℝ)⁻¹) ∧
    (∀ j, (∑ e : MatrixKernelSupport W, if e.val.2 = j then q e else 0) =
      (Fintype.card ι : ℝ)⁻¹)

/-- The entropy upper bound also applies to singular matrices, with
the extended logarithm of a zero determinant equal to minus infinity. -/
theorem matrixLogDet_le_entropic_transport (W : Matrix ι ι ℂ) :
    matrixLogDet W ≤ sSup {h : EReal | ∃ q, IsMatrixKernelCoupling W q ∧
      h = (finiteEntropyScore (fun e : MatrixKernelSupport W =>
          Complex.normSq (W e.val.1 e.val.2) / Fintype.card ι) q / 2 : ℝ)} := by
  by_cases hW : W.det = 0
  · simp only [matrixLogDet, hW, if_true, bot_le]
  obtain ⟨q, hq, hr, hc, hs⟩ := exists_matrix_entropic_transport W hW
  rw [matrixLogDet, if_neg hW]
  let y := finiteEntropyScore (fun e : MatrixKernelSupport W =>
    Complex.normSq (W e.val.1 e.val.2) / Fintype.card ι) q / 2
  calc
    _ ≤ (y : EReal) := by
      exact_mod_cast (show Real.log ‖W.det‖ / Fintype.card ι ≤ y by
        dsimp only [y]
        linarith only [hs])
    _ ≤ _ := le_sSup ⟨q, ⟨hq, hr, hc⟩, rfl⟩

/-- The ordered kernel in the two separate orthonormal eigenbases. -/
def entrySpectralKernel (K U : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  Matrix.of fun i j => K i j * U i j

private theorem kernel_projection_entry (U : Matrix ι ι ℂ) (i j k l : ι) :
    (diagonal (Pi.single i 1) * (U * diagonal (Pi.single j 1) * Uᴴ)) k l =
      Pi.single i (1 : ℂ) k * (U k j * Uᴴ j l) := by
  rw [Matrix.diagonal_mul, Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Pi.single_apply, mul_ite, mul_one,
    mul_zero, ite_mul, zero_mul]
  simp

/-- The entrywise kernel with its right basis restored is the ordered
evaluation on the two families of rank-one spectral projections. -/
theorem entrySpectralKernel_mul_adjoint_eq_spectral_sum (K U : Matrix ι ι ℂ) :
    entrySpectralKernel K U * Uᴴ =
      ∑ i, ∑ j, K i j •
        (diagonal (Pi.single i 1) * (U * diagonal (Pi.single j 1) * Uᴴ)) := by
  ext k l : 1
  rw [Matrix.mul_apply]
  simp only [entrySpectralKernel, Matrix.of_apply, Matrix.sum_apply,
    Matrix.smul_apply, smul_eq_mul, kernel_projection_entry, Pi.single_apply,
    ite_mul, mul_ite, zero_mul, one_mul, mul_zero]
  rw [Finset.sum_comm (γ := ι)]
  apply Finset.sum_congr rfl
  intro j _
  simp [mul_assoc]

/-- The normalized trace of a product of the two spectral projections
is the squared modulus of the corresponding relative unitary entry,
divided by the matrix order. -/
theorem trace_rankOne_spectralProjection_product (U : Matrix ι ι ℂ) (i j : ι) :
    (diagonal (Pi.single i 1) * (U * diagonal (Pi.single j 1) * Uᴴ)).trace.re /
      Fintype.card ι = Complex.normSq (U i j) / Fintype.card ι := by
  have he : (diagonal (Pi.single i 1) *
      (U * diagonal (Pi.single j 1) * Uᴴ)).trace = U i j * Uᴴ j i := by
    simp [Matrix.trace, Matrix.diag_apply, kernel_projection_entry, Pi.single_apply, ite_mul]
  rw [he, Matrix.conjTranspose_apply, Complex.star_def, Complex.mul_conj, Complex.ofReal_re]

/-- For the additive kernel, restoring the common basis gives the
normal matrix sum in spectral coordinates. -/
theorem entrySpectralKernel_add_mul_adjoint (a b : ι → ℂ)
    (U : Matrix ι ι ℂ) (hU : IsUnitary U) :
    entrySpectralKernel (Matrix.of fun i j => a i + b j) U * Uᴴ =
      diagonal a + U * diagonal b * Uᴴ := by
  have he : entrySpectralKernel (Matrix.of fun i j => a i + b j) U =
      diagonal a * U + U * diagonal b := by
    ext i j : 1
    simp only [entrySpectralKernel, Matrix.of_apply, Matrix.add_apply,
      Matrix.diagonal_mul, Matrix.mul_diagonal]
    ring
  rw [he, Matrix.add_mul, Matrix.mul_assoc (diagonal a), hU.1, Matrix.mul_one]

/-- Relative-entropy objective for the squared overlap probabilities
of the two bases. Restricting to the support of the entries excludes
couplings with a positive mass at a zero cost or zero overlap. -/
def matrixKernelEntropyObjective (K U : Matrix ι ι ℂ)
    (q : MatrixKernelSupport (entrySpectralKernel K U) → ℝ) : ℝ :=
  (∑ e, q e * Real.log ‖K e.val.1 e.val.2‖) -
    (∑ e, q e * Real.log (q e /
      (Complex.normSq (U e.val.1 e.val.2) / Fintype.card ι))) / 2

private theorem matrixKernelEntropyObjective_eq (K U : Matrix ι ι ℂ)
    (q : MatrixKernelSupport (entrySpectralKernel K U) → ℝ) :
    finiteEntropyScore (fun e : MatrixKernelSupport (entrySpectralKernel K U) =>
      Complex.normSq (entrySpectralKernel K U e.val.1 e.val.2) / Fintype.card ι) q / 2 =
      matrixKernelEntropyObjective K U q := by
  let n : ℝ := Fintype.card ι
  have hn : 0 < n := by exact_mod_cast Fintype.card_pos
  let W := entrySpectralKernel K U
  let p (e : MatrixKernelSupport W) := Complex.normSq (U e.val.1 e.val.2) / n
  let k (e : MatrixKernelSupport W) := ‖K e.val.1 e.val.2‖
  have hk (e : MatrixKernelSupport W) : 0 < k e :=
    norm_pos_iff.mpr (left_ne_zero_of_mul e.property)
  have hp (e : MatrixKernelSupport W) : 0 < p e :=
    div_pos (Complex.normSq_pos.mpr (right_ne_zero_of_mul e.property)) hn
  have hterm (e : MatrixKernelSupport W) :
      q e * Real.log (Complex.normSq (W e.val.1 e.val.2) / n) + Real.negMulLog (q e) =
        2 * (q e * Real.log (k e)) - q e * Real.log (q e / p e) := by
    have he : Complex.normSq (W e.val.1 e.val.2) / n = k e ^ 2 * p e := by
      simp only [W, entrySpectralKernel, Matrix.of_apply, Complex.normSq_mul, p, k,
        Complex.normSq_eq_norm_sq]
      ring
    by_cases hz : q e = 0
    · simp [hz]
    rw [he, Real.log_mul (pow_ne_zero _ (hk e).ne') (hp e).ne', Real.log_pow,
      Real.log_div hz (hp e).ne', Real.negMulLog_eq_neg]
    push_cast
    ring
  simp only [finiteEntropyScore, matrixKernelEntropyObjective, hterm,
    Finset.sum_sub_distrib, ← Finset.mul_sum, k, p, n]
  ring

/-- The finite matrix entropy bound for an arbitrary kernel and a
relative unitary. Multiplication by the adjoint restores a common basis. -/
theorem matrixLogDet_entrySpectralKernel_le_transport (K U : Matrix ι ι ℂ)
    (hU : IsUnitary U) :
    matrixLogDet (entrySpectralKernel K U * Uᴴ) ≤
      sSup {h : EReal | ∃ q, IsMatrixKernelCoupling (entrySpectralKernel K U) q ∧
        h = (matrixKernelEntropyObjective K U q : ℝ)} := by
  have hnormU : ‖Uᴴ.det‖ = 1 := by
    have ht := congrArg Matrix.det hU.1
    rw [Matrix.det_mul, Matrix.det_conjTranspose, Matrix.det_one, Complex.star_def,
      Complex.mul_conj] at ht
    have hsq : ‖U.det‖ ^ 2 = 1 := by
      simpa only [← Complex.normSq_eq_norm_sq, Complex.ofReal_re, Complex.one_re] using
        congrArg Complex.re ht
    rw [Matrix.det_conjTranspose, Complex.star_def, Complex.norm_conj]
    exact (sq_eq_sq₀ (norm_nonneg U.det) zero_le_one).mp
      (by simpa only [one_pow] using hsq)
  have hzero : (entrySpectralKernel K U * Uᴴ).det = 0 ↔ (entrySpectralKernel K U).det = 0 := by
    rw [Matrix.det_mul, mul_eq_zero]
    simp only [det_ne_zero_of_unitary (show IsUnitary Uᴴ from
      ⟨by simpa using hU.2, by simpa using hU.1⟩), or_false]
  have hlog : matrixLogDet (entrySpectralKernel K U * Uᴴ) =
      matrixLogDet (entrySpectralKernel K U) := by
    simp only [matrixLogDet, hzero]
    simp only [Matrix.det_mul, norm_mul, hnormU, mul_one]
  rw [hlog]
  simpa only [matrixKernelEntropyObjective_eq] using
    matrixLogDet_le_entropic_transport (entrySpectralKernel K U)

/-- The reverse modulus inequality fails in order two. The determinant
vanishes although each matched product has squared modulus four. -/
theorem exists_singular_sum_with_positive_matching_moduli :
    ∃ (a b : Fin 2 → ℂ) (U : Matrix (Fin 2) (Fin 2) ℂ),
      IsUnitary U ∧ determinantValue a b U = 0 ∧
        ∀ σ, Complex.normSq (matchingProduct a b σ) = 4 := by
  let t : ℂ := (Real.sqrt (1 / 2 : ℝ) : ℂ)
  have ht : t * t = (1 / 2 : ℂ) := by
    dsimp only [t]
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num : 0 ≤ (1 / 2 : ℝ))]
    norm_num
  have htc : star t = t := by simp [t, Complex.star_def]
  let U : Matrix (Fin 2) (Fin 2) ℂ := !![t, t; t, -t]
  let a : Fin 2 → ℂ := ![1, -1]
  let b : Fin 2 → ℂ := ![Complex.I, -Complex.I]
  have hUH : Uᴴ = U := by
    ext i j : 1
    fin_cases i <;> fin_cases j <;> simp [U, Matrix.conjTranspose_apply, htc]
  have hU : IsUnitary U := by
    have hu : U * U = 1 := by
      ext i j : 1
      fin_cases i <;> fin_cases j <;>
        simp [U, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply, ht] <;>
        ring_nf <;> simp [pow_two, ht] <;> ring
    exact ⟨by rw [hUH, hu], by rw [hUH, hu]⟩
  refine ⟨a, b, U, hU, ?_, ?_⟩
  · have hB : U * diagonal b * Uᴴ =
        (!![0, Complex.I; Complex.I, 0] : Matrix (Fin 2) (Fin 2) ℂ) := by
      rw [hUH]
      ext i j : 1
      fin_cases i <;> fin_cases j <;>
        simp [U, b, Matrix.mul_apply, Matrix.mul_diagonal, Fin.sum_univ_two] <;>
        ring_nf <;> simp [pow_two, ht] <;> ring
    rw [determinantValue, hB, Matrix.det_fin_two]
    simp [a, Matrix.diagonal_apply, Complex.I_mul_I]
  · intro σ
    have hterm (i j : Fin 2) : Complex.normSq (a i + b j) = 2 := by
      fin_cases i <;> fin_cases j <;>
        norm_num [a, b, Complex.normSq_apply, Complex.add_re, Complex.add_im,
          Complex.neg_re, Complex.neg_im]
    rw [matchingProduct, map_prod]
    norm_num [hterm, Fin.prod_univ_two]

end

end MOC
