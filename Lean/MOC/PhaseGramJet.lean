import MOC.Weights
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.GroupTheory.Perm.Support

/-! Formal fourth-order extraction for a phase Gram matrix. The formal
argument uses only the order of the off-diagonal coefficients. For the
first-order defect geometry see Tadej–Życzkowski, DOI:
10.1016/j.laa.2008.02.036. -/

open PowerSeries Matrix BigOperators

namespace MOC

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

section Gram

variable (G : Matrix ι ι ℂ⟦X⟧)
variable (hd : ∀ i, G i i = 1)
variable (hzero : ∀ i j, i ≠ j → (X : ℂ⟦X⟧)^2 ∣ G i j)

include hd hzero

private theorem phaseGram_leibniz (σ : Equiv.Perm ι) (d : ℕ) :
    coeff ℂ d (∏ j, G (σ j) j) =
      if 2 * σ.support.card ≤ d then
        coeff ℂ (d - 2 * σ.support.card)
          (∏ j, (if _hj : j ∈ σ.support then PowerSeries.mk
            (fun m => coeff ℂ (m+2) (G (σ j) j)) else 1))
      else 0 := by
  let Q (j : ι) := PowerSeries.mk (fun m => coeff ℂ (m+2) (G (σ j) j))
  have hQ (j : ι) (hj : j ∈ σ.support) :
      G (σ j) j = X^2 * Q j := by
    obtain ⟨q, hq⟩ := hzero (σ j) j (Equiv.Perm.mem_support.mp hj)
    have he : q = Q j := by
      ext n
      dsimp [Q]
      rw [hq, coeff_mk, coeff_X_pow_mul]
    rw [hq, ← he]
  have hfactor : (∏ j, G (σ j) j) =
      X^(2 * σ.support.card) * ∏ j, (if j ∈ σ.support then Q j else 1) := by
    rw [← Finset.prod_compl_mul_prod σ.support]
    have hone : (∏ j ∈ σ.supportᶜ, G (σ j) j) = 1 := by
      apply Finset.prod_eq_one
      intro j hj
      rw [Equiv.Perm.not_mem_support.mp (Finset.mem_compl.mp hj), hd]
    rw [hone, one_mul, Finset.prod_ite, Finset.filter_mem_eq_inter, Finset.univ_inter]
    simp only [Finset.prod_const_one, mul_one]
    calc
      _ = ∏ j ∈ σ.support, X^2 * Q j :=
        Finset.prod_congr rfl (fun j hj => hQ j hj)
      _ = _ := by rw [Finset.prod_mul_distrib, Finset.prod_const, ← pow_mul]
  rw [hfactor, coeff_X_pow_mul']
  rfl

/-- If the Gram diagonal is constant, and the off-diagonal jet starts in
degree two, the Gram determinant has no coefficients in degrees 1–3. -/
theorem phaseGram_det_coeff_pos_lt_four_zero (d : ℕ) (hd0 : 0 < d) (hd4 : d < 4) :
    coeff ℂ d G.det = 0 := by
  rw [Matrix.det_apply', map_sum]
  apply Finset.sum_eq_zero
  intro σ _
  rw [show (↑↑(Equiv.Perm.sign σ) : ℂ⟦X⟧) = C ℂ ((Equiv.Perm.sign σ : ℤ) : ℂ) by simp,
    mul_comm, coeff_mul_C]
  by_cases h : σ = 1
  · subst σ
    simp [hd, hd0.ne']
  · have hs := Equiv.Perm.two_le_card_support_of_ne_one h
    rw [phaseGram_leibniz G hd hzero σ d, if_neg (by omega), zero_mul]

/-- The first nonconstant coefficient comes only from single swaps.
This statement is a formal identity, with no analytic Taylor remainder. -/
theorem phaseGram_det_coeff_four :
    coeff ℂ 4 G.det =
      ∑ σ : Equiv.Perm ι, if σ.support.card = 2 then
        -∏ j ∈ σ.support, coeff ℂ 2 (G (σ j) j) else 0 := by
  rw [Matrix.det_apply', map_sum]
  apply Finset.sum_congr rfl
  intro σ _
  rw [show (↑↑(Equiv.Perm.sign σ) : ℂ⟦X⟧) = C ℂ ((Equiv.Perm.sign σ : ℤ) : ℂ) by simp,
    mul_comm, coeff_mul_C]
  by_cases h : σ = 1
  · subst σ
    simp [hd]
  · have hs := Equiv.Perm.two_le_card_support_of_ne_one h
    split_ifs with ht
    · have hsg : Equiv.Perm.sign σ = -1 := by
        obtain ⟨i,j,hij,rfl⟩ := Equiv.Perm.card_support_eq_two.mp ht
        exact Equiv.Perm.sign_swap hij
      rw [phaseGram_leibniz G hd hzero σ 4, ht, hsg]
      simp [coeff_zero_eq_constantCoeff_apply, Finset.prod_ite, Finset.filter_mem_eq_inter,
        Finset.univ_inter, map_prod, Equiv.Perm.support, ← coeff_zero_eq_constantCoeff_apply]
    · rw [phaseGram_leibniz G hd hzero σ 4, if_neg (by omega), zero_mul]

/-- For a Hermitian Gram jet, each transposition contributes the negative
square of one off-diagonal quadratic coefficient. -/
theorem phaseGram_det_coeff_four_re_nonpos
    (hherm : ∀ i j, coeff ℂ 2 (G j i) = star (coeff ℂ 2 (G i j))) :
    (coeff ℂ 4 G.det).re ≤ 0 := by
  rw [phaseGram_det_coeff_four G hd hzero, Complex.re_sum]
  apply Finset.sum_nonpos
  intro σ _
  split_ifs with h
  · obtain ⟨i,j,hij,rfl⟩ := Equiv.Perm.card_support_eq_two.mp h
    rw [Equiv.Perm.support_swap hij, Finset.prod_insert (by simpa using hij),
      Finset.prod_singleton, Equiv.swap_apply_left, Equiv.swap_apply_right, hherm,
      Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.neg_re, Complex.ofReal_re]
    exact neg_nonpos.mpr (Complex.normSq_nonneg _)
  · simp

end Gram

private def phaseExp (c : ℂ) : ℂ⟦X⟧ := rescale c (PowerSeries.exp ℂ)

private theorem phaseExp_mul (x y : ℂ) : phaseExp x * phaseExp y = phaseExp (x + y) :=
  PowerSeries.exp_mul_exp_eq_exp_add x y

private theorem phaseExp_zero : phaseExp 0 = 1 := by simp [phaseExp]

private theorem phaseExp_coeff (c : ℂ) (n : ℕ) :
    coeff ℂ n (phaseExp c) = c ^ n / (n.factorial : ℂ) := by
  simp [phaseExp, map_div₀, div_eq_mul_inv]

private theorem phaseExp_conj (x : ℂ) :
    PowerSeries.map (starRingEnd ℂ) (phaseExp x) = phaseExp (star x) := by
  ext n
  simp [phaseExp_coeff, map_div₀, map_pow]

/-- Formal phase Gram series of an actual mixer. -/
def formalPhaseGram (U : Matrix ι ι ℂ) (W : Matrix ι ι ℝ) : Matrix ι ι ℂ⟦X⟧ :=
  Matrix.of fun i j => ∑ k, C ℂ (U i k * star (U j k)) *
    phaseExp (Complex.I * ((W i k : ℂ) - (W j k : ℂ)))

private theorem formalPhaseGram_diag (U : Matrix ι ι ℂ) (hU : IsUnitary U)
    (W : Matrix ι ι ℝ) (i : ι) : formalPhaseGram U W i i = 1 := by
  simp only [formalPhaseGram, Matrix.of_apply, sub_self, mul_zero, phaseExp_zero, mul_one, ← map_sum]
  change C ℂ ((U * Uᴴ) i i) = 1
  simp [hU.1]

private theorem formalPhaseGram_coeff_zero (U : Matrix ι ι ℂ) (hU : IsUnitary U)
    (W : Matrix ι ι ℝ) (i j : ι) :
    coeff ℂ 0 (formalPhaseGram U W i j) = ((1 : Matrix ι ι ℂ) i j) := by
  simp only [formalPhaseGram, Matrix.of_apply, map_sum, coeff_C_mul, phaseExp_coeff,
    pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, mul_one]
  change (U * Uᴴ) i j = _
  rw [hU.1]

omit [DecidableEq ι] in
/-- The exact first phase Gram coefficient is the weighted difference of the
two row costs, independently of any smooth parameterization of unitary fibres. -/
theorem formalPhaseGram_coeff_one (U : Matrix ι ι ℂ)
    (W : Matrix ι ι ℝ) (i j : ι) :
    coeff ℂ 1 (formalPhaseGram U W i j) =
    Complex.I * ∑ k, (U i k * star (U j k)) * ((W i k : ℂ) - (W j k : ℂ)) := by
  simp only [formalPhaseGram, Matrix.of_apply, map_sum, coeff_C_mul, phaseExp_coeff,
    pow_one, Nat.factorial_one, Nat.cast_one, div_one, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

private theorem formalPhaseGram_offdiag_dvd (U : Matrix ι ι ℂ) (hU : IsUnitary U)
    (W : Matrix ι ι ℝ) (hnull : ∀ i j, coeff ℂ 1 (formalPhaseGram U W i j) = 0)
    (i j : ι) (hij : i ≠ j) :
    (X : ℂ⟦X⟧)^2 ∣ formalPhaseGram U W i j := by
  apply (PowerSeries.X_pow_dvd_iff).mpr
  intro n hn
  have hn' : n = 0 ∨ n = 1 := by omega
  rcases hn' with rfl | rfl
  · rw [formalPhaseGram_coeff_zero U hU, Matrix.one_apply_ne hij]
  · exact hnull i j

private theorem formalPhaseGram_conj (U : Matrix ι ι ℂ)
    (W : Matrix ι ι ℝ) (i j : ι) :
    PowerSeries.map (starRingEnd ℂ) (formalPhaseGram U W i j) = formalPhaseGram U W j i := by
  simp only [formalPhaseGram, Matrix.of_apply, map_sum, map_mul, map_C, phaseExp_conj,
    starRingEnd_apply, star_mul', star_star, Complex.conj_I, map_sub, Complex.conj_ofReal]
  apply Finset.sum_congr rfl
  intro k _
  have hexp : star (Complex.I * ((W i k : ℂ) - (W j k : ℂ))) =
      Complex.I * ((W j k : ℂ) - (W i k : ℂ)) := by
    simp [Complex.star_def, map_sub]
    ring
  rw [show star Complex.I * star ((W i k : ℂ) - (W j k : ℂ)) =
    Complex.I * ((W j k : ℂ) - (W i k : ℂ)) by simpa only [star_mul'] using hexp]
  ring

/-- For every genuine unitary and every first-order null entrywise phase
direction, the quartic Gram coefficient is nonpositive. -/
theorem formalPhaseGram_det_coeff_four_re_nonpos (U : Matrix ι ι ℂ) (hU : IsUnitary U)
    (W : Matrix ι ι ℝ) (hnull : ∀ i j, coeff ℂ 1 (formalPhaseGram U W i j) = 0) :
    (coeff ℂ 4 (formalPhaseGram U W).det).re ≤ 0 := by
  apply phaseGram_det_coeff_four_re_nonpos _
    (formalPhaseGram_diag U hU W) (formalPhaseGram_offdiag_dvd U hU W hnull)
  intro i j
  simpa only [coeff_map, starRingEnd_apply] using
    congrArg (coeff ℂ 2) (formalPhaseGram_conj U W i j).symm

end

end MOC
