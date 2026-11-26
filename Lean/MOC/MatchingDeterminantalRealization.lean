import MOC.TranslatedDeterminantPowers
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Matrix.Kronecker

/-! Centered matching polynomials and a sufficient contractive realization
condition. The analytic existence theorem for realizations is separate. -/

open BigOperators Matrix
open scoped Kronecker Matrix.L2OpNorm

namespace MOC

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The centered matching polynomial in commuting matrix entries. -/
def shiftedMatchingPolynomial (a b : ι → ℂ) (c : ℂ) : MvPolynomial (ι × ι) ℂ :=
  ∑ σ : Equiv.Perm ι,
    MvPolynomial.C (((Equiv.Perm.sign σ : ℤ) : ℂ) * (matchingProduct a b σ - c)) *
      ∏ j, MvPolynomial.X (σ j, j)

/-- The matching polynomial evaluated on a matrix of scalar entries. -/
def shiftedMatchingEvaluation (a b : ι → ℂ) (c : ℂ) (Z : Matrix ι ι ℂ) : ℂ :=
  (Matrix.of fun i j => (a i + b j) * Z i j).det - c * Z.det

/-- The Leibniz coefficients are the centered matching values times permutation signs. -/
theorem shiftedMatchingEvaluation_eq_sum (a b : ι → ℂ) (c : ℂ) (Z : Matrix ι ι ℂ) :
    shiftedMatchingEvaluation a b c Z =
      ∑ σ : Equiv.Perm ι, leibnizTerm Z σ * (matchingProduct a b σ - c) := by
  rw [shiftedMatchingEvaluation, Matrix.det_apply', Matrix.det_apply', Finset.mul_sum,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro σ _
  simp only [Matrix.of_apply, Finset.prod_mul_distrib, leibnizTerm, matchingProduct]
  ring

theorem eval_shiftedMatchingPolynomial (a b : ι → ℂ) (c : ℂ) (Z : Matrix ι ι ℂ) :
    MvPolynomial.eval (fun ij : ι × ι => Z ij.1 ij.2) (shiftedMatchingPolynomial a b c) =
      shiftedMatchingEvaluation a b c Z := by
  simp only [shiftedMatchingPolynomial, shiftedMatchingEvaluation_eq_sum, leibnizTerm,
    map_sum, map_mul, map_prod, MvPolynomial.eval_C, MvPolynomial.eval_X]
  exact Finset.sum_congr rfl fun σ _ => by ring

/-- All terms have degree equal to the matrix order. -/
theorem shiftedMatchingEvaluation_smul (a b : ι → ℂ) (c t : ℂ) (Z : Matrix ι ι ℂ) :
    shiftedMatchingEvaluation a b c (t • Z) =
      t ^ Fintype.card ι * shiftedMatchingEvaluation a b c Z := by
  have he : (Matrix.of fun i j => (a i + b j) * (t • Z) i j) =
      t • (Matrix.of fun i j => (a i + b j) * Z i j) := by
    ext i j : 1
    simp only [Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  simp only [shiftedMatchingEvaluation, he, Matrix.det_smul]
  ring

theorem shiftedMatchingEvaluation_unitary (a b : ι → ℂ) (c : ℂ) (U : Matrix ι ι ℂ)
    (hU : IsUnitary U) :
    shiftedMatchingEvaluation a b c U = U.det * (determinantValue a b U - c) := by
  have he := (eq_div_iff (det_ne_zero_of_unitary hU)).mp
    (determinantValue_eq_weightedEntryDet_div a b U hU)
  rw [shiftedMatchingEvaluation, ← he]
  ring

theorem norm_shiftedMatchingEvaluation_unitary (a b : ι → ℂ) (c : ℂ) (U : Matrix ι ι ℂ)
    (hU : IsUnitary U) :
    ‖shiftedMatchingEvaluation a b c U‖ = ‖determinantValue a b U - c‖ := by
  have h := congrArg Matrix.det hU.1
  rw [Matrix.det_mul, Matrix.det_conjTranspose, Matrix.det_one] at h
  have hs : Complex.normSq U.det = 1 := by
    rw [← Complex.ofReal_inj, Complex.ofReal_one, ← Complex.mul_conj]
    exact h
  have hd : ‖U.det‖ = 1 := by
    apply (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp
    simpa only [Complex.sq_norm, one_pow] using hs
  rw [shiftedMatchingEvaluation_unitary a b c U hU, norm_mul, hd, one_mul]

/-- The unitary norm comparison at every disk center is equivalent to the
conjecture. The reverse implication uses the existing local fixed-center test. -/
theorem conjecture_iff_shifted_matching_unitary_bound [Nonempty ι] :
    Conjecture ι ↔ ∀ (a b : ι → ℂ) (c : ℂ) (U : Matrix ι ι ℂ), IsUnitary U →
      ∃ σ : Equiv.Perm ι,
        ‖shiftedMatchingEvaluation a b c U‖ ≤ ‖matchingProduct a b σ - c‖ := by
  classical
  constructor
  · intro h a b c U hU
    obtain ⟨σ, _, hσ⟩ := Finset.exists_max_image Finset.univ
      (fun τ : Equiv.Perm ι => ‖matchingProduct a b τ - c‖) Finset.univ_nonempty
    have hball : determinantValue a b U ∈ Metric.closedBall c ‖matchingProduct a b σ - c‖ := by
      refine convexHull_min (s := Set.range (matchingProduct a b)) ?_ (convex_closedBall _ _)
        (h a b U hU)
      rintro _ ⟨τ, rfl⟩
      exact Metric.mem_closedBall.mpr (by simpa only [dist_eq_norm] using hσ τ (Finset.mem_univ _))
    refine ⟨σ, ?_⟩
    rw [norm_shiftedMatchingEvaluation_unitary a b c U hU]
    simpa only [Metric.mem_closedBall, dist_eq_norm] using hball
  · intro h
    apply (conjecture_iff_local_translated_normSq (ι := ι) 1 zero_lt_one).mpr
    intro a b U hU _ _
    obtain ⟨σ, hs⟩ := h a b (-1) U hU
    refine ⟨σ, ?_⟩
    rw [norm_shiftedMatchingEvaluation_unitary a b (-1) U hU,
      sub_neg_eq_add, sub_neg_eq_add, add_comm (determinantValue a b U),
      add_comm (matchingProduct a b σ)] at hs
    rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
    exact pow_le_pow_left₀ (norm_nonneg _) hs 2

private theorem unitary_kronecker_one {k : ℕ} (U : Matrix ι ι ℂ) (hU : IsUnitary U) :
    IsUnitary (U ⊗ₖ (1 : Matrix (Fin k) (Fin k) ℂ)) := by
  let I : Matrix (Fin k) (Fin k) ℂ := 1
  have hadj : (U ⊗ₖ I)ᴴ = Uᴴ ⊗ₖ Iᴴ := by
    ext ⟨i, j⟩ ⟨k', l⟩
    simp only [Matrix.conjTranspose_apply, Matrix.kronecker_apply, star_mul', mul_comm]
  change (U ⊗ₖ (1 : Matrix (Fin k) (Fin k) ℂ))ᴴ = Uᴴ ⊗ₖ (1 : Matrix (Fin k) (Fin k) ℂ)ᴴ at hadj
  rw [Matrix.conjTranspose_one] at hadj
  constructor
  · rw [hadj, ← Matrix.mul_kronecker_mul, hU.1, Matrix.mul_one, Matrix.one_kronecker_one]
  · rw [hadj, ← Matrix.mul_kronecker_mul, hU.2, Matrix.mul_one, Matrix.one_kronecker_one]

/-- A realization gives a unitary norm bound of degree equal to the matrix order. -/
theorem norm_shiftedMatchingEvaluation_le_of_realization [Nonempty ι]
    (a b : ι → ℂ) (c : ℂ) {k : ℕ} (hk : 0 < k)
    (K : Matrix (ι × Fin k) (ι × Fin k) ℂ)
    (hK : ∀ Z : Matrix ι ι ℂ, 1 - shiftedMatchingEvaluation a b c Z =
      (1 - K * (Z ⊗ₖ (1 : Matrix (Fin k) (Fin k) ℂ))).det)
    (U : Matrix ι ι ℂ) (hU : IsUnitary U) :
    ‖shiftedMatchingEvaluation a b c U‖ ≤ ‖K‖ ^ Fintype.card ι := by
  letI : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  let x := shiftedMatchingEvaluation a b c U
  let n := Fintype.card ι
  by_contra! hbad
  have hx : 0 < ‖x‖ := (pow_nonneg (norm_nonneg K) n).trans_lt hbad
  obtain ⟨t, ht⟩ := IsAlgClosed.exists_pow_nat_eq x⁻¹ (Fintype.card_pos (α := ι))
  have htn : ‖t‖ ^ n = ‖x‖⁻¹ := by rw [← norm_pow, ht, norm_inv]
  have hn : ‖K‖ * ‖t‖ < 1 := by
    have hp : (‖K‖ * ‖t‖) ^ n < 1 := by
      rw [mul_pow, htn, ← div_eq_mul_inv, div_lt_one hx]
      exact hbad
    by_contra! hge
    have hpow := pow_le_pow_left₀ (show (0 : ℝ) ≤ 1 from zero_le_one) hge n
    rw [one_pow] at hpow
    exact (not_le_of_gt hp) hpow
  let V := U ⊗ₖ (1 : Matrix (Fin k) (Fin k) ℂ)
  have hV : ‖V‖ = 1 := by
    apply (sq_eq_sq₀ (norm_nonneg V) zero_le_one).mp
    rw [pow_two, ← Matrix.l2_opNorm_conjTranspose_mul_self,
      (unitary_kronecker_one U hU).2, norm_one, one_pow]
  have hsmall : ‖K * ((t • U) ⊗ₖ (1 : Matrix (Fin k) (Fin k) ℂ))‖ < 1 := by
    rw [Matrix.smul_kronecker]
    calc
      ‖K * (t • V)‖ ≤ ‖K‖ * ‖t • V‖ := norm_mul_le _ _
      _ = ‖K‖ * ‖t‖ := by rw [norm_smul, hV, mul_one]
      _ < 1 := hn
  have hu := isUnit_one_sub_of_norm_lt_one hsmall
  have hdet := (Matrix.isUnit_iff_isUnit_det _).mp hu
  rw [← hK (t • U), shiftedMatchingEvaluation_smul, ht] at hdet
  change IsUnit (1 - x⁻¹ * x) at hdet
  rw [inv_mul_cancel₀ (norm_pos_iff.mp hx), sub_self] at hdet
  exact not_isUnit_zero hdet

/-- An approximate realization is enough. The auxiliary order can depend on
the norm budget, the two lists and the center. -/
def ApproximateMatchingRealizations (ι : Type*) [Fintype ι] [DecidableEq ι] : Prop :=
  ∀ (a b : ι → ℂ) (c : ℂ) (r : ℝ), 0 < r →
    (∀ σ : Equiv.Perm ι, ‖matchingProduct a b σ - c‖ < r ^ Fintype.card ι) →
    ∃ k : ℕ, 0 < k ∧ ∃ K : Matrix (ι × Fin k) (ι × Fin k) ℂ,
      ‖K‖ ≤ r ∧ ∀ Z : Matrix ι ι ℂ, 1 - shiftedMatchingEvaluation a b c Z =
        (1 - K * (Z ⊗ₖ (1 : Matrix (Fin k) (Fin k) ℂ))).det

/-- Existence of the approximate matching realizations implies the conjecture. -/
theorem conjecture_of_approximate_matching_realizations [Nonempty ι]
    (h : ApproximateMatchingRealizations ι) : Conjecture ι := by
  classical
  apply conjecture_iff_shifted_matching_unitary_bound.mpr
  intro a b c U hU
  by_contra! hbad
  obtain ⟨σ, _, hσ⟩ := Finset.exists_max_image Finset.univ
    (fun τ : Equiv.Perm ι => ‖matchingProduct a b τ - c‖) Finset.univ_nonempty
  obtain ⟨s, hσs, hs⟩ := exists_between (hbad σ)
  have hspos := (norm_nonneg (matchingProduct a b σ - c)).trans_lt hσs
  let r := s ^ ((Fintype.card ι : ℝ)⁻¹)
  have hr : 0 < r := Real.rpow_pos_of_pos hspos _
  have hrpow : r ^ Fintype.card ι = s :=
    Real.rpow_inv_natCast_pow hspos.le Fintype.card_ne_zero
  have hM (τ : Equiv.Perm ι) : ‖matchingProduct a b τ - c‖ < r ^ Fintype.card ι := by
    rw [hrpow]
    exact (hσ τ (Finset.mem_univ _)).trans_lt hσs
  obtain ⟨k, hk, K, hnorm, hK⟩ := h a b c r hr hM
  have hbound := (norm_shiftedMatchingEvaluation_le_of_realization a b c hk K hK U hU).trans
    (pow_le_pow_left₀ (norm_nonneg K) hnorm (Fintype.card ι))
  rw [hrpow] at hbound
  exact (not_le_of_gt hs) hbound

end

end MOC
