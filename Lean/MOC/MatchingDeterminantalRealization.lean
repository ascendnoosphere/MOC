import MOC.OperatorBallPolynomial
import MOC.StrongSupport
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

/-- A realization bounds the polynomial on the closed operator norm unit ball. -/
theorem norm_shiftedMatchingEvaluation_le_of_realization_on_ball [Nonempty ι]
    (a b : ι → ℂ) (c : ℂ) {k : ℕ} (hk : 0 < k)
    (K : Matrix (ι × Fin k) (ι × Fin k) ℂ)
    (hK : ∀ Z : Matrix ι ι ℂ, 1 - shiftedMatchingEvaluation a b c Z =
      (1 - K * (Z ⊗ₖ (1 : Matrix (Fin k) (Fin k) ℂ))).det)
    (Z : Matrix ι ι ℂ) (hZ : ‖Z‖ ≤ 1) :
    ‖shiftedMatchingEvaluation a b c Z‖ ≤ ‖K‖ ^ Fintype.card ι := by
  letI : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  let x := shiftedMatchingEvaluation a b c Z
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
  let V := Z ⊗ₖ (1 : Matrix (Fin k) (Fin k) ℂ)
  have hV : ‖V‖ = ‖Z‖ := l2_opNorm_kronecker_one Z
  have hsmall : ‖K * ((t • Z) ⊗ₖ (1 : Matrix (Fin k) (Fin k) ℂ))‖ < 1 := by
    rw [Matrix.smul_kronecker]
    calc
      ‖K * (t • V)‖ ≤ ‖K‖ * ‖t • V‖ := norm_mul_le _ _
      _ ≤ ‖K‖ * ‖t‖ := by
        rw [norm_smul, hV]
        exact mul_le_mul_of_nonneg_left (mul_le_of_le_one_right (norm_nonneg t) hZ) (norm_nonneg K)
      _ < 1 := hn
  have hu := isUnit_one_sub_of_norm_lt_one hsmall
  have hdet := (Matrix.isUnit_iff_isUnit_det _).mp hu
  rw [← hK (t • Z), shiftedMatchingEvaluation_smul, ht] at hdet
  change IsUnit (1 - x⁻¹ * x) at hdet
  rw [inv_mul_cancel₀ (norm_pos_iff.mp hx), sub_self] at hdet
  exact not_isUnit_zero hdet

/-- A unitary matrix has operator norm one. -/
theorem norm_shiftedMatchingEvaluation_le_of_realization [Nonempty ι]
    (a b : ι → ℂ) (c : ℂ) {k : ℕ} (hk : 0 < k)
    (K : Matrix (ι × Fin k) (ι × Fin k) ℂ)
    (hK : ∀ Z : Matrix ι ι ℂ, 1 - shiftedMatchingEvaluation a b c Z =
      (1 - K * (Z ⊗ₖ (1 : Matrix (Fin k) (Fin k) ℂ))).det)
    (U : Matrix ι ι ℂ) (hU : IsUnitary U) :
    ‖shiftedMatchingEvaluation a b c U‖ ≤ ‖K‖ ^ Fintype.card ι :=
  norm_shiftedMatchingEvaluation_le_of_realization_on_ball a b c hk K hK U
    (CStarRing.norm_of_mem_unitary (Matrix.mem_unitaryGroup_iff.mpr hU.1)).le

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

/-- A polynomial with constant term one and no zero on the closed matrix
unit ball has an exact realization by a strict contraction. This is the
premise from Grinshpan, Kaliuzhnyi-Verbovetskyi, Vinnikov and Woerdeman,
Theorem 3.1, https://arxiv.org/html/1503.06161#S3. Factoring and taking
direct sums gives the statement for reducible polynomials. Lean does
not yet prove this premise. -/
def StrictMatrixBallRealization (ι : Type*) [Fintype ι] [DecidableEq ι] : Prop :=
  ∀ p : MvPolynomial (ι × ι) ℂ,
    MvPolynomial.eval (fun _ => 0) p = 1 →
    (∀ Z : Matrix ι ι ℂ, ‖Z‖ ≤ 1 → MvPolynomial.eval (fun ij => Z ij.1 ij.2) p ≠ 0) →
    ∃ k : ℕ, 0 < k ∧ ∃ K : Matrix (ι × Fin k) (ι × Fin k) ℂ,
      ‖K‖ < 1 ∧ ∀ Z : Matrix ι ι ℂ, MvPolynomial.eval (fun ij => Z ij.1 ij.2) p =
        (1 - K * (Z ⊗ₖ (1 : Matrix (Fin k) (Fin k) ℂ))).det

private theorem exists_shifted_matching_realization_of_ball_bound [Nonempty ι]
    (h : StrictMatrixBallRealization ι) (a b : ι → ℂ) (c : ℂ) (r : ℝ) (hr : 0 < r)
    (hball : ∀ Z : Matrix ι ι ℂ, ‖Z‖ ≤ 1 →
      ‖shiftedMatchingEvaluation a b c Z‖ < r ^ Fintype.card ι) :
    ∃ k : ℕ, 0 < k ∧ ∃ K : Matrix (ι × Fin k) (ι × Fin k) ℂ,
      ‖K‖ < r ∧ ∀ Z : Matrix ι ι ℂ, 1 - shiftedMatchingEvaluation a b c Z =
        (1 - K * (Z ⊗ₖ (1 : Matrix (Fin k) (Fin k) ℂ))).det := by
  let n := Fintype.card ι
  let p : MvPolynomial (ι × ι) ℂ :=
    1 - MvPolynomial.C (((r : ℂ) ^ n)⁻¹) * shiftedMatchingPolynomial a b c
  have heval (Z : Matrix ι ι ℂ) :
      MvPolynomial.eval (fun ij => Z ij.1 ij.2) p =
        1 - ((r : ℂ) ^ n)⁻¹ * shiftedMatchingEvaluation a b c Z := by
    simp only [p, map_sub, map_one, map_mul, MvPolynomial.eval_C, eval_shiftedMatchingPolynomial]
  have hz : shiftedMatchingEvaluation a b c (0 : Matrix ι ι ℂ) = 0 := by
    simpa only [zero_smul, zero_pow Fintype.card_ne_zero, zero_mul] using
      shiftedMatchingEvaluation_smul a b c 0 (0 : Matrix ι ι ℂ)
  have hp0 : MvPolynomial.eval (fun _ => 0) p = 1 := by
    simpa only [Matrix.zero_apply, hz, mul_zero, sub_zero] using heval (0 : Matrix ι ι ℂ)
  have hpnz (Z : Matrix ι ι ℂ) (hZ : ‖Z‖ ≤ 1) :
      MvPolynomial.eval (fun ij => Z ij.1 ij.2) p ≠ 0 := by
    have hnorm : ‖((r : ℂ) ^ n)⁻¹ * shiftedMatchingEvaluation a b c Z‖ < 1 := by
      rw [norm_mul, norm_inv, norm_pow, Complex.norm_of_nonneg hr.le, inv_mul_eq_div,
        div_lt_one (pow_pos hr n)]
      exact hball Z hZ
    rw [heval]
    apply sub_ne_zero.mpr
    intro he
    rw [← he, norm_one] at hnorm
    exact (lt_irrefl _) hnorm
  obtain ⟨k, hk, L, hL, hrep⟩ := h p hp0 hpnz
  refine ⟨k, hk, (r : ℂ) • L, ?_, fun Z => ?_⟩
  · rw [norm_smul, Complex.norm_of_nonneg hr.le]
    simpa only [mul_one] using mul_lt_mul_of_pos_left hL hr
  · have hpow : (r : ℂ) ^ n ≠ 0 := pow_ne_zero n (Complex.ofReal_ne_zero.mpr hr.ne')
    have hs := hrep ((r : ℂ) • Z)
    rw [heval, shiftedMatchingEvaluation_smul, ← mul_assoc, inv_mul_cancel₀ hpow, one_mul,
      Matrix.smul_kronecker, Matrix.mul_smul] at hs
    rw [Matrix.smul_mul]
    exact hs

/-- The admissible norms of exact realizations at a fixed disk center. -/
def matchingRealizationNorms (a b : ι → ℂ) (c : ℂ) : Set ℝ :=
  {r | ∃ k : ℕ, 0 < k ∧ ∃ K : Matrix (ι × Fin k) (ι × Fin k) ℂ,
    ‖K‖ = r ∧ ∀ Z : Matrix ι ι ℂ, 1 - shiftedMatchingEvaluation a b c Z =
      (1 - K * (Z ⊗ₖ (1 : Matrix (Fin k) (Fin k) ℂ))).det}

/-- The infimum of the admissible norms. -/
def matchingRealizationRadius (a b : ι → ℂ) (c : ℂ) : ℝ :=
  sInf (matchingRealizationNorms a b c)

/-- Under the strict realization premise, the infimum is the root of the
maximum polynomial modulus on the closed operator norm unit ball. -/
theorem matchingRealizationRadius_eq_of_ball_maximum [Nonempty ι]
    (h : StrictMatrixBallRealization ι) (a b : ι → ℂ) (c : ℂ)
    (W : Matrix ι ι ℂ) (hW : ‖W‖ ≤ 1) (hmax : ∀ Z : Matrix ι ι ℂ, ‖Z‖ ≤ 1 →
      ‖shiftedMatchingEvaluation a b c Z‖ ≤ ‖shiftedMatchingEvaluation a b c W‖) :
    matchingRealizationRadius a b c =
      ‖shiftedMatchingEvaluation a b c W‖ ^ ((Fintype.card ι : ℝ)⁻¹) := by
  let n := Fintype.card ι
  let m := ‖shiftedMatchingEvaluation a b c W‖
  let q := m ^ ((n : ℝ)⁻¹)
  have hq : 0 ≤ q := Real.rpow_nonneg (norm_nonneg _) _
  have hqpow : q ^ n = m := Real.rpow_inv_natCast_pow (norm_nonneg _) Fintype.card_ne_zero
  let T := matchingRealizationNorms a b c
  have hex (r : ℝ) (hr : q < r) : ∃ s ∈ T, s < r := by
    have hrpow : m < r ^ n := by
      rw [← hqpow]
      exact pow_lt_pow_left₀ hr hq Fintype.card_ne_zero
    obtain ⟨k, hk, K, hK, hrep⟩ := exists_shifted_matching_realization_of_ball_bound
      h a b c r (hq.trans_lt hr) fun Z hZ => (hmax Z hZ).trans_lt hrpow
    exact ⟨‖K‖, ⟨k, hk, K, rfl, hrep⟩, hK⟩
  have hne : T.Nonempty := by
    obtain ⟨s, hs, _⟩ := hex (q + 1) (lt_add_of_pos_right _ zero_lt_one)
    exact ⟨s, hs⟩
  have hlow (r : ℝ) (hr : r ∈ T) : q ≤ r := by
    obtain ⟨k, hk, K, rfl, hrep⟩ := hr
    have hb := norm_shiftedMatchingEvaluation_le_of_realization_on_ball a b c hk K hrep W hW
    apply le_of_pow_le_pow_left₀ (Fintype.card_ne_zero (α := ι)) (norm_nonneg K)
    exact hqpow.trans_le hb
  change sInf T = q
  refine le_antisymm (le_of_forall_gt_imp_ge_of_dense fun r hr => ?_) (le_csInf hne hlow)
  obtain ⟨s, hs, hsr⟩ := hex r hr
  exact (csInf_le ⟨q, hlow⟩ hs).trans hsr.le

/-- The largest modulus of the centered matching coefficients. -/
def matchingCoefficientNorm (a b : ι → ℂ) (c : ℂ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun σ : Equiv.Perm ι => ‖matchingProduct a b σ - c‖)

/-- The conjecture is equivalent to the optimal realization radius, under
the strict matrix-ball realization premise. -/
theorem conjecture_iff_optimal_matching_realization_radius [Nonempty ι]
    (h : StrictMatrixBallRealization ι) : Conjecture ι ↔
      ∀ (a b : ι → ℂ) (c : ℂ), matchingRealizationRadius a b c =
        matchingCoefficientNorm a b c ^ ((Fintype.card ι : ℝ)⁻¹) := by
  classical
  rw [conjecture_iff_shifted_matching_unitary_bound]
  have hmax (a b : ι → ℂ) (c : ℂ) : ∃ W : Matrix ι ι ℂ, IsUnitary W ∧ ‖W‖ ≤ 1 ∧
      ∀ Z : Matrix ι ι ℂ, ‖Z‖ ≤ 1 →
        ‖shiftedMatchingEvaluation a b c Z‖ ≤ ‖shiftedMatchingEvaluation a b c W‖ := by
    simpa only [eval_shiftedMatchingPolynomial] using
      exists_unitary_maximum_mvPolynomial_matrix_eval (shiftedMatchingPolynomial a b c)
  have hcoeff (a b : ι → ℂ) (c : ℂ) (σ : Equiv.Perm ι) :
      ‖matchingProduct a b σ - c‖ ≤ matchingCoefficientNorm a b c :=
    Finset.le_sup' (fun τ : Equiv.Perm ι => ‖matchingProduct a b τ - c‖) (Finset.mem_univ σ)
  have hatt (a b : ι → ℂ) (c : ℂ) :
      ∃ σ : Equiv.Perm ι, matchingCoefficientNorm a b c = ‖matchingProduct a b σ - c‖ := by
    obtain ⟨σ, _, hs⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
      (fun σ : Equiv.Perm ι => ‖matchingProduct a b σ - c‖)
    exact ⟨σ, hs⟩
  constructor
  · intro hbound a b c
    obtain ⟨W, hW, hWn, hWmax⟩ := hmax a b c
    obtain ⟨σ, hσ⟩ := hbound a b c W hW
    obtain ⟨τ, hτ⟩ := hatt a b c
    obtain ⟨U, hU, hUval⟩ := matchingProduct_mem_determinantRange a b τ
    have hUn : ‖U‖ ≤ 1 := (CStarRing.norm_of_mem_unitary (Matrix.mem_unitaryGroup_iff.mpr hU.1)).le
    have hV := hWmax U hUn
    rw [norm_shiftedMatchingEvaluation_unitary a b c U hU, hUval, ← hτ] at hV
    rw [matchingRealizationRadius_eq_of_ball_maximum h a b c W hWn hWmax,
      le_antisymm (hσ.trans (hcoeff a b c σ)) hV]
  · intro hrad a b c U hU
    obtain ⟨W, _, hWn, hWmax⟩ := hmax a b c
    obtain ⟨σ, hσ⟩ := hatt a b c
    have he := (matchingRealizationRadius_eq_of_ball_maximum h a b c W hWn hWmax).symm.trans
      (hrad a b c)
    rw [hσ] at he
    have hp := congrArg (fun x : ℝ => x ^ Fintype.card ι) he
    have hn : Fintype.card ι ≠ 0 := Fintype.card_ne_zero
    rw [Real.rpow_inv_natCast_pow (norm_nonneg (shiftedMatchingEvaluation a b c W)) hn,
      Real.rpow_inv_natCast_pow (norm_nonneg (matchingProduct a b σ - c)) hn] at hp
    have hUn : ‖U‖ ≤ 1 := (CStarRing.norm_of_mem_unitary (Matrix.mem_unitaryGroup_iff.mpr hU.1)).le
    exact ⟨σ, (hWmax U hUn).trans_eq hp⟩

end

end MOC
