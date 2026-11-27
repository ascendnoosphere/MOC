import MOC.Support
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Data.Real.Sqrt

/-! The real polynomial system for strict determinant separation, and
soundness of a sum-of-squares certificate for its infeasibility. -/

open BigOperators Matrix

namespace MOC

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The two spectra and the mixer each use Cartesian coordinates. The
remaining variables are one strict-inequality witness per permutation. -/
abbrev DeterminantWitnessVariable (ι : Type*) :=
  (((ι ⊕ ι) ⊕ (ι × ι)) × Bool) ⊕ Equiv.Perm ι

/-- The real and imaginary Gram equations, followed by the matching equations. -/
abbrev DeterminantWitnessEquation (ι : Type*) :=
  (ι × ι × Bool) ⊕ Equiv.Perm ι

local notation "P" => MvPolynomial (DeterminantWitnessVariable ι) ℝ
local notation "Q" => MvPolynomial (DeterminantWitnessVariable ι) ℂ

private def coordinatePolynomial (k : (ι ⊕ ι) ⊕ (ι × ι)) : Q :=
  MvPolynomial.X (.inl (k, false)) + MvPolynomial.C Complex.I *
    MvPolynomial.X (.inl (k, true))

private def adjointCoordinatePolynomial (k : (ι ⊕ ι) ⊕ (ι × ι)) : Q :=
  MvPolynomial.X (.inl (k, false)) - MvPolynomial.C Complex.I *
    MvPolynomial.X (.inl (k, true))

private def polynomialComponent (f : ℂ →ₗ[ℝ] ℝ) (p : Q) : P :=
  ∑ d ∈ p.support, MvPolynomial.monomial d (f (p.coeff d))

private theorem eval_polynomialComponent (f : ℂ →ₗ[ℝ] ℝ) (p : Q)
    (x : DeterminantWitnessVariable ι → ℝ) :
    MvPolynomial.eval x (polynomialComponent f p) =
      f (MvPolynomial.eval (fun i => (x i : ℂ)) p) := by
  rw [polynomialComponent, map_sum, MvPolynomial.eval_eq (fun i => (x i : ℂ)) p, map_sum]
  apply Finset.sum_congr rfl
  intro d _
  rw [MvPolynomial.eval_monomial]
  let r : ℝ := ∏ i ∈ d.support, x i ^ d i
  have hr : (∏ i ∈ d.support, (x i : ℂ) ^ d i) = (r : ℂ) := by
    simp only [r, Complex.ofReal_prod, Complex.ofReal_pow]
  change f (p.coeff d) * r = f (p.coeff d * ∏ i ∈ d.support, (x i : ℂ) ^ d i)
  rw [hr, mul_comm (p.coeff d), ← Complex.real_smul, map_smul, smul_eq_mul, mul_comm]

private def firstPolynomial (i : ι) : Q := coordinatePolynomial (.inl (.inl i))

private def secondPolynomial (i : ι) : Q := coordinatePolynomial (.inl (.inr i))

private def mixerPolynomial : Matrix ι ι Q :=
  Matrix.of fun i j => coordinatePolynomial (.inr (i, j))

private def mixerAdjointPolynomial : Matrix ι ι Q :=
  Matrix.of fun i j => adjointCoordinatePolynomial (.inr (j, i))

/-- The real or imaginary part of an entry of the Gram matrix minus the identity. -/
def determinantGramPolynomial (i j : ι) (imaginary : Bool) : P :=
  polynomialComponent (if imaginary then Complex.imLm else Complex.reLm)
    ((mixerAdjointPolynomial * mixerPolynomial - 1 : Matrix ι ι Q) i j)

/-- The real projection of the determinant minus one matching product. -/
def determinantGapPolynomial (σ : Equiv.Perm ι) : P :=
  polynomialComponent Complex.reLm
    ((diagonal firstPolynomial + mixerPolynomial * diagonal secondPolynomial *
      mixerAdjointPolynomial).det -
        ∏ j, (firstPolynomial (σ j) + secondPolynomial j))

private def complexCoordinate (x : DeterminantWitnessVariable ι → ℝ)
    (k : (ι ⊕ ι) ⊕ (ι × ι)) : ℂ :=
  ⟨x (.inl (k, false)), x (.inl (k, true))⟩

private theorem eval_coordinatePolynomial (x : DeterminantWitnessVariable ι → ℝ)
    (k : (ι ⊕ ι) ⊕ (ι × ι)) :
    MvPolynomial.eval (fun i => (x i : ℂ)) (coordinatePolynomial k) =
      complexCoordinate x k := by
  apply Complex.ext <;>
    simp [coordinatePolynomial, complexCoordinate, Complex.mul_re, Complex.mul_im]

private theorem eval_adjointCoordinatePolynomial (x : DeterminantWitnessVariable ι → ℝ)
    (k : (ι ⊕ ι) ⊕ (ι × ι)) :
    MvPolynomial.eval (fun i => (x i : ℂ)) (adjointCoordinatePolynomial k) =
      star (complexCoordinate x k) := by
  apply Complex.ext <;>
    simp [adjointCoordinatePolynomial, complexCoordinate, Complex.star_def,
      Complex.mul_re, Complex.mul_im]

/-- Read the first spectrum from a real valuation. -/
def witnessFirstSpectrum (x : DeterminantWitnessVariable ι → ℝ) (i : ι) : ℂ :=
  complexCoordinate x (.inl (.inl i))

/-- Read the second spectrum from a real valuation. -/
def witnessSecondSpectrum (x : DeterminantWitnessVariable ι → ℝ) (i : ι) : ℂ :=
  complexCoordinate x (.inl (.inr i))

/-- Read the mixer from a real valuation. -/
def witnessMixer (x : DeterminantWitnessVariable ι → ℝ) : Matrix ι ι ℂ :=
  Matrix.of fun i j => complexCoordinate x (.inr (i, j))

private theorem eval_mixerPolynomial (x : DeterminantWitnessVariable ι → ℝ) :
    (MvPolynomial.eval (fun i => (x i : ℂ))).mapMatrix mixerPolynomial = witnessMixer x := by
  ext i j
  exact eval_coordinatePolynomial x (.inr (i, j))

private theorem eval_mixerAdjointPolynomial (x : DeterminantWitnessVariable ι → ℝ) :
    (MvPolynomial.eval (fun i => (x i : ℂ))).mapMatrix mixerAdjointPolynomial =
      (witnessMixer x)ᴴ := by
  ext i j
  exact eval_adjointCoordinatePolynomial x (.inr (j, i))

private theorem eval_diagonalPolynomial (x : DeterminantWitnessVariable ι → ℝ)
    (k : ι → (ι ⊕ ι) ⊕ (ι × ι)) :
    (MvPolynomial.eval (fun i => (x i : ℂ))).mapMatrix
      (diagonal (fun i => coordinatePolynomial (k i))) =
      diagonal (fun i => complexCoordinate x (k i)) := by
  ext i j
  by_cases h : i = j
  · subst j
    simpa only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.diagonal_apply_eq]
      using eval_coordinatePolynomial x (k i)
  · simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.diagonal_apply_ne _ h,
      map_zero]

private theorem eval_determinantGramPolynomial (x : DeterminantWitnessVariable ι → ℝ)
    (i j : ι) (imaginary : Bool) :
    MvPolynomial.eval x (determinantGramPolynomial i j imaginary) =
      (if imaginary then Complex.imLm else Complex.reLm)
        (((witnessMixer x)ᴴ * witnessMixer x - 1) i j) := by
  rw [determinantGramPolynomial, eval_polynomialComponent]
  change (if imaginary then Complex.imLm else Complex.reLm)
    ((MvPolynomial.eval (fun k => (x k : ℂ))).mapMatrix
      (mixerAdjointPolynomial * mixerPolynomial - 1) i j) = _
  rw [map_sub, map_mul, map_one, eval_mixerAdjointPolynomial, eval_mixerPolynomial]

/-- Evaluating a gap polynomial gives the real separation for one permutation. -/
theorem eval_determinantGapPolynomial (x : DeterminantWitnessVariable ι → ℝ)
    (σ : Equiv.Perm ι) :
    MvPolynomial.eval x (determinantGapPolynomial σ) =
      (determinantValue (witnessFirstSpectrum x) (witnessSecondSpectrum x) (witnessMixer x) -
        matchingProduct (witnessFirstSpectrum x) (witnessSecondSpectrum x) σ).re := by
  rw [determinantGapPolynomial, eval_polynomialComponent, map_sub, RingHom.map_det,
    map_add, map_mul, map_mul, eval_mixerPolynomial, eval_mixerAdjointPolynomial,
    map_prod]
  delta firstPolynomial secondPolynomial determinantValue matchingProduct
  delta witnessFirstSpectrum witnessSecondSpectrum
  simp only [eval_diagonalPolynomial, map_add, eval_coordinatePolynomial, Complex.reLm_coe]

/-- Assign Cartesian real variables from two spectra, a mixer, and slack values. -/
def witnessValuation (a b : ι → ℂ) (U : Matrix ι ι ℂ)
    (t : Equiv.Perm ι → ℝ) : DeterminantWitnessVariable ι → ℝ
  | .inl (.inl (.inl i), c) => if c then (a i).im else (a i).re
  | .inl (.inl (.inr i), c) => if c then (b i).im else (b i).re
  | .inl (.inr (i, j), c) => if c then (U i j).im else (U i j).re
  | .inr σ => t σ

/-- Reading the spectral and mixer coordinates recovers the supplied matrices. -/
theorem witnessValuation_values (a b : ι → ℂ) (U : Matrix ι ι ℂ)
    (t : Equiv.Perm ι → ℝ) :
    witnessFirstSpectrum (witnessValuation a b U t) = a ∧
    witnessSecondSpectrum (witnessValuation a b U t) = b ∧
    witnessMixer (witnessValuation a b U t) = U := by
  refine ⟨?_, ?_, ?_⟩
  · funext i
    exact Complex.ext rfl rfl
  · funext i
    exact Complex.ext rfl rfl
  · ext i j
    exact Complex.ext rfl rfl

/-- The evaluated real and imaginary Gram equations state unitarity. -/
theorem gramPolynomials_zero_iff (x : DeterminantWitnessVariable ι → ℝ) :
    (∀ i j c, MvPolynomial.eval x (determinantGramPolynomial i j c) = 0) ↔
      IsUnitary (witnessMixer x) := by
  simp only [eval_determinantGramPolynomial]
  constructor
  · intro h
    have hz : (witnessMixer x)ᴴ * witnessMixer x - 1 = 0 := by
      apply Matrix.ext
      intro i j
      exact Complex.ext (h i j false) (h i j true)
    have hGram := sub_eq_zero.mp hz
    exact ⟨Matrix.mul_eq_one_comm.mp hGram, hGram⟩
  · intro h i j c
    rw [h.2, sub_self]
    cases c <;> rfl

/-- In positive order the conjecture is equivalent to infeasibility of the
polynomial Gram equations and the strict matching inequalities over the reals. -/
theorem conjecture_iff_no_polynomial_witness [Nonempty ι] :
    Conjecture ι ↔ ¬ ∃ x : DeterminantWitnessVariable ι → ℝ,
      (∀ i j c, MvPolynomial.eval x (determinantGramPolynomial i j c) = 0) ∧
        ∀ σ, 0 < MvPolynomial.eval x (determinantGapPolynomial σ) := by
  rw [conjecture_iff_real_bound]
  constructor
  · rintro h ⟨x, hGram, hgap⟩
    obtain ⟨σ, hσ⟩ := h _ _ _ ((gramPolynomials_zero_iff x).mp hGram)
    exact (not_lt_of_ge hσ) (sub_pos.mp (by
      simpa only [eval_determinantGapPolynomial, Complex.sub_re] using hgap σ))
  · intro h a b U hU
    by_contra! hgap
    let x := witnessValuation a b U (fun _ => 0)
    obtain ⟨ha, hb, hM⟩ := witnessValuation_values a b U (fun _ => 0)
    have hGram : IsUnitary (witnessMixer x) := by rwa [hM]
    refine h ⟨x, (gramPolynomials_zero_iff x).mpr hGram, fun σ => ?_⟩
    rw [eval_determinantGapPolynomial, ha, hb, hM, Complex.sub_re]
    exact sub_pos.mpr (hgap σ)

/-- There is one strict separation test per permutation. -/
theorem determinantGapPolynomial_index_count (n : ℕ) :
    Fintype.card (Equiv.Perm (Fin n)) = n.factorial := by
  rw [Fintype.card_perm, Fintype.card_fin]

/-- Replace a strict inequality `g > 0` by the real equation `g t² = 1`. -/
def determinantWitnessPolynomial : DeterminantWitnessEquation ι → P
  | .inl (i, j, c) => determinantGramPolynomial i j c
  | .inr σ => determinantGapPolynomial σ * MvPolynomial.X (.inr σ) ^ 2 - 1

/-- The certificate input is a finite system of polynomial equations over
the reals, with no inequalities and no denominator. -/
theorem conjecture_iff_no_polynomial_equation_witness [Nonempty ι] :
    Conjecture ι ↔ ¬ ∃ x : DeterminantWitnessVariable ι → ℝ,
      ∀ k, MvPolynomial.eval x (determinantWitnessPolynomial k) = 0 := by
  rw [conjecture_iff_no_polynomial_witness]
  constructor
  · rintro h ⟨x, hx⟩
    refine h ⟨x, fun i j c => hx (.inl (i, j, c)), fun σ => ?_⟩
    have hproduct : MvPolynomial.eval x (determinantGapPolynomial σ) * x (.inr σ) ^ 2 = 1 := by
      apply sub_eq_zero.mp
      simpa only [determinantWitnessPolynomial, map_sub, map_mul, map_pow, MvPolynomial.eval_X,
        map_one] using hx (.inr σ)
    have hpos : 0 < MvPolynomial.eval x (determinantGapPolynomial σ) * x (.inr σ) ^ 2 := by
      rw [hproduct]
      exact zero_lt_one
    exact pos_of_mul_pos_left hpos (sq_nonneg _)
  · rintro h ⟨x, hGram, hgap⟩
    let t (σ : Equiv.Perm ι) := (Real.sqrt (MvPolynomial.eval x
      (determinantGapPolynomial σ)))⁻¹
    let y := witnessValuation (witnessFirstSpectrum x) (witnessSecondSpectrum x) (witnessMixer x) t
    obtain ⟨ha, hb, hU⟩ := witnessValuation_values (witnessFirstSpectrum x) (witnessSecondSpectrum x) (witnessMixer x) t
    have hUnitary : IsUnitary (witnessMixer y) := by
      rw [hU]
      exact (gramPolynomials_zero_iff x).mp hGram
    refine h ⟨y, ?_⟩
    rintro (⟨i, j, c⟩ | σ)
    · exact (gramPolynomials_zero_iff y).mpr hUnitary i j c
    · simp only [determinantWitnessPolynomial, map_sub, map_mul, map_pow,
        MvPolynomial.eval_X, map_one]
      have he : MvPolynomial.eval y (determinantGapPolynomial σ) =
          MvPolynomial.eval x (determinantGapPolynomial σ) := by
        rw [eval_determinantGapPolynomial, eval_determinantGapPolynomial, ha, hb, hU]
      change MvPolynomial.eval y (determinantGapPolynomial σ) * t σ ^ 2 - 1 = 0
      dsimp only [t]
      rw [he, inv_pow, Real.sq_sqrt (hgap σ).le, mul_inv_cancel₀ (hgap σ).ne', sub_self]

/-- An exact sum-of-squares identity in the real polynomial ring proves
the conjecture in the stated order. -/
theorem conjecture_of_polynomial_infeasibility_certificate [Nonempty ι] {m : ℕ}
    (s : Fin m → P) (h : DeterminantWitnessEquation ι → P)
    (hcert : -1 = (∑ j, s j ^ 2) + ∑ k, h k * determinantWitnessPolynomial k) :
    Conjecture ι := by
  apply conjecture_iff_no_polynomial_equation_witness.mpr
  rintro ⟨x, hx⟩
  have he := congrArg (MvPolynomial.eval x) hcert
  simp only [map_neg, map_one, map_add, map_sum, map_pow, map_mul, hx, mul_zero,
    Finset.sum_const_zero, add_zero] at he
  have hnonneg : 0 ≤ ∑ j, (MvPolynomial.eval x (s j)) ^ 2 :=
    Finset.sum_nonneg fun j _ => sq_nonneg _
  linarith only [he, hnonneg]

end
end MOC
