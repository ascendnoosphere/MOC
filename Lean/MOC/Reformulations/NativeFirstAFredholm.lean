import MOC.Reformulations.CStar
import MOC.Reformulations.FirstMatrix
import MOC.Geometry
import Mathlib.Data.Complex.Exponential

/-! Finite Fredholm and regularized determinants. An infinite trace-ideal
statement is not inferred here: that direction needs operator trace-ideal
approximation, a Fredholm determinant continuity theorem, and control of
infinite spectral products. -/

open BigOperators Matrix

namespace MOC.Reformulations
noncomputable section

/-- Finite Fredholm determinant points. This affine shift acts on the first
spectrum, not on the relative unitary. -/
def finiteFredholmValue {n : ℕ} (a b : Fin n → ℂ) (U : Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  ((1 : Matrix (Fin n) (Fin n) ℂ) + diagonal a + U * diagonal b * Uᴴ).det

def finiteFredholmVertex {n : ℕ} (a b : Fin n → ℂ) (σ : Equiv.Perm (Fin n)) : ℂ :=
  ∏ i, (1 + a (σ i) + b i)

theorem finiteFredholmValue_shift {n : ℕ} (a b : Fin n → ℂ)
    (U : Matrix (Fin n) (Fin n) ℂ) :
    finiteFredholmValue a b U = determinantValue (fun i => 1 + a i) b U := by
  have hd : diagonal (fun i => 1 + a i) = (1 : Matrix (Fin n) (Fin n) ℂ) + diagonal a := by
    rw [← Matrix.diagonal_one, ← Matrix.diagonal_add]
  simp only [finiteFredholmValue, determinantValue, hd, add_assoc]

theorem finiteFredholmVertex_shift {n : ℕ} (a b : Fin n → ℂ) (σ : Equiv.Perm (Fin n)) :
    finiteFredholmVertex a b σ = matchingProduct (fun i => 1 + a i) b σ :=
  rfl

/-- The finite part of Atlas 050 and 062, with actual Fredholm determinants
and eigenvalue products. The infinite closed-hull claim is a separate limit. -/
def nativeFiniteFredholmHull : Prop :=
  ∀ (n : ℕ) (a b : Fin n → ℂ) (U : Matrix (Fin n) (Fin n) ℂ), IsUnitary U →
    finiteFredholmValue a b U ∈ convexHull ℝ (Set.range (finiteFredholmVertex a b))

theorem moc_iff_nativeFiniteFredholmHull : MOCIsTrue ↔ nativeFiniteFredholmHull := by
  constructor
  · intro h n a b U hU
    simpa only [finiteFredholmValue_shift, finiteFredholmVertex_shift] using
      h n (fun i => 1 + a i) b U hU
  · intro h n a b U hU
    have hh := h n (fun i => a i - 1) b U hU
    rw [finiteFredholmValue_shift] at hh
    change determinantValue (fun i => 1 + (a i - 1)) b U ∈
      convexHull ℝ (Set.range (matchingProduct (fun i => 1 + (a i - 1)) b)) at hh
    have hs : (fun i => 1 + (a i - 1)) = a := funext fun i => by ring
    rwa [hs] at hh

/-- Finite order-two regularization via the trace of the actual sum. -/
def finiteRegularizedTwoValue {n : ℕ} (a b : Fin n → ℂ)
    (U : Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  finiteFredholmValue a b U * Complex.exp (-(diagonal a + U * diagonal b * Uᴴ).trace)

def finiteRegularizedTwoVertex {n : ℕ} (a b : Fin n → ℂ)
    (σ : Equiv.Perm (Fin n)) : ℂ :=
  ∏ i, ((1 + a (σ i) + b i) * Complex.exp (-(a (σ i) + b i)))

private theorem traceRelative {n : ℕ} (a b : Fin n → ℂ) (U : Matrix (Fin n) (Fin n) ℂ)
    (hU : IsUnitary U) :
    (diagonal a + U * diagonal b * Uᴴ).trace = (∑ i, a i) + ∑ i, b i := by
  rw [Matrix.trace_add, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hU.2, Matrix.one_mul]
  simp [Matrix.trace]

private theorem regularizedTwoVertex_eq {n : ℕ} (a b : Fin n → ℂ)
    (σ : Equiv.Perm (Fin n)) :
    finiteRegularizedTwoVertex a b σ =
      finiteFredholmVertex a b σ * Complex.exp (-((∑ i, a i) + ∑ i, b i)) := by
  unfold finiteRegularizedTwoVertex finiteFredholmVertex
  rw [Finset.prod_mul_distrib, ← Complex.exp_sum, Finset.sum_neg_distrib,
    Finset.sum_add_distrib, Equiv.sum_comp σ a]

/-- The same nonzero complex factor multiplies the determinant and every vertex.
No such factorization for regularization order three is used. -/
theorem finiteRegularizedTwoHull_iff {n : ℕ} (a b : Fin n → ℂ)
    (U : Matrix (Fin n) (Fin n) ℂ) (hU : IsUnitary U) :
    finiteRegularizedTwoValue a b U ∈
        convexHull ℝ (Set.range (finiteRegularizedTwoVertex a b)) ↔
      finiteFredholmValue a b U ∈ convexHull ℝ (Set.range (finiteFredholmVertex a b)) := by
  let c := Complex.exp (-((∑ i, a i) + ∑ i, b i))
  have hc : c ≠ 0 := Complex.exp_ne_zero _
  have hcV : finiteRegularizedTwoValue a b U = c * finiteFredholmValue a b U := by
    unfold finiteRegularizedTwoValue
    rw [traceRelative a b U hU, mul_comm]
  have hcP σ : finiteRegularizedTwoVertex a b σ = c * finiteFredholmVertex a b σ := by
    rw [regularizedTwoVertex_eq, mul_comm]
  exact hull_common_factor_iff hc hcV hcP

/-- Atlas 063 and order two of Atlas 064, on actual finite Hilbert spaces. -/
def nativeFiniteRegularizedTwoHull : Prop :=
  ∀ (n : ℕ) (a b : Fin n → ℂ) (U : Matrix (Fin n) (Fin n) ℂ), IsUnitary U →
    finiteRegularizedTwoValue a b U ∈
      convexHull ℝ (Set.range (finiteRegularizedTwoVertex a b))

theorem moc_iff_nativeFiniteRegularizedTwoHull : MOCIsTrue ↔ nativeFiniteRegularizedTwoHull := by
  rw [moc_iff_nativeFiniteFredholmHull]
  constructor
  · intro h n a b U hU
    exact (finiteRegularizedTwoHull_iff a b U hU).mpr (h n a b U hU)
  · intro h n a b U hU
    exact (finiteRegularizedTwoHull_iff a b U hU).mp (h n a b U hU)

end
end MOC.Reformulations
