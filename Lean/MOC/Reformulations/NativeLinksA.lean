import MOC.Claim
import MOC.Reformulations.SecondCoefficient
import MOC.Weights
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Eval.SMul
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

open BigOperators Finset Matrix Polynomial
open scoped Polynomial

namespace MOC.Reformulations

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The actual mixed determinant polynomial, with the first summand fixed. -/
def mixedPencilPolynomial (a b : ι → ℂ) (U : Matrix ι ι ℂ) : ℂ[X] :=
  ((diagonal a).map C + (X : ℂ[X]) • (U * diagonal b * Uᴴ).map C).det

/-- One vertex polynomial for the mixed determinant. -/
def mixedPencilVertex (a b : ι → ℂ) (σ : Equiv.Perm ι) : ℂ[X] :=
  ∏ j, (C (a (σ j)) + X * C (b j))

private theorem mixedPencil_signed (a b : ι → ℂ) (U : Matrix ι ι ℂ) (hU : IsUnitary U) :
    mixedPencilPolynomial a b U =
      ∑ σ, C (signedWeight U σ) * mixedPencilVertex a b σ := by
  letI : Infinite ℂ := Infinite.of_injective (fun n : ℕ => (n : ℂ)) Nat.cast_injective
  apply Polynomial.funext
  intro t
  simp only [mixedPencilPolynomial, mixedPencilVertex, Polynomial.eval_finset_sum,
    Polynomial.eval_prod, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X]
  rw [← Polynomial.coe_evalRingHom t, RingHom.map_det]
  have h₁ : ((diagonal a).map C + (X : ℂ[X]) • (U * diagonal b * Uᴴ).map C).map (eval t) =
      diagonal a + U * diagonal (fun i => t * b i) * Uᴴ := by
    have hdiag : diagonal (fun i => t * b i) = t • diagonal b := by
      ext i j
      by_cases hij : i = j <;> simp [Matrix.diagonal_apply, hij]
    rw [hdiag, Matrix.mul_smul, Matrix.smul_mul]
    ext i j
    simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
      Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
  change (((diagonal a).map C + (X : ℂ[X]) • (U * diagonal b * Uᴴ).map C).map (eval t)).det = _
  rw [h₁]
  exact (signed_determinant a (fun j => t * b j) U hU).symm

/-- A singleton assignment expression for a genuine mixed determinant
coefficient suffices to transport that coefficient by a positive
Birkhoff law. There is no assumption of MOC or of a compound-minor law. -/
theorem mixedPencil_coeff_hull_of_singleton (a b : ι → ℂ) (U : Matrix ι ι ℂ)
    (hU : IsUnitary U) (k : ℕ) (c : ℂ) (f : ι → ι → ℂ)
    (hexp : ∀ σ, (mixedPencilVertex a b σ).coeff k = c + ∑ j, f j (σ j)) :
    (mixedPencilPolynomial a b U).coeff k ∈
      convexHull ℝ (Set.range (fun σ => (mixedPencilVertex a b σ).coeff k)) := by
  have heval (w : Equiv.Perm ι → ℂ) (hs : ∑ σ, w σ = 1) :
      ∑ σ, w σ * (mixedPencilVertex a b σ).coeff k =
        c + ∑ j, ∑ i, marginal w i j * f j i := by
    simp_rw [hexp, mul_add, mul_sum]
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, hs, one_mul, Finset.sum_comm]
    simp_rw [sum_weighted_evaluation]
  obtain ⟨w, hw, hs, hm⟩ := exists_singleton_weights U hU
  have hs' : ∑ σ, (w σ : ℂ) = 1 := by exact_mod_cast hs
  have hid :
      (∑ σ, (w σ : ℂ) * (mixedPencilVertex a b σ).coeff k) =
        (mixedPencilPolynomial a b U).coeff k := by
    rw [mixedPencil_signed a b U hU, Polynomial.finset_sum_coeff]
    simp only [Polynomial.coeff_C_mul]
    rw [heval _ hs', heval _ (sum_signedWeight U (det_ne_zero_of_unitary hU))]
    simp only [hm, marginal_signedWeight U hU]
  rw [← hid]
  simp_rw [← Complex.real_smul]
  exact (convex_convexHull ℝ _).sum_mem (fun σ _ => hw σ) hs
    (fun σ _ => subset_convexHull ℝ _ ⟨σ, rfl⟩)


private theorem mixedPencilVertex_coeff_one (a b : ι → ℂ) (σ : Equiv.Perm ι) :
    (mixedPencilVertex a b σ).coeff 1 = ∑ j, b j * exceptProduct a (σ j) := by
  have hc (p : ℂ[X]) : p.coeff 1 = p.derivative.eval 0 := by rw [← coeff_zero_eq_eval_zero, coeff_derivative]; simp
  rw [hc, mixedPencilVertex]
  change (derivative ((Finset.univ : Finset ι).val.map
    (fun j => C (a (σ j)) + X * C (b j))).prod).eval 0 = _
  rw [derivative_prod]
  simp only [← Finset.erase_val]
  change (∑ j : ι, (∏ k ∈ Finset.univ.erase j, (C (a (σ k)) + X * C (b k))) *
    derivative (C (a (σ j)) + X * C (b j))).eval 0 = _
  simp only [eval_finset_sum, eval_mul, eval_prod, eval_add, eval_C, eval_X,
    zero_mul, add_zero, derivative_add, derivative_C, derivative_mul, derivative_X,
    one_mul, mul_zero, zero_add]
  apply Finset.sum_congr rfl
  intro j _
  rw [mul_comm, ← exceptProduct_comp]
  unfold exceptProduct
  congr 1
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ j)]
  simp only [ite_true, mul_one]
  apply Finset.prod_congr rfl
  intro k hk
  simp [Finset.ne_of_mem_erase hk]

/-- First-order polarization is an unconditional native case of Atlas 048.
Its permutation values are the independent first coefficients, not evaluations
of the determinant polynomial and not a simultaneous all-coefficient law. -/
theorem mixedPencil_first_coeff_hull (a b : ι → ℂ) (U : Matrix ι ι ℂ) (hU : IsUnitary U) :
    (mixedPencilPolynomial a b U).coeff 1 ∈
      convexHull ℝ (Set.range (fun σ => (mixedPencilVertex a b σ).coeff 1)) := by
  exact mixedPencil_coeff_hull_of_singleton a b U hU 1 0
    (fun j i => b j * exceptProduct a i)
    (fun σ => by simpa only [zero_add] using mixedPencilVertex_coeff_one a b σ)


omit [Fintype ι] in
private theorem reflect_affine_prod (a b : ι → ℂ) (S : Finset ι) :
    (∏ j ∈ S, (C (a j) + X * C (b j))).reflect S.card =
      ∏ j ∈ S, (C (b j) + X * C (a j)) := by
  have hdeg (j : ι) : (C (a j) + X * C (b j)).natDegree ≤ 1 := by
    apply Polynomial.natDegree_add_le_of_degree_le (by simp)
    exact Polynomial.natDegree_mul_le.trans (by simp)
  induction S using Finset.induction_on with
  | empty => simp
  | insert j S hj ih =>
      rw [Finset.card_insert_of_not_mem hj, Finset.prod_insert hj, Finset.prod_insert hj]
      rw [Nat.add_comm S.card 1, Polynomial.reflect_mul _ _ (hdeg j), ih]
      · have hflip : (X * C (b j)).reflect 1 = C (b j) := by
          rw [mul_comm, ← pow_one (X : ℂ[X]), Polynomial.reflect_C_mul_X_pow]
          simp
        rw [Polynomial.reflect_add, Polynomial.reflect_C, hflip]
        rw [pow_one, add_comm, mul_comm (C (a j))]
      · refine (Polynomial.natDegree_prod_le _ _).trans ?_
        simpa using (Finset.sum_le_sum fun i (_ : i ∈ S) => hdeg i)

private theorem mixedPencilVertex_coeff_pred (a b : ι → ℂ) (σ : Equiv.Perm ι)
    (hn : 1 ≤ Fintype.card ι) :
    (mixedPencilVertex a b σ).coeff (Fintype.card ι - 1) =
      ∑ j, a (σ j) * exceptProduct b j := by
  have e := reflect_affine_prod (fun j => a (σ j)) b (Finset.univ : Finset ι)
  change ((∏ j, (C (a (σ j)) + X * C (b j)))).reflect
    (Finset.univ : Finset ι).card = _ at e
  simp only [Finset.card_univ] at e
  have f := congrArg (fun p : ℂ[X] => p.coeff 1) e
  simp only [Polynomial.coeff_reflect, Polynomial.revAt_le hn] at f
  rw [mixedPencilVertex, f]
  exact mixedPencilVertex_coeff_one b (a ∘ σ) (Equiv.refl ι)

/-- Penultimate coefficient, by reflecting each affine factor; no
nonvanishing of any individual eigenvalue is required. -/
theorem mixedPencil_penultimate_coeff_hull (a b : ι → ℂ) (U : Matrix ι ι ℂ)
    (hU : IsUnitary U) (hn : 1 ≤ Fintype.card ι) :
    (mixedPencilPolynomial a b U).coeff (Fintype.card ι - 1) ∈
      convexHull ℝ (Set.range (fun σ =>
        (mixedPencilVertex a b σ).coeff (Fintype.card ι - 1))) := by
  exact mixedPencil_coeff_hull_of_singleton a b U hU _ 0
    (fun j i => a i * exceptProduct b j)
    (fun σ => by simpa only [zero_add] using mixedPencilVertex_coeff_pred a b σ hn)


/-- Both boundary coefficients, at degrees zero and the order, belong to
their matching hulls. Each vertex is independent of the permutation here. -/
theorem mixedPencil_boundary_coeff_hulls (a b : ι → ℂ) (U : Matrix ι ι ℂ)
    (hU : IsUnitary U) :
    (mixedPencilPolynomial a b U).coeff 0 ∈
      convexHull ℝ (Set.range (fun σ => (mixedPencilVertex a b σ).coeff 0)) ∧
    (mixedPencilPolynomial a b U).coeff (Fintype.card ι) ∈
      convexHull ℝ (Set.range (fun σ => (mixedPencilVertex a b σ).coeff (Fintype.card ι))) := by
  constructor
  · apply mixedPencil_coeff_hull_of_singleton a b U hU 0 (∏ i, a i) (fun _ _ => 0)
    intro σ
    rw [mixedPencilVertex, coeff_zero_eq_eval_zero, Polynomial.eval_prod]
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
      zero_mul, add_zero, Finset.sum_const_zero]
    exact Equiv.prod_comp σ a
  · apply mixedPencil_coeff_hull_of_singleton a b U hU _ (∏ j, b j) (fun _ _ => 0)
    intro σ
    have e := reflect_affine_prod (fun j => a (σ j)) b (Finset.univ : Finset ι)
    have f := congrArg (fun p : ℂ[X] => p.coeff 0) e
    simp only [Finset.card_univ, Polynomial.coeff_reflect, Polynomial.revAt_zero] at f
    rw [mixedPencilVertex, f, coeff_zero_eq_eval_zero, Polynomial.eval_prod]
    simp


/-- The simultaneous strengthening of Atlas 048 is a hull of actual
determinant polynomials. Independent coefficient hulls do not imply it
by an abstract convexity argument. -/
def SimultaneousMixedPencilHull : Prop :=
  ∀ (n : ℕ) (a b : Fin n → ℂ) (U : Matrix (Fin n) (Fin n) ℂ), IsUnitary U →
    mixedPencilPolynomial a b U ∈ convexHull ℝ (Set.range (mixedPencilVertex a b))

/-- Atlas 048 with a separate convex hull for each mixed coefficient. -/
def SeparateMixedPencilHull : Prop :=
  ∀ (n : ℕ) (a b : Fin n → ℂ) (U : Matrix (Fin n) (Fin n) ℂ), IsUnitary U →
    ∀ k : ℕ, k ≤ n →
      (mixedPencilPolynomial a b U).coeff k ∈
        convexHull ℝ (Set.range (fun σ => (mixedPencilVertex a b σ).coeff k))

theorem separateMixedPencilHull_of_simultaneous (h : SimultaneousMixedPencilHull) :
    SeparateMixedPencilHull := by
  intro n a b U hU k _
  let coeff := CStar.signedCoefficient 1 k
  have hv : coeff (mixedPencilPolynomial a b U) ∈
      coeff '' convexHull ℝ (Set.range (mixedPencilVertex a b)) :=
    ⟨_, h n a b U hU, rfl⟩
  rw [LinearMap.image_convexHull, ← Set.range_comp] at hv
  change 1 * (mixedPencilPolynomial a b U).coeff k ∈
    convexHull ℝ (Set.range fun σ => 1 * (mixedPencilVertex a b σ).coeff k) at hv
  simpa only [one_mul] using hv

theorem mixedPencil_coeff_hull_of_order_le_three {n k : ℕ} (hn : n ≤ 3) (hk : k ≤ n)
    (a b : Fin n → ℂ) (U : Matrix (Fin n) (Fin n) ℂ) (hU : IsUnitary U) :
    (mixedPencilPolynomial a b U).coeff k ∈
      convexHull ℝ (Set.range (fun σ => (mixedPencilVertex a b σ).coeff k)) := by
  have cases_k : k = 0 ∨ k = 1 ∨ k = n - 1 ∨ k = n := by omega
  rcases cases_k with rfl | rfl | hr | rfl
  · exact (mixedPencil_boundary_coeff_hulls a b U hU).1
  · exact mixedPencil_first_coeff_hull a b U hU
  · rw [hr]
    by_cases hpos : 1 ≤ n
    · have hcard : 1 ≤ Fintype.card (Fin n) := by simpa only [Fintype.card_fin] using hpos
      simpa only [Fintype.card_fin] using mixedPencil_penultimate_coeff_hull a b U hU hcard
    · have hz : n = 0 := by omega
      subst n
      simpa only [Nat.zero_sub] using (mixedPencil_boundary_coeff_hulls a b U hU).1
  · simpa only [Fintype.card_fin] using (mixedPencil_boundary_coeff_hulls a b U hU).2

private def evalOneLinear : ℂ[X] →ₗ[ℝ] ℂ where
  toFun p := p.eval 1
  map_add' p q := Polynomial.eval_add
  map_smul' r p := by
    change (r • p).eval 1 = r • p.eval 1
    exact Polynomial.eval_smul r p 1

/-- One positive law on the whole mixed determinant polynomial proves MOC.
The converse is not obtained by separately checking the first and last
coefficients, or by the pointwise spectral equivalence. -/
theorem moc_of_simultaneousMixedPencilHull (h : SimultaneousMixedPencilHull) :
    MOCIsTrue := by
  intro n a b U hU
  let S := Set.range (mixedPencilVertex a b)
  have hv : evalOneLinear (mixedPencilPolynomial a b U) ∈
      evalOneLinear '' convexHull ℝ S := ⟨_, h n a b U hU, rfl⟩
  rw [LinearMap.image_convexHull, ← Set.range_comp] at hv
  have hvertex (σ : Equiv.Perm (Fin n)) :
      evalOneLinear (mixedPencilVertex a b σ) = matchingProduct a b σ := by
    change (mixedPencilVertex a b σ).eval 1 = _
    simp [mixedPencilVertex, matchingProduct, Polynomial.eval_prod]
  have hp : evalOneLinear (mixedPencilPolynomial a b U) = determinantValue a b U := by
    change (mixedPencilPolynomial a b U).eval 1 = _
    rw [mixedPencil_signed a b U hU]
    simp only [Polynomial.eval_finset_sum, Polynomial.eval_mul, Polynomial.eval_C]
    change ∑ σ, signedWeight U σ * evalOneLinear (mixedPencilVertex a b σ) = _
    simp only [hvertex, signed_determinant a b U hU]
  have hh : (evalOneLinear ∘ mixedPencilVertex a b) = matchingProduct a b := funext hvertex
  rw [hh, hp] at hv
  exact hv

end

end MOC.Reformulations
