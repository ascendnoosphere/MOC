import MOC.Reformulations.Common
import MOC.Weights
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

/-!
C★ 11: simultaneous characteristic-polynomial hull in finite spectral
coordinates. Permutation vertices are the characteristic polynomials of the
matched commuting sums, with eigenvalues listed by column. This formulation
does not construct the universal C★ free product. The implication from the
simultaneous hull to MOC is proved; no converse is asserted.
-/

open BigOperators Matrix
open scoped Polynomial

namespace MOC.Reformulations.CStar

noncomputable section

/-- The full coefficient vector, represented as a polynomial. Taking a real
convex hull here uses one set of weights for all coefficients, rather than
one family of weights for each scalar evaluation. -/
def SimultaneousCharacteristicForm : Prop :=
  ∀ (n : ℕ) (a b : Fin n → ℂ) (U : Matrix (Fin n) (Fin n) ℂ), IsUnitary U →
    (diagonal a + U * diagonal b * Uᴴ).charpoly ∈
      convexHull ℝ (Set.range fun σ : Equiv.Perm (Fin n) =>
        (diagonal (fun j => a (σ j) + b j)).charpoly)

/-- Real-linear signed coefficient extraction, also used for the individual
elementary coefficients. -/
def signedCoefficient (c : ℂ) (k : ℕ) : Polynomial ℂ →ₗ[ℝ] ℂ where
  toFun p := c * p.coeff k
  map_add' p q := by simp [Polynomial.coeff_add, mul_add]
  map_smul' r p := by simp [Polynomial.coeff_smul, Complex.real_smul]; ring

theorem coefficient_hull_of_simultaneous (h : SimultaneousCharacteristicForm)
    {n : ℕ} (a b : Fin n → ℂ) (U : Matrix (Fin n) (Fin n) ℂ) (hU : IsUnitary U)
    (c : ℂ) (k : ℕ) :
    c * (diagonal a + U * diagonal b * Uᴴ).charpoly.coeff k ∈
      convexHull ℝ (Set.range fun σ : Equiv.Perm (Fin n) =>
        c * (diagonal (fun j => a (σ j) + b j)).charpoly.coeff k) := by
  let S := Set.range fun σ : Equiv.Perm (Fin n) =>
    (diagonal (fun j => a (σ j) + b j)).charpoly
  have he : signedCoefficient c k ((diagonal a + U * diagonal b * Uᴴ).charpoly) ∈
      signedCoefficient c k '' convexHull ℝ S :=
    ⟨_, h n a b U hU, rfl⟩
  rw [LinearMap.image_convexHull, ← Set.range_comp] at he
  exact he

/-- The simultaneous characteristic-polynomial form implies MOC by
projecting onto its constant term, with the determinant sign accounted for. -/
theorem moc_of_simultaneousCharacteristicForm (h : SimultaneousCharacteristicForm) :
    MOCIsTrue := by
  intro n a b U hU
  let c : ℂ := (-1) ^ Fintype.card (Fin n)
  have hh := coefficient_hull_of_simultaneous h a b U hU c 0
  have hs (M : Matrix (Fin n) (Fin n) ℂ) : c * M.charpoly.coeff 0 = M.det :=
    M.det_eq_sign_charpoly_coeff.symm
  simp only [hs, Matrix.det_diagonal] at hh
  exact hh

/-- The coefficient of degree `k` in `det (I + X M)` is the elementary
symmetric coefficient of index `k`. This definition includes singular matrices. -/
def elementaryCoefficient {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (k : ℕ) : ℂ :=
  (-M).charpolyRev.coeff k

theorem elementaryCoefficient_eq_neg_charpoly {n k : ℕ} (hk : k ≤ n)
    (M : Matrix (Fin n) (Fin n) ℂ) :
    elementaryCoefficient M k = (-M).charpoly.coeff (n - k) := by
  unfold elementaryCoefficient
  rw [← Matrix.reverse_charpoly, Polynomial.coeff_reverse, Matrix.charpoly_natDegree_eq_dim,
    Fintype.card_fin, Polynomial.revAt_le hk]

theorem elementaryCoefficient_top {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) :
    elementaryCoefficient M n = M.det := by
  rw [elementaryCoefficient_eq_neg_charpoly le_rfl, Nat.sub_self]
  have h := (-M).det_eq_sign_charpoly_coeff
  rw [Matrix.det_neg, Fintype.card_fin] at h
  exact mul_left_cancel₀ (pow_ne_zero n (neg_ne_zero.mpr (one_ne_zero : (1 : ℂ) ≠ 0))) h.symm

/-- C11 with weights allowed to depend on the coefficient index. -/
def SeparateCoefficientForm : Prop :=
  ∀ (n : ℕ) (a b : Fin n → ℂ) (U : Matrix (Fin n) (Fin n) ℂ), IsUnitary U →
    ∀ k : ℕ, 1 ≤ k → k ≤ n →
      elementaryCoefficient (diagonal a + U * diagonal b * Uᴴ) k ∈
        convexHull ℝ (Set.range fun σ : Equiv.Perm (Fin n) =>
          elementaryCoefficient (diagonal fun j => a (σ j) + b j) k)

theorem moc_of_separateCoefficientForm (h : SeparateCoefficientForm) : MOCIsTrue := by
  intro n a b U hU
  cases n with
  | zero => exact conjecture_le_three (by decide) a b U hU
  | succ n =>
    have htop := h (n + 1) a b U hU (n + 1) (Nat.succ_pos n) le_rfl
    simpa only [elementaryCoefficient_top, Matrix.det_diagonal] using htop

theorem separateCoefficientForm_of_simultaneous (h : SimultaneousCharacteristicForm) :
    SeparateCoefficientForm := by
  intro n a b U hU k _ hk
  have hsum : diagonal (fun j => -a j) + U * diagonal (fun j => -b j) * Uᴴ =
      -(diagonal a + U * diagonal b * Uᴴ) := by
    rw [← Matrix.diagonal_neg, ← Matrix.diagonal_neg, Matrix.mul_neg, Matrix.neg_mul, neg_add]
  have hvert (σ : Equiv.Perm (Fin n)) :
      diagonal (fun j => -a (σ j) + -b j) = -(diagonal fun j => a (σ j) + b j) := by
    rw [Matrix.diagonal_neg]
    exact congrArg Matrix.diagonal (funext fun j => (neg_add (a (σ j)) (b j)).symm)
  simpa only [one_mul, hsum, hvert, elementaryCoefficient_eq_neg_charpoly hk] using
    coefficient_hull_of_simultaneous h (fun j => -a j) (fun j => -b j) U hU 1 (n - k)

private def elementaryProduct {n : ℕ} (s : Finset (Fin n)) (d : Fin n → ℂ) : ℂ[X] :=
  ∏ j ∈ s, (1 + Polynomial.C (d j) * Polynomial.X)

private theorem coeff_affine_mul_succ (a : ℂ) (p : ℂ[X]) (k : ℕ) :
    ((1 + Polynomial.C a * Polynomial.X) * p).coeff (k + 1) =
      p.coeff (k + 1) + a * p.coeff k := by
  rw [add_mul, one_mul, mul_assoc, Polynomial.coeff_add, Polynomial.coeff_C_mul,
    mul_comm Polynomial.X p, Polynomial.coeff_mul_X]

private theorem elementaryProduct_first_coefficients {n : ℕ} (s : Finset (Fin n))
    (d : Fin n → ℂ) :
    let p := elementaryProduct s d
    let s₁ := ∑ j ∈ s, d j
    let s₂ := ∑ j ∈ s, d j ^ 2
    let s₃ := ∑ j ∈ s, d j ^ 3
    p.coeff 0 = 1 ∧ p.coeff 1 = s₁ ∧ p.coeff 2 = (s₁ ^ 2 - s₂) / 2 ∧
      p.coeff 3 = (s₁ ^ 3 - 3 * s₁ * s₂ + 2 * s₃) / 6 := by
  induction s using Finset.induction_on with
  | empty => norm_num [elementaryProduct, Polynomial.coeff_one]
  | insert i s hi ih =>
    change (elementaryProduct s d).coeff 0 = 1 ∧
      (elementaryProduct s d).coeff 1 = ∑ j ∈ s, d j ∧
      (elementaryProduct s d).coeff 2 = ((∑ j ∈ s, d j) ^ 2 - ∑ j ∈ s, d j ^ 2) / 2 ∧
      (elementaryProduct s d).coeff 3 =
        ((∑ j ∈ s, d j) ^ 3 - 3 * (∑ j ∈ s, d j) * (∑ j ∈ s, d j ^ 2) +
          2 * (∑ j ∈ s, d j ^ 3)) / 6 at ih
    obtain ⟨h₀, h₁, h₂, h₃⟩ := ih
    have hp : elementaryProduct (insert i s) d =
        (1 + Polynomial.C (d i) * Polynomial.X) * elementaryProduct s d :=
      Finset.prod_insert hi
    dsimp only
    rw [hp]
    simp only [Finset.sum_insert hi]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_mul]
      simp only [Polynomial.eval_add, Polynomial.eval_one, Polynomial.eval_mul,
        Polynomial.eval_X, mul_zero, add_zero, one_mul, ← Polynomial.coeff_zero_eq_eval_zero]
      exact h₀
    · rw [coeff_affine_mul_succ (d i) (elementaryProduct s d) 0, h₀, h₁, mul_one, add_comm]
    · rw [coeff_affine_mul_succ (d i) (elementaryProduct s d) 1, h₁, h₂]
      ring
    · rw [coeff_affine_mul_succ (d i) (elementaryProduct s d) 2, h₂, h₃]
      ring

private theorem eval_elementaryGeneratingPolynomial {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℂ) (t : ℂ) :
    (-M).charpolyRev.eval t = (1 + t • M).det := by
  rw [Matrix.charpolyRev, ← Polynomial.coe_evalRingHom t, RingHom.map_det]
  change ((1 - (Polynomial.X : ℂ[X]) • (-M).map Polynomial.C).map (Polynomial.eval t)).det =
    (1 + t • M).det
  congr 1
  ext i j
  by_cases hij : i = j
  all_goals
    simp [Matrix.map_apply, Matrix.one_apply, Matrix.sub_apply, Matrix.add_apply,
      Matrix.smul_apply, Matrix.neg_apply, smul_eq_mul, hij] <;> exact mul_comm _ _

private theorem eval_elementaryProduct_univ {n : ℕ} (d : Fin n → ℂ) (t : ℂ) :
    (elementaryProduct Finset.univ d).eval t = ∏ j, (1 + t * d j) := by
  simp only [elementaryProduct, Polynomial.eval_prod, Polynomial.eval_add, Polynomial.eval_one,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, mul_comm]

private theorem elementaryGeneratingPolynomial_diagonal {n : ℕ} (d : Fin n → ℂ) :
    (-(diagonal d)).charpolyRev = elementaryProduct Finset.univ d := by
  apply Polynomial.funext
  intro t
  rw [eval_elementaryGeneratingPolynomial, eval_elementaryProduct_univ,
    ← Matrix.diagonal_one, ← Matrix.diagonal_smul, Matrix.diagonal_add, Matrix.det_diagonal] <;> rfl

private theorem elementaryGeneratingPolynomial_signed {n : ℕ} (a b : Fin n → ℂ)
    (U : Matrix (Fin n) (Fin n) ℂ) (hU : IsUnitary U) :
    (-(diagonal a + U * diagonal b * Uᴴ)).charpolyRev =
      ∑ σ, Polynomial.C (signedWeight U σ) *
        elementaryProduct Finset.univ (fun j => a (σ j) + b j) := by
  apply Polynomial.funext
  intro t
  simp only [eval_elementaryGeneratingPolynomial, Polynomial.eval_finset_sum, Polynomial.eval_mul,
    Polynomial.eval_C, eval_elementaryProduct_univ]
  have hm : 1 + t • (diagonal a + U * diagonal b * Uᴴ) =
      diagonal (fun j => 1 + t * a j) + U * diagonal (fun j => t * b j) * Uᴴ := by
    have hb : U * diagonal (fun j => t * b j) * Uᴴ = t • (U * diagonal b * Uᴴ) := by
      change U * diagonal (t • b) * Uᴴ = _
      rw [Matrix.diagonal_smul, Matrix.mul_smul, Matrix.smul_mul]
    rw [hb, smul_add, ← add_assoc, ← Matrix.diagonal_one, ← Matrix.diagonal_smul,
      Matrix.diagonal_add] <;> rfl
  rw [hm]
  simpa only [determinantValue, matchingProduct, mul_add, add_assoc] using
    (signed_determinant (fun j => 1 + t * a j) (fun j => t * b j) U hU).symm

private theorem matchingPowerSum {n : ℕ} (a b : Fin n → ℂ) (σ : Equiv.Perm (Fin n))
    (k : ℕ) (f : ℂ → ℂ → ℂ)
    (hf : ∀ x y, (x + y) ^ k = x ^ k + y ^ k + f x y) :
    (∑ j, (a (σ j) + b j) ^ k) =
      ((∑ j, a j ^ k) + ∑ j, b j ^ k) + ∑ j, f (a (σ j)) (b j) := by
  simp_rw [hf, Finset.sum_add_distrib]
  exact congrArg (fun x : ℂ => (x + ∑ j, b j ^ k) + ∑ j, f (a (σ j)) (b j))
    (Equiv.sum_comp σ (fun j => a j ^ k))

private theorem elementaryVertex_singleton {n : ℕ} (a b : Fin n → ℂ)
    (k : ℕ) (hlo : 1 ≤ k) (hhi : k ≤ 3) :
    ∃ (c : ℂ) (f : Fin n → Fin n → ℂ), ∀ σ : Equiv.Perm (Fin n),
      (elementaryProduct Finset.univ (fun j => a (σ j) + b j)).coeff k =
        c + ∑ j, f j (σ j) := by
  let s (r : ℕ) : ℂ := (∑ j, a j ^ r) + ∑ j, b j ^ r
  have h₁ (σ : Equiv.Perm (Fin n)) : (∑ j, (a (σ j) + b j)) = s 1 := by
    simpa only [s, pow_one, Finset.sum_const_zero, add_zero] using
      matchingPowerSum a b σ 1 (fun _ _ => 0) (by intro x y; ring)
  have h₂ (σ : Equiv.Perm (Fin n)) : (∑ j, (a (σ j) + b j) ^ 2) =
      s 2 + 2 * ∑ j, a (σ j) * b j := by
    simpa only [s, Finset.mul_sum, mul_assoc] using
      matchingPowerSum a b σ 2 (fun x y => 2 * (x * y)) (by intro x y; ring)
  have h₃ (σ : Equiv.Perm (Fin n)) : (∑ j, (a (σ j) + b j) ^ 3) =
      s 3 + 3 * ∑ j, (a (σ j) ^ 2 * b j + a (σ j) * b j ^ 2) := by
    simpa only [s, Finset.mul_sum] using
      matchingPowerSum a b σ 3 (fun x y => 3 * (x ^ 2 * y + x * y ^ 2)) (by intro x y; ring)
  have hk : k = 1 ∨ k = 2 ∨ k = 3 := by omega
  rcases hk with rfl | rfl | rfl
  · refine ⟨s 1, fun _ _ => 0, fun σ => ?_⟩
    have h := (elementaryProduct_first_coefficients Finset.univ
      (fun j => a (σ j) + b j)).2.1
    rw [h, h₁, Finset.sum_const_zero, add_zero]
  · refine ⟨(s 1 ^ 2 - s 2) / 2, fun j i => -(a i * b j), fun σ => ?_⟩
    have h := (elementaryProduct_first_coefficients Finset.univ
      (fun j => a (σ j) + b j)).2.2.1
    rw [h, h₁, h₂, Finset.sum_neg_distrib]
    ring
  · refine ⟨(s 1 ^ 3 - 3 * s 1 * s 2 + 2 * s 3) / 6,
      fun j i => -(s 1) * (a i * b j) + (a i ^ 2 * b j + a i * b j ^ 2), fun σ => ?_⟩
    have h := (elementaryProduct_first_coefficients Finset.univ
      (fun j => a (σ j) + b j)).2.2.2
    rw [h, h₁, h₂, h₃]
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
    ring

/-- A single law depending only on the unitary gives the first three
elementary coefficients. The law is the Birkhoff law for singleton entries. -/
theorem firstThreeElementaryCoefficients_weights {n : ℕ}
    (a b : Fin n → ℂ) (U : Matrix (Fin n) (Fin n) ℂ) (hU : IsUnitary U) :
    ∃ w : Equiv.Perm (Fin n) → ℝ, (∀ σ, 0 ≤ w σ) ∧ (∑ σ, w σ = 1) ∧
      ∀ k : ℕ, 1 ≤ k → k ≤ 3 →
        (∑ σ, (w σ : ℂ) * elementaryCoefficient (diagonal fun j => a (σ j) + b j) k) =
          elementaryCoefficient (diagonal a + U * diagonal b * Uᴴ) k := by
  obtain ⟨w, hw, hs, hm⟩ := exists_singleton_weights U hU
  refine ⟨w, hw, hs, fun k hlo hhi => ?_⟩
  obtain ⟨c, f, hf⟩ := elementaryVertex_singleton a b k hlo hhi
  have heval (v : Equiv.Perm (Fin n) → ℂ) (hv : ∑ σ, v σ = 1) :
      (∑ σ, v σ * (elementaryProduct Finset.univ (fun j => a (σ j) + b j)).coeff k) =
        c + ∑ j, ∑ i, marginal v i j * f j i := by
    simp_rw [hf, mul_add, Finset.mul_sum]
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, hv, one_mul, Finset.sum_comm]
    simp_rw [sum_weighted_evaluation]
  have hs' : ∑ σ, (w σ : ℂ) = 1 := by exact_mod_cast hs
  simp only [elementaryCoefficient, elementaryGeneratingPolynomial_diagonal,
    elementaryGeneratingPolynomial_signed a b U hU, Polynomial.finset_sum_coeff,
    Polynomial.coeff_C_mul]
  rw [heval _ hs', heval _ (sum_signedWeight U (det_ne_zero_of_unitary hU))]
  simp only [hm, marginal_signedWeight U hU]

theorem firstThreeElementaryCoefficient_hull {n : ℕ}
    (a b : Fin n → ℂ) (U : Matrix (Fin n) (Fin n) ℂ) (hU : IsUnitary U)
    (k : ℕ) (hlo : 1 ≤ k) (hhi : k ≤ 3) :
    elementaryCoefficient (diagonal a + U * diagonal b * Uᴴ) k ∈
      convexHull ℝ (Set.range fun σ : Equiv.Perm (Fin n) =>
        elementaryCoefficient (diagonal fun j => a (σ j) + b j) k) := by
  obtain ⟨w, hw, hs, he⟩ := firstThreeElementaryCoefficients_weights a b U hU
  rw [← he k hlo hhi]
  simp_rw [← Complex.real_smul]
  exact (convex_convexHull ℝ _).sum_mem (fun σ _ => hw σ) hs
    (fun σ _ => subset_convexHull ℝ _ ⟨σ, rfl⟩)

/-- The additional premises in the separate-coefficient family are exactly the
intermediate indices from four to one below the order. -/
theorem separateCoefficientForm_iff_moc_and_intermediate :
    SeparateCoefficientForm ↔ MOCIsTrue ∧
      (∀ (n : ℕ) (a b : Fin n → ℂ) (U : Matrix (Fin n) (Fin n) ℂ), IsUnitary U →
        ∀ k : ℕ, 4 ≤ k → k < n →
          elementaryCoefficient (diagonal a + U * diagonal b * Uᴴ) k ∈
            convexHull ℝ (Set.range fun σ : Equiv.Perm (Fin n) =>
              elementaryCoefficient (diagonal fun j => a (σ j) + b j) k)) := by
  constructor
  · intro h
    exact ⟨moc_of_separateCoefficientForm h, fun n a b U hU k hk hn =>
      h n a b U hU k ((by decide : 1 ≤ 4).trans hk) hn.le⟩
  · rintro ⟨hMOC, hmiddle⟩ n a b U hU k hlo hkn
    by_cases htop : k = n
    · subst k
      simpa only [elementaryCoefficient_top, Matrix.det_diagonal] using hMOC n a b U hU
    by_cases hlow : k ≤ 3
    · exact firstThreeElementaryCoefficient_hull a b U hU k hlo hlow
    exact hmiddle n a b U hU k (by omega) (lt_of_le_of_ne hkn htop)

end

end MOC.Reformulations.CStar
