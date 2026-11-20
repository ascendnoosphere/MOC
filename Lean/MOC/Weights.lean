import MOC.Core
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Complex.BigOperators

/-! The all-order signed determinant identity and the Birkhoff reduction.
Bibliography entries 6, 9, 12, 13, and 78 motivate the distinction between
singleton marginals and the full squared-minor problem. -/

open BigOperators Matrix Finset

namespace MOC

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def leibnizTerm (U : Matrix ι ι ℂ) (σ : Equiv.Perm ι) : ℂ :=
  ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ j, U (σ j) j

def signedWeight (U : Matrix ι ι ℂ) (σ : Equiv.Perm ι) : ℂ :=
  leibnizTerm U σ / U.det

theorem sum_signedWeight (U : Matrix ι ι ℂ) (h : U.det ≠ 0) :
    ∑ σ, signedWeight U σ = 1 := by
  simp only [signedWeight, ← Finset.sum_div, leibnizTerm, ← Matrix.det_apply']
  exact div_self h

theorem signed_determinant (a b : ι → ℂ) (U : Matrix ι ι ℂ) (h : IsUnitary U) :
    ∑ σ, signedWeight U σ * matchingProduct a b σ = determinantValue a b U := by
  have hmat : (diagonal a + U * diagonal b * Uᴴ) * U =
      Matrix.of (fun i j => (a i + b j) * U i j) := by
    rw [Matrix.add_mul, Matrix.mul_assoc (U * diagonal b), h.2, Matrix.mul_one]
    ext i j
    simp only [Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.add_apply, Matrix.of_apply]
    ring
  have hd : determinantValue a b U * U.det =
      ∑ σ, leibnizTerm U σ * matchingProduct a b σ := by
    unfold determinantValue
    rw [← Matrix.det_mul, hmat, Matrix.det_apply']
    apply Finset.sum_congr rfl
    intro σ _
    simp only [leibnizTerm, matchingProduct, Matrix.of_apply, Finset.prod_mul_distrib]
    ring
  rw [(eq_div_iff (det_ne_zero_of_unitary h)).mpr hd, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro σ _
  unfold signedWeight
  ring

def marginal (w : Equiv.Perm ι → ℂ) (i j : ι) : ℂ :=
  ∑ σ, if σ j = i then w σ else 0

theorem adjugate_unitary (U : Matrix ι ι ℂ) (h : IsUnitary U) :
    U.adjugate = U.det • Uᴴ := by
  calc
    U.adjugate = (U.adjugate * U) * Uᴴ := by rw [Matrix.mul_assoc, h.1, Matrix.mul_one]
    _ = _ := by rw [Matrix.adjugate_mul, Matrix.smul_mul, Matrix.one_mul]

theorem marginal_signedWeight (U : Matrix ι ι ℂ) (h : IsUnitary U) (i j : ι) :
    marginal (signedWeight U) i j = (Complex.normSq (U i j) : ℂ) := by
  let V := U.updateCol j (Pi.single i (U i j))
  have hf : V.det = ∑ σ, if σ j = i then leibnizTerm U σ else 0 := by
    rw [Matrix.det_apply']
    apply Finset.sum_congr rfl
    intro σ _
    by_cases hij : σ j = i
    · rw [if_pos hij]
      unfold leibnizTerm
      congr 1
      apply Finset.prod_congr rfl
      intro k _
      by_cases hk : k = j
      · subst k
        simp [V, hij]
      · simp [V, Matrix.updateCol_apply, hk, Ne.symm hk]
    · rw [if_neg hij]
      have hz : (∏ k, V (σ k) k) = 0 := by
        apply Finset.prod_eq_zero (Finset.mem_univ j)
        simp [V, Pi.single_apply, hij]
      rw [hz, mul_zero]
  have hd : V.det = U i j * U.adjugate j i := by
    have hv : Pi.single i (U i j) = U i j • (Pi.single i (1 : ℂ) : ι → ℂ) := by
      funext k
      by_cases hk : k = i <;> simp [Pi.single_apply, hk]
    dsimp [V]
    rw [hv, Matrix.det_updateCol_smul, ← Matrix.det_transpose,
      ← Matrix.updateRow_transpose, ← Matrix.adjugate_apply, ← Matrix.adjugate_transpose]
    rfl
  have he : marginal (signedWeight U) i j = V.det / U.det := by
    rw [hf, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro σ _
    by_cases hσ : σ j = i <;> simp [hσ, signedWeight]
  rw [he, hd, adjugate_unitary U h, Complex.normSq_eq_conj_mul_self]
  change U i j * (U.det * star (U i j)) / U.det = star (U i j) * U i j
  field_simp [det_ne_zero_of_unitary h]
  ring

theorem normSq_transpose_doublyStochastic (U : Matrix ι ι ℂ) (h : IsUnitary U) :
    Matrix.of (fun j i => Complex.normSq (U i j)) ∈ doublyStochastic ℝ ι := by
  rw [mem_doublyStochastic_iff_sum]
  refine ⟨fun j i => Complex.normSq_nonneg _, ?_, ?_⟩
  · intro j
    have hj := congrArg (fun M : Matrix ι ι ℂ => M j j) h.2
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply_eq] at hj
    apply Complex.ofReal_injective
    rw [Complex.ofReal_sum, Complex.ofReal_one]
    simpa only [Matrix.of_apply, Complex.normSq_eq_conj_mul_self] using hj
  · intro i
    have hi := congrArg (fun M : Matrix ι ι ℂ => M i i) h.1
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply_eq] at hi
    apply Complex.ofReal_injective
    rw [Complex.ofReal_sum, Complex.ofReal_one]
    simpa only [Matrix.of_apply, Complex.normSq_eq_conj_mul_self, mul_comm] using hi

theorem exists_singleton_weights (U : Matrix ι ι ℂ) (h : IsUnitary U) :
    ∃ w : Equiv.Perm ι → ℝ, (∀ σ, 0 ≤ w σ) ∧ (∑ σ, w σ = 1) ∧
      ∀ i j, marginal (fun σ => (w σ : ℂ)) i j = (Complex.normSq (U i j) : ℂ) := by
  obtain ⟨w, hw, hs, he⟩ := exists_eq_sum_perm_of_mem_doublyStochastic
    (normSq_transpose_doublyStochastic U h)
  refine ⟨w, hw, hs, fun i j => ?_⟩
  have heij := congrArg (fun M : Matrix ι ι ℝ => M j i) he
  have hr : (∑ σ : Equiv.Perm ι, if σ j = i then w σ else 0) = Complex.normSq (U i j) := by
    simpa [Matrix.sum_apply, Matrix.smul_apply, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply,
      mul_ite, eq_comm] using heij
  unfold marginal
  have hcast := congrArg (fun t : ℝ => (t : ℂ)) hr
  simpa only [Complex.ofReal_sum, apply_ite, Complex.ofReal_zero] using hcast

theorem sum_weighted_evaluation (w : Equiv.Perm ι → ℂ) (j : ι) (f : ι → ℂ) :
    ∑ σ, w σ * f (σ j) = ∑ i, marginal w i j * f i := by
  symm
  simp only [marginal, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro σ _
  simp [ite_mul]

/-- Any matching-product expression linear in singleton assignments is certified by Birkhoff. -/
theorem holds_of_singleton_expansion (a b : ι → ℂ) (U : Matrix ι ι ℂ) (h : IsUnitary U)
    (c : ℂ) (f : ι → ι → ℂ)
    (hexp : ∀ σ, matchingProduct a b σ = c + ∑ j, f j (σ j)) : Holds a b U := by
  have heval (w : Equiv.Perm ι → ℂ) (hs : ∑ σ, w σ = 1) :
      ∑ σ, w σ * matchingProduct a b σ = c + ∑ j, ∑ i, marginal w i j * f j i := by
    simp_rw [hexp, mul_add, mul_sum]
    rw [sum_add_distrib, ← sum_mul, hs, one_mul, Finset.sum_comm]
    simp_rw [sum_weighted_evaluation]
  obtain ⟨w, hw, hs, hm⟩ := exists_singleton_weights U h
  apply holds_of_weights w hw hs
  have hs' : ∑ σ, (w σ : ℂ) = 1 := by
    simpa only [Complex.ofReal_sum, Complex.ofReal_one] using
      congrArg (fun t : ℝ => (t : ℂ)) hs
  rw [← signed_determinant a b U h, heval _ hs',
    heval _ (sum_signedWeight U (det_ne_zero_of_unitary h))]
  simp only [hm, marginal_signedWeight U h]

def exceptProduct (a : ι → ℂ) (i : ι) : ℂ :=
  ∏ k, if k = i then 1 else a k

theorem exceptProduct_comp (a : ι → ℂ) (σ : Equiv.Perm ι) (j : ι) :
    exceptProduct (a ∘ σ) j = exceptProduct a (σ j) := by
  unfold exceptProduct
  rw [← Equiv.prod_comp σ (fun k => if k = σ j then 1 else a k)]
  simp [Function.comp_def, σ.injective.eq_iff]

/-- One potentially exceptional eigenvalue of the second summand, in any order. -/
theorem holds_one_exception (a b : ι → ℂ) (U : Matrix ι ι ℂ) (h : IsUnitary U)
    (j : ι) (t : ℂ) (hb : ∀ k, k ≠ j → b k = t) : Holds a b U := by
  apply holds_of_singleton_expansion a b U h 0
    (fun k i => if k = j then (a i + b j) * exceptProduct (fun l => a l + t) i else 0)
  intro σ
  simp only [zero_add, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [← exceptProduct_comp]
  unfold matchingProduct exceptProduct
  rw [← Finset.mul_prod_erase Finset.univ (fun k => a (σ k) + b k) (Finset.mem_univ j)]
  congr 1
  simp only [Function.comp_apply]
  rw [← Finset.prod_erase (f := fun k => if k = j then 1 else a (σ k) + t)
    Finset.univ (by simp : (if j = j then (1 : ℂ) else a (σ j) + t) = 1)]
  apply Finset.prod_congr rfl
  intro k hk
  have hk' : k ≠ j := (Finset.mem_erase.mp hk).1
  simp [hk', hb k hk', Function.comp_def]

private theorem prod_add_two (a b : Fin 2 → ℂ) :
    ∏ j, (a j + b j) =
      (∏ j, a j) + (∏ j, b j) + ∑ j, exceptProduct a j * b j := by
  simp [Fin.prod_univ_succ, Fin.sum_univ_succ, exceptProduct]
  ring

private theorem prod_add_three (a b : Fin 3 → ℂ) :
    ∏ j, (a j + b j) = (∏ j, a j) + (∏ j, b j) +
      ∑ j, (exceptProduct a j * b j + a j * exceptProduct b j) := by
  simp [Fin.prod_univ_succ, Fin.sum_univ_succ, exceptProduct]
  ring

theorem conjecture_two : Conjecture (Fin 2) := by
  intro a b U h
  apply holds_of_singleton_expansion a b U h ((∏ j, a j) + ∏ j, b j)
    (fun j i => exceptProduct a i * b j)
  intro σ
  simpa [matchingProduct, Function.comp_apply, exceptProduct_comp, Equiv.prod_comp σ] using
    prod_add_two (a ∘ σ) b

theorem conjecture_three : Conjecture (Fin 3) := by
  intro a b U h
  apply holds_of_singleton_expansion a b U h ((∏ j, a j) + ∏ j, b j)
    (fun j i => exceptProduct a i * b j + a i * exceptProduct b j)
  intro σ
  simpa [matchingProduct, Function.comp_apply, exceptProduct_comp, Equiv.prod_comp σ] using
    prod_add_three (a ∘ σ) b

theorem conjecture_of_subsingleton [Subsingleton ι] : Conjecture ι := by
  intro a b U h
  apply holds_of_commute a b h
  ext i j
  have hij : i = j := Subsingleton.elim i j
  subst j
  simp [Matrix.diagonal_mul, Matrix.mul_diagonal, mul_comm]

theorem conjecture_zero : Conjecture (Fin 0) := conjecture_of_subsingleton

theorem conjecture_one : Conjecture (Fin 1) := conjecture_of_subsingleton

end

end MOC
