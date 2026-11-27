import MOC.SecularCauchyCollision
import MOC.SecularChamberBoundary

/-! Deletion of a zero residue for every polynomial determinant evaluation. -/

open BigOperators Finset Matrix Polynomial

namespace MOC

noncomputable section

variable {n : ℕ}

private theorem secularColumnModel_powers_delete (d r : Fin (n+1) → ℝ)
    (i : Fin (n+1)) (hr : r i = 0) (m : ℕ) :
    let K := secularColumnModel d r
    let L := secularColumnModel (d ∘ i.succAbove) (r ∘ i.succAbove)
    (∀ j, (K^m) j i = if j = i then (d i)^m else 0) ∧
      (K^m).submatrix i.succAbove i.succAbove = L^m := by
  intro K L
  have hcol (j : Fin (n+1)) : K j i = if j = i then d i else 0 := by
    simp only [K, secularColumnModel, Matrix.add_apply, Matrix.of_apply, hr, add_zero,
      Matrix.diagonal_apply]
    split_ifs with h
    · rw [h]
    · rfl
  have hsub (j k : Fin n) : K (i.succAbove j) (i.succAbove k) = L j k := by
    simp only [K, L, secularColumnModel, Matrix.add_apply, Matrix.of_apply, Matrix.diagonal_apply,
      Function.comp_apply, Fin.succAbove_right_inj]
  induction m with
  | zero =>
      simp only [pow_zero]
      constructor
      · intro j
        simp [Matrix.one_apply]
      · exact Matrix.submatrix_one i.succAbove (fun _ _ he => Fin.succAbove_right_inj.mp he)
  | succ m ih =>
      obtain ⟨hcolpow, hsubpow⟩ := ih
      constructor
      · intro j
        rw [pow_succ, Matrix.mul_apply, sum_eq_single i]
        · rw [hcol i, if_pos rfl, hcolpow j]
          by_cases hj : j = i <;> simp [hj, pow_succ]
        · intro k _ hk
          rw [hcol k, if_neg hk, mul_zero]
        · exact fun h => (h (mem_univ i)).elim
      · ext j k : 1
        rw [Matrix.submatrix_apply, pow_succ, pow_succ, Matrix.mul_apply, Matrix.mul_apply,
          Fin.sum_univ_succAbove _ i]
        simp only [hcolpow (i.succAbove j), i.succAbove_ne j, if_false, zero_mul, zero_add, hsub]
        apply sum_congr rfl
        intro l _
        exact congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M j l * L l k) hsubpow

/-- A zero residue makes the polynomial-evaluation column a multiple of
its coordinate vector, and evaluation on the remaining block commutes with deletion. -/
theorem secularColumnModel_aeval_delete (d r : Fin (n+1) → ℝ) (p : ℝ[X])
    (i : Fin (n+1)) (hr : r i = 0) :
    let K := secularColumnModel d r
    let L := secularColumnModel (d ∘ i.succAbove) (r ∘ i.succAbove)
    (∀ j, Polynomial.aeval K p j i = if j = i then p.eval (d i) else 0) ∧
      (Polynomial.aeval K p).submatrix i.succAbove i.succAbove = Polynomial.aeval L p := by
  intro K L
  constructor
  · intro j
    have hcol (m : ℕ) : (K^m) j i = if j = i then (d i)^m else 0 :=
      (secularColumnModel_powers_delete d r i hr m).1 j
    rw [Polynomial.aeval_eq_sum_range, Matrix.sum_apply]
    simp only [Matrix.smul_apply, smul_eq_mul, hcol]
    by_cases hj : j = i <;> simp [hj, Polynomial.eval_eq_sum_range]
  · ext j k : 1
    rw [Matrix.submatrix_apply, Polynomial.aeval_eq_sum_range, Polynomial.aeval_eq_sum_range,
      Matrix.sum_apply, Matrix.sum_apply]
    apply sum_congr rfl
    intro m _
    simp only [Matrix.smul_apply]
    exact congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => p.coeff m • M j k)
      (secularColumnModel_powers_delete d r i hr m).2

/-- Determinant deletion after any polynomial evaluation of the secular model. -/
theorem det_secular_evaluation_delete (d r : Fin (n+1) → ℝ) (p : ℝ[X])
    (a : Fin (n+1) → ℝ) (i : Fin (n+1)) (hr : r i = 0) :
    (diagonal a + Polynomial.aeval (secularColumnModel d r) p).det =
      (a i + p.eval (d i)) * (diagonal (a ∘ i.succAbove) +
        Polynomial.aeval (secularColumnModel (d ∘ i.succAbove) (r ∘ i.succAbove)) p).det := by
  let M := diagonal a + Polynomial.aeval (secularColumnModel d r) p
  obtain ⟨hc,hs⟩ := secularColumnModel_aeval_delete d r p i hr
  have hcol (j : Fin (n+1)) : M j i = diagonal (fun k => a k + p.eval (d k)) j i := by
    simp only [M, Matrix.add_apply, hc, Matrix.diagonal_apply]
    split_ifs with hij
    · rw [hij]
    · simp
  have hsub : M.submatrix i.succAbove i.succAbove =
      diagonal (a ∘ i.succAbove) +
        Polynomial.aeval (secularColumnModel (d ∘ i.succAbove) (r ∘ i.succAbove)) p := by
    change (diagonal a + Polynomial.aeval (secularColumnModel d r) p).submatrix
      i.succAbove i.succAbove = _
    rw [Matrix.submatrix_add]
    change (diagonal a).submatrix i.succAbove i.succAbove +
      (Polynomial.aeval (secularColumnModel d r) p).submatrix i.succAbove i.succAbove = _
    rw [Matrix.submatrix_diagonal _ _ (fun _ _ he => Fin.succAbove_right_inj.mp he), hs]
  change M.det = _
  rw [Matrix.det_succ_column M i, sum_eq_single i]
  · have hs' : (-1 : ℝ) ^ ((i : ℕ) + (i : ℕ)) = 1 := by
      rw [← two_mul, pow_mul]
      norm_num
    rw [hcol i, Matrix.diagonal_apply_eq, hsub, hs', one_mul]
  · intro j _ hji
    rw [hcol j, Matrix.diagonal_apply_ne _ hji, mul_zero, zero_mul]
  · exact fun h => (h (mem_univ i)).elim


end

end MOC
