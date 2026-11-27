import MOC.SecularCauchyCollision
import MOC.CauchyDeterminantSquare
import MOC.SecularCauchyHarmonic
import MOC.SecularChamberGeometry

/-! Cauchy coordinates for spectral projections of the secular column model. -/

open BigOperators Finset Matrix Polynomial

namespace MOC

noncomputable section

variable {n : ℕ}

/-- The polynomial which is one at one fixed label and zero at the others. -/
def secularLagrangePolynomial (h : Fin n → ℝ) (j : Fin n) : ℝ[X] :=
  C ((∏ k ∈ univ.erase j, (h j-h k))⁻¹) * ∏ k ∈ univ.erase j, (X-C (h k))

/-- The polynomial spectral projector on the selected labels. -/
def secularSelectionPolynomial (h : Fin n → ℝ) (J : Finset (Fin n)) : ℝ[X] :=
  ∑ j ∈ J, secularLagrangePolynomial h j

/-- The principal submatrix determinant of a polynomial spectral projector. -/
def secularProjectionMinor (d r h : Fin n → ℝ) (I J : Finset (Fin n)) : ℝ :=
  if I.card = J.card then
    ((Polynomial.aeval (secularColumnModel d r) (secularSelectionPolynomial h J)).submatrix
      (fun i : I => (i : Fin n)) (fun i : I => (i : Fin n))).det
  else 0

private theorem secularLagrangePolynomial_eval (h : Fin n → ℝ) (hh : Function.Injective h)
    (i j : Fin n) : (secularLagrangePolynomial h j).eval (h i) = (if i = j then 1 else 0) := by
  simp only [secularLagrangePolynomial, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X]
  by_cases hij : i = j
  · subst j
    rw [if_pos rfl, inv_mul_cancel₀]
    exact Finset.prod_ne_zero_iff.mpr fun k hk => sub_ne_zero.mpr (hh.ne (ne_of_mem_erase hk).symm)
  · have hz : (∏ k ∈ (univ : Finset (Fin n)).erase j, (h i-h k)) = 0 :=
      Finset.prod_eq_zero (f := fun k => h i-h k) (mem_erase.mpr ⟨hij, mem_univ i⟩) (sub_self _)
    rw [if_neg hij, hz, mul_zero]

/-- Evaluating at a spectral label gives its subset indicator. -/
theorem secularSelectionPolynomial_eval (h : Fin n → ℝ) (hh : Function.Injective h)
    (J : Finset (Fin n)) (i : Fin n) :
    (secularSelectionPolynomial h J).eval (h i) = (if i ∈ J then 1 else 0) := by
  simp only [secularSelectionPolynomial, Polynomial.eval_finset_sum,
    secularLagrangePolynomial_eval h hh]
  simp [eq_comm]

theorem cauchyMatrix_isUnit_det (d h : Fin n → ℝ)
    (hd : Function.Injective d) (hh : Function.Injective h)
    (hsep : ∀ i j, h j ≠ d i) : IsUnit (cauchyMatrix d h).det := by
  have hnodes (f : Fin n → ℝ) (hf : Function.Injective f) : directedNodeDifferences f ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    apply Finset.prod_ne_zero_iff.mpr
    intro j _
    by_cases hij : i = j
    · simp [hij]
    · simp only [if_neg hij]
      exact sub_ne_zero.mpr (hf.ne hij)
  have hden : cauchyDenominator d h ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ =>
    Finset.prod_ne_zero_iff.mpr fun j _ => sub_ne_zero.mpr (hsep i j)
  apply isUnit_iff_ne_zero.mpr
  intro hz
  have he := cauchyMatrix_det_sq d h hsep
  rw [hz, zero_pow (by decide : (2 : ℕ) ≠ 0)] at he
  exact (div_ne_zero (mul_ne_zero (hnodes d hd) (hnodes h hh)) (pow_ne_zero _ hden)) he.symm

private theorem sum_secularResidues_div_at_label (d h : Fin n → ℝ)
    (hd : Function.Injective d) (hsep : ∀ i j, h j ≠ d i) (j : Fin n) :
    (∑ i, secularResidue h d i / (h j-d i)) = 1 := by
  have hzero : (∏ i, (h j-h i)) = 0 := Finset.prod_eq_zero (mem_univ j) (sub_self _)
  have he := secular_ratio_eq_partialFractions d h hd (h j) (fun i => hsep i j)
  rw [hzero, zero_div, secularPartialFractions] at he
  simp_rw [neg_div, Finset.sum_neg_distrib] at he
  linarith only [he]

private theorem sum_dualResidues_div_at_node (d h : Fin n → ℝ)
    (hh : Function.Injective h) (hsep : ∀ i j, h j ≠ d i) (i : Fin n) :
    (∑ j, (-secularResidue d h j) / (h j-d i)) = 1 := by
  have he := sum_secularResidues_div_at_label h d hh (fun j i => (hsep i j).symm) i
  rw [← he]
  apply Finset.sum_congr rfl
  intro j _
  rw [← neg_sub (d i) (h j), neg_div_neg_eq]

/-- The Cauchy columns are right eigenvectors of the secular column model. -/
theorem secularColumnModel_mul_cauchy (d h : Fin n → ℝ) (hd : Function.Injective d)
    (hsep : ∀ i j, h j ≠ d i) :
    secularColumnModel d (secularResidue h d) * cauchyMatrix d h =
      cauchyMatrix d h * diagonal h := by
  rw [secularColumnModel, Matrix.add_mul]
  ext i j : 1
  have hsum : ((Matrix.of fun (_ : Fin n) k => secularResidue h d k) * cauchyMatrix d h) i j = 1 := by
    rw [Matrix.mul_apply]
    simpa only [Matrix.of_apply, cauchyMatrix, ← div_eq_mul_inv] using
      sum_secularResidues_div_at_label d h hd hsep j
  rw [Matrix.add_apply, Matrix.diagonal_mul, Matrix.mul_diagonal, hsum]
  change d i * (h j-d i)⁻¹ + 1 = (h j-d i)⁻¹ * h j
  field_simp [sub_ne_zero.mpr (hsep i j)] <;> ring

/-- The inverse Cauchy matrix is its transpose with a secular residue on
one side and a dual residue on the other side. -/
theorem inverse_secularCauchyMatrix (d h : Fin n → ℝ) (hd : Function.Injective d)
    (hh : Function.Injective h) (hsep : ∀ i j, h j ≠ d i) :
    (cauchyMatrix d h)⁻¹ = diagonal (fun j => -secularResidue d h j) *
      (cauchyMatrix d h)ᵀ * diagonal (secularResidue h d) := by
  let X := cauchyMatrix d h
  let r := secularResidue h d
  let c (j : Fin n) := -secularResidue d h j
  let O : Matrix (Fin n) Unit ℝ := Matrix.replicateCol Unit (fun _ => 1)
  let V : Matrix (Fin n) Unit ℝ := Matrix.replicateCol Unit c
  let R : Matrix Unit (Fin n) ℝ := Matrix.replicateRow Unit r
  have hx := cauchyMatrix_isUnit_det d h hd hh hsep
  have hXV : X * V = O := by
    ext i e : 1
    simp only [X, V, O, Matrix.mul_apply, Matrix.replicateCol_apply, cauchyMatrix,
      Matrix.of_apply, c]
    rw [← sum_dualResidues_div_at_node d h hh hsep i]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hVO : X⁻¹ * O = V := by rw [← hXV, Matrix.nonsing_inv_mul_cancel_left X V hx]
  have hKx := secularColumnModel_mul_cauchy d h hd hsep
  have hK : secularColumnModel d r = diagonal d + O * R := by
    ext i j : 1
    simp [secularColumnModel, Matrix.mul_apply, Matrix.replicateCol_apply,
      Matrix.replicateRow_apply, O, R]
  have hleft : X⁻¹ * (diagonal d + O * R) = diagonal h * X⁻¹ := by
    calc
      _ = (X⁻¹ * (secularColumnModel d r * X)) * X⁻¹ := by
        rw [hK, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_right X _ hx]
      _ = (X⁻¹ * (X * diagonal h)) * X⁻¹ := by rw [hKx]
      _ = _ := by rw [Matrix.nonsing_inv_mul_cancel_left X _ hx]
  rw [Matrix.mul_add, ← Matrix.mul_assoc, hVO] at hleft
  ext j i : 1
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.transpose_apply]
  change X⁻¹ j i = (c j * (h j-d i)⁻¹) * r i
  have hVR : (V*R) j i = c j * r i := by
    rw [Matrix.mul_apply]
    simp only [V, R, Matrix.replicateCol_apply, Matrix.replicateRow_apply, Fintype.sum_unique]
  have he := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M j i) hleft
  simp only [Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, hVR] at he
  rw [show (c j * (h j-d i)⁻¹) * r i = (c j * r i)/(h j-d i) by ring]
  apply (eq_div_iff (sub_ne_zero.mpr (hsep i j))).mpr
  linear_combination -he

/-- Polynomial evaluation in the Cauchy basis of the column model. -/
theorem secularEvaluation_columnModel_eq_cauchy (d h : Fin n → ℝ) (hd : Function.Injective d)
    (hh : Function.Injective h) (hsep : ∀ i j, h j ≠ d i) (p : ℝ[X]) :
    Polynomial.aeval (secularColumnModel d (secularResidue h d)) p =
      cauchyMatrix d h * diagonal (fun j => p.eval (h j)) * (cauchyMatrix d h)⁻¹ := by
  let K := secularColumnModel d (secularResidue h d)
  let X := cauchyMatrix d h
  have hKX : K*X = X*diagonal h := secularColumnModel_mul_cauchy d h hd hsep
  have hpowers (m : ℕ) : K^m*X = X * diagonal (fun j => (h j)^m) := by
    induction m with
    | zero => simp [Matrix.diagonal_one]
    | succ m ih =>
        rw [pow_succ, Matrix.mul_assoc, hKX, ← Matrix.mul_assoc, ih, Matrix.mul_assoc,
          Matrix.diagonal_mul_diagonal]
        congr 1
  have he : Polynomial.aeval K p * X = X * diagonal (fun j => p.eval (h j)) := by
    rw [Polynomial.aeval_eq_sum_range, Matrix.sum_mul]
    ext i j : 1
    simp only [Matrix.sum_apply, Matrix.smul_mul, hpowers, Matrix.smul_apply, smul_eq_mul,
      Matrix.mul_diagonal, Polynomial.eval_eq_sum_range, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m _
    ring
  rw [← he, Matrix.mul_nonsing_inv_cancel_right X _ (cauchyMatrix_isUnit_det d h hd hh hsep)]

/-- Evaluation of the fixed subset polynomial in the Cauchy basis. -/
theorem secularProjector_columnModel_eq_cauchy (d h : Fin n → ℝ) (hd : Function.Injective d)
    (hh : Function.Injective h) (hsep : ∀ i j, h j ≠ d i) (J : Finset (Fin n)) :
    Polynomial.aeval (secularColumnModel d (secularResidue h d)) (secularSelectionPolynomial h J) =
      cauchyMatrix d h * diagonal (fun j => if j ∈ J then (1 : ℝ) else 0) * (cauchyMatrix d h)⁻¹ := by
  rw [secularEvaluation_columnModel_eq_cauchy d h hd hh hsep]
  simp only [secularSelectionPolynomial_eval h hh J]


end

end MOC
