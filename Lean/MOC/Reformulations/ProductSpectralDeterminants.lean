import MOC.BilinearPencil
import MOC.Normal
import MOC.StrongSupport

/-! A pointwise characteristic determinant of the product of two normal
matrices, with comparison products formed from paired eigenvalues. -/

open BigOperators Matrix

namespace MOC.Reformulations

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The product determinant comparison in spectral coordinates. -/
def ProductDeterminantForm (ι : Type*) [Fintype ι] [DecidableEq ι] : Prop :=
  ∀ (x y : ι → ℂ) (U : Matrix ι ι ℂ), IsUnitary U →
    (1 + diagonal x * (U * diagonal y * Uᴴ)).det ∈
      convexHull ℝ (Set.range (fun p : Equiv.Perm ι => ∏ j, (1 + x (p j) * y j)))

/-- Inclusion for the product determinant at `1` is already equivalent to
inclusion for sums of normal matrices in the same order. -/
theorem conjecture_iff_product_determinant : Conjecture ι ↔ ProductDeterminantForm ι := by
  constructor
  · intro h x y U hU
    have hp := (conjecture_iff_bilinear_pencil.mp h) x y U hU 1 0 0 1
    simpa only [bilinearPencil, bilinearMatchingProduct, bilinearKernel, one_smul, zero_smul,
      one_mul, zero_mul, add_zero, add_comm (1 : ℂ), add_comm (1 : Matrix ι ι ℂ)] using hp
  · intro h a b U hU
    obtain ⟨t, _, ht⟩ := Set.infinite_univ.exists_not_mem_finite (Set.finite_range (fun i => -a i))
    let a' : ι → ℂ := fun i => a i + t
    let b' : ι → ℂ := fun i => b i - t
    let x : ι → ℂ := fun i => (a' i)⁻¹
    have ha (i : ι) : a' i ≠ 0 := by
      intro he
      exact ht ⟨i, by dsimp only [a'] at he; linear_combination -he⟩
    have hAX : diagonal a' * diagonal x = 1 := by
      rw [Matrix.diagonal_mul_diagonal]
      have hprod : a' * x = (fun _ => 1) := funext fun i => mul_inv_cancel₀ (ha i)
      rw [hprod, Matrix.diagonal_one]
    have hD : determinantValue a' b' U = (∏ i, a' i) *
        (1 + diagonal x * (U * diagonal b' * Uᴴ)).det := by
      rw [← Matrix.det_diagonal, ← Matrix.det_mul]
      unfold determinantValue
      congr 1
      rw [Matrix.mul_add, Matrix.mul_one, ← Matrix.mul_assoc (diagonal a') (diagonal x),
        hAX, Matrix.one_mul]
    have hp (p : Equiv.Perm ι) : matchingProduct a' b' p = (∏ i, a' i) *
        ∏ j, (1 + x (p j) * b' j) := by
      rw [← Equiv.prod_comp p a', ← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro j _
      change a' (p j) + b' j = a' (p j) * (1 + (a' (p j))⁻¹ * b' j)
      rw [mul_add, mul_one, ← mul_assoc, mul_inv_cancel₀ (ha (p j)), one_mul]
    exact (holds_shift_iff a b hU t).mp (hull_of_common_factor hD hp (h x b' U hU))

/-- The product characteristic comparison is pointwise in the spectral
parameter. No common weights for different parameter values are required. -/
def ProductCharacteristicForm (ι : Type*) [Fintype ι] [DecidableEq ι] : Prop :=
  ∀ (x y : ι → ℂ) (U : Matrix ι ι ℂ) (z : ℂ), IsUnitary U →
    (z • (1 : Matrix ι ι ℂ) - diagonal x * (U * diagonal y * Uᴴ)).det ∈
      convexHull ℝ (Set.range (fun p : Equiv.Perm ι => ∏ j, (z - x (p j) * y j)))

theorem conjecture_iff_product_characteristic : Conjecture ι ↔ ProductCharacteristicForm ι := by
  constructor
  · intro h x y U z hU
    have hp := (conjecture_iff_bilinear_pencil.mp h) x y U hU (-1) 0 0 z
    simpa only [bilinearPencil, bilinearMatchingProduct, bilinearKernel, neg_one_smul, zero_smul,
      neg_mul, one_mul, zero_mul, add_zero, sub_eq_add_neg, add_comm] using hp
  · intro h
    apply conjecture_iff_product_determinant.mpr
    intro x y U hU
    have hp := h x (fun i => -y i) U 1 hU
    have he : diagonal (fun i => -y i) = -diagonal y := (Matrix.diagonal_neg y).symm
    simpa only [he, one_smul, Matrix.mul_neg, Matrix.neg_mul, sub_neg_eq_add, mul_neg] using hp

private theorem exists_unitary_diagonalization_for_list (A : Matrix ι ι ℂ) (a : ι → ℂ)
    (hA : IsStarNormal A) (ha : A.charpoly.roots = (Finset.univ : Finset ι).val.map a) :
    ∃ U : Matrix ι ι ℂ, IsUnitary U ∧ A = U * diagonal a * Uᴴ := by
  obtain ⟨a', V, hV, he⟩ := exists_unitary_diagonalization A hA
  rw [he, roots_unitary_diagonalization a' hV] at ha
  obtain ⟨p, hp⟩ := exists_perm_of_equal_multisets a' a ha
  let P := p.permMatrix ℂ
  have hP := isUnitary_permMatrix p
  have hV' : IsUnitary Vᴴ := by
    simpa only [IsUnitary, Matrix.conjTranspose_conjTranspose] using And.intro hV.2 hV.1
  refine ⟨V * P, by simpa only [Matrix.conjTranspose_conjTranspose] using
    relative_unitary Vᴴ P hV' hP, ?_⟩
  have hd : P * diagonal a * Pᴴ = diagonal a' := by
    rw [P, permMatrix_conjugates, Matrix.submatrix_diagonal_equiv, hp]
  rw [he, ← hd, Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]

/-- Pointwise product characteristic determinants for normal matrices and
any enumerations of their eigenvalues give an equivalent comparison. -/
theorem conjecture_iff_normal_product_characteristic : Conjecture ι ↔
    ∀ (X Y : Matrix ι ι ℂ) (x y : ι → ℂ) (z : ℂ),
      IsStarNormal X → IsStarNormal Y →
      X.charpoly.roots = (Finset.univ : Finset ι).val.map x →
      Y.charpoly.roots = (Finset.univ : Finset ι).val.map y →
      (z • (1 : Matrix ι ι ℂ) - X * Y).det ∈
        convexHull ℝ (Set.range (fun p : Equiv.Perm ι => ∏ j, (z - x (p j) * y j))) := by
  rw [conjecture_iff_product_characteristic]
  constructor
  · intro h X Y x y z hX hY hx hy
    obtain ⟨V, hV, rfl⟩ := exists_unitary_diagonalization_for_list X x hX hx
    obtain ⟨W, hW, rfl⟩ := exists_unitary_diagonalization_for_list Y y hY hy
    let U := Vᴴ * W
    have hU : IsUnitary U := relative_unitary V W hV hW
    have he : V * (z • (1 : Matrix ι ι ℂ) - diagonal x * (U * diagonal y * Uᴴ)) * Vᴴ =
        z • (1 : Matrix ι ι ℂ) - (V * diagonal x * Vᴴ) * (W * diagonal y * Wᴴ) := by
      simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
        Matrix.mul_one, hV.1, U, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
      rw [show (V * (diagonal x * (Vᴴ * W * diagonal y * (Wᴴ * V)))) * Vᴴ =
          ((V * diagonal x * Vᴴ) * (W * diagonal y * Wᴴ)) * (V * Vᴴ) by
        simp only [Matrix.mul_assoc], hV.1, Matrix.mul_one]
    rw [← he, det_unitary_conjugation V _ hV]
    exact h x y U z hU
  · intro h x y U z hU
    have hx : IsStarNormal (diagonal x) := by
      simpa only [Matrix.one_mul, Matrix.conjTranspose_one, Matrix.mul_one] using
        (isStarNormal_unitary_diagonalization x (U := (1 : Matrix ι ι ℂ)) isUnitary_one)
    have hroots : (diagonal x).charpoly.roots = (Finset.univ : Finset ι).val.map x := by
      simpa only [Matrix.one_mul, Matrix.conjTranspose_one, Matrix.mul_one] using
        (roots_unitary_diagonalization x (U := (1 : Matrix ι ι ℂ)) isUnitary_one)
    exact h _ _ x y z hx (isStarNormal_unitary_diagonalization y hU) hroots
      (roots_unitary_diagonalization y hU)

end
end MOC.Reformulations
