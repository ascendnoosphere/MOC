import MOC.TwoValues
import Mathlib.LinearAlgebra.Matrix.Block

/-! The subset coefficient expansion for a real similarity, without a unitary premise. -/

open BigOperators Finset Matrix

namespace MOC

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A matching product over the real number field. -/
def realMatchingProduct (a b : ι → ℝ) (σ : Equiv.Perm ι) : ℝ :=
  ∏ j, (a (σ j) + b j)

private theorem realMatchingProduct_expand (a b : ι → ℝ) (σ : Equiv.Perm ι) :
    realMatchingProduct a b σ =
      ∑ J : Finset ι, (∏ i ∈ (J.map σ.toEmbedding)ᶜ, a i) * ∏ j ∈ J, b j := by
  apply Complex.ofReal_injective
  simpa only [realMatchingProduct, matchingProduct, Complex.ofReal_prod, Complex.ofReal_sum,
    Complex.ofReal_add, Complex.ofReal_mul] using
    matchingProduct_expand_subsets (fun i => (a i : ℂ)) (fun i => (b i : ℂ)) σ

private theorem realMatchingProduct_marker (I J : Finset ι) (h : I.card = J.card)
    (σ : Equiv.Perm ι) :
    realMatchingProduct (fun i => if i ∈ I then 0 else 1)
      (fun j => if j ∈ J then 1 else 0) σ = if J.map σ.toEmbedding = I then 1 else 0 := by
  apply Complex.ofReal_injective
  simpa only [realMatchingProduct, matchingProduct, Complex.ofReal_prod, Complex.ofReal_add,
    apply_ite, Complex.ofReal_zero, Complex.ofReal_one] using
    matchingProduct_subset_marker I J h σ

private def realBasisSignedWeight (X : Matrix ι ι ℝ) (σ : Equiv.Perm ι) : ℝ :=
  (((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ j, X (σ j) j) / X.det

private theorem determinant_eq_realBasisSigned (X Y : Matrix ι ι ℝ)
    (hYX : Y*X=1) (hX : X.det ≠ 0) (a b : ι → ℝ) :
    (diagonal a + X*diagonal b*Y).det = ∑ σ, realBasisSignedWeight X σ * realMatchingProduct a b σ := by
  have hm : (diagonal a + X*diagonal b*Y)*X = Matrix.of (fun i j => (a i+b j)*X i j) := by
    rw [Matrix.add_mul, Matrix.mul_assoc (X*diagonal b), hYX, Matrix.mul_one]
    ext i j : 1
    simp only [Matrix.add_apply, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.of_apply]
    ring
  have hv : (diagonal a + X*diagonal b*Y).det =
      (Matrix.of (fun i j => (a i+b j)*X i j)).det / X.det := by
    apply (eq_div_iff hX).mpr
    rw [← Matrix.det_mul, hm]
  rw [hv, Matrix.det_apply', Finset.sum_div]
  apply Finset.sum_congr rfl
  intro σ _
  simp only [realBasisSignedWeight, realMatchingProduct, Matrix.of_apply, Finset.prod_mul_distrib]
  ring

/-- A determinant with complementary marker labels is the determinant of
its selected spectral idempotent on the retained coordinates. -/
theorem marker_det_eq_principal_idempotent (X Y : Matrix ι ι ℝ)
    (I J : Finset ι) (hIJ : I.card = J.card) :
    let P := X * diagonal (fun j => if j ∈ J then (1 : ℝ) else 0) * Y
    (diagonal (fun i => if i ∈ I then (0 : ℝ) else 1) + P).det =
      (P.submatrix (fun i : I => (i : ι)) (fun i : I => (i : ι))).det := by
  classical
  intro P
  let e : I ≃ J := Fintype.equivOfCardEq (by simpa using hIJ)
  let X₁ : Matrix ι ι ℝ := Matrix.of fun i j =>
    if hj : j ∈ I then X i (e ⟨j, hj⟩) else (1 : Matrix ι ι ℝ) i j
  let Y₁ : Matrix ι ι ℝ := Matrix.of fun i j =>
    if hi : i ∈ I then Y (e ⟨i, hi⟩) j else (1 : Matrix ι ι ℝ) i j
  let A := X.submatrix (fun i : I => (i : ι)) (fun j : I => ((e j : J) : ι))
  let B := Y.submatrix (fun i : I => ((e i : J) : ι)) (fun j : I => (j : ι))
  have hsel (i j : ι) : P i j = ∑ k ∈ J, X i k * Y k j := by
    change ((X * diagonal (fun k => if k ∈ J then (1 : ℝ) else 0)) * Y) i j = _
    rw [Matrix.mul_apply]
    simp only [Matrix.mul_diagonal, mul_ite, ite_mul, mul_one, mul_zero, zero_mul,
      ← Finset.sum_filter, Finset.filter_univ_mem]
  have hsel' (i j : ι) : P i j = ∑ k : I, X i (e k) * Y (e k) j := by
    rw [hsel, ← Finset.sum_coe_sort]
    exact (Equiv.sum_comp e (fun k : J => X i k * Y k j)).symm
  have hP : P.submatrix (fun i : I => (i : ι)) (fun i : I => (i : ι)) = A*B := by
    ext i j : 1
    simpa only [A, B, Matrix.mul_apply, Matrix.submatrix_apply] using hsel' i j
  have hdiag (i j : ι) :
      (∑ k ∈ Iᶜ, (1 : Matrix ι ι ℝ) i k * (1 : Matrix ι ι ℝ) k j) =
        diagonal (fun i => if i ∈ I then (0 : ℝ) else 1) i j := by
    let D := diagonal (fun k => if k ∈ I then (0 : ℝ) else 1)
    have hD (k : ι) : D i k = if k ∈ Iᶜ then (1 : Matrix ι ι ℝ) i k else 0 := by
      by_cases hik : i = k
      · subst k
        by_cases hi : i ∈ I <;> simp [D, hi]
      · simp [D, Matrix.diagonal_apply_ne _ hik, Matrix.one_apply_ne hik]
    change _ = D i j
    rw [← Matrix.mul_one D, Matrix.mul_apply]
    simp only [hD, ite_mul, zero_mul, ← Finset.sum_filter, Finset.filter_univ_mem]
  have hprod : X₁*Y₁ = diagonal (fun i => if i ∈ I then (0 : ℝ) else 1) + P := by
    ext i j : 1
    rw [Matrix.mul_apply, ← Finset.sum_add_sum_compl I, Matrix.add_apply]
    have hI : (∑ k ∈ I, X₁ i k * Y₁ k j) = P i j := by
      rw [hsel', ← Finset.sum_coe_sort]
      apply Finset.sum_congr rfl
      intro k _
      simp [X₁, Y₁, k.property]
    have hK : (∑ k ∈ Iᶜ, X₁ i k * Y₁ k j) =
        ∑ k ∈ Iᶜ, (1 : Matrix ι ι ℝ) i k * (1 : Matrix ι ι ℝ) k j := by
      exact Finset.sum_congr rfl fun k hk => by simp [X₁, Y₁, mem_compl.mp hk]
    rw [hI, hK, hdiag, add_comm]
  let K := {i : ι // i ∉ I}
  let f : I ⊕ K ≃ ι := Equiv.sumCompl (fun i => i ∈ I)
  have hX : X₁.det = A.det := by
    let C := X.submatrix (fun i : K => (i : ι)) (fun j : I => ((e j : J) : ι))
    have h : X₁.submatrix f f = Matrix.fromBlocks A 0 C 1 := by
      ext (i | i) (j | j) : 1
      · change X₁ i j = A i j
        simp [X₁, A, j.property]
      · change X₁ i j = 0
        have hij : (i : ι) ≠ (j : ι) := fun he => j.property (he ▸ i.property)
        simp [X₁, j.property, Matrix.one_apply_ne hij]
      · change X₁ i j = C i j
        simp [X₁, C, j.property]
      · change X₁ i j = (1 : Matrix K K ℝ) i j
        have hv : ((i : ι) = (j : ι)) ↔ i = j := ⟨Subtype.ext, congrArg Subtype.val⟩
        simp only [X₁, Matrix.of_apply, dif_neg j.property, Matrix.one_apply, hv]
    rw [← Matrix.det_submatrix_equiv_self f X₁, h, Matrix.det_fromBlocks_zero₁₂,
      Matrix.det_one, mul_one]
  have hY : Y₁.det = B.det := by
    let C := Y.submatrix (fun i : I => ((e i : J) : ι)) (fun j : K => (j : ι))
    have h : Y₁.submatrix f f = Matrix.fromBlocks B C 0 1 := by
      ext (i | i) (j | j) : 1
      · change Y₁ i j = B i j
        simp [Y₁, B, i.property]
      · change Y₁ i j = C i j
        simp [Y₁, C, i.property]
      · change Y₁ i j = 0
        have hij : (i : ι) ≠ (j : ι) := fun he => i.property (he.symm ▸ j.property)
        simp [Y₁, i.property, Matrix.one_apply_ne hij]
      · change Y₁ i j = (1 : Matrix K K ℝ) i j
        have hv : ((i : ι) = (j : ι)) ↔ i = j := ⟨Subtype.ext, congrArg Subtype.val⟩
        simp only [Y₁, Matrix.of_apply, dif_neg i.property, Matrix.one_apply, hv]
    rw [← Matrix.det_submatrix_equiv_self f Y₁, h, Matrix.det_fromBlocks_zero₂₁,
      Matrix.det_one, mul_one]
  rw [← hprod, hP, Matrix.det_mul, Matrix.det_mul, hX, hY]

/-- The coefficients of the determinant are the principal minors of the
label projections in an arbitrary invertible real eigenbasis. -/
theorem det_inverse_basis_eq_sum_principal (X Y : Matrix ι ι ℝ)
    (hYX : Y*X=1) (hX : X.det ≠ 0) (a b : ι → ℝ) :
    (diagonal a + X*diagonal b*Y).det = ∑ J : Finset ι, ∑ I : Finset ι,
      (if I.card = J.card then
        ((X * diagonal (fun j => if j ∈ J then (1 : ℝ) else 0) * Y).submatrix
          (fun i : I => (i : ι)) (fun i : I => (i : ι))).det else 0) *
        ((∏ i ∈ Iᶜ, a i) * ∏ j ∈ J, b j) := by
  rw [determinant_eq_realBasisSigned X Y hYX hX a b]
  simp_rw [realMatchingProduct_expand, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro J _
  rw [← Finset.sum_fiberwise univ (fun σ : Equiv.Perm ι => J.map σ.toEmbedding)]
  apply Finset.sum_congr rfl
  intro I _
  have hsum : (∑ σ ∈ univ.filter (fun σ : Equiv.Perm ι => J.map σ.toEmbedding = I),
      realBasisSignedWeight X σ * ((∏ i ∈ (J.map σ.toEmbedding)ᶜ, a i) * ∏ j ∈ J, b j)) =
      (∑ σ ∈ univ.filter (fun σ : Equiv.Perm ι => J.map σ.toEmbedding = I),
        realBasisSignedWeight X σ) * ((∏ i ∈ Iᶜ, a i)*∏ j ∈ J, b j) := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun σ hσ => by rw [(Finset.mem_filter.mp hσ).2]
  rw [hsum]
  congr 1
  by_cases hIJ : I.card = J.card
  · rw [if_pos hIJ, ← marker_det_eq_principal_idempotent X Y I J hIJ,
      determinant_eq_realBasisSigned X Y hYX hX, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro σ _
    rw [realMatchingProduct_marker I J hIJ]
    by_cases hσ : J.map σ.toEmbedding = I <;> simp [hσ]
  · rw [if_neg hIJ]
    apply Finset.sum_eq_zero
    intro σ hσ
    exact False.elim (hIJ (by rw [← (Finset.mem_filter.mp hσ).2, Finset.card_map]))


end

end MOC
