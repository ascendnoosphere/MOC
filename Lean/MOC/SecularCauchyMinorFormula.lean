import MOC.SecularCauchyEigenbasis

/-! The two cut products that determine each Cauchy spectral minor. -/

open BigOperators Finset Matrix

namespace MOC

noncomputable section

variable {n : ℕ}

/-- Product of directed differences between two sets of nodes. -/
def secularCutProduct (d h : Fin n → ℝ) (I J : Finset (Fin n)) : ℝ :=
  ∏ i ∈ I, ∏ j ∈ J, (d i-h j)

/-- Product of internal directed differences between distinct nodes. -/
def secularInternalProduct (d : Fin n → ℝ) (I : Finset (Fin n)) : ℝ :=
  ∏ i ∈ I, ∏ k ∈ I.erase i, (d i-d k)

/-- The two-by-two partition expression for a minor. -/
def secularCauchyCutRatio (d h : Fin n → ℝ) (I J : Finset (Fin n)) : ℝ :=
  secularCutProduct d h I Jᶜ * secularCutProduct h d J Iᶜ /
    (secularCutProduct d d I Iᶜ * secularCutProduct h h J Jᶜ)

private theorem secularCutProduct_split (d h : Fin n → ℝ) (I J : Finset (Fin n)) :
    secularCutProduct d h I univ =
      secularCutProduct d h I J * secularCutProduct d h I Jᶜ := by
  unfold secularCutProduct
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  exact (Finset.prod_mul_prod_compl J (fun j => d i - h j)).symm

theorem secularCutProduct_reverse (d h : Fin n → ℝ) (I J : Finset (Fin n)) :
    secularCutProduct d h I J = (-1 : ℝ)^(J.card*I.card) * secularCutProduct h d J I := by
  unfold secularCutProduct
  have hprod (i : Fin n) : (∏ j ∈ J, (d i-h j)) = (-1 : ℝ)^J.card * ∏ j ∈ J, (h j-d i) := by
    rw [← Finset.prod_const, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun j _ => by ring
  simp_rw [hprod, Finset.prod_mul_distrib, Finset.prod_const, ← pow_mul]
  rw [Finset.prod_comm]

theorem secularResidue_denominator_split (d : Fin n → ℝ) (I : Finset (Fin n))
    (i : Fin n) (hi : i ∈ I) :
    (∏ k ∈ univ.erase i, (d i-d k)) =
      (∏ k ∈ I.erase i, (d i-d k)) * ∏ k ∈ Iᶜ, (d i-d k) := by
  have hd : Disjoint (I.erase i) Iᶜ := by
    rw [Finset.disjoint_left]
    exact fun k hk hkc => mem_compl.mp hkc (mem_of_mem_erase hk)
  have he : I.erase i ∪ Iᶜ = univ.erase i := by
    ext k
    by_cases hk : k = i
    · subst k; simp [hi]
    · by_cases hki : k ∈ I <;> simp [hk, hki]
  rw [← he, Finset.prod_union hd]

private theorem secularResidue_product (d h : Fin n → ℝ) (I : Finset (Fin n)) :
    (∏ i ∈ I, secularResidue h d i) =
      (-1 : ℝ)^I.card * secularCutProduct d h I univ /
        (secularInternalProduct d I * secularCutProduct d d I Iᶜ) := by
  calc
    _ = ∏ i ∈ I, ((-1 : ℝ) * ∏ j, (d i-h j)) /
        ((∏ k ∈ I.erase i, (d i-d k)) * ∏ k ∈ Iᶜ, (d i-d k)) := by
      apply Finset.prod_congr rfl
      intro i hi
      rw [secularResidue, secularResidue_denominator_split d I i hi, neg_one_mul]
    _ = _ := by
      simp only [secularCutProduct, secularInternalProduct, Finset.prod_div_distrib,
        Finset.prod_mul_distrib, Finset.prod_const]

private theorem dualSecularResidue_product (d h : Fin n → ℝ) (J : Finset (Fin n)) :
    (∏ j ∈ J, -secularResidue d h j) = secularCutProduct h d J univ /
        (secularInternalProduct h J * secularCutProduct h h J Jᶜ) := by
  calc
    _ = ∏ j ∈ J, (∏ i, (h j-d i)) /
        ((∏ k ∈ J.erase j, (h j-h k)) * ∏ k ∈ Jᶜ, (h j-h k)) := by
      apply Finset.prod_congr rfl
      intro j hj
      rw [secularResidue, secularResidue_denominator_split h J j hj, neg_div, neg_neg]
    _ = _ := by
      simp only [secularCutProduct, secularInternalProduct, Finset.prod_div_distrib,
        Finset.prod_mul_distrib]

private theorem secularCauchyMinor_prod (d h : Fin n → ℝ)
    (hd : Function.Injective d) (hh : Function.Injective h)
    (hsep : ∀ i j, h j ≠ d i) (I J : Finset (Fin n)) (hIJ : I.card = J.card) :
    secularProjectionMinor d (secularResidue h d) h I J =
      (∏ i ∈ I, secularResidue h d i) * (∏ j ∈ J, -secularResidue d h j) *
        (secularInternalProduct d I * secularInternalProduct h J /
          secularCutProduct h d J I ^ 2) := by
  classical
  let e : Fin I.card ≃ I := Fintype.equivOfCardEq (by simp)
  let f : Fin I.card ≃ J := Fintype.equivOfCardEq (by simp [hIJ])
  let row (i : Fin I.card) : Fin n := (e i : Fin n)
  let col (j : Fin I.card) : Fin n := (f j : Fin n)
  let X := cauchyMatrix d h
  let C := cauchyMatrix (d ∘ row) (h ∘ col)
  let r (i : Fin n) := secularResidue h d i
  let c (j : Fin n) := -secularResidue d h j
  have hM : ((X * diagonal (fun j => if j ∈ J then (1 : ℝ) else 0) * X⁻¹).submatrix row row) =
      C * (diagonal (c ∘ col) * Cᵀ * diagonal (r ∘ row)) := by
    rw [show X⁻¹ = diagonal c * Xᵀ * diagonal r from inverse_secularCauchyMatrix d h hd hh hsep]
    ext i j : 1
    conv_lhs => rw [Matrix.submatrix_apply, Matrix.mul_apply]
    conv_rhs => rw [Matrix.mul_apply]
    simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.transpose_apply, C, X,
      cauchyMatrix, Matrix.of_apply, Function.comp_apply]
    have hsum : (∑ k : Fin n, (h k-d (row i))⁻¹ * (if k ∈ J then 1 else 0) *
        (c k * (h k-d (row j))⁻¹ * r (row j))) =
        ∑ k ∈ J, (h k-d (row i))⁻¹ * (c k * (h k-d (row j))⁻¹ * r (row j)) := by
      have hJ : univ.filter (fun k : Fin n => k ∈ J) = J := by
        ext k
        simp
      conv_rhs => rw [← hJ, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro k _
      by_cases hkj : k ∈ J <;> simp [hkj]
    rw [hsum, ← Finset.sum_coe_sort]
    exact (Equiv.sum_comp f (fun k : J => (h k-d (row i))⁻¹ *
      (c k * (h k-d (row j))⁻¹ * r (row j)))).symm
  have hdir (w : Fin n → ℝ) (S : Finset (Fin n)) (g : Fin I.card ≃ S) :
      directedNodeDifferences (fun i => w (g i)) = secularInternalProduct w S := by
    have hinner (i : Fin I.card) :
        (∏ j : Fin I.card, if i = j then (1 : ℝ) else w (g i) - w (g j)) =
          ∏ j ∈ S.erase (g i : Fin n), (w (g i)-w j) := by
      calc
        _ = ∏ j : S, if (j : Fin n) ≠ (g i : Fin n) then w (g i)-w j else 1 := by
          rw [← Equiv.prod_comp g (fun j : S =>
            if (j : Fin n) ≠ (g i : Fin n) then w (g i)-w j else 1)]
          apply Finset.prod_congr rfl
          intro j _
          by_cases hij : i = j
          · subst j
            simp
          · have he : (g j : Fin n) ≠ (g i : Fin n) :=
              fun h => hij ((g.injective (Subtype.ext h)).symm)
            simp [hij, he]
        _ = _ := by
          rw [Finset.prod_coe_sort S (fun j => if j ≠ (g i : Fin n) then w (g i)-w j else 1),
            ← Finset.prod_filter, Finset.filter_ne']
    unfold directedNodeDifferences secularInternalProduct
    simp_rw [hinner]
    exact (Equiv.prod_comp g (fun i : S => ∏ j ∈ S.erase (i : Fin n), (w i-w j))).trans
      (Finset.prod_coe_sort S (fun i => ∏ j ∈ S.erase i, (w i-w j)))
  have hden : cauchyDenominator (d ∘ row) (h ∘ col) = secularCutProduct h d J I := by
    unfold cauchyDenominator secularCutProduct
    simp only [Function.comp_apply, row, col]
    rw [Finset.prod_comm]
    have hinner (j : J) : (∏ i : Fin I.card, (h j-d (e i))) = ∏ i ∈ I, (h j-d i) :=
      (Equiv.prod_comp e (fun i : I => h j-d i)).trans (Finset.prod_coe_sort I (fun i => h j-d i))
    calc
      _ = ∏ j : Fin I.card, (∏ i ∈ I, (h (f j)-d i)) := by
        apply Finset.prod_congr rfl
        intro j _
        exact hinner (f j)
      _ = _ := (Equiv.prod_comp f (fun j : J => ∏ i ∈ I, (h j-d i))).trans
        (Finset.prod_coe_sort J (fun j => ∏ i ∈ I, (h j-d i)))
  have hdetC : C.det^2 = secularInternalProduct d I * secularInternalProduct h J /
      secularCutProduct h d J I ^ 2 := by
    change (cauchyMatrix (d ∘ row) (h ∘ col)).det ^ 2 = _
    rw [cauchyMatrix_det_sq (d ∘ row) (h ∘ col) (fun i j => hsep (row i) (col j)), hden]
    exact congrArg (fun p : ℝ => p / secularCutProduct h d J I ^ 2)
      (congrArg₂ (·*·) (hdir d I e) (hdir h J f))
  rw [secularProjectionMinor, if_pos hIJ, secularProjector_columnModel_eq_cauchy d h hd hh hsep J,
    ← Matrix.det_submatrix_equiv_self e]
  change ((X * diagonal (fun j => if j ∈ J then (1 : ℝ) else 0) * X⁻¹).submatrix row row).det = _
  rw [hM, Matrix.det_mul, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
    Matrix.det_diagonal, Matrix.det_diagonal]
  have hr : (∏ i : Fin I.card, r (row i)) = ∏ i ∈ I, r i :=
    (Equiv.prod_comp e (fun i : I => r i)).trans (Finset.prod_coe_sort I r)
  have hc : (∏ j : Fin I.card, c (col j)) = ∏ j ∈ J, c j :=
    (Equiv.prod_comp f (fun j : J => c j)).trans (Finset.prod_coe_sort J c)
  simp only [Function.comp_apply, hr, hc]
  rw [show C.det*((∏ j ∈ J, c j)*C.det*(∏ i ∈ I, r i)) =
    (∏ i ∈ I, r i)*(∏ j ∈ J, c j)*C.det^2 by ring, hdetC]

/-- The formula for a squared Cauchy spectral minor divided by its
Vandermonde factors. -/
theorem secularProjectionMinor_eq_cutRatio (d h : Fin n → ℝ)
    (hd : Function.Injective d) (hh : Function.Injective h)
    (hsep : ∀ i j, h j ≠ d i) (I J : Finset (Fin n)) (hIJ : I.card = J.card) :
    secularProjectionMinor d (secularResidue h d) h I J = secularCauchyCutRatio d h I J := by
  rw [secularCauchyMinor_prod d h hd hh hsep I J hIJ, secularResidue_product,
    dualSecularResidue_product, secularCutProduct_split d h I J,
    secularCutProduct_split h d J I, secularCutProduct_reverse d h I J]
  have hpar : (-1 : ℝ)^I.card * (-1 : ℝ)^(J.card*I.card) = 1 := by
    rw [← pow_add, ← hIJ, add_comm I.card (I.card*I.card), ← Nat.mul_succ]
    exact (Nat.even_mul_succ_self I.card).neg_one_pow
  have hi : secularInternalProduct d I ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    exact Finset.prod_ne_zero_iff.mpr fun k hk => sub_ne_zero.mpr (hd.ne (ne_of_mem_erase hk).symm)
  have hj : secularInternalProduct h J ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro j _
    exact Finset.prod_ne_zero_iff.mpr fun k hk => sub_ne_zero.mpr (hh.ne (ne_of_mem_erase hk).symm)
  have hcross : secularCutProduct h d J I ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun j _ => Finset.prod_ne_zero_iff.mpr fun i _ =>
      sub_ne_zero.mpr (hsep i j)
  have hdcut : secularCutProduct d d I Iᶜ ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i hi => Finset.prod_ne_zero_iff.mpr fun k hk =>
      sub_ne_zero.mpr (hd.ne (fun hik => mem_compl.mp hk (hik ▸ hi)))
  have hhcut : secularCutProduct h h J Jᶜ ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun j hj => Finset.prod_ne_zero_iff.mpr fun k hk =>
      sub_ne_zero.mpr (hh.ne (fun hjk => mem_compl.mp hk (hjk ▸ hj)))
  rw [show (-1 : ℝ)^I.card * (((-1 : ℝ)^(J.card*I.card) * secularCutProduct h d J I) *
      secularCutProduct d h I Jᶜ) = secularCutProduct h d J I * secularCutProduct d h I Jᶜ from by
        rw [← mul_assoc, ← mul_assoc, hpar, one_mul]]
  unfold secularCauchyCutRatio
  field_simp [hi, hj, hcross, hdcut, hhcut]
  ring


end

end MOC
