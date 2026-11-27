import MOC.RankTwoKernelInclusion

/-! The product rule in the rank-one secular chamber for a quadratic
function of the isospectral matrix. -/

open BigOperators Matrix

namespace MOC

noncomputable section

section Field

variable {K : Type*} [Field K]

private theorem reciprocal_sub_reciprocal (x t u : K) (ht : x ≠ t) (hu : x ≠ u) :
    (x - t)⁻¹ - (x - u)⁻¹ = (t - u) * ((x - t)⁻¹ * (x - u)⁻¹) := by
  field_simp [sub_ne_zero.mpr ht, sub_ne_zero.mpr hu]

private theorem reciprocal_divided_difference (d e t : K)
    (hde : d ≠ e) (hdt : d ≠ t) (het : e ≠ t) :
    (d - t)⁻¹ / (d - e) = (e - t)⁻¹ * ((d - e)⁻¹ - (d - t)⁻¹) := by
  field_simp [sub_ne_zero.mpr hde, sub_ne_zero.mpr hdt, sub_ne_zero.mpr het]
  ring

variable {α β : Type*} [Fintype α] [Fintype β]

/-- The product rule terms for the normalized secular quadratic cancel.
The types `α` and `β` index the retained and deleted coordinates. -/
theorem secular_quadratic_product_rule_cancel
    (d r : α → K) (e s : β → K) (t u : K)
    (hde : ∀ i j, d i ≠ e j)
    (hdt : ∀ i, d i ≠ t) (hdu : ∀ i, d i ≠ u)
    (het : ∀ j, e j ≠ t) (heu : ∀ j, e j ≠ u) :
    let x (v : K) (i : α) := (d i - v)⁻¹
    let A (i : α) := ∑ j, s j / (d i - e j)
    let L (v : K) := 1 + ∑ i, r i * x v i
    let Y (v : K) (j : β) := ∑ i, r i * x v i / (d i - e j)
    let C (j : β) := 1 + ∑ i, r i / (d i - e j)
    (∑ i, r i * ((t - u) * (A i)^2 * (x t i * x u i) -
      A i * (x u i * L t - x t i * L u + A i * (x t i - x u i)))) +
      (∑ j, s j * ((t - u) * (Y t j * Y u j) - C j * (Y t j - Y u j))) = 0 := by
  intro x A L Y C
  let z (v : K) (j : β) := (e j - v)⁻¹
  have hY (v : K) (hdv : ∀ i, d i ≠ v) (hev : ∀ j, e j ≠ v) (j : β) :
      Y v j = z v j * (C j - L v) := by
    change (∑ i, r i * (d i - v)⁻¹ / (d i - e j)) =
      (e j - v)⁻¹ * ((1 + ∑ i, r i / (d i - e j)) - (1 + ∑ i, r i * (d i - v)⁻¹))
    rw [add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [mul_div_assoc, reciprocal_divided_difference _ _ _ (hde i j) (hdv i) (hev j),
      div_eq_mul_inv, ← mul_sub]
    ring
  have hFubini (v : K) : (∑ i, r i * A i * x v i) = ∑ j, s j * Y v j := by
    change (∑ i, r i * (∑ j, s j / (d i - e j)) * x v i) =
      ∑ j, s j * (∑ i, r i * x v i / (d i - e j))
    simp only [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hS (i : α) :
      (t - u) * (A i)^2 * (x t i * x u i) -
        A i * (x u i * L t - x t i * L u + A i * (x t i - x u i)) =
      A i * x t i * L u - A i * x u i * L t := by
    rw [show x t i - x u i = (t - u) * (x t i * x u i) from
      reciprocal_sub_reciprocal (d i) t u (hdt i) (hdu i)]
    ring
  have hT (j : β) :
      (t - u) * (Y t j * Y u j) - C j * (Y t j - Y u j) =
      Y u j * L t - Y t j * L u := by
    rw [hY t hdt het j, hY u hdu heu j]
    have h := reciprocal_sub_reciprocal (e j) t u (het j) (heu j)
    change z t j - z u j = (t - u) * (z t j * z u j) at h
    linear_combination -(C j - L t) * (C j - L u) * h
  simp_rw [hS, hT, mul_sub, ← mul_assoc]
  simp only [Finset.sum_sub_distrib, ← Finset.sum_mul, hFubini]
  ring

end Field

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Taking a quadratic polynomial of a diagonal matrix plus one row and
column product gives a perturbation of rank at most two. -/
theorem rank_quadratic_image_sub_diagonal_le_two (d u v : ι → ℂ) (c : ℂ) :
    let D := diagonal d
    let H := D + Matrix.vecMulVec u v
    (H * H + c • H - (D * D + c • D)).rank ≤ 2 := by
  intro D H
  let q := ∑ i, v i * u i
  have h (i j : ι) :
      (H * H + c • H - (D * D + c • D)) i j =
        (d i * u i) * v j + u i * ((d j + q + c) * v j) := by
    have hK : (vecMulVec u v : Matrix ι ι ℂ) * vecMulVec u v =
        q • vecMulVec u v := by
      ext k l : 1
      simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.smul_apply, smul_eq_mul, q,
        Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m _
      ring
    change (((D + vecMulVec u v) * (D + vecMulVec u v) + c • (D + vecMulVec u v)) -
      (D * D + c • D)) i j = _
    rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, hK, smul_add]
    simp only [Matrix.sub_apply, Matrix.add_apply, D, Matrix.diagonal_mul, Matrix.mul_diagonal,
      Matrix.vecMulVec_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  have hM : H * H + c • H - (D * D + c • D) =
      Matrix.of fun i j => (d i * u i) * v j + u i * ((d j + q + c) * v j) := by
    ext i j : 1
    exact h i j
  rw [hM]
  exact rank_two_product_kernel_le _ _ _ _

end

end MOC
