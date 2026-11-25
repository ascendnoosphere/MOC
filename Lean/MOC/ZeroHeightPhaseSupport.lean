import MOC.BilinearPencil
import MOC.TwoValues

/-! At a zero-height pivot, opposite cycle orientations constrain the phases
of the two crossed entries. A single exceptional phase on each side then
has a termwise signed certificate in the squared-minor expansion. -/

open BigOperators Finset

namespace MOC

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The two oriented three-cycles through a pivot have imaginary parts
proportional to `c * z.im` and `d * z⁻¹.im`. If the diagonal coefficients
have the same sign and both cycles satisfy the support inequality, the
relative phase `z` is real. -/
theorem phase_ratio_im_eq_zero_of_same_sign
    (t c d : ℝ) (z : ℂ) (ht : t ≠ 0) (hz : z ≠ 0) (hcd : 0 < c * d)
    (h₁ : 0 ≤ t * c * z.im) (h₂ : 0 ≤ t * d * z⁻¹.im) :
    z.im = 0 := by
  by_contra h
  have hmul := mul_nonneg h₁ h₂
  rw [Complex.inv_im] at hmul
  have he :
      (t * c * z.im) * (t * d * (-z.im / Complex.normSq z)) =
        -(t ^ 2 * (c * d) * z.im ^ 2) / Complex.normSq z := by
    simp only [div_eq_mul_inv]
    ring
  rw [he] at hmul
  have hneg := div_neg_of_neg_of_pos
    (neg_neg_of_pos (mul_pos (mul_pos (sq_pos_of_ne_zero ht) hcd) (sq_pos_of_ne_zero h)))
    (Complex.normSq_pos.mpr hz)
  exact hmul.not_lt hneg

/-- Given the two oriented cycle inequalities, the crossed product is
on the zero-height line exactly when the phase ratio is real. -/
theorem crossed_product_im_eq_zero_iff_phase_ratio
    (t c d : ℝ) (z : ℂ) (ht : t ≠ 0) (hc : c ≠ 0) (hz : z ≠ 0)
    (h₁ : 0 ≤ t * c * z.im) (h₂ : 0 ≤ t * d * z⁻¹.im) :
    ((1 + (c : ℂ) * z) * (1 + (d : ℂ) * z⁻¹)).im = 0 ↔ z.im = 0 := by
  have he : (1 + (c : ℂ) * z) * (1 + (d : ℂ) * z⁻¹) =
      1 + (c : ℂ) * d + (c : ℂ) * z + (d : ℂ) * z⁻¹ := by
    field_simp [hz] <;> ring
  rw [he]
  simp only [Complex.add_im, Complex.mul_im, Complex.one_im, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, zero_mul, zero_add, add_zero]
  constructor
  · intro h
    have hsum : t * c * z.im + t * d * z⁻¹.im = 0 := by
      rw [mul_assoc t c, mul_assoc t d, ← mul_add, h, mul_zero]
    exact (mul_eq_zero.mp (by linarith only [h₁, h₂, hsum] :
      t * c * z.im = 0)).resolve_left (mul_ne_zero ht hc)
  · intro h
    simp [h, Complex.inv_im]

private theorem normalized_matching_expansion (x y : ι → ℂ) (σ : Equiv.Perm ι) :
    bilinearMatchingProduct x y 1 0 0 1 σ =
      ∑ J : Finset ι, (∏ i ∈ J.map σ.toEmbedding, x i) * ∏ j ∈ J, y j := by
  rw [show bilinearMatchingProduct x y 1 0 0 1 σ = ∏ j, (x (σ j) * y j + 1) by
    simp only [bilinearMatchingProduct, bilinearKernel, one_mul, zero_mul, add_zero]]
  rw [Fintype.prod_add]
  simp only [Finset.prod_const_one, mul_one, Finset.prod_mul_distrib,
    Finset.prod_map, Equiv.toEmbedding_apply]

/-- The minor expansion for the normalized rank-two kernel `1 + xᵢ yⱼ`. -/
theorem bilinearPencil_one_mul_det_eq_sum_subsetMinors (x y : ι → ℂ)
    (U : Matrix ι ι ℂ) (hU : IsUnitary U) :
    (bilinearPencil x y U 1 0 0 1).det =
      ∑ J : Finset ι, ∑ I : Finset ι, (subsetMinorSq U I J : ℂ) *
        ((∏ i ∈ I, x i) * ∏ j ∈ J, y j) := by
  classical
  rw [← bilinear_signed_determinant x y U hU 1 0 0 1]
  simp_rw [normalized_matching_expansion, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro J _
  rw [← Finset.sum_fiberwise univ (fun σ : Equiv.Perm ι => J.map σ.toEmbedding)]
  apply Finset.sum_congr rfl
  intro I _
  rw [← sum_signedWeight_image_eq_subsetMinorSq U hU I J, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro σ hσ
  rw [(Finset.mem_filter.mp hσ).2]

omit [Fintype ι] in
private theorem prod_split_exception (f : ι → ℂ) (S : Finset ι) (q : ι)
    (hf : ∀ i, i ≠ q → (f i).im = 0) :
    (∏ i ∈ S, f i) =
      ((∏ i ∈ S.erase q, (f i).re : ℝ) : ℂ) * (if q ∈ S then f q else 1) := by
  have he : ((∏ i ∈ S.erase q, (f i).re : ℝ) : ℂ) = ∏ i ∈ S.erase q, f i := by
    rw [Complex.ofReal_prod]
    apply Finset.prod_congr rfl
    intro i hi
    exact Complex.ext rfl ((hf i (Finset.mem_erase.mp hi).1).symm)
  rw [he]
  by_cases h : q ∈ S
  · rw [if_pos h, Finset.prod_erase_mul S f h]
  · rw [if_neg h, Finset.erase_eq_of_not_mem h, mul_one]

omit [Fintype ι] in
private theorem mul_im_subset_products_nonneg
    (x y : ι → ℂ) (qx qy : ι) (I J : Finset ι) (t : ℝ)
    (hx : ∀ i, i ≠ qx → (x i).im = 0 ∧ 0 ≤ (x i).re)
    (hy : ∀ j, j ≠ qy → (y j).im = 0 ∧ 0 ≤ (y j).re)
    (hxq : 0 ≤ t * (x qx).im) (hyq : 0 ≤ t * (y qy).im)
    (hpair : (x qx * y qy).im = 0) :
    0 ≤ t * (((∏ i ∈ I, x i) * ∏ j ∈ J, y j) : ℂ).im := by
  let A : ℝ := ∏ i ∈ I.erase qx, (x i).re
  let B : ℝ := ∏ j ∈ J.erase qy, (y j).re
  have hA : 0 ≤ A := Finset.prod_nonneg
    (fun i hi => (hx i (Finset.mem_erase.mp hi).1).2)
  have hB : 0 ≤ B := Finset.prod_nonneg
    (fun j hj => (hy j (Finset.mem_erase.mp hj).1).2)
  rw [prod_split_exception x I qx (fun i hi => (hx i hi).1),
    prod_split_exception y J qy (fun j hj => (hy j hj).1)]
  have he (z w : ℂ) : t * (((A : ℂ) * z) * ((B : ℂ) * w)).im =
      (A * B) * (t * (z * w).im) := by
    simp only [Complex.mul_im, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
    ring
  rw [he]
  refine mul_nonneg (mul_nonneg hA hB) ?_
  by_cases hI : qx ∈ I <;> by_cases hJ : qy ∈ J <;> simp [hI, hJ, hpair, hxq, hyq]

/-- Every squared-minor term satisfies the projected bound when the two
exceptional coordinates point to the same half-plane and their product is
real. The other coordinates are nonnegative real numbers. -/
theorem mul_im_bilinearPencil_one_mul_det_nonneg_of_exception_pair
    (x y : ι → ℂ) (qx qy : ι) (U : Matrix ι ι ℂ) (hU : IsUnitary U) (t : ℝ)
    (hx : ∀ i, i ≠ qx → (x i).im = 0 ∧ 0 ≤ (x i).re)
    (hy : ∀ j, j ≠ qy → (y j).im = 0 ∧ 0 ≤ (y j).re)
    (hxq : 0 ≤ t * (x qx).im) (hyq : 0 ≤ t * (y qy).im)
    (hpair : (x qx * y qy).im = 0) :
    0 ≤ t * (bilinearPencil x y U 1 0 0 1).det.im := by
  rw [bilinearPencil_one_mul_det_eq_sum_subsetMinors x y U hU]
  simp only [Complex.im_sum, Finset.mul_sum]
  apply Finset.sum_nonneg
  intro J _
  apply Finset.sum_nonneg
  intro I _
  simp only [Complex.mul_im (subsetMinorSq U I J : ℂ), Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, add_zero]
  rw [mul_left_comm t (subsetMinorSq U I J)]
  exact mul_nonneg (subsetMinorSq_nonneg U I J)
    (mul_im_subset_products_nonneg x y qx qy I J t hx hy hxq hyq hpair)

/-- A zero-height support certificate for actual additive spectra admitting
the indicated rank-two factorization. At a pivot `p`, the factorization is
obtained by taking
`xᵢ = (aᵢ - aₚ)/(aᵢ + bₚ)` and `yⱼ = (bₚ - bⱼ)/(aₚ + bⱼ)`. -/
theorem determinantValue_re_nonpos_of_factored_exception_pair
    (a b x y l r : ι → ℂ) (qx qy : ι) (U : Matrix ι ι ℂ) (hU : IsUnitary U)
    (η : ℂ) (t : ℝ)
    (hfac : ∀ i j, a i + b j = l i * r j * (x i * y j + 1))
    (hscale : η * ((∏ i, l i) * ∏ j, r j) = (t : ℂ) * Complex.I)
    (hx : ∀ i, i ≠ qx → (x i).im = 0 ∧ 0 ≤ (x i).re)
    (hy : ∀ j, j ≠ qy → (y j).im = 0 ∧ 0 ≤ (y j).re)
    (hxq : 0 ≤ t * (x qx).im) (hyq : 0 ≤ t * (y qy).im)
    (hpair : (x qx * y qy).im = 0) :
    (η * determinantValue a b U).re ≤ 0 := by
  let C := (∏ i, l i) * ∏ j, r j
  have hp (σ : Equiv.Perm ι) :
      matchingProduct a b σ = C * bilinearMatchingProduct x y 1 0 0 1 σ := by
    simp only [matchingProduct, hfac, C, Finset.prod_mul_distrib, Equiv.prod_comp σ l,
      bilinearMatchingProduct, bilinearKernel, one_mul, zero_mul, add_zero]
  have hd : determinantValue a b U = C * (bilinearPencil x y U 1 0 0 1).det := by
    rw [← signed_determinant a b U hU, ← bilinear_signed_determinant x y U hU 1 0 0 1,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro σ _
    rw [hp, mul_left_comm (signedWeight U σ)]
  have hC : η * C = (t : ℂ) * Complex.I := hscale
  rw [hd, ← mul_assoc η C, hC, mul_assoc, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, Complex.I_mul_re,
    mul_neg, neg_nonpos]
  exact mul_im_bilinearPencil_one_mul_det_nonneg_of_exception_pair
    x y qx qy U hU t hx hy hxq hyq hpair

end MOC
