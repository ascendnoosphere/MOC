import MOC.TwoOutlierZeroSupport
import MOC.FiniteMinorLaw

/-! A nonnegative squared-minor certificate for height-zero spectral
objectives with two imaginary outliers. Complementary events are paired
before testing any coefficient signs. -/

open BigOperators Matrix

namespace MOC

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private def complSubsets : Equiv.Perm (Finset ι) :=
  ⟨(·ᶜ), (·ᶜ), compl_compl, compl_compl⟩

/-- Real part of the spectral coefficient of one subset-image event. -/
def subsetSpectralRealCost (a b : ι → ℂ) (I J : Finset ι) : ℝ :=
  ((∏ i ∈ Iᶜ, a i) * ∏ j ∈ J, b j).re

/-- An exact minor expansion of the projected determinant after pairing
complementary events. The formula needs no common probability law. -/
theorem determinant_re_eq_complement_paired_minor_cost (a b : ι → ℂ)
    (U : Matrix ι ι ℂ) (hU : IsUnitary U) :
    (determinantValue a b U).re =
      ∑ J : Finset ι, ∑ I : Finset ι, subsetMinorSq U I J *
        (subsetSpectralRealCost a b I J + subsetSpectralRealCost a b Iᶜ Jᶜ) / 2 := by
  rw [determinantValue_eq_sum_subsetMinors a b U hU]
  simp only [Complex.re_sum, Complex.re_ofReal_mul]
  let g (J I : Finset ι) := subsetMinorSq U I J * subsetSpectralRealCost a b I J
  have hc : (∑ J : Finset ι, ∑ I : Finset ι, g J I) =
      ∑ J : Finset ι, ∑ I : Finset ι, g Jᶜ Iᶜ := by
    rw [← Equiv.sum_comp (complSubsets : Equiv.Perm (Finset ι))
      (fun J => ∑ I, g J I)]
    change (∑ J : Finset ι, ∑ I : Finset ι, g Jᶜ I) = _
    apply Finset.sum_congr rfl
    intro J _
    exact (Equiv.sum_comp (complSubsets : Equiv.Perm (Finset ι)) (g Jᶜ)).symm
  calc
    _ = ((∑ J, ∑ I, g J I) + ∑ J, ∑ I, g Jᶜ Iᶜ) / 2 := by
      rw [← hc]
      change (∑ J, ∑ I, g J I) = (_ + _) / 2
      ring
    _ = _ := by
      rw [← Finset.sum_add_distrib, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro J _
      rw [← Finset.sum_add_distrib, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro I _
      simp only [g, subsetMinorSq_compl U hU, mul_add]

omit [Fintype ι] in
private theorem prod_withImaginaryOutlier_erase (x : ι → ℝ) (d : ι) (u : ℝ) (S : Finset ι) :
    (∏ i ∈ S, withImaginaryOutlier x d u i) =
      (if d ∈ S then Complex.I * (u : ℂ) else 1) * (↑(∏ i ∈ S.erase d, x i) : ℂ) := by
  have hz : (∏ i ∈ S.erase d, withImaginaryOutlier x d u i) =
      (↑(∏ i ∈ S.erase d, x i) : ℂ) := by
    rw [Complex.ofReal_prod]
    apply Finset.prod_congr rfl
    intro i hi
    simp [withImaginaryOutlier, (Finset.mem_erase.mp hi).1]
  by_cases hd : d ∈ S
  · rw [if_pos hd, ← hz]
    simpa [withImaginaryOutlier] using (Finset.mul_prod_erase S
      (withImaginaryOutlier x d u) hd).symm
  · rw [if_neg hd, one_mul, ← hz, Finset.erase_eq_of_not_mem hd]

private theorem paired_outlier_cost_nonpos (x y : ι → ℝ) (d : ι) (u v : ℝ)
    (I J : Finset ι)
    (h : ∀ K L : Finset ι, d ∉ K → d ∈ L →
      (∏ i ∈ K, x i) * (∏ j ∈ Lᶜ, y j) ≤
        u * v * (∏ i ∈ Kᶜ.erase d, x i) * (∏ j ∈ L.erase d, y j)) :
    subsetSpectralRealCost (withImaginaryOutlier x d u) (withImaginaryOutlier y d v) I J +
      subsetSpectralRealCost (withImaginaryOutlier x d u) (withImaginaryOutlier y d v) Iᶜ Jᶜ ≤ 0 := by
  by_cases hI : d ∈ I <;> by_cases hJ : d ∈ J
  · simp [subsetSpectralRealCost, prod_withImaginaryOutlier_erase, hI, hJ, -Complex.ofReal_prod, Complex.mul_re, Complex.mul_im]
  · have hr := h Iᶜ Jᶜ (by simpa using hI) (by simpa using hJ)
    simp only [compl_compl] at hr
    simp [subsetSpectralRealCost, prod_withImaginaryOutlier_erase, hI, hJ, -Complex.ofReal_prod, Complex.mul_re, Complex.mul_im,
      Finset.erase_eq_of_not_mem hJ, Finset.erase_eq_of_not_mem (show d ∉ Iᶜ by simpa using hI)]
    nlinarith only [hr]
  · have hr := h I J hI hJ
    simp [subsetSpectralRealCost, prod_withImaginaryOutlier_erase, hI, hJ, -Complex.ofReal_prod, Complex.mul_re, Complex.mul_im,
      Finset.erase_eq_of_not_mem hI, Finset.erase_eq_of_not_mem (show d ∉ Jᶜ by simpa using hJ)]
    nlinarith only [hr]
  · simp [subsetSpectralRealCost, prod_withImaginaryOutlier_erase, hI, hJ, -Complex.ofReal_prod, Complex.mul_re, Complex.mul_im]

/-- If the product of the imaginary heights dominates the complementary
spectator products on each crossed subset pair, the real part of every
unitary determinant is at most the height-zero matching support. -/
theorem two_outlier_height_zero_of_complement_certificate
    (x y : ι → ℝ) (d : ι) (u v : ℝ) (U : Matrix ι ι ℂ) (hU : IsUnitary U)
    (h : ∀ K L : Finset ι, d ∉ K → d ∈ L →
      (∏ i ∈ K, x i) * (∏ j ∈ Lᶜ, y j) ≤
        u * v * (∏ i ∈ Kᶜ.erase d, x i) * (∏ j ∈ L.erase d, y j)) :
    (determinantValue (withImaginaryOutlier x d u) (withImaginaryOutlier y d v) U).re ≤ 0 := by
  rw [determinant_re_eq_complement_paired_minor_cost _ _ U hU]
  exact Finset.sum_nonpos fun J _ => Finset.sum_nonpos fun I _ =>
    div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos (subsetMinorSq_nonneg U I J)
        (paired_outlier_cost_nonpos x y d u v I J h)) (by positivity)

end MOC
