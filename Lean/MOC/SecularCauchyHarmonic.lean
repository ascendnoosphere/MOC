import MOC.SecularResidueCalculus
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Weighted cancellation for the two partial-fraction charts of a squared
Cauchy minor. -/

open BigOperators Filter Finset Polynomial
open scoped Topology

namespace MOC

noncomputable section

variable {ι : Type*}

/-- A rational function written as one plus simple fractions. -/
def secularPartialFractions (S : Finset ι) (d c : ι → ℝ) (z : ℝ) : ℝ :=
  1 + ∑ i ∈ S, c i / (z-d i)

/-- A ratio of two monic products of the same degree has its partial
fractions given by the negatives of the secular residues. -/
theorem secular_ratio_eq_partialFractions [Fintype ι] [DecidableEq ι]
    (d h : ι → ℝ) (hd : Function.Injective d)
    (z : ℝ) (hz : ∀ i, z ≠ d i) :
    (∏ i, (z-h i)) / (∏ i, (z-d i)) = secularPartialFractions univ d
      (fun i => -secularResidue h d i) z := by
  let P := ∏ i, (z-d i)
  let r := secularResidue h d
  have hp : P ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => sub_ne_zero.mpr (hz i))
  have he := congrArg (Polynomial.eval z) (secular_polynomial_identity h d hd)
  simp only [Polynomial.eval_sub, Polynomial.eval_prod, Polynomial.eval_X, Polynomial.eval_C,
    Polynomial.eval_finset_sum, Polynomial.eval_mul] at he
  change P - (∏ i, (z-h i)) = ∑ i, r i * ∏ j ∈ univ.erase i, (z-d j) at he
  change (∏ i, (z-h i)) / P = 1 + ∑ i, (-r i) / (z-d i)
  apply (div_eq_iff hp).mpr
  rw [add_mul, one_mul, Finset.sum_mul]
  have hterm (i : ι) : ((-r i) / (z-d i)) * P = -(r i * ∏ j ∈ univ.erase i, (z-d j)) := by
    dsimp only [P]
    rw [← Finset.prod_erase_mul univ (fun j => z-d j) (mem_univ i)]
    field_simp [sub_ne_zero.mpr (hz i)]
    exact (mul_assoc _ _ _).symm
  simp_rw [hterm, Finset.sum_neg_distrib]
  linarith only [he]

private theorem hasDerivAt_partialFraction (c d z : ℝ) (h : z ≠ d) :
    HasDerivAt (fun t : ℝ => c/(t-d)) (-(c/(z-d)^2)) z := by
  have hg := (hasDerivAt_id' z).sub_const d
  convert (hasDerivAt_const z c).div hg (sub_ne_zero.mpr h) using 1
  ring

private theorem hasDerivAt_partialFraction_derivative (c d z : ℝ) (h : z ≠ d) :
    HasDerivAt (fun t : ℝ => -(c/(t-d)^2)) (2*c/(z-d)^3) z := by
  have hne := sub_ne_zero.mpr h
  have hg := ((hasDerivAt_id' z).sub_const d).pow 2
  have hh := ((hasDerivAt_const z c).div hg (pow_ne_zero 2 hne)).neg
  convert hh using 1
  field_simp [hne]
  ring

/-- The first derivative of the simple-fraction expression, away from its poles. -/
theorem hasDerivAt_secularPartialFractions (S : Finset ι) (d c : ι → ℝ) (z : ℝ)
    (hz : ∀ i ∈ S, z ≠ d i) :
    HasDerivAt (secularPartialFractions S d c) (∑ i ∈ S, -(c i/(z-d i)^2)) z := by
  simpa only [secularPartialFractions] using
    (HasDerivAt.sum fun i hi => hasDerivAt_partialFraction (c i) (d i) z (hz i hi)).const_add 1

/-- The second derivative is the cubic-pole sum. -/
theorem hasSecondDerivAt_secularPartialFractions (S : Finset ι) (d c : ι → ℝ) (z : ℝ)
    (hz : ∀ i ∈ S, z ≠ d i) :
    HasDerivAt (deriv (secularPartialFractions S d c))
      (∑ i ∈ S, 2*c i/(z-d i)^3) z := by
  have hgrad : HasDerivAt (fun t : ℝ => ∑ i ∈ S, -(c i/(t-d i)^2))
      (∑ i ∈ S, 2*c i/(z-d i)^3) z :=
    HasDerivAt.sum fun i hi => hasDerivAt_partialFraction_derivative (c i) (d i) z (hz i hi)
  apply hgrad.congr_of_eventuallyEq
  have hn : ∀ᶠ t in 𝓝 z, ∀ i ∈ S, t ≠ d i :=
    (Filter.eventually_all_finset S).mpr fun i hi => eventually_ne_nhds (hz i hi)
  filter_upwards [hn] with t ht
  exact (hasDerivAt_secularPartialFractions S d c t ht).deriv

theorem hasSecondDerivAt_const_mul_partialFractions
    (S : Finset ι) (d c : ι → ℝ) (w z : ℝ) (hz : ∀ i ∈ S, z ≠ d i) :
    HasDerivAt (deriv (fun t => w * secularPartialFractions S d c t))
      (w * ∑ i ∈ S, 2*c i/(z-d i)^3) z := by
  have hgrad := (hasSecondDerivAt_secularPartialFractions S d c z hz).const_mul w
  apply hgrad.congr_of_eventuallyEq
  have hn : ∀ᶠ t in 𝓝 z, ∀ i ∈ S, t ≠ d i :=
    (Filter.eventually_all_finset S).mpr fun i hi => eventually_ne_nhds (hz i hi)
  filter_upwards [hn] with t ht
  rw [((hasDerivAt_secularPartialFractions S d c t ht).const_mul w).deriv,
    (hasDerivAt_secularPartialFractions S d c t ht).deriv]

/-- Reciprocal cubic interactions across a complementary cut cancel in
weighted pure second derivatives. -/
theorem weighted_harmonic_of_secular_fraction_charts [Fintype ι] [DecidableEq ι]
    (F : (ι → ℝ) → ℝ) (d r a b w : ι → ℝ) (S : Finset ι)
    (hd : Function.Injective d)
    (hchart : ∀ i, (fun t => F (Function.update d i t)) =ᶠ[𝓝 (d i)]
      fun t => w i * (if i ∈ S then secularPartialFractions Sᶜ d b t
        else secularPartialFractions S d a t))
    (hleft : ∀ i ∈ S, r i = -secularPartialFractions Sᶜ d b (d i) * a i)
    (hright : ∀ i ∈ Sᶜ, r i = -secularPartialFractions S d a (d i) * b i) :
    (∑ i, r i * deriv (deriv (fun t => F (Function.update d i t))) (d i)) = 0 := by
  have hF₁ (i : ι) (hi : i ∈ S) :
      F d = w i * secularPartialFractions Sᶜ d b (d i) := by
    simpa only [Function.update_eq_self, if_pos hi] using (hchart i).eq_of_nhds
  have hF₂ (j : ι) (hj : j ∈ Sᶜ) :
      F d = w j * secularPartialFractions S d a (d j) := by
    simpa only [Function.update_eq_self, if_neg (mem_compl.mp hj)] using (hchart j).eq_of_nhds
  have hder₁ (i : ι) (hi : i ∈ S) :
      deriv (deriv (fun t => F (Function.update d i t))) (d i) =
        w i * ∑ j ∈ Sᶜ, 2 * b j / (d i-d j)^3 := by
    have he : (fun t => F (Function.update d i t)) =ᶠ[𝓝 (d i)]
        fun t => w i * secularPartialFractions Sᶜ d b t := by
      simpa only [if_pos hi] using hchart i
    have hn : ∀ j ∈ Sᶜ, d i ≠ d j := fun j hj =>
      hd.ne (fun hij => mem_compl.mp hj (hij ▸ hi))
    rw [he.deriv.deriv_eq, (hasSecondDerivAt_const_mul_partialFractions Sᶜ d b (w i) (d i) hn).deriv]
  have hder₂ (j : ι) (hj : j ∈ Sᶜ) :
      deriv (deriv (fun t => F (Function.update d j t))) (d j) =
        w j * ∑ i ∈ S, 2 * a i / (d j-d i)^3 := by
    have he : (fun t => F (Function.update d j t)) =ᶠ[𝓝 (d j)]
        fun t => w j * secularPartialFractions S d a t := by
      simpa only [if_neg (mem_compl.mp hj)] using hchart j
    have hn : ∀ i ∈ S, d j ≠ d i := fun i hi =>
      hd.ne (fun hji => mem_compl.mp hj (hji.symm ▸ hi))
    rw [he.deriv.deriv_eq, (hasSecondDerivAt_const_mul_partialFractions S d a (w j) (d j) hn).deriv]
  have hsum₁ : (∑ i ∈ S, r i * deriv (deriv (fun t => F (Function.update d i t))) (d i)) =
      ∑ i ∈ S, ∑ j ∈ Sᶜ, -F d * a i * (2 * b j / (d i-d j)^3) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [hleft i hi, hder₁ i hi, Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [hF₁ i hi]
    ring
  have hsum₂ : (∑ j ∈ Sᶜ, r j * deriv (deriv (fun t => F (Function.update d j t))) (d j)) =
      ∑ i ∈ S, ∑ j ∈ Sᶜ, -F d * b j * (2 * a i / (d j-d i)^3) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j hj
    rw [hright j hj, hder₂ j hj, Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [hF₂ j hj]
    ring
  rw [← Finset.sum_add_sum_compl S, hsum₁, hsum₂, ← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro i _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro j _
  rw [← neg_sub (d i) (d j), neg_pow, show (-1 : ℝ)^3 = -1 by norm_num, neg_one_mul, div_neg]
  ring


end

end MOC
