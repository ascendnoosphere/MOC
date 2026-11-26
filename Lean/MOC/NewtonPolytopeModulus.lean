import Mathlib.Analysis.Complex.PhragmenLindelof
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Topology.ClusterPt
import Mathlib.Topology.ContinuousOn

/-! The torus bound for a polynomial controls its value by the largest
monomial modulus at the input. -/

open Asymptotics BigOperators Bornology Filter Set
open scoped Topology Filter

namespace MOC

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [Nonempty κ]

private theorem norm_sum_monomials_le_of_nonzero
    (c : κ → ℂ) (α : κ → ι → ℕ) (C : ℝ)
    (hC : ∀ x : ι → ℂ, (∀ i, ‖x i‖ = 1) →
      ‖∑ s, c s * ∏ i, x i ^ α s i‖ ≤ C)
    (x : ι → ℂ) (hx : ∀ i, x i ≠ 0) :
    ∃ k : κ, ‖∑ s, c s * ∏ i, x i ^ α s i‖ ≤ C * ‖∏ i, x i ^ α k i‖ := by
  classical
  let w (i : ι) : ℝ := Real.log ‖x i‖
  let phase (i : ι) : ℂ := x i / (‖x i‖ : ℂ)
  let path (t : ℂ) (i : ι) : ℂ := phase i * Complex.exp ((w i : ℂ) * t)
  let weight (s : κ) : ℝ := ∑ i, (α s i : ℝ) * w i
  obtain ⟨k, _, hk⟩ := Finset.exists_max_image Finset.univ weight Finset.univ_nonempty
  let h : ℝ := weight k
  have hmax (s : κ) : weight s ≤ h := hk s (Finset.mem_univ s)
  let F (t : ℂ) : ℂ := Complex.exp (((-h : ℝ) : ℂ) * t) *
    (∑ s, c s * ∏ i, path t i ^ α s i)
  have hphase (i : ι) : ‖phase i‖ = 1 := by
    rw [phase, norm_div, Complex.norm_of_nonneg (norm_nonneg (x i))]
    exact div_self (norm_ne_zero_iff.mpr (hx i))
  have hpathNorm (t : ℂ) (i : ι) : ‖path t i‖ = Real.exp (w i * t.re) := by
    rw [path, norm_mul, hphase, one_mul, Complex.norm_exp, Complex.re_ofReal_mul]
  have hpathOne : path 1 = x := by
    funext i
    change phase i * Complex.exp ((w i : ℂ) * 1) = x i
    rw [mul_one, ← Complex.ofReal_exp, w, Real.exp_log (norm_pos_iff.mpr (hx i))]
    exact div_mul_cancel₀ _ (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (hx i)))
  have hmonomial (s : κ) (t : ℂ) :
      ‖∏ i, path t i ^ α s i‖ = Real.exp (weight s * t.re) := by
    rw [norm_prod, weight, Finset.sum_mul, Real.exp_sum]
    apply Finset.prod_congr rfl
    intro i _
    rw [norm_pow, hpathNorm, ← Real.exp_nat_mul, mul_assoc]
  have hd : Differentiable ℂ F := by
    change Differentiable ℂ (fun t : ℂ => Complex.exp (((-h : ℝ) : ℂ) * t) *
      (∑ s, c s * ∏ i, path t i ^ α s i))
    apply Differentiable.mul (differentiable_id.const_mul _).cexp
    apply Differentiable.sum
    intro s _
    apply Differentiable.const_mul _ (c s)
    apply Differentiable.finset_prod
    intro i _
    exact (((differentiable_id.const_mul (w i : ℂ)).cexp).const_mul (phase i)).pow _
  have hbounded (t : ℂ) (ht : 0 ≤ t.re) : ‖F t‖ ≤ ∑ s, ‖c s‖ := by
    rw [F, Finset.mul_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun s _ => ?_)
    rw [norm_mul, norm_mul, Complex.norm_exp, Complex.re_ofReal_mul, hmonomial,
      mul_left_comm, ← Real.exp_add]
    apply mul_le_of_le_one_right (norm_nonneg (c s))
    apply Real.exp_le_one_iff.mpr
    calc
      -h * t.re + weight s * t.re = (weight s - h) * t.re := by ring
      _ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (hmax s)) ht
  have him (y : ℝ) : ‖F ((y : ℂ) * Complex.I)‖ ≤ C := by
    have hre : ((y : ℂ) * Complex.I).re = 0 := by
      rw [Complex.re_ofReal_mul, Complex.I_re, mul_zero]
    rw [F, norm_mul, Complex.norm_exp, Complex.re_ofReal_mul, hre,
      mul_zero, Real.exp_zero, one_mul]
    apply hC
    intro i
    rw [hpathNorm, hre, mul_zero, Real.exp_zero]
  have hF : ‖F 1‖ ≤ C := by
    have hrealOne : 0 ≤ (1 : ℂ).re := by norm_num
    apply PhragmenLindelof.right_half_plane_of_bounded_on_real hd.diffContOnCl
      ?_ ?_ him hrealOne
    · refine ⟨0, by norm_num, 0, IsBigO.of_bound (∑ s, ‖c s‖) ?_⟩
      refine eventually_inf_principal.mpr (Eventually.of_forall fun t ht => ?_)
      simpa only [zero_mul, Real.exp_zero, norm_one, mul_one] using hbounded t ht.le
    · refine ⟨∑ s, ‖c s‖, ?_⟩
      change ∀ᶠ t : ℝ in atTop, ‖F (t : ℂ)‖ ≤ ∑ s, ‖c s‖
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
      exact hbounded t (by simpa only [Complex.ofReal_re] using ht)
  have hkNorm : ‖∏ i, x i ^ α k i‖ = Real.exp h := by
    rw [← hpathOne, hmonomial, Complex.one_re, mul_one]
  refine ⟨k, ?_⟩
  rw [hkNorm, mul_comm C]
  calc
    ‖∑ s, c s * ∏ i, x i ^ α s i‖ = Real.exp h * ‖F 1‖ := by
      rw [F, norm_mul, Complex.norm_exp, Complex.re_ofReal_mul, Complex.one_re, mul_one,
        hpathOne, ← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]
    _ ≤ Real.exp h * C := mul_le_mul_of_nonneg_left hF (Real.exp_pos h).le

/-- If a polynomial has modulus at most `C` whenever each variable has
modulus one, its value at any input is bounded by `C` times the largest
monomial modulus among the given terms. Index the terms by the support to
obtain the bound using the Newton polytope of a nonzero polynomial. -/
theorem norm_sum_monomials_le_of_torus_bound
    (c : κ → ℂ) (α : κ → ι → ℕ) (C : ℝ)
    (hC : ∀ x : ι → ℂ, (∀ i, ‖x i‖ = 1) →
      ‖∑ s, c s * ∏ i, x i ^ α s i‖ ≤ C) (x : ι → ℂ) :
    ∃ k : κ, ‖∑ s, c s * ∏ i, x i ^ α s i‖ ≤ C * ‖∏ i, x i ^ α k i‖ := by
  let good (k : κ) : Set (ι → ℂ) :=
    {x | ‖∑ s, c s * ∏ i, x i ^ α s i‖ ≤ C * ‖∏ i, x i ^ α k i‖}
  have hmonomial (s : κ) : Continuous (fun x : ι → ℂ => ∏ i, x i ^ α s i) :=
    continuous_finset_prod _ fun i _ => (continuous_apply i).pow _
  have hclosed : IsClosed (⋃ k, good k) := by
    refine isClosed_iUnion_of_finite fun k => isClosed_le ?_ (continuous_const.mul (hmonomial k).norm)
    exact (continuous_finset_sum _ fun s _ => continuous_const.mul (hmonomial s)).norm
  let nonzeroInputs : Set (ι → ℂ) := Set.pi Set.univ fun _ => ({0} : Set ℂ)ᶜ
  have hdense : Dense nonzeroInputs :=
    dense_pi Set.univ fun _ _ => dense_compl_singleton (0 : ℂ)
  have hsubset : nonzeroInputs ⊆ ⋃ k, good k := by
    intro z hz
    have hnonzero (i : ι) : z i ≠ 0 := by
      have hi := Set.mem_pi.mp hz i (Set.mem_univ i)
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hi
    exact Set.mem_iUnion.mpr (norm_sum_monomials_le_of_nonzero c α C hC z hnonzero)
  exact Set.mem_iUnion.mp ((closure_minimal hsubset hclosed) (hdense x))

/-- A normalized torus contraction can fail the analogous bound around a
nonzero center. Its monomials are `1`, `z`, and `z ^ 2`. -/
theorem exists_torus_contraction_failing_centered_monomial_bound :
    ∃ P : ℂ → ℂ, (∀ z, P z = (3 + 6 * z - z ^ 2) / 8) ∧ P 1 = 1 ∧
      (∀ z, ‖z‖ = 1 → ‖P z‖ ≤ 1) ∧
      (∀ k : Fin 3, ‖(8 : ℂ) ^ k.val - 64‖ < ‖P 8 - 64‖) := by
  let P (z : ℂ) : ℂ := (3 + 6 * z - z ^ 2) / 8
  refine ⟨P, fun _ => rfl, by norm_num [P], ?_, ?_⟩
  · intro z hz
    have hstar : star z * z = 1 := by
      rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self,
        Complex.normSq_eq_norm_sq, hz]
      norm_num
    have hsq : z.re ^ 2 + z.im ^ 2 = 1 := by
      calc
        _ = Complex.normSq z := by rw [Complex.normSq_apply]; ring
        _ = 1 := by rw [Complex.normSq_eq_norm_sq, hz, one_pow]
    have hnorm : ‖star z * P z‖ = ‖P z‖ := by simp [norm_mul, hz]
    have hmul : star z * P z = (3 * star z + 6 - z) / 8 := by
      calc
        _ = (3 * star z + 6 * (star z * z) - (star z * z) * z) / 8 := by
          dsimp [P]
          ring
        _ = _ := by rw [hstar]; ring
    have hre : (3 * star z + 6 - z : ℂ).re = 6 + 2 * z.re := by
      simp [Complex.star_def, Complex.mul_re, Complex.add_re, Complex.sub_re] <;> ring
    have him : (3 * star z + 6 - z : ℂ).im = -4 * z.im := by
      simp [Complex.star_def, Complex.mul_im, Complex.add_im, Complex.sub_im] <;> ring
    apply (sq_le_sq₀ (norm_nonneg _) zero_le_one).mp
    rw [← hnorm, hmul, norm_div, div_pow, Complex.sq_norm, Complex.norm_ofNat,
      one_pow, div_le_iff₀ (by norm_num : 0 < (8 : ℝ) ^ 2),
      Complex.normSq_apply, hre, him]
    nlinarith [sq_nonneg (1 - z.re)]
  · intro k
    have hP : P 8 - 64 = ((-525 / 8 : ℝ) : ℂ) := by norm_num [P]
    rw [hP, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by norm_num)]
    fin_cases k
    · rw [show (8 : ℂ) ^ (0 : ℕ) - 64 = -(63 : ℂ) by norm_num, norm_neg]
      norm_num
    · rw [show (8 : ℂ) ^ (1 : ℕ) - 64 = -(56 : ℂ) by norm_num, norm_neg]
      norm_num
    · rw [show (8 : ℂ) ^ (2 : ℕ) - 64 = (0 : ℂ) by norm_num, norm_zero]
      norm_num

end MOC
