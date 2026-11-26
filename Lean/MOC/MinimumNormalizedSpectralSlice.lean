import MOC.MinimumNormalizedSpectralMatching

/-! A real polynomial slice of a minimum-normalized spectral value. -/

open BigOperators Finset Polynomial
open scoped ComplexConjugate

namespace MOC

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Oppositely shift the two real lists and then add the same variable to
both. Divide the value by the normalization to obtain a monic polynomial. -/
def squarefreeShiftedSlice (c : SquarefreeClass ι) (a b : ι → ℝ) (t : ℝ) : ℝ[X] :=
  ∑ I : Finset ι, ∑ J : Finset ι, if Iᶜ.card = J.card then
    C ((c I J).re / (2 : ℝ) ^ Fintype.card ι) *
      ((∏ i ∈ I, X + C (a i + t)) * ∏ j ∈ J, X + C (b j - t)) else 0

/-- Complex evaluation gives the spectral value of the two shifted lists
divided by the normalization. -/
theorem squarefreeShiftedSlice_aeval {c : SquarefreeClass ι}
    (hc : IsMinimumNormalizedSpectralValue c) (a b : ι → ℝ) (t : ℝ) (s : ℂ) :
    aeval s (squarefreeShiftedSlice c a b t) =
      squarefreeSpectralValue c (fun i => ((a i + t : ℝ) : ℂ) + s)
        (fun j => ((b j - t : ℝ) : ℂ) + s) / (2 : ℂ) ^ Fintype.card ι := by
  simp only [squarefreeShiftedSlice, squarefreeSpectralValue, map_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro I _
  apply Finset.sum_congr rfl
  intro J _
  by_cases hIJ : Iᶜ.card = J.card
  · have hreal : ((c I J).re : ℂ) = c I J := by
      apply Complex.ext
      · exact Complex.ofReal_re _
      · rw [Complex.ofReal_im, (hc.nonnegative I J hIJ).1]
    have hweight :
        algebraMap ℝ ℂ ((c I J).re / (2 : ℝ) ^ Fintype.card ι) =
          c I J / (2 : ℂ) ^ Fintype.card ι := by
      change (↑((c I J).re / (2 : ℝ) ^ Fintype.card ι) : ℂ) = _
      rw [Complex.ofReal_div, Complex.ofReal_pow, Complex.ofReal_ofNat, hreal]
    have hadd (x : ℝ) : s + algebraMap ℝ ℂ x = (x : ℂ) + s :=
      add_comm s (x : ℂ)
    simp only [squarefreeDividedDivisor, if_pos hIJ, map_mul, map_prod, map_add,
      aeval_X, aeval_C, hweight, hadd, div_mul_eq_mul_div]
  · simp only [squarefreeDividedDivisor, if_neg hIJ, map_zero, mul_zero, zero_div]

/-- View the real evaluation of the slice as a complex spectral value. -/
theorem squarefreeShiftedSlice_eval {c : SquarefreeClass ι}
    (hc : IsMinimumNormalizedSpectralValue c) (a b : ι → ℝ) (t s : ℝ) :
    ((squarefreeShiftedSlice c a b t).eval s : ℂ) =
      squarefreeSpectralValue c (fun i => ((a i + t : ℝ) : ℂ) + (s : ℂ))
        (fun j => ((b j - t : ℝ) : ℂ) + (s : ℂ)) / (2 : ℂ) ^ Fintype.card ι := by
  have he := aeval_algebraMap_apply_eq_algebraMap_eval (A := ℂ) s
    (squarefreeShiftedSlice c a b t)
  change aeval (s : ℂ) (squarefreeShiftedSlice c a b t) =
    ((squarefreeShiftedSlice c a b t).eval s : ℂ) at he
  exact he.symm.trans (squarefreeShiftedSlice_aeval hc a b t (s : ℂ))

private theorem monic_linear_product (z : ι → ℝ) (I : Finset ι) :
    (∏ i ∈ I, X + C (z i)).Monic ∧
      (∏ i ∈ I, X + C (z i)).natDegree = I.card := by
  refine ⟨monic_prod_of_monic I _ (fun i _ => monic_X_add_C (z i)), ?_⟩
  rw [natDegree_prod_of_monic I _ (fun i _ => monic_X_add_C (z i))]
  simp only [natDegree_X_add_C, Finset.sum_const, nsmul_eq_mul, mul_one]

private theorem slice_products_monic_degree (a b : ι → ℝ) (t : ℝ)
    (I J : Finset ι) (hIJ : Iᶜ.card = J.card) :
    ((∏ i ∈ I, X + C (a i + t)) * ∏ j ∈ J, X + C (b j - t)).Monic ∧
      ((∏ i ∈ I, X + C (a i + t)) * ∏ j ∈ J, X + C (b j - t)).natDegree =
        Fintype.card ι := by
  obtain ⟨hmA, hdA⟩ := monic_linear_product (fun i => a i + t) I
  obtain ⟨hmB, hdB⟩ := monic_linear_product (fun j => b j - t) J
  exact ⟨hmA.mul hmB, by
    rw [hmA.natDegree_mul hmB, hdA, hdB, ← hIJ, Finset.card_add_card_compl]⟩

private theorem spectral_coefficient_sum {c : SquarefreeClass ι}
    (hc : IsMinimumNormalizedSpectralValue c) :
    (∑ I : Finset ι, ∑ J : Finset ι, if Iᶜ.card = J.card then (c I J).re else 0) =
      (2 : ℝ) ^ Fintype.card ι := by
  calc
    _ = (squarefreeSpectralValue c (fun _ => 1) (fun _ => 1)).re := by
      simp only [squarefreeSpectralValue, Complex.re_sum]
      apply Finset.sum_congr rfl
      intro I _
      apply Finset.sum_congr rfl
      intro J _
      by_cases hIJ : Iᶜ.card = J.card <;>
        simp only [squarefreeDividedDivisor, hIJ, if_true, if_false,
          Finset.prod_const_one, mul_one, mul_zero, Complex.zero_re]
    _ = _ := by
      rw [hc.normalized]
      simpa only [Complex.ofReal_pow, Complex.ofReal_ofNat] using
        Complex.ofReal_re ((2 : ℝ) ^ Fintype.card ι)

/-- The slice is monic, and its degree is the length of each list. -/
theorem squarefreeShiftedSlice_monic_degree {c : SquarefreeClass ι}
    (hc : IsMinimumNormalizedSpectralValue c) (a b : ι → ℝ) (t : ℝ) :
    (squarefreeShiftedSlice c a b t).Monic ∧
      (squarefreeShiftedSlice c a b t).natDegree = Fintype.card ι := by
  let n := Fintype.card ι
  let q := squarefreeShiftedSlice c a b t
  have hle : q.natDegree ≤ n := by
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro k hk
    change (squarefreeShiftedSlice c a b t).coeff k = 0
    simp only [squarefreeShiftedSlice, finset_sum_coeff]
    apply Finset.sum_eq_zero
    intro I _
    apply Finset.sum_eq_zero
    intro J _
    by_cases hIJ : Iᶜ.card = J.card
    · have hd := (slice_products_monic_degree a b t I J hIJ).2
      rw [if_pos hIJ, coeff_C_mul,
        coeff_eq_zero_of_natDegree_lt (hd.symm ▸ hk), mul_zero]
    · rw [if_neg hIJ, coeff_zero]
  have htop : q.coeff n = 1 := by
    change (squarefreeShiftedSlice c a b t).coeff n = 1
    calc
      _ = (∑ I : Finset ι, ∑ J : Finset ι,
          if Iᶜ.card = J.card then (c I J).re else 0) / (2 : ℝ)^n := by
        simp only [squarefreeShiftedSlice, finset_sum_coeff, Finset.sum_div]
        apply Finset.sum_congr rfl
        intro I _
        apply Finset.sum_congr rfl
        intro J _
        by_cases hIJ : Iᶜ.card = J.card
        · obtain ⟨hm, hd⟩ := slice_products_monic_degree a b t I J hIJ
          simp only [if_pos hIJ, coeff_C_mul]
          rw [← hd, hm.coeff_natDegree, mul_one]
        · simp only [if_neg hIJ, coeff_zero, zero_div]
      _ = 1 := by
        rw [spectral_coefficient_sum hc]
        exact div_self (pow_ne_zero _ (by norm_num))
  exact ⟨monic_of_natDegree_le_of_coeff_eq_one n hle htop,
    natDegree_eq_of_le_of_coeff_ne_zero hle (by rw [htop]; exact one_ne_zero)⟩

/-- Stability makes every root of the slice real. -/
theorem squarefreeShiftedSlice_splits {c : SquarefreeClass ι}
    (hc : IsMinimumNormalizedSpectralValue c) (a b : ι → ℝ) (t : ℝ) :
    (squarefreeShiftedSlice c a b t).Splits (RingHom.id ℝ) := by
  let q := squarefreeShiftedSlice c a b t
  have hno (s : ℂ) (hs : 0 < s.im) : aeval s q ≠ 0 := by
    change aeval s (squarefreeShiftedSlice c a b t) ≠ 0
    rw [squarefreeShiftedSlice_aeval hc]
    refine div_ne_zero (hc.stable _ _ (fun i => ?_) (fun j => ?_))
      (pow_ne_zero _ (by norm_num))
    · simpa only [Complex.add_im, Complex.ofReal_im, zero_add] using hs
    · simpa only [Complex.add_im, Complex.ofReal_im, zero_add] using hs
  apply Polynomial.splits_id_of_splits (i := algebraMap ℝ ℂ) (IsAlgClosed.splits_codomain q)
  intro z hz
  have hzroot : aeval z q = 0 := by
    simpa only [IsRoot.def, aeval_def, eval_map] using Polynomial.isRoot_of_mem_roots hz
  have hup : ¬ 0 < z.im := fun h => hno z h hzroot
  have hdown : ¬ z.im < 0 := by
    intro h
    have hp : 0 < (conj z).im := by
      rw [Complex.conj_im]
      exact neg_pos.mpr h
    apply hno (conj z) hp
    rw [aeval_conj, hzroot, map_zero]
  refine ⟨z.re, ?_⟩
  apply Complex.ext
  · exact Complex.ofReal_re _
  · change (z.re : ℂ).im = z.im
    rw [Complex.ofReal_im]
    exact le_antisymm (le_of_not_gt hdown) (le_of_not_gt hup)

/-- When both base lists vanish, the opposite shift leaves the slice
equal to a power of the common variable. -/
theorem squarefreeShiftedSlice_zero_base {c : SquarefreeClass ι}
    (hc : IsMinimumNormalizedSpectralValue c) (t : ℝ) :
    squarefreeShiftedSlice c (fun _ => 0) (fun _ => 0) t = X ^ Fintype.card ι := by
  apply Polynomial.funext
  intro s
  apply Complex.ofReal_injective
  rw [squarefreeShiftedSlice_eval hc, hc.constant_lists]
  simp only [zero_add, zero_sub, Complex.ofReal_neg, eval_pow, eval_X, Complex.ofReal_pow]
  have he : ((t : ℂ) + (s : ℂ)) + (-(t : ℂ) + (s : ℂ)) = 2 * (s : ℂ) := by ring
  rw [he, mul_pow]
  exact mul_div_cancel_left₀ _ (pow_ne_zero _ (by norm_num))

end

end MOC
