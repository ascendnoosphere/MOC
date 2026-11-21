import MOC.SpectralMobius
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Tactic.LinearCombination

/-! The second variation of the normalized Möbius bound after clearing denominators. -/

open BigOperators Filter Matrix Polynomial
open scoped Topology

namespace MOC

noncomputable section

private theorem coeff_two_mul (P Q : ℝ[X]) :
    (P * Q).coeff 2 = P.coeff 0 * Q.coeff 2 + P.coeff 1 * Q.coeff 1 +
      P.coeff 2 * Q.coeff 0 := by
  norm_num [Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Finset.sum_range_succ]

private theorem prod_coeffs {J : Type*} [DecidableEq J] (Q : J → ℝ[X])
    (h : ∀ i, (Q i).coeff 0 = 1) (s : Finset J) :
    (∏ i ∈ s, Q i).coeff 0 = 1 ∧
      (∏ i ∈ s, Q i).coeff 1 = ∑ i ∈ s, (Q i).coeff 1 ∧
      2 * (∏ i ∈ s, Q i).coeff 2 =
        2 * (∑ i ∈ s, (Q i).coeff 2) + (∑ i ∈ s, (Q i).coeff 1) ^ 2 -
          ∑ i ∈ s, ((Q i).coeff 1) ^ 2 := by
  induction s using Finset.induction_on with
  | empty => norm_num [coeff_one]
  | @insert i s hi ih =>
    rcases ih with ⟨h0, h1, h2⟩
    simp only [Finset.prod_insert hi, Finset.sum_insert hi, mul_coeff_zero, mul_coeff_one,
      coeff_two_mul, h i, h0, h1, one_mul, mul_one]
    refine ⟨trivial, add_comm _ _, ?_⟩
    linear_combination h2

private theorem pow_coeffs (P : ℝ[X]) (h0 : P.coeff 0 = 1) (h1 : P.coeff 1 = 0) (n : ℕ) :
    (P ^ n).coeff 0 = 1 ∧ (P ^ n).coeff 1 = 0 ∧ (P ^ n).coeff 2 = (n : ℝ) * P.coeff 2 := by
  induction n with
  | zero => norm_num [coeff_one]
  | succ n ih =>
    rcases ih with ⟨hn0, hn1, hn2⟩
    simp only [pow_succ, mul_coeff_zero, mul_coeff_one, coeff_two_mul, h0, h1, hn0, hn1, hn2,
      one_mul, mul_one, zero_mul, add_zero, Nat.cast_succ]
    exact ⟨trivial, trivial, by ring⟩

private theorem coeff_two_nonneg (P : ℝ[X]) (h0 : P.coeff 0 = 0) (h1 : P.coeff 1 = 0)
    (h : ∀ᶠ r in 𝓝 (0 : ℝ), 0 ≤ P.eval r) : 0 ≤ P.coeff 2 := by
  obtain ⟨Q, hQ⟩ := (X_pow_dvd_iff (f := P) (n := 2)).mpr (fun j hj => by
    have he : j = 0 ∨ j = 1 := by omega
    rcases he with rfl | rfl
    · exact h0
    · exact h1)
  have he : P.coeff 2 = Q.eval 0 := by
    rw [hQ, ← coeff_zero_eq_eval_zero]
    exact coeff_X_pow_mul Q 2 0
  rw [he]
  apply ge_of_tendsto (Q.continuousAt.continuousWithinAt (s := ({0} : Set ℝ)ᶜ))
  filter_upwards [h.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with r hr hne
  rw [hQ, eval_mul, eval_pow, eval_X] at hr
  exact (mul_nonneg_iff_of_pos_left (sq_pos_of_ne_zero hne)).mp hr

private theorem mobius_second_coefficient {J : Type*} [Fintype J] [DecidableEq J]
    (n : ℕ) (hn : 0 < n) (u : J → ℂ) (p : ℂ)
    (he : ∑ i, Complex.normSq (u i) = 1)
    (htrace : ∑ i, u i = 0) (hcubic : ∑ i, (Complex.normSq (u i) : ℂ) * u i = 0)
    (hmin : ∀ᶠ r : ℝ in 𝓝 0,
      1 ≤ (∑ i, Complex.normSq (u i) / Complex.normSq (1 - (r : ℂ) * (p * u i))) ^ n *
        ∏ i, Complex.normSq (1 - (r : ℂ) * (p * u i))) :
    0 ≤ (n : ℝ) * (∑ i, Complex.normSq (u i) ^ 2) * Complex.normSq p +
      (p ^ 2 * ((2 * (n : ℂ)) * (∑ i, (Complex.normSq (u i) : ℂ) * u i ^ 2) -
        ∑ i, u i ^ 2)).re := by
  let w (i : J) := Complex.normSq (u i)
  let l (i : J) := -2 * (p * u i).re
  let q (i : J) := Complex.normSq (p * u i)
  let Q (i : J) : ℝ[X] := 1 + C (l i) * X + C (q i) * X ^ 2
  let D : ℝ[X] := ∏ i, Q i
  let K (i : J) : ℝ[X] := ∏ j ∈ Finset.univ.erase i, Q j
  let N : ℝ[X] := ∑ i, C (w i) * K i
  have hQ0 (i : J) : (Q i).coeff 0 = 1 := by norm_num [Q, coeff_C_mul_X, coeff_C_mul_X_pow]
  have hQ1 (i : J) : (Q i).coeff 1 = l i := by
    norm_num [Q, coeff_one, coeff_C_mul_X, coeff_C_mul_X_pow]
  have hQ2 (i : J) : (Q i).coeff 2 = q i := by
    norm_num [Q, coeff_one, coeff_C_mul_X, coeff_C_mul_X_pow]
  have hl : (∑ i, l i) = 0 := by
    simp only [l, ← Finset.mul_sum, ← Complex.re_sum, htrace, mul_zero, Complex.zero_re]
  have hwl : (∑ i, w i * l i) = 0 := by
    calc
      _ = -2 * (∑ i, p * ((w i : ℂ) * u i)).re := by
        rw [Complex.re_sum, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        have hw : p * ((w i : ℂ) * u i) = (w i : ℂ) * (p * u i) := by ring
        simp only [l, hw, Complex.mul_re,
          Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
        ring
      _ = 0 := by
        rw [← Finset.mul_sum, show (∑ i, (w i : ℂ) * u i) = 0 from hcubic]
        simp
  have hD0 : D.coeff 0 = 1 := (prod_coeffs Q hQ0 Finset.univ).1
  have hD1 : D.coeff 1 = 0 := by
    simpa only [D, hQ1, hl] using (prod_coeffs Q hQ0 Finset.univ).2.1
  have hsq (z : ℂ) : 2 * Complex.normSq z - (-2 * z.re) ^ 2 = -2 * (z ^ 2).re := by
    simp only [Complex.normSq_apply, pow_two, Complex.mul_re]
    ring
  have hD2 : D.coeff 2 = - (∑ i, ((p * u i) ^ 2).re) := by
    have hcoeff := (prod_coeffs Q hQ0 (Finset.univ : Finset J)).2.2
    change 2 * D.coeff 2 = _ at hcoeff
    simp only [hQ1, hQ2, hl, zero_pow (by decide : (2 : ℕ) ≠ 0), add_zero] at hcoeff
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib] at hcoeff
    simp only [q, l, hsq, ← Finset.mul_sum] at hcoeff
    linarith only [hcoeff]
  have hmul (i : J) : Q i * K i = D := Finset.mul_prod_erase _ Q (Finset.mem_univ i)
  have hK0 (i : J) : (K i).coeff 0 = 1 :=
    (prod_coeffs Q hQ0 (Finset.univ.erase i)).1
  have hK1 (i : J) : (K i).coeff 1 = -l i := by
    have h := congrArg (fun f : ℝ[X] => f.coeff 1) (hmul i)
    simp only [mul_coeff_one, hD1, hQ0, hQ1, hK0, one_mul, mul_one] at h
    linarith only [h]
  have hK2 (i : J) : (K i).coeff 2 = D.coeff 2 + l i ^ 2 - q i := by
    have h := congrArg (fun f : ℝ[X] => f.coeff 2) (hmul i)
    simp only [coeff_two_mul, hQ0, hQ1, hQ2, hK0, hK1, one_mul, mul_one] at h
    linear_combination h
  have hN0 : N.coeff 0 = 1 := by
    simp only [N, finset_sum_coeff, coeff_C_mul, hK0, mul_one, show (∑ i, w i) = 1 from he]
  have hN1 : N.coeff 1 = 0 := by
    simp only [N, finset_sum_coeff, coeff_C_mul, hK1, mul_neg, Finset.sum_neg_distrib, hwl, neg_zero]
  let v (i : J) := l i ^ 2 - q i
  have hN2 : N.coeff 2 = D.coeff 2 + ∑ i, w i * v i := by
    have ht (i : J) : (K i).coeff 2 = D.coeff 2 + v i := by
      rw [hK2]
      dsimp only [v]
      ring
    simp only [N, finset_sum_coeff, coeff_C_mul, ht, mul_add, Finset.sum_add_distrib,
      ← Finset.sum_mul, show (∑ i, w i) = 1 from he, one_mul]
  have hval (i : J) (r : ℝ) : (Q i).eval r = Complex.normSq (1 - (r : ℂ) * (p * u i)) := by
    simp only [Q, l, q, eval_add, eval_one, eval_mul, eval_C, eval_X, eval_pow,
      Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  have hpos : ∀ᶠ r : ℝ in 𝓝 0, ∀ i, 0 < (Q i).eval r := by
    apply Filter.eventually_all.mpr
    intro i
    exact (Q i).continuousAt.eventually_mem (Ioi_mem_nhds (by
      rw [← coeff_zero_eq_eval_zero, hQ0]
      exact zero_lt_one))
  have hpoly : ∀ᶠ r : ℝ in 𝓝 0, 0 ≤ (N ^ n - D ^ (n - 1)).eval r := by
    filter_upwards [hmin, hpos] with r hr hp
    let E := ∑ i, w i / (Q i).eval r
    have hD : 0 < D.eval r := by
      rw [show D = ∏ i, Q i from rfl, eval_prod]
      exact Finset.prod_pos fun i _ => hp i
    have hN : N.eval r = E * D.eval r := by
      simp only [N, eval_finset_sum, eval_mul, eval_C, E, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      have hKi := congrArg (fun P : ℝ[X] => P.eval r) (hmul i)
      simp only [eval_mul] at hKi
      rw [← hKi]
      field_simp [(hp i).ne']
      ring
    have hr' : 1 ≤ E ^ n * D.eval r := by
      simpa only [E, w, D, eval_prod, hval] using hr
    rw [eval_sub, eval_pow, eval_pow, hN, sub_nonneg]
    have hp' := mul_le_mul_of_nonneg_left hr' (pow_nonneg hD.le (n - 1))
    rw [mul_one] at hp'
    calc
      D.eval r ^ (n - 1) ≤ D.eval r ^ (n - 1) * (E ^ n * D.eval r) := hp'
      _ = E ^ n * (D.eval r ^ (n - 1) * D.eval r) := by ring
      _ = (E * D.eval r) ^ n := by rw [← pow_succ, Nat.sub_add_cancel hn, mul_pow]
  obtain ⟨hpn0, hpn1, hpn2⟩ := pow_coeffs N hN0 hN1 n
  obtain ⟨hpd0, hpd1, hpd2⟩ := pow_coeffs D hD0 hD1 (n - 1)
  have hn' : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by simpa using Nat.cast_sub hn
  have hcoef := coeff_two_nonneg (N ^ n - D ^ (n - 1))
    (by simp only [coeff_sub, hpn0, hpd0, sub_self])
    (by simp only [coeff_sub, hpn1, hpd1, sub_self]) hpoly
  simp only [coeff_sub, hpn2, hpd2, hn', hN2] at hcoef
  have hred : 0 ≤ D.coeff 2 + (n : ℝ) * (∑ i, w i * v i) := by
    nlinarith only [hcoef]
  have hv (i : J) : w i * v i = w i ^ 2 * Complex.normSq p +
      2 * (p ^ 2 * ((w i : ℂ) * u i ^ 2)).re := by
    simp only [v, l, q, w, Complex.normSq_apply, pow_two, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im]
    ring
  let A := ∑ i, w i ^ 2
  let B := ∑ i, (w i : ℂ) * u i ^ 2
  let C₂ := ∑ i, u i ^ 2
  have hD2' : D.coeff 2 = -(p ^ 2 * C₂).re := by
    rw [hD2, show C₂ = ∑ i, u i ^ 2 from rfl, Finset.mul_sum, Complex.re_sum]
    simp only [mul_pow]
  have hvsum : (∑ i, w i * v i) = A * Complex.normSq p + 2 * (p ^ 2 * B).re := by
    simp_rw [hv]
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum, ← Complex.re_sum]
    rw [show (∑ i, p ^ 2 * ((w i : ℂ) * u i ^ 2)) = p ^ 2 * B by rw [show B = _ from rfl, Finset.mul_sum]]
  have hterm : (p ^ 2 * ((2 * (n : ℂ)) * B - C₂)).re =
      2 * (n : ℝ) * (p ^ 2 * B).re - (p ^ 2 * C₂).re := by
    rw [mul_sub, Complex.sub_re, show p ^ 2 * ((2 * (n : ℂ)) * B) =
      (2 * (n : ℂ)) * (p ^ 2 * B) by ring]
    simp only [Complex.mul_re (2 * (n : ℂ)), Complex.mul_re (2 : ℂ),
      Complex.mul_im (2 : ℂ), Complex.re_ofNat, Complex.im_ofNat, Complex.natCast_re,
      Complex.natCast_im, mul_zero, zero_mul, sub_zero, add_zero]
  change 0 ≤ (n : ℝ) * A * Complex.normSq p + (p ^ 2 * ((2 * (n : ℂ)) * B - C₂)).re
  rw [hterm]
  rw [hD2', hvsum] at hred
  nlinarith only [hred]

private theorem norm_le_of_mobius_quadratic (m : ℝ) (z : ℂ)
    (h : ∀ p : ℂ, 0 ≤ m * Complex.normSq p + (p ^ 2 * z).re) : ‖z‖ ≤ m := by
  by_cases hz : z = 0
  · simpa only [hz, norm_zero, Complex.normSq_one, mul_one, mul_zero, Complex.zero_re, add_zero]
      using h (1 : ℂ)
  obtain ⟨p, hp⟩ := IsAlgClosed.exists_pow_nat_eq (-star z) (n := 2) zero_lt_two
  have hnorm : Complex.normSq p = ‖z‖ := by
    rw [Complex.normSq_eq_norm_sq, ← norm_pow, hp, norm_neg, Complex.star_def, Complex.norm_conj]
  have hreal : (p ^ 2 * z).re = -‖z‖ ^ 2 := by
    rw [hp, neg_mul, mul_comm (star z) z, Complex.star_def, Complex.mul_conj, Complex.neg_re,
      Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  have hpos : 0 ≤ (m - ‖z‖) * ‖z‖ := by
    have hp' := h p
    rw [hnorm, hreal] at hp'
    nlinarith only [hp']
  exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_right (norm_pos_iff.mpr hz)).mp hpos)

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- The Möbius second variation bounds the anisotropic fourth moment of a
positive support-gap maximizer by its scalar fourth moment. -/
theorem fourth_moment_mobius_bound (a b : ι → ℂ) (U : Matrix ι ι ℂ) (hU : IsUnitary U)
    (η : ℂ) (hη : Complex.normSq η = 1) (henergy : spectralEnergy a b = 1) {g : ℝ} (hg : 0 < g)
    (hgap : ∀ σ : Equiv.Perm ι,
      g ≤ (η * (determinantValue a b U - matchingProduct a b σ)).re)
    (hmax : ∀ (c d : ι → ℂ) (k : ℂ), spectralEnergy c d ≤ 1 → Complex.normSq k = 1 →
      ∃ σ : Equiv.Perm ι, (k * (determinantValue c d U - matchingProduct c d σ)).re ≤ g) :
    ‖(2 * (Fintype.card ι : ℂ)) * ((∑ i, (Complex.normSq (a i) : ℂ) * a i ^ 2) +
      ∑ i, (Complex.normSq (b i) : ℂ) * b i ^ 2) - ((∑ i, a i ^ 2) + ∑ i, b i ^ 2)‖ ≤
      (Fintype.card ι : ℝ) * ((∑ i, Complex.normSq (a i) ^ 2) + ∑ i, Complex.normSq (b i) ^ 2) := by
  have htrace := equal_trace_of_positive_support_gap_maximizer a b U hU η g
    henergy.le hg hgap fun c d hcd => hmax c d η hcd hη
  have hcubic := equal_cubic_moments_of_positive_gap_maximizer a b U hU η hη henergy hg hgap hmax
  let u : ι ⊕ ι → ℂ := Sum.elim a (fun i => -b i)
  have he : ∑ i, Complex.normSq (u i) = 1 := by
    simpa only [spectralEnergy, u, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
      Complex.normSq_neg] using henergy
  have hs : ∑ i, u i = 0 := by
    simp only [u, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Finset.sum_neg_distrib,
      htrace, add_neg_cancel]
  have hc : ∑ i, (Complex.normSq (u i) : ℂ) * u i = 0 := by
    simp only [u, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Complex.normSq_neg,
      mul_neg, Finset.sum_neg_distrib, hcubic, add_neg_cancel]
  apply norm_le_of_mobius_quadratic
  intro p
  let E (r : ℝ) := ∑ i, Complex.normSq (u i) / Complex.normSq (1 - (r : ℂ) * (p * u i))
  have hEvalEnergy (r : ℝ) : E r = spectralEnergy (mobiusSpectrum ((r : ℂ) * p) a)
      (mobiusSpectrum (-((r : ℂ) * p)) b) := by
    simp only [E, spectralEnergy, mobiusSpectrum, Complex.normSq_div, Fintype.sum_sum_type,
      u, Sum.elim_inl, Sum.elim_inr, Complex.normSq_neg, mul_neg, neg_mul, sub_neg_eq_add, mul_assoc]
  have hEvalProd (r : ℝ) :
      (∏ i, Complex.normSq (1 - (r : ℂ) * (p * u i))) =
        Complex.normSq (mobiusDenominator a b ((r : ℂ) * p)) := by
    simp only [mobiusDenominator, map_mul, map_prod, Fintype.prod_sum_type, u, Sum.elim_inl,
      Sum.elim_inr, mul_neg, sub_neg_eq_add, mul_assoc]
  have hE : ContinuousAt E (0 : ℝ) := by
    have hi (i : ι ⊕ ι) :
        ContinuousAt (fun r : ℝ => Complex.normSq (u i) /
          Complex.normSq (1 - (r : ℂ) * (p * u i))) 0 := by
      refine continuousAt_const.div (Complex.continuous_normSq.continuousAt.comp' ?_) (by simp)
      fun_prop
    exact tendsto_finset_sum Finset.univ (fun i _ => hi i)
  have hE0 : E 0 = 1 := by
    simpa only [E, Complex.ofReal_zero, zero_mul, sub_zero, Complex.normSq_one, div_one] using he
  have hpos : ∀ᶠ r in 𝓝 (0 : ℝ), 0 < E r :=
    hE.eventually_mem (Ioi_mem_nhds (by rw [hE0]; exact zero_lt_one))
  have ha : ∀ᶠ r : ℝ in 𝓝 0, ∀ i, 1 - ((r : ℂ) * p) * a i ≠ 0 := by
    apply Filter.eventually_all.mpr
    intro i
    exact (show ContinuousAt (fun r : ℝ => 1 - ((r : ℂ) * p) * a i) 0 by
      fun_prop).eventually_ne (by simp)
  have hb : ∀ᶠ r : ℝ in 𝓝 0, ∀ i, 1 + ((r : ℂ) * p) * b i ≠ 0 := by
    apply Filter.eventually_all.mpr
    intro i
    exact (show ContinuousAt (fun r : ℝ => 1 + ((r : ℂ) * p) * b i) 0 by
      fun_prop).eventually_ne (by simp)
  have hmin : ∀ᶠ r : ℝ in 𝓝 0, 1 ≤ E r ^ Fintype.card ι *
      ∏ i, Complex.normSq (1 - (r : ℂ) * (p * u i)) := by
    filter_upwards [ha, hb, hpos] with r hra hrb hrE
    rw [hEvalEnergy, hEvalProd]
    rw [hEvalEnergy] at hrE
    exact spectralEnergy_mobius_bound a b U hU η hη hg hgap hmax ((r : ℂ) * p) hra hrb hrE
  simpa only [u, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Complex.normSq_neg, neg_sq]
    using mobius_second_coefficient (Fintype.card ι) Fintype.card_pos u p he hs hc hmin

/-- On a real spectral line through zero, the imaginary direction bounds the
scalar fourth moment by the reciprocal of the matrix order. -/
theorem real_fourth_moment_bound_of_mobius_quadratic (n A : ℝ) (hn : 0 < n)
    (h : ∀ p : ℂ, 0 ≤ n * A * Complex.normSq p + (p ^ 2 * ((2 * n * A - 1 : ℝ) : ℂ)).re) :
    A ≤ n⁻¹ := by
  have hI := h Complex.I
  rw [Complex.I_sq, neg_mul, one_mul, Complex.neg_re, Complex.ofReal_re, Complex.normSq_I, mul_one] at hI
  rw [← one_div]
  apply (le_div_iff₀ hn).mpr
  nlinarith only [hI]

end

end MOC

