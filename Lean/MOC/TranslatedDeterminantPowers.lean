import MOC.Support
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.LinearAlgebra.Matrix.Permanent

/-! A fixed disk center suffices after a common scaling of both spectra.
The second test replaces the maximum matching distance by finite power sums. -/

open Filter BigOperators
open scoped Topology ComplexConjugate

namespace MOC

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

private theorem translated_normSq (r : ℝ) (z : ℂ) :
    Complex.normSq (1 + (r : ℂ) * z) =
      1 + r * (2 * z.re + r * Complex.normSq z) := by
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.one_re,
    Complex.one_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

private theorem matching_bounds_distance (a b : ι → ℂ) (U : Matrix ι ι ℂ)
    (h : Holds a b U) (c : ℂ) :
    ∃ σ, Complex.normSq (determinantValue a b U - c) ≤
      Complex.normSq (matchingProduct a b σ - c) := by
  classical
  obtain ⟨σ, _, hσ⟩ := Finset.exists_max_image Finset.univ
    (fun τ : Equiv.Perm ι => ‖matchingProduct a b τ - c‖) Finset.univ_nonempty
  have hball : determinantValue a b U ∈ Metric.closedBall c ‖matchingProduct a b σ - c‖ := by
    refine convexHull_min (s := Set.range (matchingProduct a b)) ?_ (convex_closedBall _ _) h
    rintro _ ⟨τ, rfl⟩
    exact Metric.mem_closedBall.mpr (by simpa only [dist_eq_norm] using hσ τ (Finset.mem_univ _))
  refine ⟨σ, ?_⟩
  rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq,
    sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)]
  simpa only [Metric.mem_closedBall, dist_eq_norm] using hball

/-- At any positive order it suffices to bound the distance to `-1`.
Both spectra can be restricted to any open disk about zero. -/
theorem conjecture_iff_local_translated_normSq (R : ℝ) (hR : 0 < R) :
    Conjecture ι ↔ ∀ (a b : ι → ℂ) (U : Matrix ι ι ℂ), IsUnitary U →
      (∀ i, ‖a i‖ < R) → (∀ i, ‖b i‖ < R) →
      ∃ σ, Complex.normSq (1 + determinantValue a b U) ≤
        Complex.normSq (1 + matchingProduct a b σ) := by
  classical
  constructor
  · intro h a b U hU _ _
    simpa only [sub_neg_eq_add, add_comm (1 : ℂ)] using
      matching_bounds_distance a b U (h a b U hU) (-1)
  · intro h
    apply conjecture_iff_real_bound.mpr
    intro a b U hU
    by_contra! hbad
    let d := determinantValue a b U
    let p := matchingProduct a b
    let n := Fintype.card ι
    have hn : n ≠ 0 := Fintype.card_ne_zero
    have hgap : ∀ᶠ t : ℝ in 𝓝 0, ∀ σ,
        0 < 2 * (d.re - (p σ).re) + t ^ n * (Complex.normSq d - Complex.normSq (p σ)) := by
      apply Filter.eventually_all.mpr
      intro σ
      have hc : Continuous (fun t : ℝ =>
          2 * (d.re - (p σ).re) + t ^ n * (Complex.normSq d - Complex.normSq (p σ))) := by
        fun_prop
      apply continuousAt_const.eventually_lt hc.continuousAt
      simpa only [zero_pow hn, zero_mul, add_zero] using
        mul_pos (show (0 : ℝ) < 2 by norm_num) (sub_pos.mpr (hbad σ))
    have hsmall (x : ι → ℂ) : ∀ᶠ t : ℝ in 𝓝 0, ∀ i, ‖(t : ℂ) * x i‖ < R := by
      apply Filter.eventually_all.mpr
      intro i
      have hc : Continuous (fun t : ℝ => ‖(t : ℂ) * x i‖) := by fun_prop
      exact hc.continuousAt.eventually_lt continuousAt_const (by simpa using hR)
    have hnear := (hgap.and ((hsmall a).and (hsmall b))).filter_mono
      (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
    obtain ⟨t, ⟨hgt, hat, hbt⟩, ht⟩ := (hnear.and self_mem_nhdsWithin).exists
    have htpos : 0 < t := ht
    obtain ⟨σ, hs⟩ := h (fun i => (t : ℂ) * a i) (fun i => (t : ℂ) * b i) U hU hat hbt
    rw [determinantValue_scale, matchingProduct_scale, ← Complex.ofReal_pow,
      translated_normSq, translated_normSq] at hs
    change 1 + t ^ n * (2 * d.re + t ^ n * Complex.normSq d) ≤
      1 + t ^ n * (2 * (p σ).re + t ^ n * Complex.normSq (p σ)) at hs
    nlinarith only [hs, mul_pos (pow_pos htpos n) (hgt σ)]

private theorem finite_power_sum_test {J : Type*} [Fintype J] [Nonempty J]
    (x : ℝ) (p : J → ℝ) (hx : 0 ≤ x) (hp : ∀ i, 0 ≤ p i) :
    (∃ i, x ≤ p i) ↔ ∀ k : ℕ, x ^ k ≤ ∑ i, p i ^ k := by
  classical
  constructor
  · rintro ⟨i, hi⟩ k
    exact (pow_le_pow_left₀ hx hi k).trans
      (Finset.single_le_sum (fun j _ => pow_nonneg (hp j) k) (Finset.mem_univ i))
  · intro h
    by_contra! hstrict
    obtain ⟨m, _, hmax⟩ := Finset.exists_max_image Finset.univ p Finset.univ_nonempty
    have hxpos := (hp m).trans_lt (hstrict m)
    let N : ℝ := Fintype.card J
    have hN : 0 < N := by
      dsimp [N]
      exact_mod_cast (Fintype.card_pos : 0 < Fintype.card J)
    obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (div_pos zero_lt_one hN)
      ((div_lt_one hxpos).mpr (hstrict m))
    rw [div_pow, div_lt_div_iff₀ (pow_pos hxpos k) hN, one_mul] at hk
    have hsum : (∑ i, p i ^ k) ≤ N * p m ^ k := by
      calc
        _ ≤ ∑ _ : J, p m ^ k := Finset.sum_le_sum fun i _ =>
          pow_le_pow_left₀ (hp i) (hmax i (Finset.mem_univ _)) k
        _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, N]
    linarith only [hk, (h k).trans hsum]

/-- A symmetric sum over permutations gives an equivalent test. Each
exponent is a separate inequality on the same pair of bounded spectra. -/
theorem conjecture_iff_local_translated_power_sums (R : ℝ) (hR : 0 < R) :
    Conjecture ι ↔ ∀ (a b : ι → ℂ) (U : Matrix ι ι ℂ), IsUnitary U →
      (∀ i, ‖a i‖ < R) → (∀ i, ‖b i‖ < R) → ∀ k : ℕ,
      Complex.normSq (1 + determinantValue a b U) ^ k ≤
        ∑ σ : Equiv.Perm ι, Complex.normSq (1 + matchingProduct a b σ) ^ k := by
  rw [conjecture_iff_local_translated_normSq R hR]
  exact forall_congr' fun a => forall_congr' fun b => forall_congr' fun U =>
    forall_congr' fun _ => forall_congr' fun _ => forall_congr' fun _ =>
      finite_power_sum_test _ _ (Complex.normSq_nonneg _) (fun _ => Complex.normSq_nonneg _)

/-- Each mixed moment of the matching values is the permanent of one
matrix of pair sums. Rows index the first spectrum. -/
theorem matching_mixed_moment_eq_permanent (a b : ι → ℂ) (r s : ℕ) :
    (∑ σ, matchingProduct a b σ ^ r * conj (matchingProduct a b σ) ^ s) =
      Matrix.permanent (Matrix.of fun i j => (a i + b j) ^ r * conj (a i + b j) ^ s) := by
  simp only [Matrix.permanent, Matrix.of_apply, matchingProduct, map_prod,
    Finset.prod_mul_distrib, Finset.prod_pow]

/-- The translated power sum can be evaluated using mixed moments of
orders up to `k` in each variable. Each moment is a permanent. -/
theorem translated_matching_power_sum_eq_permanents (a b : ι → ℂ) (k : ℕ) :
    (∑ σ, (Complex.normSq (1 + matchingProduct a b σ) ^ k : ℝ) : ℝ) =
      (∑ r ∈ Finset.range (k + 1), ∑ s ∈ Finset.range (k + 1),
        ((k.choose r : ℂ) * (k.choose s : ℂ)) *
          Matrix.permanent (Matrix.of fun i j => (a i + b j) ^ r * conj (a i + b j) ^ s)).re := by
  classical
  let c (r : ℕ) : ℂ := k.choose r
  let K := Finset.range (k + 1)
  have hbin (z : ℂ) : (1 + z) ^ k = ∑ r ∈ K, z ^ r * c r := by
    rw [add_comm 1 z, add_pow]
    simp only [K, c, one_pow, mul_one]
  have hterm (z : ℂ) : ((Complex.normSq (1 + z) ^ k : ℝ) : ℂ) =
      ∑ r ∈ K, ∑ s ∈ K, c r * c s * (z ^ r * conj z ^ s) := by
    rw [Complex.ofReal_pow, ← Complex.mul_conj, mul_pow, map_add, map_one, hbin, hbin,
      Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro r _
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun s _ => by ring)
  have heq : (∑ σ, ((Complex.normSq (1 + matchingProduct a b σ) ^ k : ℝ) : ℂ)) =
      ∑ r ∈ K, ∑ s ∈ K, c r * c s *
        Matrix.permanent (Matrix.of fun i j => (a i + b j) ^ r * conj (a i + b j) ^ s) := by
    simp_rw [hterm]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro r _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro s _
    rw [← Finset.mul_sum, matching_mixed_moment_eq_permanent]
  simpa only [Complex.re_sum, Complex.ofReal_re, K, c] using congrArg Complex.re heq

end MOC
