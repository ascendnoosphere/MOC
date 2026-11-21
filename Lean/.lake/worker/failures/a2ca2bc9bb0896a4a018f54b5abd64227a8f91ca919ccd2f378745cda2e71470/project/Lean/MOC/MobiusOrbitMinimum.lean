import MOC.SpectralMobius
import Mathlib.Topology.MetricSpace.Bounded

/-! Centering and coercivity of the energy-denominator functional on a
fractional-linear orbit of distinct signed spectral points. -/

open BigOperators Filter
open scoped Topology

namespace MOC

noncomputable section

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- The squared deviations of finitely many points from their mean. -/
def centeredEnergy (u : κ → ℂ) : ℝ :=
  ∑ i, Complex.normSq (u i - (∑ j, u j) / (Fintype.card κ : ℂ))

omit [DecidableEq κ] in
theorem centeredEnergy_nonneg (u : κ → ℂ) : 0 ≤ centeredEnergy u :=
  Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _

omit [DecidableEq κ] in
theorem centeredEnergy_eq_sum_sub_mean [Nonempty κ] (u : κ → ℂ) :
    centeredEnergy u = (∑ i, Complex.normSq (u i)) -
      Complex.normSq (∑ i, u i) / (Fintype.card κ : ℝ) := by
  let z : ℂ := ∑ j, u j
  let N : ℝ := Fintype.card κ
  let μ : ℂ := z / (N : ℂ)
  have hN : N ≠ 0 := Nat.cast_ne_zero.mpr (Fintype.card_ne_zero (α := κ))
  have hsq : Complex.normSq μ = Complex.normSq z / N ^ 2 := by
    dsimp only [μ]
    rw [map_div₀, Complex.normSq_ofReal, sq]
  have hprod : (z * conj μ).re = Complex.normSq z / N := by
    rw [show μ = z / (N : ℂ) by rfl, map_div₀, Complex.conj_ofReal, mul_div_assoc,
      Complex.mul_conj, ← Complex.ofReal_div, Complex.ofReal_re]
  have hre : (∑ i, (u i * conj μ).re) = (z * conj μ).re := by
    dsimp only [z]
    rw [Finset.sum_mul, Complex.re_sum]
  change (∑ i, Complex.normSq (u i - μ)) = _ - Complex.normSq z / N
  simp_rw [Complex.normSq_sub]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, ← Finset.mul_sum, hre, hsq, hprod]
  change (∑ i, Complex.normSq (u i)) + N * (Complex.normSq z / N ^ 2) -
    2 * (Complex.normSq z / N) = _
  field_simp [hN] <;> ring

omit [DecidableEq κ] in
/-- The ordered sum of squared pairwise distances is twice the number of
points times their centered energy. -/
theorem sum_pairwise_normSq_eq_centeredEnergy [Nonempty κ] (u : κ → ℂ) :
    (∑ i, ∑ j, Complex.normSq (u i - u j)) = 2 * (Fintype.card κ : ℝ) * centeredEnergy u := by
  let z : ℂ := ∑ j, u j
  let N : ℝ := Fintype.card κ
  have hN : N ≠ 0 := Nat.cast_ne_zero.mpr (Fintype.card_ne_zero (α := κ))
  have hf : (∑ j, conj (u j)) = conj z := (map_sum conj u Finset.univ).symm
  have hcross : (∑ i, ∑ j, (u i * conj (u j)).re) = Complex.normSq z := by
    have he : (∑ i, ∑ j, u i * conj (u j)) = z * conj z := by
      simp_rw [← Finset.mul_sum]
      rw [← Finset.sum_mul, hf]
    simpa only [Complex.re_sum, Complex.mul_conj, Complex.ofReal_re] using congrArg Complex.re he
  simp_rw [Complex.normSq_sub, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [centeredEnergy_eq_sum_sub_mean]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Finset.mul_sum, hcross]
  change N * (∑ i, Complex.normSq (u i)) + N * (∑ i, Complex.normSq (u i)) -
    2 * Complex.normSq z = 2 * N * ((∑ i, Complex.normSq (u i)) - Complex.normSq z / N)
  field_simp [hN]
  ring

/-- Every pair of points gives a lower bound on the centered energy. -/
theorem pair_normSq_le_two_centeredEnergy (u : κ → ℂ) (i j : κ) :
    Complex.normSq (u i - u j) ≤ 2 * centeredEnergy u := by
  by_cases hij : i = j
  · subst j
    simpa only [sub_self, Complex.normSq_zero] using mul_nonneg zero_le_two (centeredEnergy_nonneg u)
  let μ : ℂ := (∑ k, u k) / (Fintype.card κ : ℂ)
  let v (k : κ) := u k - μ
  have hpair : Complex.normSq (v i) + Complex.normSq (v j) ≤ centeredEnergy u := by
    have h := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ ({i,j} : Finset κ))
      (f := fun k => Complex.normSq (v k)) (fun _ _ _ => Complex.normSq_nonneg _)
    simpa only [Finset.sum_pair hij] using h
  have he : u i - u j = v i - v j := by simp only [v]; ring
  rw [he]
  linarith only [hpair, Complex.normSq_sub (v i) (v j), Complex.normSq_add (v i) (v j),
    Complex.normSq_nonneg (v i + v j)]

/-- Powered centered energy times the squared common denominator for points
written in the difference convention. -/
def mobiusOrbitFunctional (u : κ → ℂ) (n : ℕ) (t : ℂ) : ℝ :=
  centeredEnergy (mobiusSpectrum t u) ^ n * ∏ j, Complex.normSq (1 - t * u j)

/-- The zero anchor contributes the factor one, and its pair with any other
point gives an explicit lower bound even arbitrarily close to a pole. -/
theorem mobiusOrbitFunctional_pole_lower (u : κ → ℂ) (n : ℕ) {i₀ i : κ}
    (h₀ : u i₀ = 0) (hi : i ≠ i₀) (hn : n ≠ 0) {t : ℂ}
    (hreg : ∀ j, 1 - t * u j ≠ 0) :
    (Complex.normSq (u i) / 2) ^ n *
        (∏ j ∈ Finset.univ.erase i, Complex.normSq (1 - t * u j)) /
        Complex.normSq (1 - t * u i) ^ (n - 1) ≤ mobiusOrbitFunctional u n t := by
  let D (j : κ) := Complex.normSq (1 - t * u j)
  have hp : Complex.normSq (u i) / (2 * D i) ≤ centeredEnergy (mobiusSpectrum t u) := by
    have h := pair_normSq_le_two_centeredEnergy (mobiusSpectrum t u) i i₀
    have hz : mobiusSpectrum t u i₀ = 0 := by simp [mobiusSpectrum, h₀]
    rw [hz, sub_zero, mobiusSpectrum, map_div₀] at h
    change Complex.normSq (u i) / D i ≤ 2 * centeredEnergy (mobiusSpectrum t u) at h
    rw [← div_div, div_le_iff₀ zero_lt_two, mul_comm]
    exact h
  have hP : 0 ≤ ∏ j, D j := Finset.prod_nonneg fun _ _ => Complex.normSq_nonneg _
  have hDi : 0 < D i := Complex.normSq_pos.mpr (hreg i)
  have hm := mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (div_nonneg (Complex.normSq_nonneg _) (mul_nonneg zero_le_two hDi.le)) hp n) hP
  have hprod : (∏ j, D j) = D i * ∏ j ∈ Finset.univ.erase i, D j :=
    (Finset.mul_prod_erase _ D (Finset.mem_univ i)).symm
  have hi' : n = (n - 1) + 1 := by omega
  calc
    _ = (Complex.normSq (u i) / (2 * D i)) ^ n * ∏ j, D j := by
      change (Complex.normSq (u i) / 2) ^ n * (∏ j ∈ Finset.univ.erase i, D j) /
        D i ^ (n - 1) = _
      rw [hprod, ← div_div, div_pow, _root_.div_mul_eq_mul_div]
      have hpow : D i ^ n = D i ^ (n - 1) * D i := by
        conv_lhs => rw [hi', pow_succ]
      rw [hpow]
      field_simp [hDi.ne']
    _ ≤ _ := hm

end

end MOC
