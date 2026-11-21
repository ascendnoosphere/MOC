import MOC.SpectralMobius
import Mathlib.Topology.MetricSpace.Bounded

/-! Centering and coercivity of the energy-denominator functional on a
fractional-linear orbit of distinct signed spectral points. -/

open BigOperators Filter
open scoped ComplexConjugate Topology

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
  field_simp [hN] <;> ring

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
    (h₀ : u i₀ = 0) (hn : n ≠ 0) {t : ℂ}
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
    rw [mul_comm 2 (D i), ← div_div, div_le_iff₀ zero_lt_two,
      mul_comm (centeredEnergy (mobiusSpectrum t u)) 2]
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
      rw [hprod, ← div_div, div_pow (Complex.normSq (u i) / 2) (D i) n]
      have hpow : D i ^ n = D i ^ (n - 1) * D i := by
        conv_lhs => rw [hi', pow_succ]
      rw [hpow]
      field_simp [hDi.ne'] <;> ring
    _ ≤ _ := hm

private theorem normSq_denominator_bounds (t x : ℂ) (h : 2 ≤ ‖t‖ * ‖x‖) :
    ‖t‖ ^ 2 * (Complex.normSq x / 4) ≤ Complex.normSq (1 - t * x) ∧
    Complex.normSq (1 - t * x) ≤ 4 * ‖t‖ ^ 2 * Complex.normSq x := by
  have hlow : ‖t‖ * ‖x‖ / 2 ≤ ‖1 - t * x‖ := calc
    _ ≤ ‖t‖ * ‖x‖ - 1 := by linarith only [h]
    _ = ‖t * x‖ - ‖(1 : ℂ)‖ := by rw [norm_mul, norm_one]
    _ ≤ ‖t * x - 1‖ := norm_sub_norm_le _ _
    _ = ‖1 - t * x‖ := norm_sub_rev _ _
  have hhigh : ‖1 - t * x‖ ≤ 2 * (‖t‖ * ‖x‖) := calc
    _ ≤ ‖(1 : ℂ)‖ + ‖t * x‖ := norm_sub_le _ _
    _ ≤ _ := by rw [norm_one, norm_mul]; linarith only [h]
  simp only [Complex.normSq_eq_norm_sq]
  constructor
  · have hs := pow_le_pow_left₀ (by positivity : 0 ≤ ‖t‖ * ‖x‖ / 2) hlow 2
    nlinarith only [hs]
  · have hs := pow_le_pow_left₀ (norm_nonneg _) hhigh 2
    nlinarith only [hs]

/-- Far from zero the functional grows at least as `‖t‖ ^ (2 * (n - 1))`.
The product in the constant runs over all except the zero anchor. -/
theorem mobiusOrbitFunctional_large_lower (u : κ → ℂ) (n : ℕ)
    (hcard : Fintype.card κ = 2 * n) (hn : 2 ≤ n) {i₀ i : κ}
    (h₀ : u i₀ = 0) (hi : i ≠ i₀) (t : ℂ)
    (hlarge : ∀ j, j ≠ i₀ → 2 ≤ ‖t‖ * ‖u j‖) :
    ((∏ j ∈ Finset.univ.erase i₀, Complex.normSq (u j) / 4) / (8 : ℝ)^n) *
      (‖t‖ ^ 2) ^ (n - 1) ≤ mobiusOrbitFunctional u n t := by
  let D (j : κ) := Complex.normSq (1 - t * u j)
  let b : ℝ := ‖t‖ ^ 2
  let S := (Finset.univ : Finset κ).erase i₀
  let C : ℝ := ∏ j ∈ S, Complex.normSq (u j) / 4
  have ht : 0 < ‖t‖ := by
    by_contra! ht
    have h := hlarge i hi
    rw [le_antisymm ht (norm_nonneg _), zero_mul] at h
    norm_num at h
  have hb : 0 < b := pow_pos ht _
  have hu : 0 < Complex.normSq (u i) := by
    apply Complex.normSq_pos.mpr
    intro hz
    have h := hlarge i hi
    norm_num [hz] at h
  have hdp : 0 < D i := (mul_pos hb (div_pos hu (by norm_num))).trans_le
    (normSq_denominator_bounds t (u i) (hlarge i hi)).1
  have he : 1 / (8 * b) ≤ centeredEnergy (mobiusSpectrum t u) := by
    have h := pair_normSq_le_two_centeredEnergy (mobiusSpectrum t u) i i₀
    have hz : mobiusSpectrum t u i₀ = 0 := by simp [mobiusSpectrum, h₀]
    rw [hz, sub_zero, mobiusSpectrum, map_div₀] at h
    change Complex.normSq (u i) / D i ≤ 2 * centeredEnergy (mobiusSpectrum t u) at h
    have hrecip : 1 / (4 * b) ≤ Complex.normSq (u i) / D i := by
      apply (div_le_div_iff₀ (mul_pos (by norm_num) hb) hdp).mpr
      rw [one_mul]
      simpa only [mul_assoc, mul_left_comm, mul_comm] using
        (normSq_denominator_bounds t (u i) (hlarge i hi)).2
    have hfactor : 2 * (1 / (8 * b)) = 1 / (4 * b) := by
      field_simp [hb.ne'] <;> ring
    linarith only [h, hrecip, hfactor]
  have hc : 0 ≤ C := Finset.prod_nonneg fun _ _ => div_nonneg (Complex.normSq_nonneg _) (by norm_num)
  have hd : b ^ (2 * n - 1) * C ≤ ∏ j, D j := by
    have hz : D i₀ = 1 := by simp [D, h₀]
    have hS : S.card = 2 * n - 1 := by simp [S, hcard]
    rw [← Finset.mul_prod_erase Finset.univ D (Finset.mem_univ i₀), hz, one_mul]
    dsimp only [C]
    simpa only [Finset.prod_mul_distrib, Finset.prod_const, hS] using
      Finset.prod_le_prod
        (f := fun j => b * (Complex.normSq (u j) / 4)) (g := D) (s := S)
        (fun _ _ => mul_nonneg hb.le (div_nonneg (Complex.normSq_nonneg _) (by norm_num)))
        (fun j hj => (normSq_denominator_bounds t (u j)
          (hlarge j (Finset.ne_of_mem_erase hj))).1)
  have hn' : n + (n - 1) = 2 * n - 1 := by omega
  change C / (8 : ℝ)^n * b^(n-1) ≤ mobiusOrbitFunctional u n t
  calc
    _ = (1 / (8 * b)) ^ n * (b ^ (2 * n - 1) * C) := by
      rw [one_div_pow, mul_pow, ← hn', pow_add]
      field_simp [hb.ne'] <;> ring
    _ ≤ _ :=
      mul_le_mul (pow_le_pow_left₀ (by positivity) he n) hd
        (mul_nonneg (pow_nonneg hb.le _) hc) (pow_nonneg (centeredEnergy_nonneg _) _)

private theorem denominator_ne_iff (x t : ℂ) (hx : x ≠ 0) :
    1 - t * x ≠ 0 ↔ t ≠ x⁻¹ := by
  apply not_congr
  constructor
  · intro h
    have ht := (sub_eq_zero.mp h).symm
    calc
      t = (t * x) * x⁻¹ := by rw [mul_assoc, mul_inv_cancel₀ hx, mul_one]
      _ = x⁻¹ := by rw [ht, one_mul]
  · intro h
    rw [h, inv_mul_cancel₀ hx, sub_self]

private theorem continuous_normSq_denominator (x : ℂ) :
    Continuous (fun t : ℂ => Complex.normSq (1 - t * x)) :=
  Complex.continuous_normSq.comp (continuous_const.sub (continuous_id.mul continuous_const))

/-- A simple pole of a distinct family has infinite centered orbit energy
as soon as the energy is raised to a power of at least two. -/
theorem tendsto_mobiusOrbitFunctional_pole (u : κ → ℂ) (n : ℕ) (hn : 2 ≤ n)
    {i₀ i : κ} (h₀ : u i₀ = 0) (hinj : Function.Injective u) (hi : u i ≠ 0) :
    Tendsto (mobiusOrbitFunctional u n) (𝓝[≠] (u i)⁻¹) atTop := by
  let p := (u i)⁻¹
  let D (j : κ) (t : ℂ) := Complex.normSq (1 - t * u j)
  let P (t : ℂ) := ∏ j ∈ Finset.univ.erase i, D j t
  let c : ℝ := (Complex.normSq (u i) / 2) ^ n
  have hval (j : κ) (hj : j ≠ i) : 1 - p * u j ≠ 0 := by
    intro h
    have he : p * u j = 1 := (sub_eq_zero.mp h).symm
    apply hj
    apply hinj
    calc
      u j = u i * (p * u j) := by
        rw [← mul_assoc]
        simp [p, mul_inv_cancel₀ hi]
      _ = u i := by rw [he, mul_one]
  have hne : ∀ᶠ t : ℂ in 𝓝[≠] p, t ≠ p := self_mem_nhdsWithin
  have hreg : ∀ᶠ t : ℂ in 𝓝[≠] p, ∀ j, 1 - t * u j ≠ 0 := by
    apply Filter.eventually_all.mpr
    intro j
    by_cases hj : j = i
    · subst j
      exact hne.mono fun t ht => (denominator_ne_iff _ _ hi).mpr ht
    · have hc : Continuous (fun t : ℂ => 1 - t * u j) :=
        continuous_const.sub (continuous_id.mul continuous_const)
      exact (hc.continuousAt.eventually_ne (hval j hj)).filter_mono nhdsWithin_le_nhds
  have hzero : D i p = 0 := by simp [D, p, inv_mul_cancel₀ hi, Complex.normSq_zero]
  have hD : Tendsto (D i) (𝓝[≠] p) (𝓝[>] (0 : ℝ)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · rw [← hzero]
      exact (continuous_normSq_denominator (u i)).continuousAt.continuousWithinAt
    · exact hreg.mono fun t ht => Complex.normSq_pos.mpr (ht i)
  have hP : Continuous P := continuous_finset_prod _ fun j _ => continuous_normSq_denominator (u j)
  have hPpos : 0 < P p := Finset.prod_pos fun j hj =>
    Complex.normSq_pos.mpr (hval j (Finset.ne_of_mem_erase hj))
  have hnearp : ∀ᶠ t in 𝓝[≠] p, P p / 2 < P t :=
    (hP.continuousAt.eventually_mem (Ioi_mem_nhds (by linarith only [hPpos]))).filter_mono
      nhdsWithin_le_nhds
  have hc : 0 < c := pow_pos (div_pos (Complex.normSq_pos.mpr hi) zero_lt_two) _
  have hlim : Tendsto (fun t => ((D i t)⁻¹) ^ (n - 1)) (𝓝[≠] p) atTop :=
    (tendsto_pow_atTop (by omega : n - 1 ≠ 0)).comp (tendsto_inv_nhdsGT_zero.comp hD)
  apply tendsto_atTop_mono' _ ?_ (hlim.const_mul_atTop (mul_pos hc (half_pos hPpos)))
  filter_upwards [hreg, hnearp] with t ht hpt
  change (c * (P p / 2)) * ((D i t)⁻¹) ^ (n - 1) ≤ _
  calc
    _ ≤ (c * P t) * ((D i t)⁻¹) ^ (n - 1) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpt.le hc.le)
        (pow_nonneg (inv_nonneg.mpr (Complex.normSq_nonneg _)) _)
    _ = (c * P t) / D i t ^ (n - 1) := by rw [← inv_pow, ← div_eq_mul_inv]
    _ ≤ _ := mobiusOrbitFunctional_pole_lower u n (i := i) h₀ (by omega) ht

/-- With one zero anchor and exactly `2n` distinct points, infinity is
another end at which the orbit functional diverges. -/
theorem tendsto_mobiusOrbitFunctional_cocompact (u : κ → ℂ) (n : ℕ)
    (hcard : Fintype.card κ = 2 * n) (hn : 2 ≤ n) {i₀ : κ}
    (h₀ : u i₀ = 0) (hinj : Function.Injective u) :
    Tendsto (mobiusOrbitFunctional u n) (cocompact ℂ) atTop := by
  let C : ℝ := (∏ j ∈ Finset.univ.erase i₀, Complex.normSq (u j) / 4) / (8 : ℝ)^n
  have hnonzero (j : κ) (hj : j ≠ i₀) : u j ≠ 0 := fun he => hj (hinj (he.trans h₀.symm))
  have hC : 0 < C := div_pos (Finset.prod_pos fun j hj =>
    div_pos (Complex.normSq_pos.mpr (hnonzero j (Finset.ne_of_mem_erase hj))) (by norm_num))
    (by positivity)
  obtain ⟨i, hi⟩ := Fintype.exists_ne_of_one_lt_card (by rw [hcard]; omega) i₀
  have hlarge : ∀ᶠ t : ℂ in cocompact ℂ, ∀ j, j ≠ i₀ → 2 ≤ ‖t‖ * ‖u j‖ := by
    apply Filter.eventually_all.mpr
    intro j
    by_cases hj : j = i₀
    · exact Filter.Eventually.of_forall fun _ h => (h hj).elim
    · have hu : 0 < ‖u j‖ := norm_pos_iff.mpr (hnonzero j hj)
      exact ((tendsto_atTop.1 (tendsto_norm_cocompact_atTop (E := ℂ))) (2 / ‖u j‖)).mono
        fun t ht _ => (div_le_iff₀ hu).mp ht
  have hlim : Tendsto (fun t : ℂ => (‖t‖ ^ 2) ^ (n - 1)) (cocompact ℂ) atTop := by
    simp only [← pow_mul]
    exact (tendsto_pow_atTop (by omega : 2 * (n - 1) ≠ 0)).comp tendsto_norm_cocompact_atTop
  exact tendsto_atTop_mono' _
    (hlarge.mono fun t ht => mobiusOrbitFunctional_large_lower u n hcard hn h₀ hi t ht)
    (hlim.const_mul_atTop hC)

private theorem continuousAt_mobiusOrbitFunctional (u : κ → ℂ) (n : ℕ) (t : ℂ)
    (ht : ∀ j, 1 - t * u j ≠ 0) : ContinuousAt (mobiusOrbitFunctional u n) t := by
  let v (i : κ) (s : ℂ) := mobiusSpectrum s u i
  have hv (i : κ) : ContinuousAt (v i) t := by
    have hc : Continuous (fun s : ℂ => 1 - s * u i) :=
      continuous_const.sub (continuous_id.mul continuous_const)
    exact continuousAt_const.div hc.continuousAt (ht i)
  have hs : ContinuousAt (fun s : ℂ => ∑ j, v j s) t := by
    exact tendsto_finset_sum _ fun j _ => hv j
  have hm := hs.div_const (Fintype.card κ : ℂ)
  have he : ContinuousAt (fun s => centeredEnergy (mobiusSpectrum s u)) t := by
    unfold centeredEnergy
    exact tendsto_finset_sum _ fun i _ => Complex.continuous_normSq.continuousAt.comp ((hv i).sub hm)
  have hd : Continuous (fun s : ℂ => ∏ j, Complex.normSq (1 - s * u j)) :=
    continuous_finset_prod _ fun j _ => continuous_normSq_denominator (u j)
  exact (he.pow n).mul hd.continuousAt

/-- A distinct signed family of size `2n` with a zero anchor has a
Möbius parameter minimizing its centered orbit functional away from all poles. -/
theorem exists_mobiusOrbitFunctional_minimizer (u : κ → ℂ) (n : ℕ)
    (hcard : Fintype.card κ = 2 * n) (hn : 2 ≤ n) {i₀ : κ}
    (h₀ : u i₀ = 0) (hinj : Function.Injective u) :
    ∃ t : ℂ, (∀ j, 1 - t * u j ≠ 0) ∧
      ∀ s : ℂ, (∀ j, 1 - s * u j ≠ 0) → mobiusOrbitFunctional u n t ≤ mobiusOrbitFunctional u n s := by
  let f := mobiusOrbitFunctional u n
  let K : Set ℂ := {t | (∀ j, 1 - t * u j ≠ 0) ∧ f t ≤ f 0}
  have hKclosed : IsClosed K := isClosed_of_closure_subset fun t ht => by
    have hf := mem_closure_iff_frequently.mp ht
    by_cases hr : ∀ j, 1 - t * u j ≠ 0
    · refine ⟨hr, le_of_not_gt ?_⟩
      intro hgt
      have he := (continuousAt_mobiusOrbitFunctional u n t hr).eventually_mem (Ioi_mem_nhds hgt)
      obtain ⟨s, hs, hs'⟩ := (hf.and_eventually he).exists
      exact (not_lt_of_ge hs.2) hs'
    · push_neg at hr
      obtain ⟨i, hi⟩ := hr
      have hnz : u i ≠ 0 := by
        intro hz
        simp [hz] at hi
      have htinv : t = (u i)⁻¹ := by
        by_contra h
        exact (denominator_ne_iff _ _ hnz).mpr h hi
      have hnot : t ∉ K := fun h => h.1 i hi
      have hfne : ∃ᶠ s in 𝓝[≠] t, s ∈ K :=
        frequently_nhdsWithin_iff.mpr (hf.mono fun s hs => ⟨hs, fun h => hnot (h ▸ hs)⟩)
      have hlim : Tendsto f (𝓝[≠] t) atTop := by
        rw [htinv]
        exact tendsto_mobiusOrbitFunctional_pole u n hn h₀ hinj hnz
      obtain ⟨s, hs, hgt⟩ := (hfne.and_eventually ((tendsto_atTop.1 hlim) (f 0 + 1))).exists
      exact False.elim (by linarith only [hs.2, hgt])
  have hlim : Tendsto f (cocompact ℂ) atTop :=
    tendsto_mobiusOrbitFunctional_cocompact u n hcard hn h₀ hinj
  have hcompl : Kᶜ ∈ cocompact ℂ := ((tendsto_atTop.1 hlim) (f 0 + 1)).mono fun t ht htK =>
    (not_lt_of_ge htK.2) (by linarith only [ht])
  obtain ⟨L, hL, hKL⟩ := mem_cocompact'.mp hcompl
  have hK : IsCompact K := hL.of_isClosed_subset hKclosed (by simpa only [compl_compl] using hKL)
  have h0K : (0 : ℂ) ∈ K := ⟨by simp, le_rfl⟩
  have hc : ContinuousOn f K :=
    fun t ht => (continuousAt_mobiusOrbitFunctional u n t ht.1).continuousWithinAt
  obtain ⟨t, ht, hmin⟩ := hK.exists_isMinOn ⟨0, h0K⟩ hc
  refine ⟨t, ht.1, fun s hs => ?_⟩
  by_cases hsK : f s ≤ f 0
  · exact hmin ⟨hs,hsK⟩
  · exact ht.2.trans (le_of_lt (lt_of_not_ge hsK))

end

end MOC
