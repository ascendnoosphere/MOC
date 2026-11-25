import MOC.SpectralMobius
import MOC.SpectralPerturbation
import MOC.SpectralSecondVariation
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
    rw [show μ = z / (N : ℂ) by rfl, map_div₀, Complex.conj_ofReal, ← mul_div_assoc,
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
    _ = (c * P t) / D i t ^ (n - 1) := by rw [inv_pow, ← div_eq_mul_inv]
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

omit [DecidableEq κ] in
/-- Centering removes translations and transforms squared energy by the
squared norm of a common complex multiplier. -/
theorem centeredEnergy_affine [Nonempty κ] (u : κ → ℂ) (a b : ℂ) :
    centeredEnergy (fun i => a * u i + b) = Complex.normSq a * centeredEnergy u := by
  let N : ℂ := Fintype.card κ
  have hN : N ≠ 0 := Nat.cast_ne_zero.mpr (Fintype.card_ne_zero (α := κ))
  have hm : (∑ i, (a * u i + b)) / N = a * ((∑ i, u i) / N) + b := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul]
    change (a * (∑ i, u i) + N * b) / N = _
    field_simp [hN] <;> ring
  unfold centeredEnergy
  change (∑ i, Complex.normSq (a * u i + b - (∑ j, (a * u j + b)) / N)) =
    Complex.normSq a * ∑ i, Complex.normSq (u i - (∑ j, u j) / N)
  rw [hm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Complex.normSq_mul]
  congr 1
  ring

private theorem mobius_denominator_rebase (x t s m : ℂ)
    (ht : 1 - t * x ≠ 0) (hScale : 1 + s * m ≠ 0) :
    let scale := 1 + s * m
    let q := t + s / scale
    1 - s * (x / (1 - t * x) - m) = scale * (1 - q * x) / (1 - t * x) := by
  dsimp only
  field_simp [ht, hScale] <;> ring

/-- In the rebased chart, each Möbius point is an affine image of the
corresponding point in the original chart. -/
private theorem mobius_point_rebase (x t s m : ℂ)
    (ht : 1 - t * x ≠ 0) (hScale : 1 + s * m ≠ 0)
    (hs : 1 - s * (x / (1 - t * x) - m) ≠ 0) :
    let scale := 1 + s * m
    let q := t + s / scale
    (x / (1 - t * x) - m) / (1 - s * (x / (1 - t * x) - m)) =
      (scale ^ 2)⁻¹ * (x / (1 - q * x)) - m / scale := by
  intro scale q
  have hscale : scale ≠ 0 := hScale
  have hd : 1 - s * (x / (1 - t * x) - m) = scale * (1 - q * x) / (1 - t * x) :=
    mobius_denominator_rebase x t s m ht hScale
  have hq : 1 - q * x ≠ 0 := by
    intro he
    apply hs
    rw [hd, he, mul_zero, zero_div]
  calc
    _ = (x - m * (1 - t * x)) / (scale * (1 - q * x)) := by
      rw [hd]
      field_simp [ht, hscale, hq] <;> ring
    _ = _ := by
      field_simp [hscale, hq]
      dsimp only [q, scale]
      field_simp [hScale] <;> ring

/-- With `2n` signed points, the affine multiplier and the new
denominator cancel exactly in the rebased energy-denominator functional. -/
theorem mobiusOrbitFunctional_rebase [Nonempty κ] (u : κ → ℂ) (n : ℕ)
    (hcard : Fintype.card κ = 2 * n) (t s m : ℂ)
    (ht : ∀ j, 1 - t * u j ≠ 0) (hScale : 1 + s * m ≠ 0)
    (hs : ∀ j, 1 - s * (mobiusSpectrum t u j - m) ≠ 0) :
    let v (j : κ) := mobiusSpectrum t u j - m
    let q := t + s / (1 + s * m)
    mobiusOrbitFunctional v n s * (∏ j, Complex.normSq (1 - t * u j)) =
      mobiusOrbitFunctional u n q := by
  intro v q
  let scale : ℂ := 1 + s * m
  let L := Complex.normSq scale
  let Dt := ∏ j, Complex.normSq (1 - t * u j)
  let Dq := ∏ j, Complex.normSq (1 - q * u j)
  let E := centeredEnergy (mobiusSpectrum q u)
  have hL : L ≠ 0 := (Complex.normSq_pos.mpr hScale).ne'
  have hDt : Dt ≠ 0 := Finset.prod_ne_zero_iff.mpr fun j _ => (Complex.normSq_pos.mpr (ht j)).ne'
  have hden (j : κ) : 1 - s * v j = scale * (1 - q * u j) / (1 - t * u j) :=
    mobius_denominator_rebase (u j) t s m (ht j) hScale
  have htrans : mobiusSpectrum s v =
      fun j => (scale ^ 2)⁻¹ * mobiusSpectrum q u j + (-(m / scale)) := by
    funext j
    simpa only [mobiusSpectrum, v, sub_eq_add_neg] using
      (mobius_point_rebase (u j) t s m (ht j) hScale (hs j))
  have hE : centeredEnergy (mobiusSpectrum s v) = (L ^ 2)⁻¹ * E := by
    rw [htrans, centeredEnergy_affine, map_inv₀, map_pow]
  have hD : (∏ j, Complex.normSq (1 - s * v j)) = L ^ (2 * n) * Dq / Dt := by
    simp_rw [hden, map_div₀, Complex.normSq_mul, Finset.prod_div_distrib,
      Finset.prod_mul_distrib]
    rw [Finset.prod_const, Finset.card_univ, hcard]
  change centeredEnergy (mobiusSpectrum s v) ^ n *
    (∏ j, Complex.normSq (1 - s * v j)) * Dt = E ^ n * Dq
  rw [hE, hD, mul_assoc, div_mul_cancel₀ _ hDt, mul_pow]
  calc
    _ = ((L ^ 2)⁻¹ ^ n * L ^ (2 * n)) * (E ^ n * Dq) := by ring
    _ = _ := by
      rw [inv_pow, ← pow_mul, inv_mul_cancel₀ (pow_ne_zero _ hL), one_mul]

private theorem mobiusOrbitFunctional_scale [Nonempty κ] (u : κ → ℂ) (n : ℕ) (r t : ℂ) :
    mobiusOrbitFunctional (fun j => r * u j) n t =
      Complex.normSq r ^ n * mobiusOrbitFunctional u n (t * r) := by
  have he : mobiusSpectrum t (fun j => r * u j) =
      fun j => r * mobiusSpectrum (t * r) u j + 0 := by
    funext j
    simp only [mobiusSpectrum, mul_assoc, mul_div_assoc, add_zero]
  unfold mobiusOrbitFunctional
  rw [he, centeredEnergy_affine, mul_pow, mul_assoc]
  simp only [mul_assoc]

/-- A minimum in the original orbit becomes a local minimum at zero after
rebasing at the minimizing parameter and applying any translation. -/
theorem mobiusOrbitFunctional_rebase_isLocalMin [Nonempty κ] (u : κ → ℂ) (n : ℕ)
    (hcard : Fintype.card κ = 2 * n) (t m : ℂ)
    (ht : ∀ j, 1 - t * u j ≠ 0)
    (hmin : ∀ q : ℂ, (∀ j, 1 - q * u j ≠ 0) →
      mobiusOrbitFunctional u n t ≤ mobiusOrbitFunctional u n q) :
    IsLocalMin (mobiusOrbitFunctional (fun j => mobiusSpectrum t u j - m) n) 0 := by
  let v (j : κ) := mobiusSpectrum t u j - m
  let Dt := ∏ j, Complex.normSq (1 - t * u j)
  have hDt : 0 < Dt := Finset.prod_pos fun j _ => Complex.normSq_pos.mpr (ht j)
  have hbase : mobiusOrbitFunctional v n 0 * Dt = mobiusOrbitFunctional u n t := by
    simpa only [zero_mul, add_zero, zero_div] using
      mobiusOrbitFunctional_rebase u n hcard t 0 m ht (by simp) (by simp)
  have hScale : ∀ᶠ s : ℂ in 𝓝 0, 1 + s * m ≠ 0 := by
    have hc : Continuous (fun s : ℂ => 1 + s * m) :=
      continuous_const.add (continuous_id.mul continuous_const)
    exact hc.continuousAt.eventually_ne (by simp)
  have hs : ∀ᶠ s : ℂ in 𝓝 0, ∀ j, 1 - s * v j ≠ 0 := by
    apply Filter.eventually_all.mpr
    intro j
    have hc : Continuous (fun s : ℂ => 1 - s * v j) :=
      continuous_const.sub (continuous_id.mul continuous_const)
    exact hc.continuousAt.eventually_ne (by simp)
  filter_upwards [hScale, hs] with s hsScale hvs
  let q := t + s / (1 + s * m)
  have hq (j : κ) : 1 - q * u j ≠ 0 := by
    intro he
    have hden : 1 - s * v j = (1 + s * m) * (1 - q * u j) / (1 - t * u j) :=
      mobius_denominator_rebase (u j) t s m (ht j) hsScale
    apply hvs j
    rw [hden, he, mul_zero, zero_div]
  change mobiusOrbitFunctional v n 0 ≤ mobiusOrbitFunctional v n s
  apply (mul_le_mul_right hDt).mp
  rw [hbase, mobiusOrbitFunctional_rebase u n hcard t s m ht hsScale hvs]
  exact hmin q hq

private theorem orbit_line_hasDerivAt (f : ℝ → ℂ) (d : ℂ) (h : HasDerivAt f d 0) :
    HasDerivAt (fun t => Complex.normSq (f t)) (2 * (d * conj (f 0)).re) 0 := by
  have hr := Complex.reCLM.hasFDerivAt.comp_hasDerivAt 0 h
  have hi := Complex.imCLM.hasFDerivAt.comp_hasDerivAt 0 h
  have he : d.re * (f 0).re + (f 0).re * d.re +
      (d.im * (f 0).im + (f 0).im * d.im) = 2 * (d * conj (f 0)).re := by
    simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
    ring
  simpa only [Function.comp_apply, Complex.reCLM_apply, Complex.imCLM_apply,
    Complex.normSq_apply, he] using (hr.mul hr).add (hi.mul hi)

private theorem mobius_on_real_line_hasDerivAt (z k : ℂ) :
    HasDerivAt (fun t : ℝ => z / (1 - ((t : ℂ) * k) * z)) (z * (k * z)) 0 := by
  have h : HasDerivAt (fun w : ℂ => 1 - (w * k) * z) (-(k * z)) 0 := by
    simpa only [one_mul, id_eq] using (((hasDerivAt_id (0 : ℂ)).mul_const k).mul_const z).const_sub 1
  have hd : HasDerivAt (fun w : ℂ => z / (1 - (w * k) * z)) (z * (k * z)) ((0 : ℝ) : ℂ) := by
    have hc := (hasDerivAt_const (0 : ℂ) z).div h (by simp)
    simpa only [Complex.ofReal_zero, zero_mul, sub_zero, one_pow, mul_neg, sub_neg_eq_add,
      zero_add, div_one] using hc
  exact hd.comp_ofReal

private theorem centeredEnergy_mobius_on_real_line_hasDerivAt [Nonempty κ]
    (u : κ → ℂ) (hmean : (∑ j, u j) = 0) (k : ℂ) :
    HasDerivAt (fun t : ℝ => centeredEnergy (mobiusSpectrum ((t : ℂ) * k) u))
      (2 * (k * ∑ j, (Complex.normSq (u j) : ℂ) * u j).re) 0 := by
  let v (t : ℝ) := mobiusSpectrum ((t : ℂ) * k) u
  have h0 : v 0 = u := by simp [v]
  have hv (j : κ) : HasDerivAt (fun t => v t j) (u j * (k * u j)) 0 :=
    mobius_on_real_line_hasDerivAt (u j) k
  have hs (j : κ) : HasDerivAt (fun t => Complex.normSq (v t j))
      (2 * (k * ((Complex.normSq (u j) : ℂ) * u j)).re) 0 := by
    have h := orbit_line_hasDerivAt _ _ (hv j)
    have he : (u j * (k * u j)) * conj (u j) = k * ((Complex.normSq (u j) : ℂ) * u j) := by
      rw [← Complex.mul_conj]
      ring
    simpa only [h0, he] using h
  have hsum : HasDerivAt (fun t => ∑ j, Complex.normSq (v t j))
      (2 * (k * ∑ j, (Complex.normSq (u j) : ℂ) * u j).re) 0 := by
    simpa only [Finset.mul_sum, Complex.re_sum] using
      HasDerivAt.sum (u := Finset.univ) (fun j _ => hs j)
  have hm : HasDerivAt (fun t => Complex.normSq (∑ j, v t j) / (Fintype.card κ : ℝ)) 0 0 := by
    have hf := HasDerivAt.sum (u := Finset.univ) (fun j _ => hv j)
    have hd := (orbit_line_hasDerivAt _ _ hf).div_const (Fintype.card κ : ℝ)
    simpa only [h0, hmean, map_zero, mul_zero, Complex.zero_re, zero_div] using hd
  simpa only [centeredEnergy_eq_sum_sub_mean, sub_zero, v] using hsum.sub hm

private theorem denominatorEnergy_mobius_on_real_line_hasDerivAt (u : κ → ℂ)
    (hmean : (∑ j, u j) = 0) (k : ℂ) :
    HasDerivAt (fun t : ℝ => ∏ j, Complex.normSq (1 - ((t : ℂ) * k) * u j)) 0 0 := by
  have hc : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 0 := by
    simpa only [Complex.ofRealCLM_apply, Complex.ofReal_one] using
      (Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ)))
  have hd (j : κ) : HasDerivAt (fun t : ℝ => 1 - ((t : ℂ) * k) * u j) (-(k * u j)) 0 := by
    simpa only [one_mul] using ((hc.mul_const k).mul_const (u j)).const_sub 1
  have hf : HasDerivAt (fun t : ℝ => ∏ j, (1 - ((t : ℂ) * k) * u j)) 0 0 := by
    simpa only [Finset.prod_apply, Complex.ofReal_zero, zero_mul, sub_zero, Finset.prod_const_one,
      one_smul, Finset.sum_neg_distrib, ← Finset.mul_sum, hmean, mul_zero, neg_zero] using
      HasDerivAt.finset_prod (u := Finset.univ) (fun j _ => hd j)
  simpa only [map_prod, zero_mul, Complex.zero_re, mul_zero] using orbit_line_hasDerivAt _ _ hf

/-- At a centered, positive-energy local minimum in its own Möbius chart,
the squared-norm-weighted first moment vanishes. -/
theorem sum_cubic_eq_zero_at_mobiusOrbitLocalMin [Nonempty κ] (u : κ → ℂ) (n : ℕ)
    (hn : n ≠ 0) (hmean : (∑ j, u j) = 0) (hpos : 0 < centeredEnergy u)
    (hmin : IsLocalMin (mobiusOrbitFunctional u n) 0) :
    (∑ j, (Complex.normSq (u j) : ℂ) * u j) = 0 := by
  let z : ℂ := ∑ j, (Complex.normSq (u j) : ℂ) * u j
  have hz (k : ℂ) : (k * z).re = 0 := by
    let p (t : ℝ) : ℂ := (t : ℂ) * k
    have hp : p 0 = 0 := by simp [p]
    have hc : ContinuousAt p 0 := (Complex.continuous_ofReal.mul continuous_const).continuousAt
    have hlocal : IsLocalMin (fun t => mobiusOrbitFunctional u n (p t)) 0 := by
      have hbase : IsLocalMin (mobiusOrbitFunctional u n) (p 0) := by
        simpa only [hp] using hmin
      exact hbase.comp_continuous hc
    have he := centeredEnergy_mobius_on_real_line_hasDerivAt u hmean k
    have hD := denominatorEnergy_mobius_on_real_line_hasDerivAt u hmean k
    have hDeriv : HasDerivAt (fun t => mobiusOrbitFunctional u n (p t))
        ((n : ℝ) * centeredEnergy u ^ (n - 1) * (2 * (k * z).re)) 0 := by
      simpa only [p, mobiusOrbitFunctional, Complex.ofReal_zero, zero_mul, sub_zero,
        mobiusSpectrum_zero, Complex.normSq_one, Finset.prod_const_one, mul_one, mul_zero,
        add_zero, z] using (he.pow (n := n)).mul hD
    have hd := hlocal.hasDerivAt_eq_zero hDeriv
    have hcoef : 0 < (n : ℝ) * centeredEnergy u ^ (n - 1) :=
      mul_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)) (pow_pos hpos _)
    exact (mul_eq_zero.mp ((mul_eq_zero.mp hd).resolve_left hcoef.ne')).resolve_left two_ne_zero
  apply Complex.ext
  · simpa [z] using hz 1
  · simpa [z, Complex.mul_re] using hz Complex.I

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- A regular strict support violation has a representative in its Möbius
orbit with unit energy and equal ordinary and cubic moments. Zero is a local
minimum in the representative's chart, and the relative eigenbasis and
distinct matching products are preserved. -/
theorem exists_mobius_balanced_support_violation (hn : 2 ≤ Fintype.card ι)
    (a b : ι → ℂ) (U : Matrix ι ι ℂ) (hU : IsUnitary U) (η : ℂ)
    (hsigned : Function.Injective (Sum.elim a (fun j => -b j)))
    (hmatch : Function.Injective (matchingProduct a b))
    (hbad : ∀ σ : Equiv.Perm ι,
      (η * matchingProduct a b σ).re < (η * determinantValue a b U).re) :
    ∃ (c d : ι → ℂ) (k : ℂ),
      Function.Injective (Sum.elim c (fun j => -d j)) ∧
      Function.Injective (matchingProduct c d) ∧ spectralEnergy c d = 1 ∧
      (∑ i, c i) = ∑ j, d j ∧
      (∑ i, (Complex.normSq (c i) : ℂ) * c i) = ∑ j, (Complex.normSq (d j) : ℂ) * d j ∧
      IsLocalMin (mobiusOrbitFunctional (Sum.elim c (fun j => -d j)) (Fintype.card ι)) 0 ∧
      ∀ σ : Equiv.Perm ι,
        (k * matchingProduct c d σ).re < (k * determinantValue c d U).re := by
  let n := Fintype.card ι
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  let s : ℂ := -a i₀
  let a₀ (i : ι) := a i + s
  let b₀ (j : ι) := b j - s
  let u : ι ⊕ ι → ℂ := Sum.elim a₀ (fun j => -b₀ j)
  have hu (j : ι ⊕ ι) : u j = Sum.elim a (fun j => -b j) j + s := by
    cases j <;> simp [u, a₀, b₀, sub_eq_add_neg, add_comm]
  have huinj : Function.Injective u := by
    intro i j h
    apply hsigned
    rw [hu i, hu j] at h
    exact add_right_cancel h
  have hcard : Fintype.card (ι ⊕ ι) = 2 * n := by
    rw [Fintype.card_sum, two_mul]
  have h₀ : u (Sum.inl i₀) = 0 := by simp [u, a₀, s]
  obtain ⟨t, ht, hmin⟩ := exists_mobiusOrbitFunctional_minimizer u n hcard hn h₀ huinj
  let m : ℂ := (∑ j, mobiusSpectrum t u j) / (Fintype.card (ι ⊕ ι) : ℂ)
  let v (j : ι ⊕ ι) := mobiusSpectrum t u j - m
  have hN : (Fintype.card (ι ⊕ ι) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hmean : (∑ j, v j) = 0 := by
    dsimp only [v]
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    dsimp only [m]
    field_simp [hN] <;> ring
  have hvinj : Function.Injective v := by
    intro i j h
    apply huinj
    have hd : mobiusSpectrum t u i = mobiusSpectrum t u j := add_right_cancel (by
      simpa only [v, sub_eq_add_neg] using h)
    change u i / (1 - t * u i) = u j / (1 - t * u j) at hd
    have he := (div_eq_div_iff (ht i) (ht j)).mp hd
    apply sub_eq_zero.mp
    calc
      u i - u j = u i * (1 - t * u j) - u j * (1 - t * u i) := by ring
      _ = 0 := sub_eq_zero.mpr he
  let E := centeredEnergy v
  have hE : 0 < E := by
    have hne : v (Sum.inl i₀) ≠ v (Sum.inr i₀) := fun h => by cases hvinj h
    have hp := Complex.normSq_pos.mpr (sub_ne_zero.mpr hne)
    have hle := pair_normSq_le_two_centeredEnergy v (Sum.inl i₀) (Sum.inr i₀)
    change _ ≤ 2 * E at hle
    linarith only [hp, hle]
  have hminV : IsLocalMin (mobiusOrbitFunctional v n) 0 :=
    mobiusOrbitFunctional_rebase_isLocalMin u n hcard t m ht hmin
  have hcubic := sum_cubic_eq_zero_at_mobiusOrbitLocalMin v n
    (zero_lt_two.trans_le hn).ne' hmean hE hminV
  let r : ℝ := (Real.sqrt E)⁻¹
  have hr : r ≠ 0 := inv_ne_zero (Real.sqrt_pos_of_pos hE).ne'
  have hrsq : r ^ 2 = E⁻¹ := by rw [show r = (Real.sqrt E)⁻¹ by rfl, inv_pow, Real.sq_sqrt hE.le]
  let w (j : ι ⊕ ι) := (r : ℂ) * v j
  have hminW : IsLocalMin (mobiusOrbitFunctional w n) 0 := by
    have hc : ContinuousAt (fun s : ℂ => s * (r : ℂ)) 0 :=
      (continuous_id.mul continuous_const).continuousAt
    have hbase : IsLocalMin (mobiusOrbitFunctional v n) ((0 : ℂ) * (r : ℂ)) := by
      simpa only [zero_mul] using hminV
    have hlocal : IsLocalMin (fun s : ℂ => mobiusOrbitFunctional v n (s * (r : ℂ))) 0 :=
      IsLocalMin.comp_continuous (g := fun s : ℂ => s * (r : ℂ)) (b := 0) hbase hc
    filter_upwards [hlocal] with s hs
    change mobiusOrbitFunctional w n 0 ≤ mobiusOrbitFunctional w n s
    rw [mobiusOrbitFunctional_scale v n (r : ℂ) 0, mobiusOrbitFunctional_scale v n (r : ℂ) s]
    exact mul_le_mul_of_nonneg_left hs (pow_nonneg (Complex.normSq_nonneg _) _)
  let c (i : ι) := mobiusSpectrum t a₀ i + (-m)
  let d (j : ι) := mobiusSpectrum (-t) b₀ j - (-m)
  have ha (i : ι) : 1 - t * a₀ i ≠ 0 := ht (Sum.inl i)
  have hb (j : ι) : 1 + t * b₀ j ≠ 0 := by
    simpa only [u, Sum.elim_inr, mul_neg, sub_neg_eq_add] using ht (Sum.inr j)
  have hleft (i : ι) : v (Sum.inl i) = c i := sub_eq_add_neg _ _
  have hright (j : ι) : v (Sum.inr j) = -d j := by
    change (-b₀ j) / (1 - t * (-b₀ j)) - m = -(b₀ j / (1 - (-t) * b₀ j) - (-m))
    rw [mul_neg, neg_mul, neg_div]
    ring
  let c' (i : ι) := (r : ℂ) * c i
  let d' (j : ι) := (r : ℂ) * d j
  have hw : w = Sum.elim c' (fun j => -d' j) := by
    funext j
    cases j with
    | inl i => simp only [w, hleft, Sum.elim_inl, c']
    | inr j => simp only [w, hright, mul_neg, Sum.elim_inr, d']
  have hEcd : spectralEnergy c d = E := by
    have he := centeredEnergy_eq_sum_sub_mean v
    rw [hmean, Complex.normSq_zero, zero_div, sub_zero] at he
    simpa only [Fintype.sum_sum_type, hleft, hright, Complex.normSq_neg, spectralEnergy, E] using he.symm
  have hsum : (∑ j, w j) = 0 := by simp only [w, ← Finset.mul_sum, hmean, mul_zero]
  have hcub : (∑ j, (Complex.normSq (w j) : ℂ) * w j) = 0 := by
    have he (j : ι ⊕ ι) : (Complex.normSq (w j) : ℂ) * w j =
        ((Complex.normSq (r : ℂ) : ℂ) * (r : ℂ)) * ((Complex.normSq (v j) : ℂ) * v j) := by
      simp only [w, Complex.normSq_mul, Complex.ofReal_mul]
      ring
    simp only [he, ← Finset.mul_sum, hcubic, mul_zero]
  let Δ := mobiusDenominator a₀ b₀ t
  let R : ℂ := (r : ℂ) ^ n
  have hΔ : Δ ≠ 0 := mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun i _ => ha i)
    (Finset.prod_ne_zero_iff.mpr fun j _ => hb j)
  have hr' : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr
  have hR : R ≠ 0 := pow_ne_zero n hr'
  let k := η * Δ / R
  have hmp (σ : Equiv.Perm ι) : matchingProduct c' d' σ = R * (matchingProduct a b σ / Δ) := by
    rw [matchingProduct_scale c d (r : ℂ) σ,
      matchingProduct_shift (mobiusSpectrum t a₀) (mobiusSpectrum (-t) b₀) (-m) σ,
      matchingProduct_mobius a₀ b₀ t σ ha hb, matchingProduct_shift a b s σ]
  have hdet : determinantValue c' d' U = R * (determinantValue a b U / Δ) := by
    rw [determinantValue_scale c d U (r : ℂ),
      determinantValue_shift (mobiusSpectrum t a₀) (mobiusSpectrum (-t) b₀) hU (-m),
      determinantValue_mobius a₀ b₀ U hU t ha hb, determinantValue_shift a b hU s]
  refine ⟨c', d', k, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hw]
    exact fun i j h => hvinj (mul_left_cancel₀ hr' h)
  · intro σ τ h
    rw [hmp σ, hmp τ] at h
    exact hmatch ((div_left_inj' hΔ).mp (mul_left_cancel₀ hR h))
  · rw [spectralEnergy_scale c d r, hrsq, hEcd, inv_mul_cancel₀ hE.ne']
  · apply sub_eq_zero.mp
    simpa only [hw, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
      Finset.sum_neg_distrib, ← sub_eq_add_neg] using hsum
  · apply sub_eq_zero.mp
    simpa only [hw, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Complex.normSq_neg,
      mul_neg, Finset.sum_neg_distrib, ← sub_eq_add_neg] using hcub
  · simpa only [hw] using hminW
  · intro σ
    have he (z : ℂ) : k * (R * (z / Δ)) = η * z := by
      dsimp only [k]
      field_simp [hΔ, hR] <;> ring
    rw [hmp σ, hdet, he (matchingProduct a b σ), he (determinantValue a b U)]
    exact hbad σ

omit [Nonempty ι] in
private theorem signed_injective_of_regular_products (a b : ι → ℂ)
    (hcross : ∀ i j, a i + b j ≠ 0)
    (hmatch : Function.Injective (matchingProduct a b)) :
    Function.Injective (Sum.elim a (fun j => -b j)) := by
  have hswap (i j : ι) (hij : i ≠ j) : Equiv.swap i j ≠ Equiv.refl ι := by
    intro h
    have he := congrArg (fun σ : Equiv.Perm ι => σ i) h
    exact hij (by simpa using he.symm)
  have hfixed (f : ι → ℂ) {i j : ι} (h : f i = f j) (k : ι) : f (Equiv.swap i j k) = f k := by
    by_cases hi : k = i
    · subst k
      simpa using h.symm
    by_cases hj : k = j
    · subst k
      simpa using h
    rw [Equiv.swap_apply_of_ne_of_ne hi hj]
  have ha : Function.Injective a := by
    intro i j h
    by_cases hij : i = j
    · exact hij
    exfalso
    refine hswap i j hij (hmatch ?_)
    unfold matchingProduct
    apply Finset.prod_congr rfl
    intro k _
    rw [hfixed a h k, Equiv.refl_apply]
  have hb : Function.Injective b := by
    intro i j h
    by_cases hij : i = j
    · exact hij
    exfalso
    refine hswap i j hij (hmatch ?_)
    unfold matchingProduct
    calc
      _ = ∏ k, (a (Equiv.swap i j k) + b (Equiv.swap i j k)) := by
        apply Finset.prod_congr rfl
        intro k _
        rw [hfixed b h k]
      _ = _ := by
        simpa only [Equiv.refl_apply] using Equiv.prod_comp (Equiv.swap i j) (fun k => a k + b k)
  intro i j h
  cases i with
  | inl i =>
    cases j with
    | inl j => exact congrArg Sum.inl (ha h)
    | inr j => exact (hcross i j (add_eq_zero_iff_eq_neg.mpr h)).elim
  | inr i =>
    cases j with
    | inl j => exact (hcross j i (add_eq_zero_iff_eq_neg.mpr h.symm)).elim
    | inr j => exact congrArg Sum.inr (hb (neg_injective h))

omit [DecidableEq ι] in
private theorem eventually_centered_spectral_minimum (a b : ι → ℂ)
    (henergy : spectralEnergy a b = 1) (htrace : (∑ i, a i) = ∑ j, b j)
    (hmin : IsLocalMin (mobiusOrbitFunctional (Sum.elim a (fun j => -b j)) (Fintype.card ι)) 0) :
    ∀ᶠ t : ℂ in 𝓝 0,
      1 ≤ centeredSpectralEnergy (mobiusSpectrum t a) (mobiusSpectrum (-t) b) ^ Fintype.card ι *
        Complex.normSq (mobiusDenominator a b t) := by
  let u : ι ⊕ ι → ℂ := Sum.elim a (fun j => -b j)
  have hval (t : ℂ) : mobiusOrbitFunctional u (Fintype.card ι) t =
      centeredSpectralEnergy (mobiusSpectrum t a) (mobiusSpectrum (-t) b) ^ Fintype.card ι *
        Complex.normSq (mobiusDenominator a b t) := by
    have hv : mobiusSpectrum t u = Sum.elim (mobiusSpectrum t a)
        (fun j => -mobiusSpectrum (-t) b j) := by
      funext j
      cases j <;> simp only [u, mobiusSpectrum, Sum.elim_inl, Sum.elim_inr, mul_neg, neg_mul, neg_div]
    have he : centeredEnergy (mobiusSpectrum t u) =
        centeredSpectralEnergy (mobiusSpectrum t a) (mobiusSpectrum (-t) b) := by
      rw [centeredEnergy_eq_sum_sub_mean, hv]
      simp only [centeredSpectralEnergy, spectralEnergy, Fintype.sum_sum_type, Sum.elim_inl,
        Sum.elim_inr, Complex.normSq_neg, Finset.sum_neg_distrib, ← sub_eq_add_neg,
        Fintype.card_sum, Nat.cast_add, two_mul]
    have hd : (∏ j, Complex.normSq (1 - t * u j)) = Complex.normSq (mobiusDenominator a b t) := by
      simp only [mobiusDenominator, map_mul, map_prod, Fintype.prod_sum_type, u,
        Sum.elim_inl, Sum.elim_inr, mul_neg, sub_neg_eq_add]
    simp only [mobiusOrbitFunctional, he, hd]
  have hzero : mobiusOrbitFunctional u (Fintype.card ι) 0 = 1 := by
    rw [hval 0]
    simp [centeredSpectralEnergy, mobiusDenominator, henergy, htrace]
  filter_upwards [hmin] with t ht
  change mobiusOrbitFunctional u (Fintype.card ι) 0 ≤ mobiusOrbitFunctional u (Fintype.card ι) t at ht
  rwa [hzero, hval t] at ht

/-- The conjecture in positive order at least two reduces to unit-energy
spectra with distinct signed points and matching products, equal ordinary
and cubic moments, and the centered fourth-moment inequality. -/
theorem conjecture_iff_mobius_balanced_regular (hn : 2 ≤ Fintype.card ι) :
    Conjecture ι ↔ ∀ (a b : ι → ℂ) (U : Matrix ι ι ℂ), IsUnitary U →
      Function.Injective (Sum.elim a (fun j => -b j)) →
      Function.Injective (matchingProduct a b) → spectralEnergy a b = 1 →
      (∑ i, a i) = (∑ j, b j) →
      (∑ i, (Complex.normSq (a i) : ℂ) * a i) = ∑ j, (Complex.normSq (b j) : ℂ) * b j →
      ‖(2 * (Fintype.card ι : ℂ)) * ((∑ i, (Complex.normSq (a i) : ℂ) * a i ^ 2) +
        ∑ i, (Complex.normSq (b i) : ℂ) * b i ^ 2) - ((∑ i, a i ^ 2) + ∑ i, b i ^ 2)‖ ≤
        (Fintype.card ι : ℝ) * ((∑ i, Complex.normSq (a i) ^ 2) + ∑ i, Complex.normSq (b i) ^ 2) -
          Complex.normSq ((∑ i, a i ^ 2) + ∑ i, b i ^ 2) / 2 →
      Holds a b U := by
  constructor
  · intro h a b U hU _ _ _ _ _ _
    exact h a b U hU
  · intro h
    apply (conjecture_iff_regular_matching_products (ι := ι)).mpr
    intro a b U hU hcross hmatch
    by_contra hbad
    rw [holds_iff_directional] at hbad
    push_neg at hbad
    obtain ⟨η, hη⟩ := hbad
    obtain ⟨c, d, k, hcd, hmatch', henergy, htrace, hcubic, hmin, hstrict⟩ :=
      exists_mobius_balanced_support_violation hn a b U hU η
        (signed_injective_of_regular_products a b hcross hmatch) hmatch hη
    have hfourth := fourth_moment_bound_of_eventually_centered_mobius_minimum c d henergy htrace hcubic
      ((eventually_centered_spectral_minimum c d henergy htrace hmin).mono fun _ ht _ _ _ => ht)
    obtain ⟨σ, hσ⟩ := (holds_iff_directional c d U).mp
      (h c d U hU hcd hmatch' henergy htrace hcubic hfourth) k
    exact (not_le_of_gt (hstrict σ)) hσ

end

end MOC
