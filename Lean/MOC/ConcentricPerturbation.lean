import MOC.CircleSpectra
import MOC.DisjointCircles
import MOC.ScaledUnitaryMaximum

/-! Radius-preserving perturbation removes simple-spectrum assumptions. -/

open Filter Matrix
open scoped Topology

namespace MOC

private noncomputable def perturbUnitSpectrum {n : ℕ} (a : Fin n → ℂ) (t : ℝ) (i : Fin n) : ℂ :=
  a i * circleRotation (t * (i.val : ℝ))

private theorem continuous_perturbUnitSpectrum {n : ℕ} (a : Fin n → ℂ) :
    Continuous (perturbUnitSpectrum a) := by
  apply continuous_pi
  intro i
  exact continuous_const.mul (continuous_circleRotation.comp (continuous_id.mul continuous_const))

private theorem perturbUnitSpectrum_zero {n : ℕ} (a : Fin n → ℂ) : perturbUnitSpectrum a 0 = a := by
  funext i
  simp [perturbUnitSpectrum, circleRotation]

private theorem perturbUnitSpectrum_normSq {n : ℕ} (a : Fin n → ℂ) (t : ℝ) (i : Fin n) :
    Complex.normSq (perturbUnitSpectrum a t i) = Complex.normSq (a i) := by
  simp only [perturbUnitSpectrum, Complex.normSq_mul, circleRotation_normSq, mul_one]

private theorem eventually_injective_perturbUnitSpectrum {n : ℕ} (a : Fin n → ℂ)
    (ha : ∀ i, a i ≠ 0) : ∀ᶠ t in 𝓝[≠] (0 : ℝ), Function.Injective (perturbUnitSpectrum a t) := by
  change ∀ᶠ t in 𝓝[≠] (0 : ℝ), ∀ i j, perturbUnitSpectrum a t i = perturbUnitSpectrum a t j → i = j
  apply Filter.eventually_all.mpr
  intro i
  apply Filter.eventually_all.mpr
  intro j
  by_cases h : a i = a j
  · filter_upwards [(self_mem_nhdsWithin : ∀ᶠ t in 𝓝[≠] (0 : ℝ), t ≠ 0)] with t ht he
    unfold perturbUnitSpectrum at he
    rw [h] at he
    have he' := circleRotation_injective (mul_left_cancel₀ (ha j) he)
    have hval : (i.val : ℝ) = j.val := mul_left_cancel₀ ht he'
    exact Fin.ext (by exact_mod_cast hval)
  · have hcont (k : Fin n) : Continuous (fun t => perturbUnitSpectrum a t k) :=
      (continuous_apply k).comp (continuous_perturbUnitSpectrum a)
    have ht : perturbUnitSpectrum a 0 i - perturbUnitSpectrum a 0 j ≠ 0 := by
      simpa only [perturbUnitSpectrum_zero] using sub_ne_zero.mpr h
    have hdiff := ((hcont i).sub (hcont j)).continuousAt.eventually_ne ht
    filter_upwards [hdiff.filter_mono (nhdsWithin_le_nhds : 𝓝[≠] (0 : ℝ) ≤ 𝓝 0)] with t ht he
    exact False.elim (ht (sub_eq_zero.mpr he))

/-- Inclusion for concentric spectra of radii one and `r`, allowing repeated
eigenvalues. -/
theorem holds_of_concentric_unit_normalized {n : ℕ} (a b : Fin n → ℂ)
    (ha : ∀ i, Complex.normSq (a i) = 1) (hb : ∀ i, Complex.normSq (b i) = 1)
    (r : ℝ) (hr : 0 < r) (hr' : r < 1) (U : Matrix (Fin n) (Fin n) ℂ) (hU : IsUnitary U) :
    Holds a (fun i => (r : ℂ) * b i) U := by
  by_contra hbad
  rw [holds_iff_directional] at hbad
  push_neg at hbad
  obtain ⟨η, hsep⟩ := hbad
  let f := perturbUnitSpectrum a
  let g (t : ℝ) (i : Fin n) := (r : ℂ) * perturbUnitSpectrum b t i
  have hf : Continuous f := continuous_perturbUnitSpectrum a
  have hg : Continuous g := by
    apply continuous_pi
    intro i
    exact continuous_const.mul ((continuous_apply i).comp (continuous_perturbUnitSpectrum b))
  have hdet : Continuous (fun t => (η * determinantValue (f t) (g t) U).re) := by
    unfold determinantValue
    fun_prop
  have hmatching (σ : Equiv.Perm (Fin n)) : Continuous (fun t => (η * matchingProduct (f t) (g t) σ).re) := by
    have he : Continuous (fun t => matchingProduct (f t) (g t) σ) := by
      unfold matchingProduct
      apply continuous_finset_prod
      intro j _
      fun_prop
    fun_prop
  have hstrict : ∀ᶠ t in 𝓝[≠] (0 : ℝ), ∀ σ : Equiv.Perm (Fin n),
      (η * matchingProduct (f t) (g t) σ).re < (η * determinantValue (f t) (g t) U).re := by
    apply Filter.eventually_all.mpr
    intro σ
    exact ((hmatching σ).continuousAt.eventually_lt hdet.continuousAt
      (by simpa only [f, g, perturbUnitSpectrum_zero] using hsep σ)).filter_mono nhdsWithin_le_nhds
  have han (i : Fin n) : a i ≠ 0 := Complex.normSq_pos.mp (by rw [ha]; exact zero_lt_one)
  have hbn (i : Fin n) : b i ≠ 0 := Complex.normSq_pos.mp (by rw [hb]; exact zero_lt_one)
  obtain ⟨t, hts, hta, htb⟩ := (hstrict.and
    ((eventually_injective_perturbUnitSpectrum a han).and
      (eventually_injective_perturbUnitSpectrum b hbn))).exists
  have hh := holds_of_simple_concentric r hr hr' (f t) (perturbUnitSpectrum b t)
    (fun i => (perturbUnitSpectrum_normSq a t i).trans (ha i))
    (fun i => (perturbUnitSpectrum_normSq b t i).trans (hb i)) hta htb U hU
  obtain ⟨σ, hσ⟩ := (holds_iff_directional (f t) (g t) U).mp hh η
  exact (not_le_of_gt (hts σ)) hσ

private theorem holds_of_larger_circle_first {n : ℕ} (a b : Fin n → ℂ)
    (A B : ℝ) (hB : 0 < B) (hBA : B < A)
    (ha : ∀ i, Complex.normSq (a i) = A) (hb : ∀ i, Complex.normSq (b i) = B)
    (U : Matrix (Fin n) (Fin n) ℂ) (hU : IsUnitary U) : Holds a b U := by
  let r := Real.sqrt A
  let s := Real.sqrt B
  let q := s / r
  let x (i : Fin n) := a i / (r : ℂ)
  let y (i : Fin n) := b i / (s : ℂ)
  have hA := hB.trans hBA
  have hr : 0 < r := Real.sqrt_pos_of_pos hA
  have hs : 0 < s := Real.sqrt_pos_of_pos hB
  have hsr : s < r := Real.sqrt_lt_sqrt hB.le hBA
  have hx (i : Fin n) : Complex.normSq (x i) = 1 := by
    rw [show x i = a i / (r : ℂ) from rfl, Complex.normSq_div, ha,
      Complex.normSq_ofReal, Real.mul_self_sqrt hA.le, div_self hA.ne']
  have hy (i : Fin n) : Complex.normSq (y i) = 1 := by
    rw [show y i = b i / (s : ℂ) from rfl, Complex.normSq_div, hb,
      Complex.normSq_ofReal, Real.mul_self_sqrt hB.le, div_self hB.ne']
  have h := holds_of_concentric_unit_normalized x y hx hy q
    (div_pos hs hr) ((div_lt_one hr).mpr hsr) U hU
  have hz := hull_of_common_factor (determinantValue_scale _ _ U (r : ℂ))
    (matchingProduct_scale _ _ (r : ℂ)) h
  have hl : (fun i => (r : ℂ) * x i) = a := by
    funext i
    dsimp only [x]
    field_simp [Complex.ofReal_ne_zero.mpr hr.ne'] <;> ring
  have hr' : (fun i => (r : ℂ) * ((q : ℂ) * y i)) = b := by
    funext i
    dsimp only [q, y]
    rw [Complex.ofReal_div]
    field_simp [Complex.ofReal_ne_zero.mpr hr.ne', Complex.ofReal_ne_zero.mpr hs.ne'] <;> ring
  simpa only [hl, hr'] using hz

/-- Both spectra on any concentric pair of circles satisfy the determinant
inclusion in every finite order. -/
theorem holds_of_concentric_circles {n : ℕ} (a b : Fin n → ℂ) (A B : ℝ)
    (ha : ∀ i, Complex.normSq (a i) = A) (hb : ∀ i, Complex.normSq (b i) = B)
    (U : Matrix (Fin n) (Fin n) ℂ) (hU : IsUnitary U) : Holds a b U := by
  by_cases hn : n ≤ 3
  · exact conjecture_le_three hn a b U hU
  let i₀ : Fin n := ⟨0, by omega⟩
  have hA : 0 ≤ A := ha i₀ ▸ Complex.normSq_nonneg (a i₀)
  have hB : 0 ≤ B := hb i₀ ▸ Complex.normSq_nonneg (b i₀)
  have hUs : IsUnitary Uᴴ := by
    simpa only [IsUnitary, Matrix.conjTranspose_conjTranspose] using And.intro hU.2 hU.1
  by_cases hA₀ : A = 0
  · have ha₀ : a = 0 := funext fun i => Complex.normSq_eq_zero.mp ((ha i).trans hA₀)
    apply (holds_swap_iff a b hU).mp
    apply holds_of_commute b a hUs
    rw [ha₀]
    change Commute Uᴴ (diagonal fun _ : Fin n => (0 : ℂ))
    rw [Matrix.diagonal_zero]
    exact Commute.zero_right _
  by_cases hB₀ : B = 0
  · have hb₀ : b = 0 := funext fun i => Complex.normSq_eq_zero.mp ((hb i).trans hB₀)
    apply holds_of_commute a b hU
    rw [hb₀]
    change Commute U (diagonal fun _ : Fin n => (0 : ℂ))
    rw [Matrix.diagonal_zero]
    exact Commute.zero_right _
  have hAp : 0 < A := lt_of_le_of_ne hA (Ne.symm hA₀)
  have hBp : 0 < B := lt_of_le_of_ne hB (Ne.symm hB₀)
  rcases lt_trichotomy A B with h | h | h
  · exact (holds_swap_iff a b hU).mp (holds_of_larger_circle_first b a B A hAp h hb ha Uᴴ hUs)
  · let p : ℂ := (Real.sqrt A : ℝ)
    have hp : p ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos_of_pos hAp).ne'
    have hpA : Complex.normSq p = A := by
      dsimp only [p]
      rw [Complex.normSq_ofReal, Real.mul_self_sqrt hA]
    apply holds_of_tangent_circles a b p (-p) 1 (neg_ne_zero.mpr hp) one_ne_zero _ _ U hU
    · intro i
      rw [show a i - p - -p = a i by ring, Complex.normSq_neg, hpA]
      exact ha i
    · intro i
      rw [Complex.ofReal_one, one_mul, show -b i - p - -p = -b i by ring,
        Complex.normSq_neg, Complex.normSq_neg, hpA, h]
      exact hb i
  · exact holds_of_larger_circle_first a b A B hBp h ha hb U hU

/-- Two strictly disjoint spectral circles, including nested circles,
satisfy the determinant inclusion in every finite order. -/
theorem holds_of_disjoint_circles {n : ℕ} (a b : Fin n → ℂ)
    (U : Matrix (Fin n) (Fin n) ℂ) (hU : IsUnitary U)
    (c d : ℂ) (hd : d ≠ 0) (r s : ℝ) (hr : 0 < r) (hs : 0 < s)
    (hdisjoint : r + s < 1 ∨ 1 < |r - s|)
    (ha : ∀ i, Complex.normSq ((a i - c) / d) = r ^ 2)
    (hb : ∀ i, Complex.normSq ((-b i - c) / d - 1) = s ^ 2) : Holds a b U :=
  holds_of_disjoint_circles_of_concentric a b U hU c d hd r s hr hs hdisjoint ha hb
    (fun x y A B hx hy => holds_of_concentric_circles x y A B hx hy U hU)

end MOC
