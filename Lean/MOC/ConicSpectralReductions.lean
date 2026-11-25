import MOC.FractionalFiniteNormalization
import MOC.GeneralizedSpectralCircles
import MOC.MobiusCircleDefect
import MOC.SpectralPerturbation
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Tactic.LinearCombination

/-! Tests for the determinant inclusion with one spectrum on a fixed conic.
The relative unitary is fixed throughout the reduction. -/

open Filter Set Matrix
open scoped Topology

namespace MOC

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Test only first spectra with distinct entries in the prescribed set. -/
def SpectralCurveTest (C : Set ℂ) (U : Matrix ι ι ℂ) : Prop :=
  ∀ (a b : ι → ℂ), Function.Injective a → (∀ i, a i ∈ C) → Holds a b U

/-- The standard parabola. A complex affine map with nonzero slope
transports its test to that of any similar parabola. -/
def spectralParabola : Set ℂ :=
  Set.range fun t : ℝ => (t : ℂ) + Complex.I * (t ^ 2 : ℝ)

/-- A hyperbola with real asymptote directions `1` and `d`,
and product parameter `k`. The directions are nonparallel
when `d.im ≠ 0`. -/
def spectralHyperbola (d : ℂ) (k : ℝ) : Set ℂ :=
  {z | ∃ x y : ℝ, x * y = k ∧ z = (x : ℂ) + (y : ℂ) * d}

private theorem isClosed_spectral_holds (U : Matrix ι ι ℂ) :
    IsClosed {p : (ι → ℂ) × (ι → ℂ) | Holds p.1 p.2 U} := by
  have he : {p : (ι → ℂ) × (ι → ℂ) | Holds p.1 p.2 U} =
      ⋂ k : ℂ, ⋃ σ : Equiv.Perm ι, {p : (ι → ℂ) × (ι → ℂ) |
        (k * determinantValue p.1 p.2 U).re ≤ (k * matchingProduct p.1 p.2 σ).re} := by
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_iUnion]
    exact holds_iff_directional p.1 p.2 U
  rw [he]
  refine isClosed_iInter fun k => isClosed_iUnion_of_finite fun σ => isClosed_le ?_ ?_
  · unfold determinantValue
    fun_prop
  · have hc : Continuous fun p : (ι → ℂ) × (ι → ℂ) => matchingProduct p.1 p.2 σ := by
      unfold matchingProduct
      apply continuous_finset_prod
      intro j _
      fun_prop
    exact Complex.continuous_re.comp (continuous_const.mul hc)

private theorem holds_of_spectral_limits {T : Type*} {l : Filter T} [l.NeBot]
    (U : Matrix ι ι ℂ) {A B : T → ι → ℂ} {a b : ι → ℂ}
    (ha : Tendsto A l (𝓝 a)) (hb : Tendsto B l (𝓝 b))
    (h : ∀ᶠ t in l, Holds (A t) (B t) U) : Holds a b U :=
  (isClosed_spectral_holds U).mem_of_tendsto (ha.prodMk_nhds hb) h

private theorem eventually_injective_left {T : Type*} {l : Filter T}
    {A : T → ι → ℂ} {a : ι → ℂ}
    (ha : Tendsto A l (𝓝 a)) (hinj : Function.Injective a) :
    ∀ᶠ t in l, Function.Injective (A t) := by
  change ∀ᶠ t in l, ∀ i j, A t i = A t j → i = j
  apply Filter.eventually_all.mpr
  intro i
  apply Filter.eventually_all.mpr
  intro j
  by_cases hij : i = j
  · exact Filter.Eventually.of_forall fun _ _ => hij
  · have hi := (continuous_apply i).continuousAt.tendsto.comp ha
    have hj := (continuous_apply j).continuousAt.tendsto.comp ha
    have hnear := (isOpen_ne_fun continuous_fst continuous_snd).mem_nhds
      (show (a i, a j) ∈ {p : ℂ × ℂ | p.1 ≠ p.2} from hinj.ne hij)
    exact ((hi.prodMk_nhds hj) hnear).mono fun _ hn he => False.elim (hn he)

private theorem holds_affine_spectral_iff (a b : ι → ℂ) (U : Matrix ι ι ℂ)
    (hU : IsUnitary U) (s t : ℂ) (hs : s ≠ 0) :
    Holds (fun i => s * a i + t) (fun j => s * b j - t) U ↔ Holds a b U := by
  have h := holds_fractional_iff a b U hU s t 0 1
    (by simpa using hs) (fun _ => by simp) (fun _ => by simp)
  have hb : (fun j => -(s * -b j + t)) = (fun j => s * b j - t) := by
    funext j
    ring
  simpa only [fractionalMap, Function.comp_apply, zero_mul, zero_add, div_one, hb] using h

/-- An invertible complex affine map preserves the fixed-unitary spectral test. -/
theorem spectralCurveTest_affine_image_iff (C : Set ℂ) (U : Matrix ι ι ℂ)
    (hU : IsUnitary U) (s t : ℂ) (hs : s ≠ 0) :
    SpectralCurveTest ((fun z : ℂ => s * z + t) '' C) U ↔ SpectralCurveTest C U := by
  constructor
  · intro h a b ha hC
    have hinj : Function.Injective (fun i => s * a i + t) := by
      intro i j hij
      exact ha (mul_left_cancel₀ hs (add_right_cancel hij))
    exact (holds_affine_spectral_iff a b U hU s t hs).mp
      (h _ _ hinj (fun i => ⟨a i, hC i, rfl⟩))
  · intro h a b ha hC
    choose x hx hax using hC
    have hinj : Function.Injective x := by
      intro i j hij
      exact ha ((hax i).symm.trans ((congrArg (fun z => s * z + t) hij).trans (hax j)))
    have he : (fun j => s * ((b j + t) / s) - t) = b := by
      funext j
      field_simp [hs]
    have hh := (holds_affine_spectral_iff x (fun j => (b j + t) / s) U hU s t hs).mpr
      (h _ _ hinj hx)
    rwa [he, funext hax] at hh

/-- Apply the chart to the first spectrum. If a partner entry is at the pole,
perturb only that partner list and remove the perturbation by closedness. -/
theorem holds_of_fractional_spectral_test (a b : ι → ℂ) (U : Matrix ι ι ℂ)
    (hU : IsUnitary U) (α β γ δ : ℂ) (hd : α * δ - β * γ ≠ 0)
    (ha : ∀ i, γ * a i + δ ≠ 0)
    (h : ∀ c : ι → ℂ, Holds (fractionalMap α β γ δ ∘ a) c U) :
    Holds a b U := by
  let B (t : ℂ) (j : ι) := b j + t
  have hB : Continuous B := continuous_pi fun j => by
    dsimp only [B]
    fun_prop
  have hlim : Tendsto B (𝓝[≠] (0 : ℂ)) (𝓝 b) := by
    have hz : B 0 = b := funext fun j => add_zero (b j)
    rw [← hz]
    exact hB.continuousAt.continuousWithinAt
  have hreg : ∀ᶠ t in 𝓝[≠] (0 : ℂ), ∀ j, γ * (-B t j) + δ ≠ 0 := by
    apply Filter.eventually_all.mpr
    intro j
    by_cases hj : γ * (-b j) + δ = 0
    · have hγ : γ ≠ 0 := by
        intro he
        have hδ : δ = 0 := by simpa only [he, zero_mul, zero_add] using hj
        exact hd (by simp only [he, hδ, mul_zero, sub_self])
      filter_upwards [self_mem_nhdsWithin] with t ht
      have hden : γ * (-B t j) + δ = -(γ * t) := by
        calc
          _ = (γ * (-b j) + δ) - γ * t := by dsimp only [B]; ring
          _ = _ := by rw [hj, zero_sub]
      rw [hden]
      exact neg_ne_zero.mpr (mul_ne_zero hγ ht)
    · have hc : Continuous (fun t => γ * (-B t j) + δ) := by
        dsimp only [B]
        fun_prop
      exact ((hc.continuousAt.eventually_ne (by simpa only [B, add_zero] using hj))).filter_mono
        nhdsWithin_le_nhds
  apply holds_of_spectral_limits U tendsto_const_nhds hlim
  filter_upwards [hreg] with t ht
  exact (holds_fractional_iff a (B t) U hU α β γ δ hd ha ht).mp (h _)

private theorem holds_of_scaled_curve_approximation {C : Set ℂ}
    (a b : ι → ℂ) (U : Matrix ι ι ℂ) (hU : IsUnitary U)
    (h : SpectralCurveTest C U) (ha : Function.Injective a)
    (A : ℝ → ι → ℂ) (hA : Tendsto A (𝓝[≠] (0 : ℝ)) (𝓝 a))
    (hscale : ∀ ε : ℝ, ε ≠ 0 → ∃ s t : ℂ, s ≠ 0 ∧
      A ε ∈ (fun c : ι → ℂ => fun i => s * c i + t) '' {c | ∀ i, c i ∈ C}) :
    Holds a b U := by
  apply holds_of_spectral_limits U hA tendsto_const_nhds
  filter_upwards [self_mem_nhdsWithin, eventually_injective_left hA ha] with ε hε hinj
  obtain ⟨s, t, hs, x, hx, he⟩ := hscale ε hε
  exact ((spectralCurveTest_affine_image_iff C U hU s t hs).mpr h) (A ε) b hinj
    (fun i => ⟨x i, hx i, congrFun he i⟩)

/-- The two vertical lines of real parts (1,-1) are common affine
limits of the standard parabola, with one affine map for the whole list. -/
theorem holds_of_parabolic_test_on_parallel_lines (a b : ι → ℂ) (U : Matrix ι ι ℂ)
    (hU : IsUnitary U) (h : SpectralCurveTest spectralParabola U)
    (ha : Function.Injective a) (hline : ∀ i, (a i).re = 1 ∨ (a i).re = -1) :
    Holds a b U := by
  let q (i : ι) : ℝ := (a i).re * (a i).im / 2
  let E (i : ι) : ℂ := (q i : ℂ) + Complex.I * (q i ^ 2 : ℝ)
  let A (ε : ℝ) (i : ι) := a i + (ε : ℂ) * E i
  have hA : Continuous A := continuous_pi fun i => by
    dsimp only [A]
    fun_prop
  have hzero : A 0 = a := by
    funext i
    simp only [A, Complex.ofReal_zero, zero_mul, add_zero]
  apply holds_of_scaled_curve_approximation a b U hU h ha A
  · rw [← hzero]
    exact hA.continuousAt.continuousWithinAt
  · intro ε hε
    let x (i : ι) : ℝ := (a i).re / ε + q i
    let p (i : ι) : ℂ := (x i : ℂ) + Complex.I * (x i ^ 2 : ℝ)
    refine ⟨(ε : ℂ), -Complex.I / (ε : ℂ), Complex.ofReal_ne_zero.mpr hε,
      p, (fun i => ⟨x i, rfl⟩), ?_⟩
    funext i
    have hs : (a i).re ^ 2 = 1 := by
      rcases hline i with hr | hr <;> rw [hr] <;> norm_num
    have hsC : ((a i).re : ℂ) ^ 2 = 1 := by exact_mod_cast hs
    have hq : (2 : ℂ) * ((a i).re : ℂ) * (q i : ℂ) = ((a i).im : ℂ) := by
      have hr : 2 * (a i).re * q i = (a i).im := by
        unfold q
        calc
          _ = (a i).re ^ 2 * (a i).im := by ring
          _ = _ := by rw [hs, one_mul]
      exact_mod_cast hr
    have hdec : a i = ((a i).re : ℂ) + Complex.I * ((a i).im : ℂ) := by
      simpa only [mul_comm Complex.I] using (Complex.re_add_im (a i)).symm
    change (ε : ℂ) * p i + -Complex.I / (ε : ℂ) = a i + (ε : ℂ) * E i
    have hpoly :
        (ε : ℂ) * p i + -Complex.I / (ε : ℂ) =
          ((a i).re : ℂ) + (ε : ℂ) * (q i : ℂ) +
            Complex.I * (((((a i).re : ℂ) ^ 2) - 1) / (ε : ℂ) +
              2 * ((a i).re : ℂ) * (q i : ℂ) + (ε : ℂ) * (q i : ℂ) ^ 2) := by
      simp only [p, x, Complex.ofReal_add, Complex.ofReal_div, Complex.ofReal_pow]
      field_simp [Complex.ofReal_ne_zero.mpr hε] <;> ring
    rw [hpoly, hsC, sub_self, zero_div, zero_add, hq]
    calc
      _ = (((a i).re : ℂ) + Complex.I * ((a i).im : ℂ)) + (ε : ℂ) * E i := by
        simp only [E, Complex.ofReal_pow]
        ring
      _ = _ := congrArg (fun z : ℂ => z + (ε : ℂ) * E i) hdec.symm

private def hyperbolicX (k x y ε : ℝ) : ℝ :=
  if x ≠ 0 then x else if y ≠ 0 then ε ^ 2 * k / y else ε

private def hyperbolicY (k x y ε : ℝ) : ℝ :=
  if x ≠ 0 then ε ^ 2 * k / x else if y ≠ 0 then y else ε * k

private theorem hyperbolic_product (k x y ε : ℝ) :
    hyperbolicX k x y ε * hyperbolicY k x y ε = ε ^ 2 * k := by
  unfold hyperbolicX hyperbolicY
  by_cases hx : x ≠ 0
  · simp only [if_pos hx]
    field_simp [hx]
  · simp only [if_neg hx]
    by_cases hy : y ≠ 0
    · simp only [if_pos hy, div_mul_cancel₀ _ hy]
    · simp only [if_neg hy]
      ring

/-- The asymptote union is the common limit of scalar dilations of
a fixed hyperbola. The argument includes entries at the intersection. -/
theorem holds_of_hyperbolic_test_on_asymptotes (a b : ι → ℂ)
    (d : ℂ) (k : ℝ) (U : Matrix ι ι ℂ) (hU : IsUnitary U)
    (h : SpectralCurveTest (spectralHyperbola d k) U) (ha : Function.Injective a)
    (haxes : ∀ i, ∃ x y : ℝ, x * y = 0 ∧ a i = (x : ℂ) + (y : ℂ) * d) :
    Holds a b U := by
  choose x y hxy hax using haxes
  let A (ε : ℝ) (i : ι) :=
    (hyperbolicX k (x i) (y i) ε : ℂ) + (hyperbolicY k (x i) (y i) ε : ℂ) * d
  have hA : Continuous A := by
    apply continuous_pi
    intro i
    by_cases hx : x i ≠ 0 <;> by_cases hy : y i ≠ 0 <;>
      simp only [A, hyperbolicX, hyperbolicY, hx, hy, if_true, if_false] <;> fun_prop
  have hzero : A 0 = a := by
    funext i
    rw [hax i]
    rcases mul_eq_zero.mp (hxy i) with hx | hy
    · by_cases hy' : y i ≠ 0
      · simp [A, hyperbolicX, hyperbolicY, hx, hy']
      · simp [A, hyperbolicX, hyperbolicY, hx, not_ne_iff.mp hy']
    · by_cases hx' : x i ≠ 0
      · simp [A, hyperbolicX, hyperbolicY, hy, hx']
      · simp [A, hyperbolicX, hyperbolicY, hy, not_ne_iff.mp hx']
  apply holds_of_scaled_curve_approximation a b U hU h ha A
  · rw [← hzero]
    exact hA.continuousAt.continuousWithinAt
  · intro ε hε
    let X (i : ι) := hyperbolicX k (x i) (y i) ε / ε
    let Y (i : ι) := hyperbolicY k (x i) (y i) ε / ε
    let p (i : ι) : ℂ := (X i : ℂ) + (Y i : ℂ) * d
    refine ⟨(ε : ℂ), 0, Complex.ofReal_ne_zero.mpr hε, p, ?_, ?_⟩
    · intro i
      refine ⟨X i, Y i, ?_, rfl⟩
      dsimp only [X, Y]
      rw [div_mul_div_comm, hyperbolic_product]
      field_simp [hε]
    · funext i
      simp only [A, p, X, Y, Complex.ofReal_div, add_zero]
      field_simp [Complex.ofReal_ne_zero.mpr hε]

private theorem injective_left_of_injective_products (a b : ι → ℂ)
    (h : Function.Injective (matchingProduct a b)) : Function.Injective a := by
  intro i j hij
  by_contra hne
  have hswap : ∀ k, a (Equiv.swap i j k) = a k := by
    intro k
    by_cases hi : k = i
    · subst k
      simpa using hij.symm
    by_cases hj : k = j
    · subst k
      simpa using hij
    rw [Equiv.swap_apply_of_ne_of_ne hi hj]
  have he : matchingProduct a b (Equiv.swap i j) = matchingProduct a b 1 := by
    unfold matchingProduct
    apply Finset.prod_congr rfl
    intro k _
    simp only [Equiv.Perm.one_apply, hswap]
  have hval := congrArg (fun p : Equiv.Perm ι => p i) (h he)
  exact hne (by simpa using hval.symm)

private theorem holds_all_of_injective_left (U : Matrix ι ι ℂ)
    (h : ∀ a b : ι → ℂ, Function.Injective a → Holds a b U) :
    ∀ a b : ι → ℂ, Holds a b U := by
  intro a b
  by_contra hf
  rw [holds_iff_directional] at hf
  push_neg at hf
  obtain ⟨η, hη⟩ := hf
  obtain ⟨a', b', _, hinj, hsep⟩ := exists_regular_spectra_of_support_violation a b U η hη
  obtain ⟨σ, hσ⟩ := (holds_iff_directional a' b' U).mp
    (h a' b' (injective_left_of_injective_products a' b' hinj)) η
  exact (not_le_of_gt (hsep σ)) hσ

/-- Order four can be tested on the standard parabola with the same mixer. -/
theorem four_spectralParabola_test_iff (U : Matrix (Fin 4) (Fin 4) ℂ) (hU : IsUnitary U) :
    SpectralCurveTest spectralParabola U ↔ ∀ a b : Fin 4 → ℂ, Holds a b U := by
  constructor
  · intro h
    apply holds_all_of_injective_left U
    intro a b ha
    obtain ⟨α, β, γ, δ, hd, hreg, h0, h1, R, _, h2⟩ :=
      exists_pole_avoiding_three_point_approximation (Set.range a) (Set.finite_range a)
        (a 0) (a 1) (a 2) (ha.ne (by decide)) (ha.ne (by decide)) (ha.ne (by decide)) 1
    let x : Fin 4 → ℂ := fractionalMap α β γ δ ∘ a
    have hx : Function.Injective x := fun i j he =>
      ha (fractionalMap_injOn α β γ δ hd (hreg _ ⟨i, rfl⟩) (hreg _ ⟨j, rfl⟩) he)
    have hreal (i : Fin 4) (hi : i ≠ 3) : (x i).im = 0 := by
      fin_cases i
      · simp only [x, Function.comp_apply, h0, Complex.zero_im]
      · simp only [x, Function.comp_apply, h1, Complex.one_im]
      · simp only [x, Function.comp_apply, h2, Complex.ofReal_im]
      · exact (hi rfl).elim
    apply holds_of_fractional_spectral_test a b U hU α β γ δ hd
      (fun i => hreg _ ⟨i, rfl⟩)
    intro c
    change Holds x c U
    let H := (x 3).im
    let r : ℝ := if H = 0 then 1 else 2 / H
    have hr : r ≠ 0 := by
      by_cases he : H = 0
      · simp [r, he]
      · exact if_neg he ▸ div_ne_zero (by norm_num) he
    let s : ℂ := (r : ℂ) * Complex.I
    have hs : s ≠ 0 := mul_ne_zero (Complex.ofReal_ne_zero.mpr hr) Complex.I_ne_zero
    apply (holds_affine_spectral_iff x c U hU s 1 hs).mp
    apply holds_of_parabolic_test_on_parallel_lines _ _ U hU h
    · intro i j he
      exact hx (mul_left_cancel₀ hs (add_right_cancel he))
    · intro i
      have he : (s * x i + 1).re = 1 - r * (x i).im := by
        simp only [s, Complex.add_re, Complex.one_re, Complex.mul_re, Complex.mul_im,
          Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero,
          zero_mul, sub_zero, zero_sub, one_mul, mul_one, add_zero]
        ring
      rw [he]
      by_cases hi : i = 3
      · subst i
        by_cases hz : H = 0
        · left
          change 1 - r * H = 1
          rw [hz, mul_zero, sub_zero]
        · right
          change 1 - r * H = -1
          rw [show r = 2 / H from if_neg hz, div_mul_cancel₀ _ hz]
          norm_num
      · left
        rw [hreal i hi, mul_zero, sub_zero]
  · intro h a b _ _
    exact h a b

/-- Order four can be tested on one fixed hyperbola with nonparallel asymptotes. -/
theorem four_spectralHyperbola_test_iff (d : ℂ) (k : ℝ) (hdim : d.im ≠ 0)
    (U : Matrix (Fin 4) (Fin 4) ℂ) (hU : IsUnitary U) :
    SpectralCurveTest (spectralHyperbola d k) U ↔ ∀ a b : Fin 4 → ℂ, Holds a b U := by
  constructor
  · intro h
    apply holds_all_of_injective_left U
    intro a b ha
    obtain ⟨α, β, γ, δ, hd, hreg, h0, h1, R, _, h2⟩ :=
      exists_pole_avoiding_three_point_approximation (Set.range a) (Set.finite_range a)
        (a 0) (a 1) (a 2) (ha.ne (by decide)) (ha.ne (by decide)) (ha.ne (by decide)) 1
    let x : Fin 4 → ℂ := fractionalMap α β γ δ ∘ a
    have hx : Function.Injective x := fun i j he =>
      ha (fractionalMap_injOn α β γ δ hd (hreg _ ⟨i, rfl⟩) (hreg _ ⟨j, rfl⟩) he)
    have hreal (i : Fin 4) (hi : i ≠ 3) : (x i).im = 0 := by
      fin_cases i
      · simp only [x, Function.comp_apply, h0, Complex.zero_im]
      · simp only [x, Function.comp_apply, h1, Complex.one_im]
      · simp only [x, Function.comp_apply, h2, Complex.ofReal_im]
      · exact (hi rfl).elim
    apply holds_of_fractional_spectral_test a b U hU α β γ δ hd
      (fun i => hreg _ ⟨i, rfl⟩)
    intro c
    change Holds x c U
    let v : ℝ := (x 3).im / d.im
    let u : ℝ := (x 3).re - v * d.re
    have hdim' : v * d.im = (x 3).im := div_mul_cancel₀ _ hdim
    apply (holds_affine_spectral_iff x c U hU 1 (-(u : ℂ)) one_ne_zero).mp
    apply holds_of_hyperbolic_test_on_asymptotes _ _ d k U hU h
    · intro i j he
      exact hx (mul_left_cancel₀ one_ne_zero (add_right_cancel he))
    · intro i
      by_cases hi : i = 3
      · subst i
        refine ⟨0, v, zero_mul _, ?_⟩
        apply Complex.ext
        · simp only [one_mul, Complex.add_re, Complex.neg_re, Complex.ofReal_re,
            Complex.zero_re, Complex.mul_re, Complex.ofReal_im, zero_mul, sub_zero, zero_add, u]
          ring
        · simp only [one_mul, Complex.add_im, Complex.neg_im, Complex.ofReal_im,
            Complex.zero_im, Complex.mul_im, Complex.ofReal_re, zero_mul, add_zero, zero_add,
            neg_zero, hdim']
      · refine ⟨(x i).re - u, 0, mul_zero _, ?_⟩
        apply Complex.ext
        · simp only [one_mul, Complex.add_re, Complex.neg_re, Complex.ofReal_re,
            Complex.zero_re, Complex.mul_re, Complex.ofReal_im, zero_mul, sub_zero, add_zero]
          ring
        · simp only [one_mul, Complex.add_im, Complex.neg_im, Complex.ofReal_im,
            Complex.zero_im, Complex.mul_im, Complex.ofReal_re, zero_mul, add_zero, neg_zero,
            hreal i hi]
  · intro h a b _ _
    exact h a b

private theorem real_tilted_product_at {u v : ℂ}
    (hu : 0 < u.im) (hv : 0 < v.im) :
    ∃ t : ℝ, ((u - (t : ℂ)) * (v - (t : ℂ))).im = 0 ∧
      ((u - (t : ℂ)) * (v - (t : ℂ))).re < 0 := by
  let t : ℝ := (u.re * v.im + u.im * v.re) / (u.im + v.im)
  have hsum : 0 < u.im + v.im := add_pos hu hv
  have hleft : u.re - t = (u.re - v.re) * u.im / (u.im + v.im) := by
    dsimp only [t]
    field_simp [hsum.ne'] <;> ring
  have hright : v.re - t = (v.re - u.re) * v.im / (u.im + v.im) := by
    dsimp only [t]
    field_simp [hsum.ne'] <;> ring
  refine ⟨t, ?_, ?_⟩
  · simp only [Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
      Complex.ofReal_im, sub_zero]
    rw [hleft, hright]
    ring
  · have hprod : (u.re - t) * (v.re - t) ≤ 0 := by
      rw [hleft, hright]
      by_cases h : u.re ≤ v.re
      · exact mul_nonpos_of_nonpos_of_nonneg
          (div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr h) hu.le) hsum.le)
          (div_nonneg (mul_nonneg (sub_nonneg.mpr h) hv.le) hsum.le)
      · have h' := (lt_of_not_ge h).le
        exact mul_nonpos_of_nonneg_of_nonpos
          (div_nonneg (mul_nonneg (sub_nonneg.mpr h') hu.le) hsum.le)
          (div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr h') hv.le) hsum.le)
    simp only [Complex.mul_re, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
      Complex.ofReal_im, sub_zero]
    exact sub_neg.mpr (hprod.trans_lt (mul_pos hu hv))

/-- Given two points in the upper half-plane, a real reciprocal change of
coordinates makes their secant parallel to any specified nonzero direction.
The proof uses a real quadratic with negative constant term. -/
theorem exists_real_reciprocal_secant {u v d : ℂ} (hu : 0 < u.im) (hv : 0 < v.im)
    (huv : u ≠ v) (hd : d ≠ 0) :
    ∃ t c : ℝ, -(u - (t : ℂ))⁻¹ - (-(v - (t : ℂ))⁻¹) = (c : ℂ) * d := by
  let g (t : ℝ) : ℂ := (u - (t : ℂ)) * (v - (t : ℂ))
  let e := d / (u - v)
  have he : e ≠ 0 := div_ne_zero hd (sub_ne_zero.mpr huv)
  obtain ⟨t₀, him, hre⟩ := real_tilted_product_at hu hv
  change (g t₀).im = 0 at him
  change (g t₀).re < 0 at hre
  have hreal : ∃ t : ℝ, (e * g t).im = 0 := by
    by_cases hei : e.im = 0
    · exact ⟨t₀, by rw [Complex.mul_im, him, hei, mul_zero, zero_mul, add_zero]⟩
    · let w : ℂ := 2 * (t₀ : ℂ) - (u + v)
      let B := (e * w).im / e.im
      let C := (g t₀).re
      let Q := B ^ 2 - 4 * C
      have hQ : 0 ≤ Q := by
        dsimp only [Q, C]
        nlinarith [sq_nonneg B]
      let x := (-B + Real.sqrt Q) / 2
      have hx : x ^ 2 + B * x + C = 0 := by
        have hs : Real.sqrt Q ^ 2 = Q := Real.sq_sqrt hQ
        dsimp only [x, Q] at hs ⊢
        nlinarith
      have hg : g (t₀ + x) = g t₀ + w * (x : ℂ) + ((x : ℂ) ^ 2) := by
        simp only [g, w, Complex.ofReal_add]
        ring
      have hsq : (e * ((x : ℂ) ^ 2)).im = e.im * x ^ 2 := by
        rw [← Complex.ofReal_pow]
        simp only [Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re, mul_zero, zero_add]
      have hw : (e * (w * (x : ℂ))).im = (e * w).im * x := by
        rw [← mul_assoc, Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re, mul_zero, zero_add]
      have hB : e.im * B = (e * w).im := by
        dsimp only [B]
        rw [mul_comm, div_mul_cancel₀ _ hei]
      refine ⟨t₀ + x, ?_⟩
      calc
        _ = e.im * C + (e * w).im * x + e.im * x ^ 2 := by
          rw [hg, mul_add, mul_add, Complex.add_im, Complex.add_im, Complex.mul_im e (g t₀),
            him, mul_zero, zero_add, hw, hsq]
        _ = e.im * (x ^ 2 + B * x + C) := by rw [← hB]; ring
        _ = 0 := by rw [hx, mul_zero]
  obtain ⟨t, ht⟩ := hreal
  have hun : u - (t : ℂ) ≠ 0 := by
    intro h
    have hi := congrArg Complex.im h
    simp only [Complex.sub_im, Complex.ofReal_im, Complex.zero_im, sub_zero] at hi
    exact hu.ne' hi
  have hvn : v - (t : ℂ) ≠ 0 := by
    intro h
    have hi := congrArg Complex.im h
    simp only [Complex.sub_im, Complex.ofReal_im, Complex.zero_im, sub_zero] at hi
    exact hv.ne' hi
  have hcast : ((e * g t).re : ℂ) = e * g t :=
    Complex.ext (Complex.ofReal_re _) (by rw [Complex.ofReal_im, ht])
  refine ⟨((e * g t).re)⁻¹, ?_⟩
  rw [Complex.ofReal_inv, hcast]
  change -(u - (t : ℂ))⁻¹ - (-(v - (t : ℂ))⁻¹) =
    (d / (u - v) * ((u - (t : ℂ)) * (v - (t : ℂ))))⁻¹ * d
  field_simp [hun, hvn, hd, sub_ne_zero.mpr huv] <;> ring

/-- The ellipse with real and imaginary semiaxes `r` and `1`. -/
def spectralEllipse (r : ℝ) : Set ℂ :=
  {z | (z.re / r) ^ 2 + z.im ^ 2 = 1}

private theorem real_quadratic_root (A B C : ℝ) (hA : A ≠ 0)
    (hD : 0 ≤ B ^ 2 - 4 * A * C) :
    ∃ x : ℝ, A * x ^ 2 + B * x + C = 0 := by
  let d := Real.sqrt (B ^ 2 - 4 * A * C)
  refine ⟨(-B + d) / (2 * A), ?_⟩
  have hd : d ^ 2 = B ^ 2 - 4 * A * C := Real.sq_sqrt hD
  have hscale : 4 * A ^ 2 ≠ 0 := mul_ne_zero (by norm_num) (pow_ne_zero 2 hA)
  apply mul_left_cancel₀ hscale
  calc
    _ = A * (d ^ 2 - (B ^ 2 - 4 * A * C)) := by field_simp [hA] <;> ring
    _ = 4 * A ^ 2 * 0 := by rw [hd, sub_self, mul_zero, mul_zero]

private def ellipseSquare (r : ℝ) (z : ℂ) : ℝ := (z.re / r) ^ 2 + z.im ^ 2

private theorem ellipseSquare_pos (r : ℝ) (hr : r ≠ 0) {z : ℂ} (hz : z ≠ 0) :
    0 < ellipseSquare r z := by
  have he : ellipseSquare r z ≠ 0 := by
    intro hzq
    unfold ellipseSquare at hzq
    have hre2 : (z.re / r) ^ 2 = 0 := by nlinarith [sq_nonneg z.im, sq_nonneg (z.re / r)]
    have him2 : z.im ^ 2 = 0 := by nlinarith [sq_nonneg z.im, sq_nonneg (z.re / r)]
    have hre : z.re / r = 0 :=
      (mul_eq_zero.mp (by simpa only [pow_two] using hre2)).elim id id
    have him : z.im = 0 :=
      (mul_eq_zero.mp (by simpa only [pow_two] using him2)).elim id id
    exact hz (Complex.ext ((div_eq_zero_iff.mp hre).resolve_right hr) him)
  exact lt_of_le_of_ne (add_nonneg (sq_nonneg _) (sq_nonneg _)) he.symm

/- A square root of the wanted cross ratio yields antipodal points.
Solving one real quadratic makes the two ellipse squares equal. -/
theorem exists_ellipse_antipodes (r : ℝ) (hr : 0 < r) (w : ℂ)
    (hw : w ≠ 0) (hw₁ : w ^ 2 ≠ 1)
    (shape : 4 * r ^ 2 * w.re ^ 2 ≤ (r ^ 2 - 1) ^ 2 * w.im ^ 2) :
    ∃ u v : ℂ, u ∈ spectralEllipse r ∧ -u ∈ spectralEllipse r ∧
      v ∈ spectralEllipse r ∧ -v ∈ spectralEllipse r ∧
      Function.Injective (![u, -u, v, -v] : Fin 4 → ℂ) ∧
      spectralCrossRatio u (-u) v (-v) = w ^ 2 := by
  let A := w.re
  let B := w.im * (r ^ 2 - 1) / r
  have hD : 0 ≤ B ^ 2 - 4 * A * A := by
    apply sub_nonneg.mpr
    apply (mul_le_mul_right₀ (sq_pos_of_pos hr)).mp
    have hB : B ^ 2 * r ^ 2 = (r ^ 2 - 1) ^ 2 * w.im ^ 2 := by
      dsimp only [B]
      field_simp [hr.ne'] <;> ring
    rw [hB]
    dsimp only [A]
    convert shape using 1 <;> ring
  obtain ⟨y, hy⟩ : ∃ y : ℝ, A * y ^ 2 + B * y + A = 0 := by
    by_cases hA : A = 0
    · exact ⟨0, by simp [hA]⟩
    · exact real_quadratic_root A B A hA hD
  let s : ℂ := ⟨r, y⟩
  let p : ℂ := (1 + w) * s
  let q : ℂ := (1 - w) * s
  have hsn : s ≠ 0 := by
    intro hs
    exact hr.ne' (congrArg Complex.re hs)
  have hwp : 1 + w ≠ 0 := by
    intro he
    have hw' : w = -1 := eq_neg_of_add_eq_zero_right he
    exact hw₁ (by rw [hw']; norm_num)
  have hwm : 1 - w ≠ 0 := by
    intro he
    have hw' : w = 1 := (sub_eq_zero.mp he).symm
    exact hw₁ (by rw [hw']; norm_num)
  have hpn : p ≠ 0 := mul_ne_zero hwp hsn
  have hqn : q ≠ 0 := mul_ne_zero hwm hsn
  have hEq : ellipseSquare r p = ellipseSquare r q := by
    have hdiff : ellipseSquare r p - ellipseSquare r q =
        4 * (A * y ^ 2 + B * y + A) := by
      simp only [ellipseSquare, p, q, s, A, B, Complex.mul_re, Complex.mul_im,
        Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
        Complex.one_re, Complex.one_im, zero_add, zero_sub]
      field_simp [hr.ne'] <;> ring
    exact sub_eq_zero.mp (by rw [hdiff, hy, mul_zero])
  let c : ℝ := Real.sqrt (ellipseSquare r p)
  have hc : 0 < c := Real.sqrt_pos.2 (ellipseSquare_pos r hr.ne' hpn)
  have hcc : c ^ 2 = ellipseSquare r p := Real.sq_sqrt
    (ellipseSquare_pos r hr.ne' hpn).le
  let u := p / (c : ℂ)
  let v := q / (c : ℂ)
  have hden : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc.ne'
  have hscale (z : ℂ) :
      ellipseSquare r (z / (c : ℂ)) = ellipseSquare r z / c ^ 2 := by
    simp only [ellipseSquare, Complex.div_re, Complex.div_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.normSq_ofReal, mul_zero, add_zero, sub_zero]
    field_simp [hr.ne', hc.ne'] <;> ring
  have hu : u ∈ spectralEllipse r := by
    change ellipseSquare r (p / (c : ℂ)) = 1
    rw [hscale, hcc, div_self (ellipseSquare_pos r hr.ne' hpn).ne']
  have hv : v ∈ spectralEllipse r := by
    change ellipseSquare r (q / (c : ℂ)) = 1
    rw [hscale, hcc, hEq, div_self (ellipseSquare_pos r hr.ne' hqn).ne']
  have hneg (z : ℂ) (hz : z ∈ spectralEllipse r) : -z ∈ spectralEllipse r := by
    change ((-z).re / r) ^ 2 + (-z).im ^ 2 = 1
    simp only [Complex.neg_re, Complex.neg_im, neg_div]
    calc
      _ = (z.re / r) ^ 2 + z.im ^ 2 := by ring
      _ = 1 := hz
  have hh (z : ℂ) (hn : z ≠ 0) : z ≠ -z := by
    intro he
    apply hn
    linear_combination he / 2
  have huneq : u ≠ 0 := div_ne_zero hpn hden
  have hvneq : v ≠ 0 := div_ne_zero hqn hden
  have huv : u ≠ v := by
    intro h
    have he : p = q := by
      have he := congrArg (fun z : ℂ => z * (c : ℂ)) h
      simpa only [u, v, div_mul_cancel₀ _ hden] using he
    have hm : w * s = 0 := by
      unfold p q at he
      linear_combination he / 2
    exact (mul_ne_zero hw hsn) hm
  have huv' : u ≠ -v := by
    intro h
    have he : p = -q := by
      have he := congrArg (fun z : ℂ => z * (c : ℂ)) h
      simpa only [u, v, neg_mul, div_mul_cancel₀ _ hden] using he
    apply hsn
    unfold p q at he
    linear_combination he / 2
  refine ⟨u, v, hu, hneg u hu, hv, hneg v hv, ?_, ?_⟩
  · have h₁ := hh u huneq
    have h₂ := hh v hvneq
    have h₃ : -u ≠ -v := fun he => huv (neg_injective he)
    have h₄ : -u ≠ v := fun he => huv' ((neg_eq_iff_eq_neg.mp he))
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp_all
  · have hsum : u - -v ≠ 0 := sub_ne_zero.mpr huv'
    have hsum' : -u - v ≠ 0 := by
      have he : -u - v = -(u - -v) := by ring
      rw [he]
      exact neg_ne_zero.mpr hsum
    have hm : u - v = w * (u - -v) := by
      dsimp only [u, v, p, q]
      field_simp [hden] <;> ring
    have hm' : -u - -v = w * (-u - v) := by
      linear_combination -hm
    unfold spectralCrossRatio
    rw [hm, hm']
    field_simp [hsum, hsum'] <;> ring

private theorem norm_one_sub_sq (z : ℂ) :
    ‖1 - z‖ ^ 2 = 1 + ‖z‖ ^ 2 - 2 * z.re := by
  rw [Complex.sq_norm, Complex.normSq_sub, Complex.sq_norm]
  simp only [Complex.normSq_one, one_mul, Complex.conj_re]

private theorem re_le_half_norm_of_longest_opposite (z : ℂ)
    (h₁ : 1 ≤ ‖1 - z‖) (hz : ‖z‖ ≤ ‖1 - z‖) :
    z.re ≤ ‖z‖ / 2 := by
  have h₁' := (sq_le_sq₀ zero_le_one (norm_nonneg (1 - z))).mpr h₁
  have hz' := (sq_le_sq₀ (norm_nonneg z) (norm_nonneg (1 - z))).mpr hz
  rw [norm_one_sub_sq] at h₁' hz'
  by_cases h : ‖z‖ ≤ 1
  · have hm := mul_le_mul_of_nonneg_left h (norm_nonneg z)
    nlinarith
  · have h' : 1 ≤ ‖z‖ := (lt_of_not_ge h).le
    nlinarith

private theorem crossRatio_orbit_half_norm (z : ℂ) (hzero : z ≠ 0) :
    z.re ≤ ‖z‖ / 2 ∨ (1 - z).re ≤ ‖1 - z‖ / 2 ∨
      ((z - 1) / z).re ≤ ‖(z - 1) / z‖ / 2 := by
  by_cases h : ‖z‖ ≤ ‖1 - z‖
  · by_cases ht : 1 ≤ ‖1 - z‖
    · exact Or.inl (re_le_half_norm_of_longest_opposite z ht h)
    · right
      right
      have hu : ‖z‖ ≤ 1 := h.trans (lt_of_not_ge ht).le
      have hv : ‖1 - z‖ ≤ 1 := (lt_of_not_ge ht).le
      have hsmall := mul_le_mul_of_nonneg_left h (norm_nonneg z)
      have hconst := (sq_le_sq₀ (norm_nonneg (1 - z)) zero_le_one).mpr hv
      have hrew : 2 * ((z - 1).re * z.re + (z - 1).im * z.im) =
          ‖z‖ ^ 2 + ‖1 - z‖ ^ 2 - 1 := by
        rw [norm_one_sub_sq, Complex.sq_norm]
        simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.one_re,
          Complex.one_im, sub_zero]
        ring
      rw [Complex.div_re, ← Complex.sq_norm, norm_div, norm_sub_rev z 1]
      have hn : 0 < ‖z‖ := norm_pos_iff.mpr hzero
      apply (div_le_iff₀ (sq_pos_of_pos hn)).mpr
      rw [show ‖1 - z‖ / ‖z‖ / 2 * ‖z‖ ^ 2 = ‖z‖ * ‖1 - z‖ / 2 by
        field_simp [hn.ne'] <;> ring]
      nlinarith
  · have h' : ‖1 - z‖ ≤ ‖z‖ := (lt_of_not_ge h).le
    by_cases ht : 1 ≤ ‖z‖
    · right
      left
      apply re_le_half_norm_of_longest_opposite
      · simpa only [sub_sub_cancel] using ht
      · simpa only [sub_sub_cancel] using h'
    · right
      right
      have hu : ‖z‖ ≤ 1 := (lt_of_not_ge ht).le
      have hv : ‖1 - z‖ ≤ 1 := h'.trans hu
      have hsmall := mul_le_mul_of_nonneg_left h' (norm_nonneg (1 - z))
      have hconst := (sq_le_sq₀ (norm_nonneg z) zero_le_one).mpr hu
      have hrew : 2 * ((z - 1).re * z.re + (z - 1).im * z.im) =
          ‖z‖ ^ 2 + ‖1 - z‖ ^ 2 - 1 := by
        rw [norm_one_sub_sq, Complex.sq_norm]
        simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.one_re,
          Complex.one_im, sub_zero]
        ring
      rw [Complex.div_re, ← Complex.sq_norm, norm_div, norm_sub_rev z 1]
      have hn : 0 < ‖z‖ := norm_pos_iff.mpr hzero
      apply (div_le_iff₀ (sq_pos_of_pos hn)).mpr
      rw [show ‖1 - z‖ / ‖z‖ / 2 * ‖z‖ ^ 2 = ‖z‖ * ‖1 - z‖ / 2 by
        field_simp [hn.ne'] <;> ring]
      nlinarith

private theorem one_sub_spectralCrossRatio (a b c d : ℂ)
    (had : a ≠ d) (hbc : b ≠ c) :
    1 - spectralCrossRatio a b c d = ((d - c) * (b - a)) / ((d - a) * (b - c)) := by
  unfold spectralCrossRatio
  field_simp [sub_ne_zero.mpr had, sub_ne_zero.mpr had.symm, sub_ne_zero.mpr hbc] <;> ring

private theorem spectralCrossRatio_ne_zero_one (a b c d : ℂ)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    spectralCrossRatio a b c d ≠ 0 ∧ spectralCrossRatio a b c d ≠ 1 := by
  refine ⟨div_ne_zero (mul_ne_zero (sub_ne_zero.mpr hac) (sub_ne_zero.mpr hbd))
    (mul_ne_zero (sub_ne_zero.mpr had) (sub_ne_zero.mpr hbc)), ?_⟩
  intro he
  have h := one_sub_spectralCrossRatio a b c d had hbc
  rw [he, sub_self] at h
  exact div_ne_zero (mul_ne_zero (sub_ne_zero.mpr hcd.symm) (sub_ne_zero.mpr hab.symm))
    (mul_ne_zero (sub_ne_zero.mpr had.symm) (sub_ne_zero.mpr hbc)) h.symm

private theorem crossRatio_chart (a b : Fin 4 → ℂ)
    (ha : Function.Injective a) (hb : Function.Injective b)
    (hcr : spectralCrossRatio (a 0) (a 1) (a 2) (a 3) =
      spectralCrossRatio (b 0) (b 1) (b 2) (b 3)) :
    ∃ α β γ δ : ℂ, α * δ - β * γ ≠ 0 ∧
      (∀ i, γ * a i + δ ≠ 0) ∧ fractionalMap α β γ δ ∘ a = b := by
  have haₙ (i j : Fin 4) (hij : i ≠ j) : a i - a j ≠ 0 := sub_ne_zero.mpr (ha.ne hij)
  have hbₙ (i j : Fin 4) (hij : i ≠ j) : b i - b j ≠ 0 := sub_ne_zero.mpr (hb.ne hij)
  let s := (a 1 - a 2) / (a 1 - a 0)
  let t := (b 1 - b 2) / (b 1 - b 0)
  have hs : s ≠ 0 := div_ne_zero (haₙ 1 2 (by decide)) (haₙ 1 0 (by decide))
  have ht : t ≠ 0 := div_ne_zero (hbₙ 1 2 (by decide)) (hbₙ 1 0 (by decide))
  let α := b 2 * s - b 0 * t
  let β := -(b 2 * s * a 0) + b 0 * t * a 2
  let γ := s - t
  let δ := -(s * a 0) + t * a 2
  have hdet : α * δ - β * γ ≠ 0 := by
    have he : α * δ - β * γ = (s * t) * (b 2 - b 0) * (a 2 - a 0) := by
      dsimp only [α, β, γ, δ]
      ring
    rw [he]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero hs ht) (hbₙ 2 0 (by decide))) (haₙ 2 0 (by decide))
  have hpf (i : Fin 4) :
      s * (a i - a 0) * (b i - b 2) = t * (a i - a 2) * (b i - b 0) := by
    fin_cases i
    · simp
    · change s * (a 1 - a 0) * (b 1 - b 2) = t * (a 1 - a 2) * (b 1 - b 0)
      dsimp only [s, t]
      field_simp [haₙ 1 0 (by decide), hbₙ 1 0 (by decide)] <;> ring
    · simp
    · have h₁ := one_sub_spectralCrossRatio (a 0) (a 1) (a 2) (a 3)
        (ha.ne (by decide)) (ha.ne (by decide))
      have h₂ := one_sub_spectralCrossRatio (b 0) (b 1) (b 2) (b 3)
        (hb.ne (by decide)) (hb.ne (by decide))
      rw [hcr, h₂] at h₁
      change s * (a 3 - a 0) * (b 3 - b 2) = t * (a 3 - a 2) * (b 3 - b 0)
      have hh := (div_eq_div_iff (mul_ne_zero (hbₙ 3 0 (by decide)) (hbₙ 1 2 (by decide)))
        (mul_ne_zero (haₙ 3 0 (by decide)) (haₙ 1 2 (by decide)))).mp h₁
      dsimp only [s, t]
      field_simp [haₙ 1 0 (by decide), hbₙ 1 0 (by decide)]
      linear_combination hh
  have hnum (i : Fin 4) : α * a i + β = b i * (γ * a i + δ) := by
    dsimp only [α, β, γ, δ]
    linear_combination -(hpf i)
  have hreg (i : Fin 4) : γ * a i + δ ≠ 0 := by
    intro h
    have h' : α * a i + β = 0 := by rw [hnum i, h, mul_zero]
    exact hdet (by linear_combination α * h - γ * h')
  refine ⟨α, β, γ, δ, hdet, hreg, ?_⟩
  funext i
  unfold fractionalMap Function.comp
  apply (div_eq_iff (hreg i)).mpr
  exact hnum i

private theorem ellipse_chart_of_half_norm (r : ℝ) (hr : 0 < r)
    (hs : 12 * r ^ 2 ≤ (r ^ 2 - 1) ^ 2)
    (a : Fin 4 → ℂ) (ha : Function.Injective a)
    (hangle : let z := spectralCrossRatio (a 0) (a 1) (a 2) (a 3); z.re ≤ ‖z‖ / 2) :
    ∃ α β γ δ : ℂ, α * δ - β * γ ≠ 0 ∧
      (∀ i, γ * a i + δ ≠ 0) ∧ (∀ i, fractionalMap α β γ δ (a i) ∈ spectralEllipse r) := by
  let z := spectralCrossRatio (a 0) (a 1) (a 2) (a 3)
  change z.re ≤ ‖z‖ / 2 at hangle
  have hz := spectralCrossRatio_ne_zero_one (a 0) (a 1) (a 2) (a 3)
    (ha.ne (by decide)) (ha.ne (by decide)) (ha.ne (by decide))
    (ha.ne (by decide)) (ha.ne (by decide)) (ha.ne (by decide))
  obtain ⟨w, hw⟩ := IsAlgClosed.exists_pow_nat_eq z (n := 2) two_pos
  have hwn : w ≠ 0 := fun he => hz.1 (by simpa only [he, zero_pow two_ne_zero] using hw.symm)
  have hw₁ : w ^ 2 ≠ 1 := fun he => hz.2 (hw.symm.trans he)
  have hrw : (w ^ 2).re = w.re ^ 2 - w.im ^ 2 := by simp only [pow_two, Complex.mul_re]
  have hnormw : ‖w ^ 2‖ = w.re ^ 2 + w.im ^ 2 := by
    rw [norm_pow, Complex.sq_norm]
    simp only [Complex.normSq_apply, pow_two]
  rw [← hw, hrw, hnormw] at hangle
  have hshape : 4 * r ^ 2 * w.re ^ 2 ≤ (r ^ 2 - 1) ^ 2 * w.im ^ 2 := by
    calc
      _ ≤ (4 * r ^ 2) * (3 * w.im ^ 2) :=
        mul_le_mul_of_nonneg_left (by linarith only [hangle]) (by positivity)
      _ = (12 * r ^ 2) * w.im ^ 2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hs (sq_nonneg _)
  obtain ⟨u, v, hu, hnegU, hv, hnegV, hInj, hRatio⟩ :=
    exists_ellipse_antipodes r hr w hwn hw₁ hshape
  let b : Fin 4 → ℂ := ![u, -u, v, -v]
  have he : z = spectralCrossRatio (b 0) (b 1) (b 2) (b 3) := by
    simpa [b] using hw.symm.trans hRatio.symm
  obtain ⟨α, β, γ, δ, hd, hreg, ht⟩ := crossRatio_chart a b ha hInj he
  refine ⟨α, β, γ, δ, hd, hreg, fun i => ?_⟩
  have hmem (j : Fin 4) : b j ∈ spectralEllipse r := by
    fin_cases j
    · simpa [b] using hu
    · simpa [b] using hnegU
    · simpa [b] using hv
    · simpa [b] using hnegV
  have hi : fractionalMap α β γ δ (a i) = b i := congrFun ht i
  rw [hi]
  exact hmem i

private theorem half_norm_crossRatio_ordering (a : Fin 4 → ℂ) (ha : Function.Injective a) :
    ∃ p : Equiv.Perm (Fin 4),
      let z := spectralCrossRatio (a (p 0)) (a (p 1)) (a (p 2)) (a (p 3))
      z.re ≤ ‖z‖ / 2 := by
  let z := spectralCrossRatio (a 0) (a 1) (a 2) (a 3)
  have hne (i j : Fin 4) (hij : i ≠ j) : a i - a j ≠ 0 :=
    sub_ne_zero.mpr (ha.ne hij)
  have h0 : z ≠ 0 := div_ne_zero (mul_ne_zero (hne 0 2 (by decide)) (hne 1 3 (by decide)))
    (mul_ne_zero (hne 0 3 (by decide)) (hne 1 2 (by decide)))
  rcases crossRatio_orbit_half_norm z h0 with hz | hz | hz
  · exact ⟨Equiv.refl _, hz⟩
  · let p : Equiv.Perm (Fin 4) := Equiv.swap 1 2
    have hp₀ : p 0 = 0 := by decide
    have hp₁ : p 1 = 2 := by decide
    have hp₂ : p 2 = 1 := by decide
    have hp₃ : p 3 = 3 := by decide
    have he : spectralCrossRatio (a (p 0)) (a (p 1)) (a (p 2)) (a (p 3)) = 1 - z := by
      simp only [hp₀, hp₁, hp₂, hp₃, z, spectralCrossRatio]
      field_simp [hne 0 3 (by decide), hne 1 2 (by decide), hne 2 1 (by decide)] <;> ring
    exact ⟨p, by simpa only [he] using hz⟩
  · let p : Equiv.Perm (Fin 4) := (Equiv.swap 1 2).trans (Equiv.swap 0 1)
    have hp₀ : p 0 = 1 := by decide
    have hp₁ : p 1 = 2 := by decide
    have hp₂ : p 2 = 0 := by decide
    have hp₃ : p 3 = 3 := by decide
    have he : spectralCrossRatio (a (p 0)) (a (p 1)) (a (p 2)) (a (p 3)) = (z - 1) / z := by
      simp only [hp₀, hp₁, hp₂, hp₃, z, spectralCrossRatio]
      field_simp [hne 1 3 (by decide), hne 2 0 (by decide), hne 0 2 (by decide),
        hne 0 3 (by decide), hne 1 2 (by decide)] <;> ring
    exact ⟨p, by simpa only [he] using hz⟩

/-- The stated ellipse semiaxis threshold is sufficient for an exact order-four
test. The proof chooses a cross-ratio ordering by the longest side of its
triangle. The mixer is unchanged. -/
theorem four_spectralEllipse_test_iff (r : ℝ) (hr : 2 + Real.sqrt 3 ≤ r)
    (U : Matrix (Fin 4) (Fin 4) ℂ) (hU : IsUnitary U) :
    SpectralCurveTest (spectralEllipse r) U ↔ ∀ a b : Fin 4 → ℂ, Holds a b U := by
  have hrp : 0 < r := by linarith [Real.sqrt_nonneg (3 : ℝ)]
  have hsq : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hb : 2 ≤ r - Real.sqrt 3 := by linarith
  have hb' := (sq_le_sq₀ (by norm_num : (0 : ℝ) ≤ 2) (by linarith : 0 ≤ r - Real.sqrt 3)).mpr hb
  have hsmall : 2 * Real.sqrt 3 * r ≤ r ^ 2 - 1 := by nlinarith
  have hsmall₀ : 0 ≤ 2 * Real.sqrt 3 * r := by positivity
  have hs := (sq_le_sq₀ hsmall₀ (hsmall₀.trans hsmall)).mpr hsmall
  have hshape : 12 * r ^ 2 ≤ (r ^ 2 - 1) ^ 2 := by
    rw [show (2 * Real.sqrt 3 * r) ^ 2 = 12 * r ^ 2 by rw [mul_pow, mul_pow, hsq]; ring] at hs
    exact hs
  constructor
  · intro h
    apply holds_all_of_injective_left U
    intro a b ha
    obtain ⟨p, hangle⟩ := half_norm_crossRatio_ordering a ha
    obtain ⟨α, β, γ, δ, hd, hreg, hEll⟩ :=
      ellipse_chart_of_half_norm r hrp hshape (a ∘ p) (ha.comp p.injective) hangle
    have hag (i : Fin 4) : γ * a i + δ ≠ 0 := by
      obtain ⟨j, rfl⟩ := p.surjective i
      exact hreg j
    apply holds_of_fractional_spectral_test a b U hU α β γ δ hd hag
    intro c
    apply h _ _ (fun i j he =>
      ha (fractionalMap_injOn α β γ δ hd (hag i) (hag j) he))
    intro i
    obtain ⟨j, rfl⟩ := p.surjective i
    exact hEll j
  · intro h a b _ _
    exact h a b

private theorem holds_of_parabolic_test_at_two_heights (a b : ι → ℂ)
    (U : Matrix ι ι ℂ) (hU : IsUnitary U) (h : SpectralCurveTest spectralParabola U)
    (ha : Function.Injective a) (y : ℝ) (hy : ∀ i, (a i).im = 0 ∨ (a i).im = y) :
    Holds a b U := by
  let r : ℝ := if y = 0 then 1 else 2 / y
  have hr : r ≠ 0 := by
    by_cases he : y = 0
    · simp [r, he]
    · simpa only [r, if_neg he] using (div_ne_zero (by norm_num : (2 : ℝ) ≠ 0) he)
  let s : ℂ := (r : ℂ) * Complex.I
  have hs : s ≠ 0 := mul_ne_zero (Complex.ofReal_ne_zero.mpr hr) Complex.I_ne_zero
  apply (holds_affine_spectral_iff a b U hU s 1 hs).mp
  apply holds_of_parabolic_test_on_parallel_lines _ _ U hU h
  · intro i j he
    exact ha (mul_left_cancel₀ hs (add_right_cancel he))
  · intro i
    have he : (s * a i + 1).re = 1 - r * (a i).im := by
      simp only [s, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.one_re,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero,
        zero_mul, sub_zero, zero_sub, one_mul, mul_one, add_zero]
      ring
    rw [he]
    rcases hy i with h₀ | hyi
    · exact Or.inl (by rw [h₀, mul_zero, sub_zero])
    · rw [hyi]
      by_cases hy₀ : y = 0
      · exact Or.inl (by rw [hy₀, mul_zero, sub_zero])
      · right
        rw [show r = 2 / y from if_neg hy₀, div_mul_cancel₀ _ hy₀]
        norm_num

private theorem holds_of_hyperbolic_test_on_two_intersecting_lines (a b : ι → ℂ)
    (d : ℂ) (k : ℝ) (U : Matrix ι ι ℂ) (hU : IsUnitary U)
    (h : SpectralCurveTest (spectralHyperbola d k) U) (ha : Function.Injective a)
    (x : ℝ) (hax : ∀ i, (a i).im = 0 ∨ ∃ y : ℝ, a i = (x : ℂ) + (y : ℂ) * d) :
    Holds a b U := by
  apply (holds_affine_spectral_iff a b U hU 1 (-(x : ℂ)) one_ne_zero).mp
  apply holds_of_hyperbolic_test_on_asymptotes _ _ d k U hU h
  · intro i j he
    exact ha (mul_left_cancel₀ one_ne_zero (add_right_cancel he))
  · intro i
    rcases hax i with hi | ⟨y, hy⟩
    · refine ⟨(a i).re - x, 0, mul_zero _, ?_⟩
      apply Complex.ext
      · simp only [one_mul, Complex.add_re, Complex.neg_re, Complex.ofReal_re, Complex.zero_re,
          Complex.mul_re, Complex.ofReal_im, zero_mul, sub_zero, add_zero]
        ring
      · simp only [one_mul, Complex.add_im, Complex.neg_im, Complex.ofReal_im, Complex.zero_im,
          Complex.mul_im, Complex.ofReal_re, zero_mul, add_zero, neg_zero, hi]
    · refine ⟨0, y, zero_mul _, ?_⟩
      rw [hy, one_mul, Complex.ofReal_zero, zero_add]
      ring

private theorem holds_of_open_curve_chart {m : Type*} [Fintype m] [DecidableEq m]
    (a b : m → ℂ) (U : Matrix m m ℂ) (hU : IsUnitary U)
    (ha : Function.Injective a) (i j : m) (hij : i ≠ j)
    (hreal : ∀ k, k ≠ i → k ≠ j → (a k).im = 0)
    (hi : 0 ≤ (a i).im) (hj : 0 ≤ (a j).im) (d : ℂ) (hd : d ≠ 0)
    (h : ∀ x y : m → ℂ, Function.Injective x →
      (∀ k, k ≠ i → k ≠ j → (x k).im = 0) →
      (∃ r : ℝ, x i - x j = (r : ℂ) * d) → Holds x y U) :
    Holds a b U := by
  have hupper (x : m → ℂ) (hx : Function.Injective x)
      (hxreal : ∀ k, k ≠ i → k ≠ j → (x k).im = 0)
      (hxli : 0 < (x i).im) (hxlj : 0 < (x j).im) : Holds x b U := by
    obtain ⟨t, r, ht⟩ := exists_real_reciprocal_secant hxli hxlj (hx.ne hij) hd
    let f (z : ℂ) := fractionalMap 0 (-1) 1 (-(t : ℂ)) z
    have hf (z : ℂ) : f z = -(z - (t : ℂ))⁻¹ := by
      simp only [f, fractionalMap, zero_mul, zero_add, one_mul, ← sub_eq_add_neg, neg_div,
        one_div]
    let A (s : ℝ) (k : m) := if k = i ∨ k = j then x k else x k + (s : ℂ)
    have hA : Continuous A := continuous_pi fun k => by
      by_cases hk : k = i ∨ k = j <;> simp only [A, hk, if_true, if_false] <;> fun_prop
    have hAz : A 0 = x := by
      funext k
      by_cases hk : k = i ∨ k = j <;> simp [A, hk]
    have hlim : Tendsto A (𝓝[≠] (0 : ℝ)) (𝓝 x) := by
      rw [← hAz]
      exact hA.continuousAt.continuousWithinAt
    have hnear : ∀ᶠ s in 𝓝[≠] (0 : ℝ), ∀ k, A s k - (t : ℂ) ≠ 0 := by
      apply Filter.eventually_all.mpr
      intro k
      by_cases hk : x k - (t : ℂ) = 0
      · have hkn : ¬ (k = i ∨ k = j) := by
          intro he
          rcases he with rfl | rfl
          · have him := congrArg Complex.im hk
            simp only [Complex.sub_im, Complex.ofReal_im, Complex.zero_im, sub_zero] at him
            exact hxli.ne' him
          · have him := congrArg Complex.im hk
            simp only [Complex.sub_im, Complex.ofReal_im, Complex.zero_im, sub_zero] at him
            exact hxlj.ne' him
        filter_upwards [self_mem_nhdsWithin] with s hs
        have he : A s k - (t : ℂ) = (s : ℂ) := by
          simp only [A, if_neg hkn]
          linear_combination hk
        rw [he]
        exact Complex.ofReal_ne_zero.mpr hs
      · have hc : Continuous fun s => A s k - (t : ℂ) :=
          ((continuous_apply k).comp hA).sub continuous_const
        have hkn : A 0 k - (t : ℂ) ≠ 0 := by rwa [hAz]
        exact (hc.continuousAt.eventually_ne hkn).filter_mono nhdsWithin_le_nhds
    apply holds_of_spectral_limits U hlim tendsto_const_nhds
    filter_upwards [eventually_injective_left hlim hx, hnear] with s hs hreg
    apply holds_of_fractional_spectral_test (A s) b U hU 0 (-1) 1 (-(t : ℂ))
      (by norm_num) (fun k => by simpa only [one_mul, ← sub_eq_add_neg] using hreg k)
    intro c
    change Holds (f ∘ A s) c U
    apply h _ _
    · intro k l he
      exact hs (fractionalMap_injOn _ _ _ _ (by norm_num)
        (by simpa only [one_mul, ← sub_eq_add_neg] using hreg k)
        (by simpa only [one_mul, ← sub_eq_add_neg] using hreg l) he)
    · intro k hki hkj
      change (f (A s k)).im = 0
      rw [hf]
      simp only [A, if_neg (not_or.mpr ⟨hki, hkj⟩), Complex.neg_im, Complex.inv_im,
        Complex.sub_im, Complex.add_im, Complex.ofReal_im, hxreal k hki hkj,
        sub_zero, zero_add, neg_zero, zero_div]
    · refine ⟨r, ?_⟩
      simpa only [Function.comp_apply, A, if_pos (Or.inl rfl), if_pos (Or.inr rfl), hf] using ht
  let A (s : ℝ) (k : m) := if k = i ∨ k = j then a k + (s : ℂ) * Complex.I else a k
  have hA : Continuous A := continuous_pi fun k => by
    by_cases he : k = i ∨ k = j <;> simp only [A, he, if_true, if_false] <;> fun_prop
  have hzero : A 0 = a := by
    funext k
    by_cases he : k = i ∨ k = j <;> simp [A, he]
  have hlim : Tendsto A (𝓝[>] (0 : ℝ)) (𝓝 a) := by
    rw [← hzero]
    exact hA.continuousAt.continuousWithinAt
  apply holds_of_spectral_limits U hlim tendsto_const_nhds
  filter_upwards [self_mem_nhdsWithin, eventually_injective_left hlim ha] with s hs hxi
  have hpos : 0 < s := hs
  have hopp (k : m) (hk : k = i ∨ k = j) : (A s k).im = (a k).im + s := by
    simp only [A, if_pos hk, Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_one, mul_zero, add_zero]
  refine hupper (A s) hxi (fun k hki hkj => ?_) ?_ ?_
  · simp only [A, if_neg (not_or.mpr ⟨hki, hkj⟩), hreal k hki hkj]
  · rw [hopp i (Or.inl rfl)]
    exact add_pos_of_nonneg_of_pos hi hpos
  · rw [hopp j (Or.inr rfl)]
    exact add_pos_of_nonneg_of_pos hj hpos

private theorem exists_exterior_circle_chart (a : ι → ℂ) (o : ℂ) (ho : o ≠ 0)
    (ha : ∀ i, Complex.normSq o ≤ Complex.normSq (a i - o)) :
    ∃ α β γ δ : ℂ, α * δ - β * γ ≠ 0 ∧
      (∀ i, γ * a i + δ ≠ 0) ∧
      (∀ i, 0 ≤ (fractionalMap α β γ δ (a i)).im) ∧
      (∀ i, Complex.normSq (a i - o) = Complex.normSq o →
        (fractionalMap α β γ δ (a i)).im = 0) := by
  let f (t : ℝ) := o + o * circleRotation t
  have hf : Function.Injective f := by
    intro t s hts
    exact circleRotation_injective (mul_left_cancel₀ ho (add_left_cancel hts))
  obtain ⟨_, ⟨t, rfl⟩, ht⟩ := (Set.infinite_range_of_injective hf).exists_not_mem_finset
    (Finset.univ.image a)
  let p := f t
  let u := o - p
  have hu : u ≠ 0 := by
    have heq : u = -(o * circleRotation t) := by dsimp only [u, p, f]; ring
    rw [heq]
    exact neg_ne_zero.mpr (mul_ne_zero ho (fun he => by
      have hn := circleRotation_normSq t
      rw [he, Complex.normSq_zero] at hn
      exact zero_ne_one hn))
  have hnorm : Complex.normSq u = Complex.normSq o := by
    have heq : u = -(o * circleRotation t) := by dsimp only [u, p, f]; ring
    rw [heq, Complex.normSq_neg, Complex.normSq_mul, circleRotation_normSq, mul_one]
  have hreg (i : ι) : a i - p ≠ 0 := fun h =>
    ht (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, sub_eq_zero.mp h⟩)
  let k := Complex.I / 2
  let β := -k * p - Complex.I * u
  have hd : k * -p - β * 1 ≠ 0 := by
    have he : k * -p - β * 1 = Complex.I * u := by dsimp only [β]; ring
    rw [he]
    exact mul_ne_zero Complex.I_ne_zero hu
  have hchart (i : ι) :
      (fractionalMap k β 1 (-p) (a i)).im =
        (Complex.normSq (a i - o) - Complex.normSq o) /
          (2 * Complex.normSq (a i - p)) := by
    let w := a i - p
    have hn : 0 < Complex.normSq w := Complex.normSq_pos.mpr (hreg i)
    have hh : fractionalMap k β 1 (-p) (a i) = k - Complex.I * (u / w) := by
      simp only [fractionalMap, β, one_mul, ← sub_eq_add_neg]
      change _ / w = _
      field_simp [hreg i] <;> dsimp only [w] <;> ring
    have hcross : (u / w).re * Complex.normSq w = (w * star u).re := by
      rw [Complex.div_re, div_mul_cancel₀ _ hn.ne']
      simp only [Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im]
      ring
    have hnorm' : Complex.normSq (a i - o) =
        Complex.normSq w + Complex.normSq o - 2 * (w * star u).re := by
      rw [show a i - o = w - u by dsimp only [w, u]; ring, Complex.normSq_sub, hnorm] <;> rfl
    rw [hh, hnorm']
    have hk : k.im = 1 / 2 := by norm_num [k, Complex.div_im, Complex.normSq_apply]
    simp only [Complex.sub_im, Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul,
      one_mul, zero_add, hk]
    have hden : 2 * Complex.normSq w ≠ 0 := mul_ne_zero (by norm_num) hn.ne'
    apply (eq_div_iff hden).mpr
    linear_combination -2 * hcross
  refine ⟨k, β, 1, -p, hd, (fun i => by simpa only [one_mul, ← sub_eq_add_neg] using hreg i),
    ?_, ?_⟩
  · intro i
    rw [hchart]
    exact div_nonneg (sub_nonneg.mpr (ha i)) (mul_nonneg (by norm_num) (Complex.normSq_nonneg _))
  · intro i he
    rw [hchart, he, sub_self, zero_div]

private theorem holds_of_five_upper_chart
    (a b : Fin 5 → ℂ) (U : Matrix (Fin 5) (Fin 5) ℂ) (hU : IsUnitary U)
    (ha : Function.Injective a) (hpos : ∀ i, 0 ≤ (a i).im)
    (i j k : Fin 5) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hi : (a i).im = 0) (hj : (a j).im = 0) (hk : (a k).im = 0)
    (d : ℂ) (hd : d ≠ 0)
    (h : ∀ x y : Fin 5 → ℂ, Function.Injective x →
      ∀ p q : Fin 5, (∀ l, l ≠ p → l ≠ q → (x l).im = 0) →
      (∃ r : ℝ, x p - x q = (r : ℂ) * d) → Holds x y U) :
    Holds a b U := by
  classical
  let S : Finset (Fin 5) := {i, j, k}
  have hS : S.card = 3 := by
    simp [S, Finset.card_insert_of_not_mem, hij, hik, hjk]
  let T := (Finset.univ : Finset (Fin 5)) \ S
  have hT : T.card = 2 := by
    change (Finset.univ \ S).card = 2
    rw [Finset.card_sdiff (Finset.subset_univ S), hS]
    decide
  obtain ⟨p, q, hpq, hEq⟩ := Finset.card_eq_two.mp hT
  apply holds_of_open_curve_chart a b U hU ha p q hpq (d := d) (hd := hd)
  · intro l hlp hlq
    have hl : l ∈ S := by
      by_contra hs
      have ht : l ∈ T := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hs⟩
      rw [hEq] at ht
      exact (by simpa [hlp, hlq] using ht : False)
    rcases (by simpa only [S, Finset.mem_insert, Finset.mem_singleton] using hl :
      l = i ∨ l = j ∨ l = k) with rfl | rfl | rfl
    · exact hi
    · exact hj
    · exact hk
  · exact hpos p
  · exact hpos q
  · exact fun x y hx hreal hsec => h x y hx p q hreal hsec

private theorem five_open_curve_reduction
    (U : Matrix (Fin 5) (Fin 5) ℂ) (hU : IsUnitary U) (d : ℂ) (hd : d ≠ 0)
    (h : ∀ x y : Fin 5 → ℂ, Function.Injective x →
      ∀ p q : Fin 5, (∀ l, l ≠ p → l ≠ q → (x l).im = 0) →
      (∃ r : ℝ, x p - x q = (r : ℂ) * d) → Holds x y U) :
    ∀ a b : Fin 5 → ℂ, Holds a b U := by
  classical
  apply holds_all_of_injective_left U
  intro a b ha
  let P : Finset (Fin 5 × Fin 5) := Finset.univ.filter fun p => p.1 ≠ p.2
  have hP : P.Nonempty :=
    ⟨(0, 1), Finset.mem_filter.mpr ⟨Finset.mem_univ _, by decide⟩⟩
  let D (p : Fin 5 × Fin 5) := Complex.normSq (a p.2 - a p.1)
  obtain ⟨p, hp, hmin⟩ := Finset.exists_min_image P D hP
  let i := p.1
  let j := p.2
  have hij : i ≠ j := (Finset.mem_filter.mp hp).2
  let Δ := a j - a i
  have hΔ : Δ ≠ 0 := sub_ne_zero.mpr (ha.ne hij.symm)
  let x (l : Fin 5) := (a l - a i) / Δ
  have hx : Function.Injective x := by
    intro l m he
    have h' : x l * Δ = x m * Δ := congrArg (· * Δ) he
    simp only [x, div_mul_cancel₀ _ hΔ] at h'
    exact ha (sub_left_inj.mp h')
  have hxi : x i = 0 := by simp [x]
  have hxj : x j = 1 := div_self hΔ
  have hnx (l : Fin 5) (hli : l ≠ i) : 1 ≤ Complex.normSq (x l) := by
    have hr := hmin (i, l) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hli.symm⟩)
    change Complex.normSq Δ ≤ Complex.normSq (a l - a i) at hr
    rw [show x l = (a l - a i) / Δ from rfl, Complex.normSq_div]
    exact (le_div_iff₀ (Complex.normSq_pos.mpr hΔ)).mpr (by rwa [one_mul])
  have hnx' (l : Fin 5) (hlj : l ≠ j) : 1 ≤ Complex.normSq (x l - 1) := by
    have hr := hmin (j, l) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlj.symm⟩)
    change Complex.normSq Δ ≤ Complex.normSq (a l - a j) at hr
    rw [show x l - 1 = (a l - a j) / Δ by
      change (a l - a i) / Δ - 1 = (a l - a j) / Δ
      field_simp [hΔ] <;> dsimp only [Δ] <;> ring, Complex.normSq_div]
    exact (le_div_iff₀ (Complex.normSq_pos.mpr hΔ)).mpr (by rwa [one_mul])
  let E (l : Fin 5) := Complex.normSq (x l) - (x l).re
  have hE₀ : E i = 0 := by simp [E, hxi]
  have hE₁ : E j = 0 := by simp [E, hxj]
  have hE (l : Fin 5) (hli : l ≠ i) (hlj : l ≠ j) : 0 < E l := by
    have h₁ := hnx l hli
    have h₂ := hnx' l hlj
    rw [Complex.normSq_sub, Complex.normSq_one, map_one, mul_one] at h₂
    dsimp only [E]
    linarith
  have hxaff : x = fun l => Δ⁻¹ * a l - Δ⁻¹ * a i := by
    funext l
    simp only [x, div_eq_mul_inv]
    ring
  have hleft : (fun l => Δ⁻¹ * a l + -(Δ⁻¹ * a i)) = x := by
    simpa only [sub_eq_add_neg] using hxaff.symm
  have hright : (fun l => Δ⁻¹ * b l - (-(Δ⁻¹ * a i))) =
      (fun l => Δ⁻¹ * b l + Δ⁻¹ * a i) := by
    funext l
    rw [sub_neg_eq_add]
  apply (holds_affine_spectral_iff a b U hU Δ⁻¹ (-(Δ⁻¹ * a i)) (inv_ne_zero hΔ)).mp
  rw [hleft, hright]
  generalize (fun l => Δ⁻¹ * b l + Δ⁻¹ * a i) = c
  by_cases hcol : ∀ l, (x l).im = 0
  · exact h x c hx 0 0 (fun l _ _ => hcol l) ⟨0, by simp⟩
  · push_neg at hcol
    obtain ⟨k₀, hk₀⟩ := hcol
    let η : ℝ := if 0 < (x k₀).im then 1 else -1
    let G (l : Fin 5) := 2 * η * (x l).im
    have hGi : G i = 0 := by simp [G, hxi]
    have hGj : G j = 0 := by simp [G, hxj]
    let Q := (Finset.univ : Finset (Fin 5)).filter fun l => 0 < G l
    have hQ : Q.Nonempty := by
      refine ⟨k₀, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
      change 0 < 2 * η * (x k₀).im
      by_cases ht : 0 < (x k₀).im
      · simpa only [η, if_pos ht, mul_one] using mul_pos (by norm_num : (0 : ℝ) < 2) ht
      · have hneg := lt_of_le_of_ne (le_of_not_gt ht) hk₀
        simp only [η, if_neg ht]
        nlinarith
    obtain ⟨k, hk, hleast⟩ := Finset.exists_min_image Q (fun l => E l / G l) hQ
    have hGk : 0 < G k := (Finset.mem_filter.mp hk).2
    have hki : k ≠ i := fun he => hGk.ne' (he.symm ▸ hGi)
    have hkj : k ≠ j := fun he => hGk.ne' (he.symm ▸ hGj)
    let s := E k / G k
    have hs : 0 ≤ s := (div_pos (hE k hki hkj) hGk).le
    let o : ℂ := ⟨1/2, s * η⟩
    have ho : o ≠ 0 := by
      intro he
      have hzero := congrArg Complex.re he
      change (1 / 2 : ℝ) = 0 at hzero
      norm_num at hzero
    have hgap (l : Fin 5) : Complex.normSq (x l - o) - Complex.normSq o = E l - s * G l := by
      simp only [o, E, G, Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
      ring
    have hB (l : Fin 5) : Complex.normSq o ≤ Complex.normSq (x l - o) := by
      apply sub_nonneg.mp
      rw [hgap]
      by_cases hl : 0 < G l
      · have hsl := hleast l (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hl⟩)
        exact sub_nonneg.mpr ((le_div_iff₀ hl).mpr hsl)
      · have hEn : 0 ≤ E l := by
          by_cases hli : l = i
          · rwa [hli, hE₀]
          · by_cases hlj : l = j
            · rwa [hlj, hE₁]
            · exact (hE l hli hlj).le
        exact sub_nonneg.mpr ((mul_nonpos_of_nonneg_of_nonpos hs (le_of_not_gt hl)).trans hEn)
    obtain ⟨α, β, γ, δ, hdet, hreg, hUp, hBoundary⟩ := exists_exterior_circle_chart x o ho hB
    apply holds_of_fractional_spectral_test x c U hU α β γ δ hdet hreg
    intro y
    let z := fractionalMap α β γ δ ∘ x
    have hz : Function.Injective z := fun l m he =>
      hx (fractionalMap_injOn α β γ δ hdet (hreg l) (hreg m) he)
    have hb₀ : Complex.normSq (x i - o) = Complex.normSq o :=
      sub_eq_zero.mp (by rw [hgap, hE₀, hGi, mul_zero, sub_zero])
    have hb₁ : Complex.normSq (x j - o) = Complex.normSq o :=
      sub_eq_zero.mp (by rw [hgap, hE₁, hGj, mul_zero, sub_zero])
    have hbk : Complex.normSq (x k - o) = Complex.normSq o :=
      sub_eq_zero.mp (by rw [hgap, show s = E k / G k from rfl,
        div_mul_cancel₀ _ hGk.ne', sub_self])
    exact holds_of_five_upper_chart z y U hU hz hUp i j k hij hki.symm hkj.symm
      (hBoundary i hb₀) (hBoundary j hb₁) (hBoundary k hbk) d hd h

/-- The order-five parabola test. The circle comes from the nearest pair
and the first point reached by moving the center on its perpendicular
bisector. Boundary coincidences are included by closedness. -/
theorem five_spectralParabola_test_iff (U : Matrix (Fin 5) (Fin 5) ℂ) (hU : IsUnitary U) :
    SpectralCurveTest spectralParabola U ↔ ∀ a b : Fin 5 → ℂ, Holds a b U := by
  constructor
  · intro h
    apply five_open_curve_reduction U hU 1 one_ne_zero
    rintro x y hx p q hreal ⟨r, hr⟩
    apply holds_of_parabolic_test_at_two_heights x y U hU h hx (x p).im
    intro l
    by_cases hlp : l = p
    · exact Or.inr (by rw [hlp])
    · by_cases hlq : l = q
      · right
        have he := congrArg Complex.im hr
        simp only [Complex.sub_im, mul_one, Complex.ofReal_im] at he
        rw [hlq, sub_eq_zero.mp he]
      · exact Or.inl (hreal l hlp hlq)
  · intro h a b _ _
    exact h a b

/-- The order-five hyperbola test, for any choice of its two nonparallel
asymptote directions and fixed product parameter. -/
theorem five_spectralHyperbola_test_iff (d : ℂ) (k : ℝ) (hdim : d.im ≠ 0)
    (U : Matrix (Fin 5) (Fin 5) ℂ) (hU : IsUnitary U) :
    SpectralCurveTest (spectralHyperbola d k) U ↔ ∀ a b : Fin 5 → ℂ, Holds a b U := by
  constructor
  · intro h
    apply five_open_curve_reduction U hU d (fun he => hdim (congrArg Complex.im he))
    rintro x y hx p q hreal ⟨r, hr⟩
    let s : ℝ := (x p).im / d.im
    let z : ℝ := (x p).re - s * d.re
    have hs : s * d.im = (x p).im := div_mul_cancel₀ _ hdim
    have hp : x p = (z : ℂ) + (s : ℂ) * d := by
      apply Complex.ext
      · simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
          zero_mul, sub_zero, z]
        ring
      · simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
          zero_mul, add_zero, zero_add, hs]
    have hq : x q = (z : ℂ) + ((s - r : ℝ) : ℂ) * d := by
      have hpq := sub_eq_iff_eq_add.mp hr
      rw [hp] at hpq
      rw [Complex.ofReal_sub]
      linear_combination -hpq
    apply holds_of_hyperbolic_test_on_two_intersecting_lines x y d k U hU h hx z
    intro l
    by_cases hlp : l = p
    · exact Or.inr ⟨s, hlp.symm ▸ hp⟩
    · by_cases hlq : l = q
      · exact Or.inr ⟨s - r, hlq.symm ▸ hq⟩
      · exact Or.inl (hreal l hlp hlq)
  · intro h a b _ _
    exact h a b

end

end MOC
