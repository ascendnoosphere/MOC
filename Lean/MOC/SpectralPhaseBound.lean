import MOC.SpectralKKT
import Mathlib.Tactic.LinearCombination

/-! A coordinate bound when the normalized gap has one active matching. -/

open BigOperators Filter Matrix
open scoped ComplexConjugate Topology

namespace MOC

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private def phaseLeft (a : ι → ℂ) : ι ⊕ ι → ℂ → ι → ℂ
  | .inl i, z => Function.update a i (z * a i)
  | .inr _, _ => a

private def phaseRight (b : ι → ℂ) : ι ⊕ ι → ℂ → ι → ℂ
  | .inl _, _ => b
  | .inr j, z => Function.update b j (z * b j)

private theorem phase_energy (a b : ι → ℂ) (k : ι ⊕ ι) (z : ℂ)
    (hz : Complex.normSq z = 1) :
    spectralEnergy (phaseLeft a k z) (phaseRight b k z) = spectralEnergy a b := by
  have hu (f : ι → ℂ) (i : ι) (j : ι) :
      Complex.normSq (Function.update f i (z * f i) j) = Complex.normSq (f j) := by
    by_cases h : j = i
    · subst j
      rw [Function.update_self, map_mul, hz, one_mul]
    · rw [Function.update_of_ne h]
  cases k <;> simp only [phaseLeft, phaseRight, spectralEnergy, hu]

private theorem phase_matching (a b : ι → ℂ) (σ : Equiv.Perm ι) (k : ι ⊕ ι) (z : ℂ) :
    matchingProduct (phaseLeft a k z) (phaseRight b k z) σ =
      matchingProduct a b σ +
        matchingCoordinateCoefficient a b σ k * ((z - 1) * Sum.elim a b k) := by
  let j := Sum.elim σ.symm id k
  let f (l : ι) := a (σ l) + b l
  let F (l : ι) := phaseLeft a k z (σ l) + phaseRight b k z l
  have ho (l : ι) (hl : l ≠ j) : F l = f l := by
    cases k with
    | inl i =>
      have hi : σ l ≠ i := fun h => hl (by simpa using congrArg σ.symm h)
      simp [F, f, phaseLeft, phaseRight, Function.update_of_ne hi]
    | inr i =>
      have hi : l ≠ i := hl
      simp [F, f, phaseLeft, phaseRight, Function.update_of_ne hi]
  have hj : F j = f j + (z - 1) * Sum.elim a b k := by
    cases k with
    | inl i =>
      change Function.update a i (z * a i) (σ (σ.symm i)) + b (σ.symm i) =
        a (σ (σ.symm i)) + b (σ.symm i) + (z - 1) * a i
      have he : σ (σ.symm i) = i := σ.apply_symm_apply i
      have hupdate : Function.update a i (z * a i) (σ (σ.symm i)) = z * a i :=
        (congrArg (Function.update a i (z * a i)) he).trans (Function.update_self i _ a)
      rw [hupdate, he]
      ring
    | inr i =>
      change a (σ i) + Function.update b i (z * b i) i =
        a (σ i) + b i + (z - 1) * b i
      rw [Function.update_self]
      ring
  have hp : (∏ l ∈ Finset.univ.erase j, F l) = ∏ l ∈ Finset.univ.erase j, f l := by
    exact Finset.prod_congr rfl fun l hl => ho l (Finset.mem_erase.mp hl).1
  have hcoef : matchingCoordinateCoefficient a b σ k = ∏ l ∈ Finset.univ.erase j, f l := by
    cases k <;> rfl
  change (∏ l, F l) = (∏ l, f l) + _
  rw [← Finset.prod_erase_mul _ F (Finset.mem_univ j), hp, hj,
    ← Finset.prod_erase_mul _ f (Finset.mem_univ j), hcoef, mul_add]

private theorem phase_determinant (a b : ι → ℂ) (U : Matrix ι ι ℂ) (hU : IsUnitary U)
    (k : ι ⊕ ι) (z : ℂ) :
    determinantValue (phaseLeft a k z) (phaseRight b k z) U =
      determinantValue a b U +
        determinantCoordinateCoefficient a b U k * ((z - 1) * Sum.elim a b k) := by
  rw [← signed_determinant _ _ U hU, ← signed_determinant a b U hU]
  simp only [phase_matching, determinantCoordinateCoefficient, mul_add,
    Finset.sum_add_distrib, Finset.sum_mul, mul_assoc]

private def unitPhase (t : ℝ) : ℂ :=
  (((1 - t ^ 2) / (1 + t ^ 2) : ℝ) : ℂ) + ((2 * t / (1 + t ^ 2) : ℝ) : ℂ) * Complex.I

private theorem continuous_unitPhase : Continuous unitPhase := by
  have hden (t : ℝ) : 1 + t ^ 2 ≠ 0 := by positivity
  have hc : Continuous (fun t : ℝ => 1 + t ^ 2) := by fun_prop
  have hre := (show Continuous (fun t : ℝ => 1 - t ^ 2) by fun_prop).div₀ hc hden
  have him := (show Continuous (fun t : ℝ => 2 * t) by fun_prop).div₀ hc hden
  exact (Complex.continuous_ofReal.comp hre).add
    ((Complex.continuous_ofReal.comp him).mul continuous_const)

private theorem unitPhase_normSq (t : ℝ) : Complex.normSq (unitPhase t) = 1 := by
  have h : 1 + t ^ 2 ≠ 0 := by positivity
  rw [unitPhase, Complex.normSq_add_mul_I]
  field_simp [h]
  ring

private theorem unitPhase_ne_one {t : ℝ} (ht : t ≠ 0) : unitPhase t ≠ 1 := by
  intro he
  have him := congrArg Complex.im he
  have h : 1 + t ^ 2 ≠ 0 := by positivity
  have hn : (2 : ℝ) * t / (1 + t ^ 2) ≠ 0 := div_ne_zero (mul_ne_zero (by norm_num) ht) h
  exact hn (by simpa only [unitPhase, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
    Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.one_im, mul_zero, mul_one,
    add_zero, zero_add] using him)

private theorem radial_phase_bound (g q : ℝ) (hg : 0 < g)
    (hmax : ∀ᶠ t in 𝓝 (0 : ℝ),
      Complex.normSq ((g : ℂ) + ((g * q : ℝ) : ℂ) * (unitPhase t - 1)) ≤ g * g) :
    q ≤ 1 := by
  by_contra! hq
  obtain ⟨t, ht, ht0⟩ := ((hmax.filter_mono
    (nhdsWithin_le_nhds : 𝓝[≠] (0 : ℝ) ≤ 𝓝 0)).and self_mem_nhdsWithin).exists
  have hunit := unitPhase_normSq t
  have hid : Complex.normSq ((g : ℂ) + ((g * q : ℝ) : ℂ) * (unitPhase t - 1)) =
      g * g + g * g * (q * (q - 1)) * Complex.normSq (unitPhase t - 1) := by
    simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re,
      Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im,
      Complex.ofReal_re, Complex.ofReal_im] at hunit ⊢
    linear_combination (g * g * q) * hunit
  have hpos := mul_pos (mul_pos (mul_pos hg hg)
    (mul_pos (zero_lt_one.trans hq) (sub_pos.mpr hq)))
    (Complex.normSq_pos.mpr (sub_ne_zero.mpr (unitPhase_ne_one ht0)))
  rw [hid] at ht
  exact (not_lt_of_ge ht) (lt_add_of_pos_right _ hpos)

/-- If a positive normalized support gap has one active matching, each spectral
coordinate carries at most the reciprocal of the matrix order in squared norm. -/
theorem spectral_coordinate_bound_of_unique_active [Nonempty ι]
    (a b : ι → ℂ) (U : Matrix ι ι ℂ) (hU : IsUnitary U)
    (η : ℂ) (g : ℝ) (σ : Equiv.Perm ι)
    (henergy : spectralEnergy a b = 1) (hη : Complex.normSq η = 1) (hg : 0 < g)
    (hσ : (η * (determinantValue a b U - matchingProduct a b σ)).re = g)
    (hstrict : ∀ τ : Equiv.Perm ι, τ ≠ σ →
      g < (η * (determinantValue a b U - matchingProduct a b τ)).re)
    (hmax : ∀ (c d : ι → ℂ) (κ : ℂ), spectralEnergy c d ≤ 1 → Complex.normSq κ = 1 →
      ∃ τ : Equiv.Perm ι, (κ * (determinantValue c d U - matchingProduct c d τ)).re ≤ g)
    (k : ι ⊕ ι) : (Fintype.card ι : ℝ) * Complex.normSq (Sum.elim a b k) ≤ 1 := by
  let active := {τ : Equiv.Perm ι //
    (η * (determinantValue a b U - matchingProduct a b τ)).re = g}
  have hgap (τ : Equiv.Perm ι) :
      g ≤ (η * (determinantValue a b U - matchingProduct a b τ)).re := by
    by_cases h : τ = σ
    · subst τ
      exact hσ.ge
    · exact (hstrict τ h).le
  obtain ⟨s, w, _, hw, hval, hcoord⟩ := exists_active_matching_coordinate_balance a b U hU η g
    henergy hgap (fun c d he => hmax c d η he hη)
  have hsingle (τ : active) : τ.1 = σ := by
    by_contra h
    exact (ne_of_gt (hstrict τ.1 h)) τ.2
  have hsum (f : Equiv.Perm ι → ℂ) : (∑ τ ∈ s, (w τ : ℂ) * f τ.1) = f σ := by
    simp_rw [hsingle]
    rw [← Finset.sum_mul, ← Complex.ofReal_sum, hw, Complex.ofReal_one, one_mul]
  rw [hsum (fun τ => η * (determinantValue a b U - matchingProduct a b τ))] at hval
  have hco := hcoord k
  rw [hsum (fun τ => η * (determinantCoordinateCoefficient a b U k -
    matchingCoordinateCoefficient a b τ k))] at hco
  let A (t : ℝ) := phaseLeft a k (unitPhase t)
  let B (t : ℝ) := phaseRight b k (unitPhase t)
  let G (τ : Equiv.Perm ι) (t : ℝ) := η * (determinantValue (A t) (B t) U -
    matchingProduct (A t) (B t) τ)
  have hG (τ : Equiv.Perm ι) (t : ℝ) : G τ t =
      η * (determinantValue a b U - matchingProduct a b τ) +
        η * (determinantCoordinateCoefficient a b U k - matchingCoordinateCoefficient a b τ k) *
          ((unitPhase t - 1) * Sum.elim a b k) := by
    dsimp only [G, A, B]
    rw [phase_determinant _ _ U hU, phase_matching]
    ring
  have hG0 (τ : Equiv.Perm ι) :
      G τ 0 = η * (determinantValue a b U - matchingProduct a b τ) := by
    simp [hG, unitPhase]
  have hc (τ : Equiv.Perm ι) : Continuous (G τ) := by
    rw [show G τ = _ from funext (hG τ)]
    exact continuous_const.add (continuous_const.mul ((continuous_unitPhase.sub
      continuous_const).mul continuous_const))
  let S (t : ℝ) := Real.sqrt (Complex.normSq (G σ t))
  let p (t : ℝ) := conj (G σ t) / (S t : ℂ)
  have hs0 : S 0 = g := by
    dsimp only [S]
    rw [hG0, hval, Complex.normSq_ofReal, Real.sqrt_mul_self hg.le]
  have hp0 : p 0 = 1 := by
    simp [p, hG0, hval, hs0, hg.ne']
  have hsc : Continuous S := Real.continuous_sqrt.comp (Complex.continuous_normSq.comp (hc σ))
  have hpc : ContinuousAt p 0 := by
    refine ((hc σ).continuousAt.star).div₀
      (Complex.continuous_ofReal.continuousAt.comp hsc.continuousAt) ?_
    exact_mod_cast (show S 0 ≠ 0 by rw [hs0]; exact hg.ne')
  have hspos : ∀ᶠ t in 𝓝 (0 : ℝ), 0 < S t :=
    hsc.continuousAt.eventually_mem (Ioi_mem_nhds (hs0.symm ▸ hg))
  have hother : ∀ᶠ t in 𝓝 (0 : ℝ),
      ∀ τ : {τ : Equiv.Perm ι // τ ≠ σ}, g < (p t * G τ.1 t).re := by
    apply Filter.eventually_all.mpr
    intro τ
    have ht : ContinuousAt (fun t => (p t * G τ.1 t).re) 0 :=
      Complex.continuous_re.continuousAt.comp (hpc.mul (hc τ.1).continuousAt)
    exact ht.eventually_mem (Ioi_mem_nhds (by simpa [hp0, hG0] using hstrict τ.1 τ.2))
  apply radial_phase_bound g _ hg
  filter_upwards [hspos, hother] with t ht hother
  have hSq : S t * S t = Complex.normSq (G σ t) :=
    Real.mul_self_sqrt (Complex.normSq_nonneg _)
  have hSq₀ : Complex.normSq (G σ t) ≠ 0 := by rw [← hSq]; positivity
  have hpn : Complex.normSq (p t) = 1 := by
    dsimp only [p]
    rw [Complex.normSq_div, Complex.normSq_conj, Complex.normSq_ofReal, hSq, div_self hSq₀]
  have hE : spectralEnergy (A t) (B t) ≤ 1 :=
    ((phase_energy _ _ _ _ (unitPhase_normSq t)).trans henergy).le
  obtain ⟨τ, hτ⟩ := hmax (A t) (B t) (p t * η) hE (by rw [map_mul, hpn, hη, mul_one])
  rw [mul_assoc] at hτ
  change (p t * G τ t).re ≤ g at hτ
  have hτσ : τ = σ := Classical.byContradiction fun h => (not_lt_of_ge hτ) (hother ⟨τ, h⟩)
  subst τ
  have halign : p t * G σ t = (S t : ℂ) := by
    have hne : (S t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
    dsimp only [p]
    rw [div_mul_eq_mul_div₀, ← Complex.normSq_eq_conj_mul_self, ← hSq,
      Complex.ofReal_mul, mul_div_cancel_right₀ _ hne]
  rw [halign, Complex.ofReal_re] at hτ
  have hle : Complex.normSq (G σ t) ≤ g * g := by
    rw [← hSq]
    exact mul_le_mul hτ hτ ht.le hg.le
  have hform : G σ t =
      (g : ℂ) + ((g * ((Fintype.card ι : ℝ) * Complex.normSq (Sum.elim a b k)) : ℝ) : ℂ) *
        (unitPhase t - 1) := by
    rw [hG, hval, hco]
    let x := Sum.elim a b k
    let n : ℝ := Fintype.card ι
    calc
      _ = (g : ℂ) + ((n * g : ℝ) : ℂ) * (conj x * x) * (unitPhase t - 1) := by
        dsimp only [x, n]
        ring
      _ = _ := by
        rw [← Complex.normSq_eq_conj_mul_self]
        simp only [n, x, Complex.ofReal_mul]
        ring
  rwa [← hform]

end

end MOC
