import MOC.Weights
import Mathlib.Tactic.LinearCombination

/-! A fixed permutation law on one spectral side can be tested by interpolation. -/

open BigOperators Matrix
open scoped ComplexConjugate

namespace MOC

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The weighted sum of matching products for real weights. -/
def weightedMatchingValue (a b : ι → ℂ) (w : Equiv.Perm ι → ℝ) : ℂ :=
  ∑ σ, (w σ : ℂ) * matchingProduct a b σ

/-- One probability law works for every second spectrum at fixed first spectrum
and relative unitary. -/
def HasCommonWeights (a : ι → ℂ) (U : Matrix ι ι ℂ) : Prop :=
  ∃ w : Equiv.Perm ι → ℝ, (∀ σ, 0 ≤ w σ) ∧ (∑ σ, w σ = 1) ∧
    ∀ b, weightedMatchingValue a b w = determinantValue a b U

theorem HasCommonWeights.holds {a : ι → ℂ} {U : Matrix ι ι ℂ}
    (h : HasCommonWeights a U) (b : ι → ℂ) : Holds a b U := by
  obtain ⟨w, hw, hs, hb⟩ := h
  exact holds_of_weights w hw hs (hb b)

theorem matching_update_interp (a b : ι → ℂ) (j : ι) (σ : Equiv.Perm ι) (z : ℂ) :
    let m (t : ℂ) := matchingProduct a (Function.update b j t) σ
    m z = m 0 + (m 1 - m 0) * z := by
  dsimp only
  let c := ∏ k ∈ Finset.univ.erase j, (a (σ k) + b k)
  have hm (t : ℂ) : matchingProduct a (Function.update b j t) σ = (a (σ j) + t) * c := by
    unfold matchingProduct
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j), Function.update_self]
    congr 1
    apply Finset.prod_congr rfl
    intro k hk
    rw [Function.update_of_ne (Finset.mem_erase.mp hk).1]
  rw [hm z, hm 0, hm 1]
  ring

private theorem weighted_matching_update_interp (a b : ι → ℂ) (j : ι)
    (w : Equiv.Perm ι → ℝ) (z : ℂ) :
    let F (t : ℂ) := weightedMatchingValue a (Function.update b j t) w
    F z = F 0 + (F 1 - F 0) * z := by
  let m (t : ℂ) (σ : Equiv.Perm ι) := matchingProduct a (Function.update b j t) σ
  change (∑ σ, (w σ : ℂ) * m z σ) =
    (∑ σ, (w σ : ℂ) * m 0 σ) +
      ((∑ σ, (w σ : ℂ) * m 1 σ) - ∑ σ, (w σ : ℂ) * m 0 σ) * z
  have hm (σ : Equiv.Perm ι) : m z σ = m 0 σ + (m 1 σ - m 0 σ) * z :=
    matching_update_interp a b j σ z
  calc
    _ = ∑ σ, ((w σ : ℂ) * m 0 σ + ((w σ : ℂ) * m 1 σ - (w σ : ℂ) * m 0 σ) * z) := by
      apply Finset.sum_congr rfl
      intro σ _
      rw [hm σ]
      ring
    _ = _ := by rw [Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_sub_distrib]

theorem determinant_update_interp (a b : ι → ℂ) (j : ι) (U : Matrix ι ι ℂ)
    (hU : IsUnitary U) (z : ℂ) :
    let d (t : ℂ) := determinantValue a (Function.update b j t) U
    d z = d 0 + (d 1 - d 0) * z := by
  simpa only [weightedMatchingValue, real_signed_determinant _ _ U hU] using
    weighted_matching_update_interp a b j (realSignedWeight U) z

/-- Agreement at two values of a single partner entry implies agreement at
every value of that entry, with the other entries and the weights fixed. -/
theorem weightedMatchingValue_eq_of_two_updates (a b : ι → ℂ) (U : Matrix ι ι ℂ)
    (hU : IsUnitary U) (w : Equiv.Perm ι → ℝ) (j : ι) {s t : ℂ} (hst : s ≠ t)
    (hs : weightedMatchingValue a (Function.update b j s) w =
      determinantValue a (Function.update b j s) U)
    (ht : weightedMatchingValue a (Function.update b j t) w =
      determinantValue a (Function.update b j t) U) (z : ℂ) :
    weightedMatchingValue a (Function.update b j z) w =
      determinantValue a (Function.update b j z) U := by
  let f (r : ℂ) := weightedMatchingValue a (Function.update b j r) w
  let g (r : ℂ) := determinantValue a (Function.update b j r) U
  have hf (r : ℂ) : f r = f 0 + (f 1 - f 0) * r :=
    weighted_matching_update_interp a b j w r
  have hg (r : ℂ) : g r = g 0 + (g 1 - g 0) * r :=
    determinant_update_interp a b j U hU r
  change f s = g s at hs
  change f t = g t at ht
  change f z = g z
  have hprod : ((f 1 - f 0) - (g 1 - g 0)) * (s - t) = 0 := calc
    _ = (f s - g s) - (f t - g t) := by
      rw [hf s, hg s, hf t, hg t]
      ring
    _ = 0 := by simp only [hs, ht, sub_self]
  have hcoeff := (mul_eq_zero.mp hprod).resolve_right (sub_ne_zero.mpr hst)
  rw [hf s, hg s] at hs
  rw [hf z, hg z]
  linear_combination hs + (z - s) * hcoeff

/-- A fixed law for the (2^n) zero-one partners works for every complex partner. -/
theorem weightedMatchingValue_eq_all_iff_binary (a : ι → ℂ) (U : Matrix ι ι ℂ)
    (hU : IsUnitary U) (w : Equiv.Perm ι → ℝ) :
    (∀ b, weightedMatchingValue a b w = determinantValue a b U) ↔
      ∀ b : ι → ℂ, (∀ i, b i = 0 ∨ b i = 1) →
        weightedMatchingValue a b w = determinantValue a b U := by
  constructor
  · exact fun h b _ => h b
  · intro h
    have hall (S : Finset ι) :
        ∀ b : ι → ℂ, (∀ j, j ∉ S → b j = 0 ∨ b j = 1) →
          weightedMatchingValue a b w = determinantValue a b U := by
      induction S using Finset.induction_on with
      | empty => exact fun b hb => h b (fun j => hb j (by simp))
      | @insert i S hi ih =>
        intro b hb
        have htest (z : ℂ) (hz : z = 0 ∨ z = 1) :
            weightedMatchingValue a (Function.update b i z) w =
              determinantValue a (Function.update b i z) U := by
          apply ih
          intro j hj
          by_cases hji : j = i
          · subst j
            simpa only [Function.update_self] using hz
          · rw [Function.update_of_ne hji]
            exact hb j (by simp [hji, hj])
        have he := weightedMatchingValue_eq_of_two_updates a b U hU w i zero_ne_one
          (htest 0 (Or.inl rfl)) (htest 1 (Or.inr rfl)) (b i)
        simpa only [Function.update_eq_self] using he
    exact fun b => hall Finset.univ b fun j hj => (hj (Finset.mem_univ j)).elim

/-- For common weights, testing all real partners is already equivalent to
testing all complex partners. -/
theorem weightedMatchingValue_eq_all_iff_real (a : ι → ℂ) (U : Matrix ι ι ℂ)
    (hU : IsUnitary U) (w : Equiv.Perm ι → ℝ) :
    (∀ b, weightedMatchingValue a b w = determinantValue a b U) ↔
      ∀ b : ι → ℝ, weightedMatchingValue a (fun i => (b i : ℂ)) w =
        determinantValue a (fun i => (b i : ℂ)) U := by
  constructor
  · exact fun h b => h _
  · intro h
    apply (weightedMatchingValue_eq_all_iff_binary a U hU w).mpr
    intro b hb
    have hb' : (fun i => ((b i).re : ℂ)) = b := by
      funext i
      rcases hb i with hi | hi <;> simp [hi]
    simpa only [hb'] using h (fun i => (b i).re)

private theorem weightedMatchingValue_conj (a : ι → ℝ) (b : ι → ℂ)
    (w : Equiv.Perm ι → ℝ) :
    weightedMatchingValue (fun i => (a i : ℂ)) (fun i => conj (b i)) w =
      conj (weightedMatchingValue (fun i => (a i : ℂ)) b w) := by
  simp only [weightedMatchingValue, matchingProduct, map_sum, map_prod, map_mul, map_add,
    Complex.conj_ofReal]

/-- With a real first spectrum and real weights, one frozen nonreal partner
entry is equivalent to freeing that entry. In order five this turns a
common law for one four-entry slice into a common law for all five entries. -/
theorem weightedMatchingValue_eq_all_iff_frozen_nonreal (a : ι → ℝ) (U : Matrix ι ι ℂ)
    (hU : IsUnitary U) (w : Equiv.Perm ι → ℝ) (j : ι) {c : ℂ} (hc : c.im ≠ 0) :
    (∀ b, weightedMatchingValue (fun i => (a i : ℂ)) b w =
      determinantValue (fun i => (a i : ℂ)) b U) ↔
    ∀ b : ι → ℂ,
      weightedMatchingValue (fun i => (a i : ℂ)) (Function.update b j c) w =
        determinantValue (fun i => (a i : ℂ)) (Function.update b j c) U := by
  constructor
  · exact fun h b => h _
  · intro h b
    let A : ι → ℂ := fun i => a i
    have hconj (d : ι → ℂ) :
        determinantValue A (fun i => conj (d i)) U = conj (determinantValue A d U) := by
      simpa only [weightedMatchingValue, real_signed_determinant _ _ U hU] using
        weightedMatchingValue_conj a d (realSignedWeight U)
    have hflip : (fun i => conj (Function.update (fun k => conj (b k)) j c i)) =
        Function.update b j (conj c) := by
      funext i
      by_cases hi : i = j
      · subst i
        simp
      · simp [Function.update_of_ne hi]
    have hh := congrArg (starRingEnd ℂ) (h (fun k => conj (b k)))
    change conj (weightedMatchingValue A (Function.update (fun k => conj (b k)) j c) w) =
      conj (determinantValue A (Function.update (fun k => conj (b k)) j c) U) at hh
    rw [← hconj, ← weightedMatchingValue_conj a, hflip] at hh
    have hne : c ≠ conj c := by
      intro he
      have him := congrArg Complex.im he
      rw [Complex.conj_im] at him
      exact hc (by linarith)
    have he := weightedMatchingValue_eq_of_two_updates A b U hU w j hne (h b) hh (b j)
    simpa only [Function.update_eq_self] using he

end

end MOC
