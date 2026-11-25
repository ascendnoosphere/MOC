import MOC.ConstantProfileLimit
import MOC.FiniteProfileLimit
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.MetricSpace.Sequences
import Mathlib.Tactic.FieldSimp

/-! The bounded and divergent alternatives for a normalized positive
deficit along a contact curve both lead to contradictions. -/

open BigOperators Filter Matrix
open scoped Topology

namespace MOC

/-- There is no positive normalized deficit along actual anchored profiles
whose matching gaps converge to nonnegative real numbers. -/
theorem no_positive_deficit_on_anchored_profile_sequence {n : ℕ}
    (U : Matrix (Fin n) (Fin n) ℂ) (hU : IsUnitary U)
    (r : Equiv.Perm (Fin n))
    (P : ℕ → Equiv.Perm (Fin n) → ℂ)
    (T : ℕ → Fin n → Fin n → ℂ) (c : Equiv.Perm (Fin n) → ℝ)
    (hactual : ∀ k, ∃ a b : Fin n → ℂ, matchingProduct a b = P k)
    (hnz : ∀ k σ, P k σ ≠ 0)
    (hdef : ∀ k, (∑ σ, signedWeight U σ * P k σ) = P k r + 1)
    (hc : ∀ σ, 0 ≤ c σ)
    (hlim : ∀ σ, Tendsto (fun k => P k r - P k σ) atTop (𝓝 (c σ : ℂ)))
    (hfactor : ∀ k, ∃ A : ℂ, ∀ σ, P k σ = A * ∏ j, (1 - T k (σ j) j))
    (hratio : ∀ i j, ∃ π τ : Equiv.Perm (Fin n), ∀ k,
      (1 - T k i j) * P k τ = P k π) : False := by
  by_cases hb : ∃ M : ℝ, ∃ᶠ k in atTop, P k r ∈ Metric.closedBall (0 : ℂ) M
  · obtain ⟨M, hM⟩ := hb
    obtain ⟨γ, _, φ, hφ, hγ⟩ :=
      (isCompact_closedBall (0 : ℂ) M).isSeqCompact.subseq_of_frequently_in hM
    let q (σ : Equiv.Perm (Fin n)) : ℂ := γ - c σ
    have ht (σ : Equiv.Perm (Fin n)) : Tendsto (fun k => P (φ k) σ) atTop (𝓝 (q σ)) := by
      have hx := hγ.sub ((hlim σ).comp hφ.tendsto_atTop)
      simpa only [Function.comp_apply, sub_sub_cancel, q] using hx
    have hsum := tendsto_finset_sum Finset.univ fun σ _ => (ht σ).const_mul (signedWeight U σ)
    have hadd := hγ.add (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℂ)) atTop (𝓝 1))
    have hplus : Tendsto (fun k => ∑ σ, signedWeight U σ * P (φ k) σ) atTop (𝓝 (γ + 1)) :=
      hadd.congr' (Filter.Eventually.of_forall fun k => (hdef (φ k)).symm)
    exact no_positive_deficit_of_finite_profile_limit atTop U hU (fun k => P (φ k)) q
      (Filter.Eventually.of_forall fun k => hactual (φ k)) (tendsto_pi_nhds.mpr ht) γ
      (fun σ => by simp [q]) (fun σ => by simpa only [q, Complex.sub_re, Complex.ofReal_re]
        using sub_le_self γ.re (hc σ)) (tendsto_nhds_unique hsum hplus)
  · let ε (k : ℕ) := (P k r)⁻¹
    let G (σ : Equiv.Perm (Fin n)) (k : ℕ) := P k r - P k σ
    have hnorm : Tendsto (fun k => ‖P k r‖) atTop atTop := by
      apply tendsto_atTop.mpr
      intro M
      have hno : ¬ ∃ᶠ k in atTop, P k r ∈ Metric.closedBall (0 : ℂ) M :=
        fun h => hb ⟨M, h⟩
      rw [Filter.not_frequently] at hno
      filter_upwards [hno] with k hk
      exact (lt_of_not_ge (by simpa only [Metric.mem_closedBall, dist_zero_right] using hk)).le
    have hε : Tendsto ε atTop (𝓝 0) := by
      apply tendsto_zero_iff_norm_tendsto_zero.mpr
      simpa only [ε, norm_inv, Function.comp_apply] using tendsto_inv_atTop_zero.comp hnorm
    have hεnz (k : ℕ) : ε k ≠ 0 := inv_ne_zero (hnz k r)
    have hdiv (k : ℕ) (σ : Equiv.Perm (Fin n)) : 1 - ε k * G σ k = P k σ / P k r := by
      dsimp only [ε, G]
      field_simp [hnz k r] <;> ring
    have hrat (i j : Fin n) : ∃ π τ : Equiv.Perm (Fin n), ∀ᶠ k in atTop,
        1 - T k i j = (1 - ε k * G π k) / (1 - ε k * G τ k) := by
      obtain ⟨π, τ, hπτ⟩ := hratio i j
      refine ⟨π, τ, Filter.Eventually.of_forall fun k => ?_⟩
      rw [hdiv, hdiv, div_div_div_cancel_right₀ (hnz k r)]
      exact (eq_div_iff (hnz k τ)).mpr (hπτ k)
    have hG (σ : Equiv.Perm (Fin n)) : ∀ᶠ k in atTop,
        G σ k = ((∏ j, (1 - T k (r j) j)) - ∏ j, (1 - T k (σ j) j)) /
          (ε k * ∏ j, (1 - T k (r j) j)) := by
      apply Filter.Eventually.of_forall
      intro k
      let F (τ : Equiv.Perm (Fin n)) := ∏ j, (1 - T k (τ j) j)
      obtain ⟨A, hA⟩ := hfactor k
      have hAF : A * F r ≠ 0 := (hA r) ▸ hnz k r
      have ha : A ≠ 0 := fun hz => hAF (by simp [hz])
      have hf : F r ≠ 0 := fun hz => hAF (by simp [hz])
      change P k r - P k σ = (F r - F σ) / ((P k r)⁻¹ * F r)
      rw [show P k r = A * F r from hA r, show P k σ = A * F σ from hA σ]
      field_simp [ha, hf] <;> ring
    have hsum : ∀ᶠ k in atTop, (∑ σ, signedWeight U σ * G σ k) = -1 := by
      apply Filter.Eventually.of_forall
      intro k
      simp only [G, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
      rw [sum_signedWeight U (det_ne_zero_of_unitary hU), one_mul, hdef]
      ring
    exact no_positive_deficit_of_divergent_profile_limit atTop U hU r ε T G c hε
      (Filter.Eventually.of_forall hεnz) hc hlim hrat hG hsum

end MOC
