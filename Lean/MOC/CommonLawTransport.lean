import MOC.RealFractionalChart
import Mathlib.Topology.Algebra.Module.Cardinality
import Mathlib.Topology.Instances.Matrix

/-! Transport one set of weights for all partners under a fractional-linear
change of the first spectrum. Continuity accounts for partner values at a pole. -/

open BigOperators Matrix

namespace MOC

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem pullback_all_partners (a : ι → ℂ) (U : Matrix ι ι ℂ) (hU : IsUnitary U)
    (w : Equiv.Perm ι → ℝ) (α β γ δ : ℂ) (hd : α*δ-β*γ ≠ 0)
    (ha : ∀ i, γ*a i+δ ≠ 0)
    (he : ∀ b, weightedMatchingValue (fractionalMap α β γ δ ∘ a) b w =
      determinantValue (fractionalMap α β γ δ ∘ a) b U) :
    ∀ b, weightedMatchingValue a b w = determinantValue a b U := by
  classical
  have regular (b : ι → ℂ) (hb : ∀ j, γ*(-b j)+δ ≠ 0) :
      weightedMatchingValue a b w = determinantValue a b U := by
    obtain ⟨k, hk, hp, hz⟩ := exists_fractional_factor a b U hU α β γ δ hd ha hb
    let f := fractionalMap α β γ δ
    have hw : weightedMatchingValue (f ∘ a) (fun i => -f (-b i)) w =
        k * weightedMatchingValue a b w := by
      rw [weightedMatchingValue, weightedMatchingValue, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      rw [hp]
      ring
    exact mul_left_cancel₀ hk (hw.symm.trans ((he _).trans hz))
  intro b
  by_cases hg : γ = 0
  · subst γ
    have hn : δ ≠ 0 := by intro h; simp [h] at hd
    exact regular b (fun j => by simpa using hn)
  let B (t : ℂ) (i : ι) := b i + t
  let bad (j : ι) := δ/γ - b j
  have hdense : Dense (Set.range bad)ᶜ := (Set.finite_range bad).countable.dense_compl ℂ
  have hclosed : IsClosed {t : ℂ | weightedMatchingValue a (B t) w = determinantValue a (B t) U} := by
    apply isClosed_eq
    · unfold weightedMatchingValue matchingProduct B
      fun_prop
    · unfold determinantValue B
      fun_prop
  have hs : (Set.range bad)ᶜ ⊆ {t : ℂ | weightedMatchingValue a (B t) w =
      determinantValue a (B t) U} := by
    intro t ht
    apply regular
    intro j hj
    apply ht
    refine ⟨j, ?_⟩
    have h₁ : δ = (b j + t)*γ := by
      change γ * -(b j + t) + δ = 0 at hj
      linear_combination hj
    have h₂ : δ / γ = b j + t := (div_eq_iff hg).mpr h₁
    simp [bad, h₂]
  have hzero := closure_minimal hs hclosed (hdense 0)
  simpa [B] using hzero

private theorem regular_inverse (α β γ δ z : ℂ) (hd : α*δ-β*γ ≠ 0) (h : γ*z+δ ≠ 0) :
    -γ * fractionalMap α β γ δ z + α ≠ 0 ∧
    fractionalMap δ (-β) (-γ) α (fractionalMap α β γ δ z) = z := by
  have he : -γ * fractionalMap α β γ δ z + α = (α*δ-β*γ)/(γ*z+δ) := by
    unfold fractionalMap
    field_simp [h] <;> ring
  have hn := he.trans_ne (div_ne_zero hd h)
  refine ⟨hn, (div_eq_iff hn).mpr ?_⟩
  unfold fractionalMap
  field_simp [h] <;> ring

/-- At a fixed unitary, the same weights work for all complex partners before
and after a regular fractional-linear change of the first spectrum. -/
theorem all_partner_weights_fractional_iff (a : ι → ℂ) (U : Matrix ι ι ℂ) (hU : IsUnitary U)
    (w : Equiv.Perm ι → ℝ) (α β γ δ : ℂ) (hd : α*δ-β*γ ≠ 0)
    (ha : ∀ i, γ*a i+δ ≠ 0) :
    (∀ b, weightedMatchingValue (fractionalMap α β γ δ ∘ a) b w =
      determinantValue (fractionalMap α β γ δ ∘ a) b U) ↔
    (∀ b, weightedMatchingValue a b w = determinantValue a b U) := by
  refine ⟨pullback_all_partners a U hU w α β γ δ hd ha, ?_⟩
  intro he
  let f := fractionalMap α β γ δ
  have hdet : δ*α-(-β)*(-γ) ≠ 0 := by
    convert hd using 1 <;> ring
  have hcomp : fractionalMap δ (-β) (-γ) α ∘ (f ∘ a) = a :=
    funext fun i => (regular_inverse α β γ δ (a i) hd (ha i)).2
  apply pullback_all_partners (f ∘ a) U hU w δ (-β) (-γ) α hdet
    (fun i => (regular_inverse α β γ δ (a i) hd (ha i)).1)
  rwa [hcomp]

theorem commonWeights_fractional_iff (a : ι → ℂ) (U : Matrix ι ι ℂ) (hU : IsUnitary U)
    (α β γ δ : ℂ) (hd : α*δ-β*γ ≠ 0) (ha : ∀ i, γ*a i+δ ≠ 0) :
    HasCommonWeights (fractionalMap α β γ δ ∘ a) U ↔ HasCommonWeights a U := by
  constructor <;> rintro ⟨w, hw, hs, he⟩ <;> refine ⟨w, hw, hs, ?_⟩
  · exact (all_partner_weights_fractional_iff a U hU w α β γ δ hd ha).mp he
  · exact (all_partner_weights_fractional_iff a U hU w α β γ δ hd ha).mpr he

/-- At a fixed unitary, common laws for real first spectra give common laws
for first spectra on any generalized circle. -/
theorem commonWeights_on_circle_of_real (U : Matrix ι ι ℂ) (hU : IsUnitary U)
    (hreal : ∀ x : ι → ℝ, HasCommonWeights (fun i => (x i : ℂ)) U)
    (a : ι → ℂ) (hc : SpectrumOnGeneralizedCircle a) : HasCommonWeights a U := by
  obtain ⟨α, β, γ, δ, hd, ha, him⟩ := exists_real_fractional_chart a hc
  let f := fractionalMap α β γ δ
  have hfun : (fun i => (((f (a i)).re : ℝ) : ℂ)) = f ∘ a := by
    funext i
    exact Complex.ext rfl (by simpa only [Complex.ofReal_im] using (him i).symm)
  apply (commonWeights_fractional_iff a U hU α β γ δ hd ha).mp
  rw [← hfun]
  exact hreal (fun i => (f (a i)).re)

end

end MOC
