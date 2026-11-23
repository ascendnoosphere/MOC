import MOC.WeightedDiamondChart
import MOC.TwoFreeEntries
import Mathlib.Topology.Compactness.Compact

/-! Closure of the common-weight condition and its application to the order-four chart. -/

open BigOperators Matrix
open scoped Topology

namespace MOC

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- At fixed U, the set of first spectra that admit a common law is closed. -/
theorem isClosed_hasCommonWeights (U : Matrix ι ι ℂ) :
    IsClosed {a : ι → ℂ | HasCommonWeights a U} := by
  classical
  let W := Equiv.Perm ι → Set.Icc (0 : ℝ) 1
  let T : Set ((ι → ℂ) × W) := {p | (∑ σ, (p.2 σ : ℝ)) = 1 ∧
    ∀ b, weightedMatchingValue p.1 b (fun σ => (p.2 σ : ℝ)) = determinantValue p.1 b U}
  have hT : IsClosed T := by
    apply IsClosed.inter
    · apply isClosed_eq _ continuous_const
      apply continuous_finset_sum
      intro σ _
      exact continuous_subtype_val.comp ((continuous_apply σ).comp continuous_snd)
    · apply isClosed_setOf_forall
      intro b
      apply isClosed_eq
      · unfold weightedMatchingValue matchingProduct
        apply continuous_finset_sum
        intro σ _
        apply Continuous.mul
        · exact Complex.continuous_ofReal.comp
            (continuous_subtype_val.comp ((continuous_apply σ).comp continuous_snd))
        · apply continuous_finset_prod
          intro j _
          exact ((continuous_apply (σ j)).comp continuous_fst).add continuous_const
      · unfold determinantValue
        fun_prop
  have he : Prod.fst '' T = {a : ι → ℂ | HasCommonWeights a U} := by
    ext a
    constructor
    · rintro ⟨⟨a',w⟩, hw, rfl⟩
      exact ⟨fun σ => (w σ : ℝ), fun σ => (w σ).property.1, hw.1, hw.2⟩
    · rintro ⟨w, hw, hs, he⟩
      let v : W := fun σ => ⟨w σ, hw σ, by
        rw [← hs]
        exact Finset.single_le_sum (fun p _ => hw p) (Finset.mem_univ σ)⟩
      exact ⟨(a,v), ⟨hs, he⟩, rfl⟩
  rw [← he]
  exact isClosedMap_fst_of_compactSpace T hT

private theorem commonWeights_four_simple
    (hc : ∀ u : ℝ, 0 < u → WeightedDiamondFacetCompletenessAt (u / (1 + u)))
    (a : Fin 4 → ℝ) (ha : Function.Injective a)
    (U : Matrix (Fin 4) (Fin 4) ℂ) (hU : IsUnitary U) :
    HasCommonWeights (fun i => (a i : ℂ)) U := by
  let A (i : Fin 4) : ℂ := a i
  have hV : IsUnitary Uᴴ := ⟨by simpa using hU.2, by simpa using hU.1⟩
  obtain ⟨w, hw, hs, he⟩ := exists_right_weights_four_of_weightedDiamond_support_le_two
    (RayCoefficients.weightedDiamond_support_le_two_of_lower_chart hc) a ha Uᴴ hV
  let e : Equiv.Perm (Equiv.Perm (Fin 4)) :=
    ⟨fun σ => σ.symm, fun σ => σ.symm, fun _ => rfl, fun _ => rfl⟩
  refine ⟨fun σ => w σ.symm, fun σ => hw _, (Equiv.sum_comp e w).trans hs, ?_⟩
  intro b
  rw [weightedMatchingValue_swap b A w]
  have hd : determinantValue b A Uᴴ = determinantValue A b U := by
    simpa [determinantValue, add_comm] using
      (determinantValue_relative b A U (1 : Matrix (Fin 4) (Fin 4) ℂ) hU).symm
  exact (he b).trans hd

/-- One set of nonnegative weights represents every complex partner at
fixed U and a fixed real spectrum of order four, with any multiplicities. -/
theorem commonWeights_four_real_of_lower_chart
    (hchart : ∀ u : ℝ, 0 < u → WeightedDiamondFacetCompletenessAt (u / (1 + u)))
    (a : Fin 4 → ℝ) (U : Matrix (Fin 4) (Fin 4) ℂ)
    (hU : IsUnitary U) : HasCommonWeights (fun i => (a i : ℂ)) U := by
  classical
  let A (t : ℝ) (i : Fin 4) := a i + t * (i.val : ℝ)
  let bad (p : Fin 4 × Fin 4) := (a p.2 - a p.1) / ((p.1.val : ℝ) - p.2.val)
  have hd : Dense (Set.range bad)ᶜ := (Set.finite_range bad).countable.dense_compl ℝ
  have hinj (t : ℝ) (ht : t ∉ Set.range bad) : Function.Injective (A t) := by
    intro i j he
    by_contra hne
    have hn : (i.val : ℝ) - j.val ≠ 0 := by
      apply sub_ne_zero.mpr
      exact_mod_cast (fun h => hne (Fin.ext h) : i.val ≠ j.val)
    apply ht
    refine ⟨(i,j), ?_⟩
    change (a j - a i) / ((i.val : ℝ) - j.val) = t
    symm
    apply (eq_div_iff hn).mpr
    dsimp [A] at he
    linarith only [he]
  let f (t : ℝ) (i : Fin 4) : ℂ := A t i
  have hf : Continuous f := by unfold f A; fun_prop
  have hc : IsClosed {t : ℝ | HasCommonWeights (f t) U} :=
    (isClosed_hasCommonWeights U).preimage hf
  have hsub : (Set.range bad)ᶜ ⊆ {t : ℝ | HasCommonWeights (f t) U} :=
    fun t ht => commonWeights_four_simple hchart (A t) (hinj t ht) U hU
  have hzero := closure_minimal hsub hc (hd 0)
  simpa [f, A] using hzero

end

end MOC
