import MOC.HermitianByNormalFour
import MOC.WeightedDiamondOrdinaryFacets

/-! The weighted-diamond facet completeness criterion for the order-four
Hermitian-by-normal theorem. -/

open BigOperators Matrix

namespace MOC

noncomputable section

abbrev WeightedDiamondFacetIndex := FourPerm × (Fin 12 ⊕ Fin 4)

private abbrev DiamondTable (M : Type*) := Finset (Fin 4) → Finset (Fin 4) → M

/-- The twelve ordinary and four mixed forms and their row relabelings. -/
def weightedDiamondFacet {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (i : WeightedDiamondFacetIndex) (x : R) (m : DiamondTable M) : M :=
  let p : DiamondTable M := fun I J => m (I.map i.1.toEmbedding) J
  i.2.elim (fun k => weightedDiamondOrdinaryForm k x p) (fun k => weightedDiamondHardForm k x p)

/-- Relabeling the rows of a permutation profile acts by inverse left composition. -/
theorem weightedDiamondFacet_permProfile {R : Type*} [CommRing R]
    (i : WeightedDiamondFacetIndex) (x : R) (σ : FourPerm) :
    weightedDiamondFacet i x (diamondPermProfile (R := R) σ) =
      i.2.elim (fun k => weightedDiamondOrdinaryForm k x (diamondPermProfile (i.1⁻¹ * σ)))
        (fun k => weightedDiamondHardForm k x (diamondPermProfile (i.1⁻¹ * σ))) := by
  have hprofile : (fun I J => diamondPermProfile (R := R) σ (I.map i.1.toEmbedding) J) =
      diamondPermProfile (i.1⁻¹ * σ) := by
    funext I J
    have hmap : (J.map (i.1⁻¹ * σ).toEmbedding).map i.1.toEmbedding = J.map σ.toEmbedding := by
      rw [Finset.map_map]
      congr 1
      apply Function.Embedding.ext
      intro j
      exact i.1.apply_symm_apply (σ j)
    simp only [diamondPermProfile, ← hmap, Finset.map_inj]
  simp only [weightedDiamondFacet, hprofile]

/-- Every score upper bound on the permutations is a nonnegative combination
of the weighted-diamond facet forms, as a function on the permutations. -/
def WeightedDiamondFacetCompletenessAt (x : ℝ) : Prop :=
  ∀ c f g s, (∀ σ, weightedDiamondScore (1 + x) f g s σ ≤ c) →
    ∃ d : WeightedDiamondFacetIndex → ℝ, (∀ i, 0 ≤ d i) ∧ ∀ σ : FourPerm,
      c - weightedDiamondScore (1 + x) f g s σ =
        ∑ i : WeightedDiamondFacetIndex, d i * weightedDiamondFacet i x (diamondPermProfile σ)

private theorem weightedDiamondFacet_nonneg (i : WeightedDiamondFacetIndex) (x : ℝ) (hx : 0 ≤ x)
    (U : Matrix (Fin 4) (Fin 4) ℂ) (hU : IsUnitary U) :
    0 ≤ weightedDiamondFacet i x (subsetMinorSq U) := by
  rcases i with ⟨ρ, k⟩
  let V := U.submatrix ρ (Equiv.refl (Fin 4))
  have hV : IsUnitary V := unitary_reindex _ _ hU
  have htab (I J : Finset (Fin 4)) : subsetMinorSq U (I.map ρ.toEmbedding) J =
      subsetMinorSq V I J := by
    change _ = subsetMinorSq (U.submatrix ρ (Equiv.refl (Fin 4))) I J
    rw [squared_minor_reindex ρ (Equiv.refl (Fin 4)) U hU]
    change _ = subsetMinorSq U (I.map ρ.toEmbedding) (J.map (Function.Embedding.refl (Fin 4)))
    rw [Finset.map_refl]
  cases k with
  | inl k => simpa only [weightedDiamondFacet, Sum.elim_inl, htab] using
      weightedDiamondOrdinaryForm_nonneg k x hx V hV
  | inr k => simpa only [weightedDiamondFacet, Sum.elim_inr, htab] using
      weightedDiamondHardForm_nonneg k x hx V hV

private def facetLinear (i : WeightedDiamondFacetIndex) (x : ℝ) :
    DiamondTable ℝ →ₗ[ℝ] ℝ :=
  weightedDiamondFacet i x diamondEvaluate

set_option maxHeartbeats 600000 in
private theorem facetLinear_apply (i : WeightedDiamondFacetIndex) (x : ℝ) (m : DiamondTable ℝ) :
    facetLinear i x m = weightedDiamondFacet i x m := by
  rcases i with ⟨ρ, k | k⟩ <;> fin_cases k <;>
    simp only [facetLinear, weightedDiamondFacet, Sum.elim_inl, Sum.elim_inr,
      weightedDiamondOrdinaryForm, weightedDiamondHardForm, Matrix.cons_val_zero',
      Matrix.cons_val_succ', LinearMap.add_apply, LinearMap.sub_apply, LinearMap.neg_apply,
      LinearMap.smul_apply, diamondEvaluate, LinearMap.coe_mk, AddHom.coe_mk]

private def scoreSlackLinear (t c : ℝ) (f g : Fin 4 → ℝ) (s : Finset (Fin 4) → ℝ) :
    DiamondTable ℝ →ₗ[ℝ] ℝ :=
  c • diamondEvaluate ∅ ∅ -
    ((∑ i, f i • diamondEvaluate {i} {0}) + (∑ i, g i • diamondEvaluate {i} {3}) +
      (∑ I, s I • diamondEvaluate I {0, 1}) + t • ∑ I, s I • diamondEvaluate I {0, 2})

private theorem scoreSlackLinear_apply (t c : ℝ) (f g : Fin 4 → ℝ) (s : Finset (Fin 4) → ℝ)
    (σ : FourPerm) : scoreSlackLinear t c f g s (diamondPermProfile σ) =
      c - weightedDiamondScore t f g s σ := by
  simp only [scoreSlackLinear, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.sum_apply,
    LinearMap.smul_apply, smul_eq_mul, diamondEvaluate, LinearMap.coe_mk, AddHom.coe_mk,
    diamondPermProfile, Finset.map_empty, if_pos rfl, mul_one, Finset.map_singleton,
    Equiv.toEmbedding_apply, Finset.singleton_inj, mul_ite, mul_zero, Finset.sum_ite_eq,
    Finset.mem_univ, if_true, weightedDiamondScore]

/-- Completeness of the stated forms implies the support test at the
associated middle weight. -/
theorem weightedDiamondSupport_of_facetCompleteness (x : ℝ) (hx : 0 ≤ x)
    (hc : WeightedDiamondFacetCompletenessAt x) (U : Matrix (Fin 4) (Fin 4) ℂ)
    (hU : IsUnitary U) : WeightedDiamondSupportAt (1 + x) U := by
  classical
  intro f g s
  let D := weightedDiamondScore (1 + x) f g s
  obtain ⟨σ, _, hσ⟩ := Finset.exists_max_image Finset.univ D
    ⟨Equiv.refl (Fin 4), Finset.mem_univ _⟩
  obtain ⟨d, hd, hdecomp⟩ := hc (D σ) f g s (fun τ => hσ τ (Finset.mem_univ _))
  let L := scoreSlackLinear (1 + x) (D σ) f g s
  let G : DiamondTable ℝ →ₗ[ℝ] ℝ := ∑ i, d i • facetLinear i x
  have hLG (τ : FourPerm) : L (diamondPermProfile τ) = G (diamondPermProfile τ) := by
    simpa only [L, G, scoreSlackLinear_apply, LinearMap.sum_apply, LinearMap.smul_apply,
      smul_eq_mul, facetLinear_apply, D] using hdecomp τ
  have hnonneg : 0 ≤ L (subsetMinorSq U) := by
    rw [diamondLinearForm_eq_of_perm_eq L G hLG U hU]
    simp only [G, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, facetLinear_apply]
    exact Finset.sum_nonneg fun i _ => mul_nonneg (hd i) (weightedDiamondFacet_nonneg i x hx U hU)
  rw [diamond_weighted_profile U hU, map_sum] at hnonneg
  simp only [map_smul, smul_eq_mul, L, scoreSlackLinear_apply, mul_sub,
    Finset.sum_sub_distrib, ← Finset.sum_mul, sum_realSignedWeight U hU, one_mul] at hnonneg
  exact ⟨σ, sub_nonneg.mp hnonneg⟩

/-- The positive-parameter facet completeness criterion suffices for the
order-four Hermitian-by-normal theorem. -/
theorem hermitianByNormal_four_of_weightedDiamond_facets
    (hc : ∀ x : ℝ, 0 < x → WeightedDiamondFacetCompletenessAt x) : HermitianByNormal (Fin 4) := by
  apply hermitianByNormal_four_of_weightedDiamond_support
  intro t ht U hU
  have hx : 0 < t - 1 := sub_pos.mpr ht
  have h := weightedDiamondSupport_of_facetCompleteness (t - 1) hx.le (hc _ hx) U hU
  rwa [show 1 + (t - 1) = t by ring] at h

/-- The support test is closed in the middle weight, since the finitely many
permutation scores and the unitary score are continuous. -/
theorem isClosed_weightedDiamondSupportAt (U : Matrix (Fin 4) (Fin 4) ℂ) :
    IsClosed {t : ℝ | WeightedDiamondSupportAt t U} := by
  simp only [WeightedDiamondSupportAt, Set.setOf_forall, Set.setOf_exists]
  refine isClosed_iInter fun f => isClosed_iInter fun g => isClosed_iInter fun s => ?_
  have hs (σ : FourPerm) : Continuous (fun t : ℝ => weightedDiamondScore t f g s σ) := by
    unfold weightedDiamondScore
    fun_prop
  exact isClosed_iUnion_of_finite fun σ => isClosed_le
    (continuous_finset_sum _ (fun τ _ => continuous_const.mul (hs τ))) (hs σ)

/-- It suffices to verify the facet census on a dense set of middle weights.
Exceptional parameters need no separate census. -/
theorem hermitianByNormal_four_of_dense_weightedDiamond_facets (S : Set ℝ) (hS : Dense S)
    (hc : ∀ t ∈ S, 1 < t → WeightedDiamondFacetCompletenessAt (t - 1)) :
    HermitianByNormal (Fin 4) := by
  apply hermitianByNormal_four_of_weightedDiamond_support
  intro t ht U hU
  have ho : IsOpen (Set.Ioi (1 : ℝ)) := isOpen_Ioi
  have hs : Set.Ioi (1 : ℝ) ∩ S ⊆ {q | WeightedDiamondSupportAt q U} := by
    rintro q ⟨hq, hqS⟩
    have hx : 0 ≤ q - 1 := sub_nonneg.mpr (le_of_lt hq)
    have h := weightedDiamondSupport_of_facetCompleteness (q - 1) hx (hc q hqS hq) U hU
    rwa [show 1 + (q - 1) = q by ring] at h
  exact closure_minimal hs (isClosed_weightedDiamondSupportAt U)
    (hS.open_subset_closure_inter ho ht)

end

end MOC
