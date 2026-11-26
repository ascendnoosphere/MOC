import MOC.SpectralMinorDecomposition
import MOC.Small

/-! A slope slice of the joint coefficient hull can be tested by mixtures of
at most three points. The slope is fixed, and the intercept is projected
in one real direction at a time. -/

open BigOperators Finset

namespace MOC

noncomputable section

private theorem slope_relation {T : Finset (ℂ × ℂ)}
    (h : ¬ AffineIndependent ℝ (fun p : T => p.val.2)) :
    ∃ g : (ℂ × ℂ) → ℝ, (∑ p ∈ T, g p) = 0 ∧
      (∑ p ∈ T, g p • p.2) = 0 ∧ ∃ p ∈ T, g p ≠ 0 := by
  classical
  rw [affineIndependent_iff_of_fintype] at h
  push_neg at h
  obtain ⟨v, hv, hlin, p, hp⟩ := h
  rw [Finset.weightedVSub_eq_linear_combination _ hv] at hlin
  let g (q : ℂ × ℂ) : ℝ := if hq : q ∈ T then v ⟨q, hq⟩ else 0
  have hcoe (q : T) : g q.val = v q := by simp [g, q.property]
  refine ⟨g, ?_, ?_, ⟨p.val, p.property, ?_⟩⟩
  · rw [← Finset.sum_attach T]
    change (∑ q : T, g q.val) = 0
    simpa only [hcoe] using hv
  · rw [← Finset.sum_attach T]
    change (∑ q : T, g q.val • q.val.2) = 0
    simpa only [hcoe] using hlin
  · simpa only [hcoe] using hp

private theorem erase_slope_weight (T : Finset (ℂ × ℂ)) (c w : (ℂ × ℂ) → ℝ)
    (hn : ∀ p ∈ T, 0 ≤ w p)
    (h : ¬ AffineIndependent ℝ (fun p : T => p.val.2)) :
    ∃ p₀ ∈ T, ∃ v : (ℂ × ℂ) → ℝ,
      (∀ p ∈ T.erase p₀, 0 ≤ v p) ∧
      (∑ p ∈ T.erase p₀, v p) = ∑ p ∈ T, w p ∧
      (∑ p ∈ T.erase p₀, v p • p.2) = ∑ p ∈ T, w p • p.2 ∧
      (∑ p ∈ T, w p * c p) ≤ ∑ p ∈ T.erase p₀, v p * c p := by
  classical
  obtain ⟨g, hg, hgt, hgn⟩ := slope_relation h
  have horient : ∃ f : (ℂ × ℂ) → ℝ, (∑ p ∈ T, f p) = 0 ∧
      (∑ p ∈ T, f p • p.2) = 0 ∧ (∃ p ∈ T, f p ≠ 0) ∧
      (∑ p ∈ T, f p * c p) ≤ 0 := by
    by_cases hc : (∑ p ∈ T, g p * c p) ≤ 0
    · exact ⟨g, hg, hgt, hgn, hc⟩
    · refine ⟨fun p => -g p, ?_, ?_, ?_, ?_⟩
      · simp only [Finset.sum_neg_distrib, hg, neg_zero]
      · simp only [neg_smul, Finset.sum_neg_distrib, hgt, neg_zero]
      · obtain ⟨p, hp, hne⟩ := hgn
        exact ⟨p, hp, neg_ne_zero.mpr hne⟩
      · simpa only [neg_mul, Finset.sum_neg_distrib, neg_nonpos] using (lt_of_not_ge hc).le
  obtain ⟨f, hf, hft, hfn, hfc⟩ := horient
  let Q := T.filter (fun p => 0 < f p)
  have hQ : Q.Nonempty := by
    obtain ⟨p, hp, hp'⟩ := Finset.exists_pos_of_sum_zero_of_exists_nonzero f hf hfn
    exact ⟨p, Finset.mem_filter.mpr ⟨hp, hp'⟩⟩
  obtain ⟨p₀, hp₀, hmin⟩ := Q.exists_min_image (fun p => w p / f p) hQ
  obtain ⟨hpT, hpF⟩ := Finset.mem_filter.mp hp₀
  let r := w p₀ / f p₀
  let v (p : ℂ × ℂ) : ℝ := w p - r * f p
  have hr : 0 ≤ r := div_nonneg (hn _ hpT) hpF.le
  have hv₀ : v p₀ = 0 := by
    dsimp only [v, r]
    rw [div_mul_cancel₀ _ hpF.ne', sub_self]
  refine ⟨p₀, hpT, v, ?_, ?_, ?_, ?_⟩
  · intro p hp
    have hpT' := (Finset.mem_erase.mp hp).2
    change 0 ≤ w p - r * f p
    rw [sub_nonneg]
    by_cases hpF' : 0 < f p
    · exact (le_div_iff₀ hpF').mp (hmin p (Finset.mem_filter.mpr ⟨hpT', hpF'⟩))
    · exact (mul_nonpos_of_nonneg_of_nonpos hr (le_of_not_gt hpF')).trans (hn _ hpT')
  · rw [Finset.sum_erase T hv₀]
    simp only [v, Finset.sum_sub_distrib, ← Finset.mul_sum, hf, mul_zero, sub_zero]
  · rw [Finset.sum_erase T (f := fun p => v p • p.2) (a := p₀) (by simp only [hv₀, zero_smul])]
    simp only [v, sub_smul, mul_smul, Finset.sum_sub_distrib, ← Finset.smul_sum,
      hft, smul_zero, sub_zero]
  · rw [Finset.sum_erase T (f := fun p => v p * c p) (a := p₀) (by simp only [hv₀, zero_mul])]
    have hproj : (∑ p ∈ T, v p * c p) =
        (∑ p ∈ T, w p * c p) - r * (∑ p ∈ T, f p * c p) := by
      simp only [v, sub_mul, mul_assoc, Finset.sum_sub_distrib, Finset.mul_sum]
    rw [hproj, sub_eq_add_neg]
    exact le_add_of_nonneg_right (neg_nonneg.mpr (mul_nonpos_of_nonneg_of_nonpos hr hfc))

/-- The weights of a slope simplex give the prescribed slope and attain at
least the required intercept projection. -/
def SlopeSliceCertificate (S : Set (ℂ × ℂ)) (x y η : ℂ) : Prop :=
  ∃ T : Finset (ℂ × ℂ), (↑T : Set (ℂ × ℂ)) ⊆ S ∧ T.card ≤ 3 ∧
    AffineIndependent ℝ (fun p : T => p.val.2) ∧ ∃ w : (ℂ × ℂ) → ℝ,
    (∀ p ∈ T, 0 ≤ w p) ∧ (∑ p ∈ T, w p) = 1 ∧ (∑ p ∈ T, w p • p.2) = y ∧
    (η * x).re ≤ ∑ p ∈ T, w p * (η * p.1).re

private theorem project_intercept (T : Finset (ℂ × ℂ)) (w : (ℂ × ℂ) → ℝ) (η : ℂ) :
    (η * (∑ p ∈ T, w p • p).1).re = ∑ p ∈ T, w p * (η * p.1).re := by
  let L : ℂ →ₗ[ℝ] ℝ := Complex.reLm.comp (LinearMap.mulLeft ℝ η)
  change L (∑ p ∈ T, w p • p).1 = _
  simp only [Prod.fst_sum, Prod.smul_fst, map_sum, map_smul, smul_eq_mul] <;> rfl

private theorem slope_slice_certificate_of_mem {S : Set (ℂ × ℂ)} (hS : S.Finite)
    {x y : ℂ} (h : (x, y) ∈ convexHull ℝ S) (η : ℂ) :
    SlopeSliceCertificate S x y η := by
  classical
  let Good (T : Finset (ℂ × ℂ)) : Prop := (↑T : Set (ℂ × ℂ)) ⊆ S ∧
    ∃ w : (ℂ × ℂ) → ℝ, (∀ p ∈ T, 0 ≤ w p) ∧ (∑ p ∈ T, w p) = 1 ∧
      (∑ p ∈ T, w p • p.2) = y ∧ (η * x).re ≤ ∑ p ∈ T, w p * (η * p.1).re
  have hgood : ∃ n : ℕ, ∃ T : Finset (ℂ × ℂ), T.card = n ∧ Good T := by
    let T := hS.toFinset
    have hT : (↑T : Set (ℂ × ℂ)) = S := hS.coe_toFinset
    have hh : (x, y) ∈ convexHull ℝ (↑T : Set (ℂ × ℂ)) := by
      rw [hT]
      exact h
    obtain ⟨w, hn, hsum, he⟩ := Finset.mem_convexHull'.mp hh
    have hysum : (∑ p ∈ T, w p • p.2) = y := by
      simpa only [Prod.snd_sum, Prod.smul_snd] using congrArg Prod.snd he
    have hxsum := project_intercept T w η
    rw [he] at hxsum
    exact ⟨T.card, T, rfl, fun p hp => hT ▸ hp, w, hn, hsum, hysum, hxsum.le⟩
  obtain ⟨T, hcard, hsub, w, hn, hsum, hslope, hproj⟩ := Nat.find_spec hgood
  have hind : AffineIndependent ℝ (fun p : T => p.val.2) := by
    by_contra hdep
    obtain ⟨p, hp, v, hvn, hvsum, hvslope, hvproj⟩ :=
      erase_slope_weight T (fun q => (η * q.1).re) w hn hdep
    have hlt : (T.erase p).card < Nat.find hgood := by
      rw [← hcard]
      exact Finset.card_erase_lt_of_mem hp
    apply Nat.find_min hgood hlt
    refine ⟨T.erase p, rfl, ?_⟩
    exact ⟨fun q hq => hsub (Finset.mem_of_mem_erase hq), v, hvn, hvsum.trans hsum,
      hvslope.trans hslope, hproj.trans hvproj⟩
  have hsize := hind.card_le_finrank_succ.trans (Nat.add_le_add_right (Submodule.finrank_le _) 1)
  have hThree : T.card ≤ 3 := by
    simpa only [Fintype.card_coe, Complex.finrank_real_complex] using hsize
  exact ⟨T, hsub, hThree, hind, w, hn, hsum, hslope, hproj⟩

/-- At a fixed slope, membership of the joint coefficient hull is equivalent
to a slope simplex certificate for every intercept direction. -/
theorem joint_coefficient_hull_iff_slope_slice {S : Set (ℂ × ℂ)} (hS : S.Finite)
    (x y : ℂ) : (x, y) ∈ convexHull ℝ S ↔ ∀ η : ℂ, SlopeSliceCertificate S x y η := by
  classical
  constructor
  · exact slope_slice_certificate_of_mem hS
  · intro h
    by_contra hn
    obtain ⟨L, c, hL, hpoint⟩ := geometric_hahn_banach_closed_point
      (convex_convexHull ℝ S) hS.isClosed_convexHull hn
    obtain ⟨η, θ, hrepr⟩ := productFunctional L
    obtain ⟨T, hTS, _, _, w, hw, hsum, hslope, hproj⟩ := h η
    let z := ∑ p ∈ T, w p • p
    have hz : z ∈ convexHull ℝ S := (convex_convexHull ℝ S).sum_mem hw hsum
      (fun p hp => subset_convexHull ℝ S (hTS hp))
    have hzy : z.2 = y := by
      simpa only [z, Prod.snd_sum, Prod.smul_snd] using hslope
    have hzx : (η * z.1).re = ∑ p ∈ T, w p * (η * p.1).re :=
      project_intercept T w η
    have hle : L (x, y) ≤ L z := by
      rw [hrepr (x, y), hrepr z, Complex.add_re, Complex.add_re, hzy, hzx]
      exact add_le_add_right hproj _
    exact (not_le_of_gt ((hL z hz).trans hpoint)) hle

/-- The weights on one slope simplex are unique at the prescribed slope. -/
theorem slope_simplex_weights_unique (T : Finset (ℂ × ℂ))
    (hind : AffineIndependent ℝ (fun p : T => p.val.2)) (w v : (ℂ × ℂ) → ℝ)
    (hsum : (∑ p ∈ T, w p) = ∑ p ∈ T, v p)
    (hslope : (∑ p ∈ T, w p • p.2) = ∑ p ∈ T, v p • p.2) :
    ∀ p ∈ T, w p = v p := by
  intro p hp
  have hsum' : (∑ q : T, w q.val) = ∑ q : T, v q.val := by
    simpa only [Finset.univ_eq_attach, Finset.sum_attach] using hsum
  have hslope' : (∑ q : T, w q.val • q.val.2) = ∑ q : T, v q.val • q.val.2 := by
    rwa [Finset.univ_eq_attach, Finset.sum_attach T (fun p => w p • p.2), Finset.sum_attach T (fun p => v p • p.2)]
  exact hind.eq_of_sum_eq_sum hsum' hslope' ⟨p, hp⟩ (Finset.mem_univ _)

/-- List the intercepts of the simplex mixtures at one prescribed slope. -/
def slopeSliceIntercepts (S : Set (ℂ × ℂ)) (y : ℂ) : Set ℂ :=
  {x | ∃ T : Finset (ℂ × ℂ), (↑T : Set (ℂ × ℂ)) ⊆ S ∧ T.card ≤ 3 ∧
    AffineIndependent ℝ (fun p : T => p.val.2) ∧ ∃ w : (ℂ × ℂ) → ℝ,
    (∀ p ∈ T, 0 ≤ w p) ∧ (∑ p ∈ T, w p) = 1 ∧ (∑ p ∈ T, w p • p.2) = y ∧
    (∑ p ∈ T, w p • p.1) = x}

theorem slopeSliceIntercepts_finite {S : Set (ℂ × ℂ)} (hS : S.Finite) (y : ℂ) :
    (slopeSliceIntercepts S y).Finite := by
  classical
  let C (T : Finset (ℂ × ℂ)) : Set ℂ := {x |
    AffineIndependent ℝ (fun p : T => p.val.2) ∧ ∃ w : (ℂ × ℂ) → ℝ,
    (∑ p ∈ T, w p) = 1 ∧ (∑ p ∈ T, w p • p.2) = y ∧ (∑ p ∈ T, w p • p.1) = x}
  have hC (T : Finset (ℂ × ℂ)) : (C T).Subsingleton := by
    rintro x ⟨hind, w, hw, hwy, hwx⟩ z ⟨_, v, hv, hvy, hvz⟩
    have he := slope_simplex_weights_unique T hind w v (hw.trans hv.symm) (hwy.trans hvy.symm)
    rw [← hwx, ← hvz]
    exact Finset.sum_congr rfl (fun p hp => congrArg (fun r : ℝ => r • p.1) (he p hp))
  have hfinite : (⋃ T ∈ (↑hS.toFinset.powerset : Set (Finset (ℂ × ℂ))), C T).Finite :=
    hS.toFinset.powerset.finite_toSet.biUnion (fun T _ => (hC T).finite)
  apply hfinite.subset
  rintro x ⟨T, hTS, _, hind, w, _, hw, hwy, hwx⟩
  have ht : T ∈ hS.toFinset.powerset := Finset.mem_powerset.mpr (fun p hp => by
    rw [Set.Finite.mem_toFinset]
    exact hTS hp)
  exact Set.mem_iUnion₂.mpr ⟨T, ht, hind, w, hw, hwy, hwx⟩

/-- The joint coefficient slice is the planar hull of the intercepts from
the slope simplices. Each simplex contributes at most one intercept. -/
theorem joint_coefficient_hull_iff_intercept_hull {S : Set (ℂ × ℂ)} (hS : S.Finite)
    (x y : ℂ) : (x, y) ∈ convexHull ℝ S ↔ x ∈ convexHull ℝ (slopeSliceIntercepts S y) := by
  classical
  constructor
  · intro h
    let C := slopeSliceIntercepts S y
    letI : Finite C := (slopeSliceIntercepts_finite hS y).to_subtype
    change x ∈ convexHull ℝ C
    rw [← (Subtype.range_coe : Set.range ((↑) : C → ℂ) = C)]
    apply mem_hull_of_directional_bound
    intro η
    obtain ⟨T, hTS, hsize, hind, w, hw, hsum, hslope, hproj⟩ :=
      slope_slice_certificate_of_mem hS h η
    let z := ∑ p ∈ T, w p • p
    have hz : z.1 ∈ C := ⟨T, hTS, hsize, hind, w, hw, hsum, hslope, by
      simp only [z, Prod.fst_sum, Prod.smul_fst]⟩
    refine ⟨⟨z.1, hz⟩, ?_⟩
    change (η * x).re ≤ (η * z.1).re
    rw [show (η * z.1).re = _ from project_intercept T w η]
    exact hproj
  · intro h
    let K : Set ℂ := {z | (z, y) ∈ convexHull ℝ S}
    have hK : Convex ℝ K := by
      intro z hz v hv a b ha hb hab
      change (a • z + b • v, y) ∈ convexHull ℝ S
      have hp : a • (z, y) + b • (v, y) ∈ convexHull ℝ S :=
        (convex_convexHull ℝ S) hz hv ha hb hab
      have he : a • (z, y) + b • (v, y) = (a • z + b • v, y) := by
        refine Prod.ext (by rfl) ?_
        change a • y + b • y = y
        rw [← add_smul, hab, one_smul]
      exact he ▸ hp
    change x ∈ K
    refine convexHull_min ?_ hK h
    rintro z ⟨T, hTS, _, _, w, hw, hsum, hy, hz⟩
    have hmem : (∑ p ∈ T, w p • p) ∈ convexHull ℝ S :=
      (convex_convexHull ℝ S).sum_mem hw hsum (fun p hp => subset_convexHull ℝ S (hTS hp))
    have he : (∑ p ∈ T, w p • p) = (z, y) := by
      apply Prod.ext
      · simpa only [Prod.fst_sum, Prod.smul_fst] using hz
      · simpa only [Prod.snd_sum, Prod.smul_snd] using hy
    change (z, y) ∈ convexHull ℝ S
    exact he ▸ hmem

/-- For fixed spectral lists and mixer, one slope simplex test per intercept
direction is equivalent to determinant inclusion for every free entry. -/
theorem one_free_partner_iff_slope_slice {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a b : ι → ℂ) (j : ι) (U : Matrix ι ι ℂ) (hU : IsUnitary U) :
    let P (z : ℂ) (p : Equiv.Perm ι) := matchingProduct a (Function.update b j z) p
    let D (z : ℂ) := determinantValue a (Function.update b j z) U
    (∀ z : ℂ, Holds a (Function.update b j z) U) ↔
      ∀ η : ℂ, SlopeSliceCertificate (Set.range fun p => (P 0 p, P 1 p - P 0 p))
        (D 0) (D 1 - D 0) η := by
  intro P D
  have hD (z : ℂ) : D z = D 0 + z * (D 1 - D 0) := by
    simpa only [D, mul_comm z] using determinant_update_interp a b j U hU z
  have hP (z : ℂ) (p : Equiv.Perm ι) : P z p = P 0 p + z * (P 1 p - P 0 p) := by
    simpa only [P, mul_comm z] using matching_update_interp a b j p z
  have heval : (∀ z : ℂ, Holds a (Function.update b j z) U) ↔
      ∀ z : ℂ, D 0 + z * (D 1 - D 0) ∈
        convexHull ℝ (Set.range fun p => P 0 p + z * (P 1 p - P 0 p)) := by
    apply forall_congr'
    intro z
    change D z ∈ convexHull ℝ (Set.range (P z)) ↔ _
    rw [hD z, funext (hP z)]
  rw [heval, affinePencil_hull_iff_joint]
  exact joint_coefficient_hull_iff_slope_slice (Set.finite_range _) _ _

/-- At each order, fix the mixer and all but one partner entry and test
the finite slope slice in every intercept direction. -/
def FreeEigenvalueSlopeSliceTest (n : ℕ) : Prop :=
  ∀ (a b : Fin n → ℂ) (j : Fin n) (U : Matrix (Fin n) (Fin n) ℂ), IsUnitary U →
    let P (z : ℂ) (p : Equiv.Perm (Fin n)) := matchingProduct a (Function.update b j z) p
    let D (z : ℂ) := determinantValue a (Function.update b j z) U
    ∀ η : ℂ, SlopeSliceCertificate (Set.range fun p => (P 0 p, P 1 p - P 0 p))
      (D 0) (D 1 - D 0) η

theorem freeEigenvalueSlopeSliceTest_iff (n : ℕ) :
    FreeEigenvalueSlopeSliceTest n ↔ Conjecture (Fin n) := by
  constructor
  · intro h a b U hU
    by_cases hn : n = 0
    · subst n
      exact conjecture_zero a b U hU
    let j : Fin n := ⟨0, Nat.pos_of_ne_zero hn⟩
    have hh := (one_free_partner_iff_slope_slice a b j U hU).mpr (h a b j U hU) (b j)
    simpa only [Function.update_eq_self] using hh
  · intro h a b j U hU
    exact (one_free_partner_iff_slope_slice a b j U hU).mp
      (fun z => h a (Function.update b j z) U hU)

end

end MOC
