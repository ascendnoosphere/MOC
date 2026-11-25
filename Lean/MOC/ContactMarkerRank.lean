import MOC.ContactDifferenceRank
import MOC.TwoValues

/-! Linear dependence of matching functions is detected by subset incidences.
The minor law motivating these markers is due to Merikoski and Virtanen,
DOI: 10.1016/0024-3795(89)90709-X. The representation-theoretic
description in M. Speck, *Determinants of Sums of Normal Matrices*,
Auburn University (2024), Theorem 2.2.31, is not used here.
Repository: https://etd.auburn.edu/handle/10415/9283 (no DOI identified). -/

open Finset

namespace MOC

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

/-- Evaluation at complementary binary spectra detects the fibre sums
of arbitrary complex matching coefficients, not just probability weights. -/
theorem sum_matchingProduct_eq_zero_iff_subset_fibres
    (p : κ → Equiv.Perm ι) (c : κ → ℂ) :
    (∀ a b : ι → ℂ, ∑ k, c k * matchingProduct a b (p k) = 0) ↔
      ∀ I J : Finset ι, ∑ k ∈ univ.filter (fun k => J.map (p k).toEmbedding = I), c k = 0 := by
  classical
  constructor
  · intro h I J
    by_cases hIJ : I.card = J.card
    · have he := h (fun i => if i ∈ I then 0 else 1) (fun j => if j ∈ J then 1 else 0)
      simp_rw [matchingProduct_subset_marker I J hIJ] at he
      rw [Finset.sum_filter]
      convert he using 1
      apply Finset.sum_congr rfl
      intro k _
      split_ifs <;> simp
    · have hempty : univ.filter (fun k => J.map (p k).toEmbedding = I) = ∅ := by
        apply Finset.filter_eq_empty_iff.mpr
        intro k _ he
        exact hIJ (by rw [← he, Finset.card_map])
      simp [hempty]
  · intro h a b
    simp_rw [matchingProduct_expand_subsets, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro J _
    rw [← Finset.sum_fiberwise univ (fun k => J.map (p k).toEmbedding)]
    apply Finset.sum_eq_zero
    intro I _
    rw [← zero_mul ((∏ i ∈ Iᶜ, a i) * ∏ j ∈ J, b j), ← h I J, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k hk
    rw [(Finset.mem_filter.mp hk).2]

/-- The difference of the two incidences in a subset-image fibre. -/
def contactMarkerDifference (r q : Equiv.Perm ι) (IJ : Finset ι × Finset ι) : ℂ :=
  (if IJ.2.map r.toEmbedding = IJ.1 then 1 else 0) -
    (if IJ.2.map q.toEmbedding = IJ.1 then 1 else 0)

/-- Exact linear relations of contact differences can be tested in
the subset-incidence space. No spectral samples or numerical rank tests are used. -/
theorem linearIndependent_contactDifference_iff_markers
    (r : Equiv.Perm ι) (q : κ → Equiv.Perm ι) :
    LinearIndependent ℂ (fun k => contactDifference r (q k)) ↔
      LinearIndependent ℂ (fun k => contactMarkerDifference r (q k)) := by
  classical
  simp only [Fintype.linearIndependent_iff]
  suffices aux : ∀ c : κ → ℂ,
      (∑ k, c k • contactDifference r (q k) = 0) ↔
        (∑ k, c k • contactMarkerDifference r (q k) = 0) by
    simp_rw [aux]
  intro c
  let p : κ ⊕ κ → Equiv.Perm ι := Sum.elim (fun _ => r) q
  let d : κ ⊕ κ → ℂ := Sum.elim c (fun k => -c k)
  have hspec : (∑ k, c k • contactDifference r (q k) = 0) ↔
      ∀ a b : ι → ℂ, ∑ k, d k * matchingProduct a b (p k) = 0 := by
    simp only [funext_iff, Finset.sum_apply, Pi.smul_apply, Pi.zero_apply, Prod.forall,
      contactDifference, smul_eq_mul]
    simp only [d, p, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, mul_sub, neg_mul,
      Finset.sum_neg_distrib, Finset.sum_sub_distrib, sub_eq_add_neg, mul_add, mul_neg,
      Finset.sum_add_distrib]
  rw [hspec, sum_matchingProduct_eq_zero_iff_subset_fibres]
  simp only [funext_iff, Finset.sum_apply, Pi.smul_apply, Pi.zero_apply, Prod.forall,
    contactMarkerDifference, smul_eq_mul]
  apply forall₂_congr
  intro I J
  simp only [Finset.sum_filter, Fintype.sum_sum_type, p, d, Sum.elim_inl, Sum.elim_inr,
    mul_sub, Finset.sum_sub_distrib, sub_eq_add_neg]
  have h₁ (k : κ) : (if J.map r.toEmbedding = I then c k else 0) =
      c k * (if J.map r.toEmbedding = I then 1 else 0) := by split_ifs <;> simp
  have h₂ (k : κ) : (if J.map (q k).toEmbedding = I then -c k else 0) =
      -(c k * (if J.map (q k).toEmbedding = I then 1 else 0)) := by split_ifs <;> simp
  simp only [h₁, h₂, mul_add, mul_neg, Finset.sum_add_distrib, Finset.sum_neg_distrib]

end MOC
