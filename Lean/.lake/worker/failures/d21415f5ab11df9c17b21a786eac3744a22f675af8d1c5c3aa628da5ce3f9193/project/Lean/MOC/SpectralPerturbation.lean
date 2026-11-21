import MOC.Support
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Topology.Baire.CompleteMetrizable

/-! A strict support violation persists at spectra with nonzero and distinct
matching products. -/

open BigOperators Polynomial
open scoped Topology

namespace MOC

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private abbrev SpectrumPair (ι : Type*) := (ι → ℂ) × (ι → ℂ)

private def spectralLine (x y : SpectrumPair ι) (t : ℂ) : SpectrumPair ι :=
  (fun i => x.1 i + t * (y.1 i - x.1 i), fun i => x.2 i + t * (y.2 i - x.2 i))

private theorem dense_ne_zero_of_polynomial_lines (f : SpectrumPair ι → ℂ)
    (hnonzero : ∃ y, f y ≠ 0)
    (hpoly : ∀ x y, ∃ p : Polynomial ℂ, ∀ t, p.eval t = f (spectralLine x y t)) :
    Dense {x | f x ≠ 0} := by
  rw [dense_iff_inter_open]
  rintro O hO ⟨x, hx⟩
  obtain ⟨y, hy⟩ := hnonzero
  obtain ⟨p, hp⟩ := hpoly x y
  have h₁ : spectralLine x y 1 = y := by
    apply Prod.ext <;> funext i <;> simp [spectralLine]
  have hp₀ : p ≠ 0 := by
    intro he
    exact hy (by simpa only [h₁, he, eval_zero] using (hp 1).symm)
  have hroots : IsClosed ({t : ℂ | p.IsRoot t} \ {0}) :=
    ((finite_setOf_isRoot hp₀).subset Set.diff_subset).isClosed
  have hroot : ∀ᶠ t in 𝓝 (0 : ℂ), t ∉ ({s : ℂ | p.IsRoot s} \ {0}) :=
    hroots.isOpen_compl.mem_nhds (by simp)
  have hne : ∀ᶠ t in 𝓝[≠] (0 : ℂ), f (spectralLine x y t) ≠ 0 := by
    filter_upwards [hroot.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with t ht h₀
    exact fun hz => ht ⟨(hp t).trans hz, h₀⟩
  have hc : Continuous (spectralLine x y) := by
    apply Continuous.prodMk <;> apply continuous_pi <;> intro i <;>
      simp only [spectralLine] <;> fun_prop
  have hnear : ∀ᶠ t in 𝓝[≠] (0 : ℂ), spectralLine x y t ∈ O :=
    (hc.continuousAt.eventually_mem (hO.mem_nhds
      (by simpa [spectralLine] using hx))).filter_mono nhdsWithin_le_nhds
  obtain ⟨t, ht, htnz⟩ := (hnear.and hne).exists
  exact ⟨spectralLine x y t, ht, htnz⟩

private theorem matchingProducts_ne_at_some_spectra (σ τ : Equiv.Perm ι) (h : σ ≠ τ) :
    ∃ x : SpectrumPair ι, matchingProduct x.1 x.2 σ ≠ matchingProduct x.1 x.2 τ := by
  classical
  obtain ⟨j, hj⟩ := not_forall.mp (fun he : ∀ j, σ j = τ j => h (Equiv.ext he))
  let a (i : ι) : ℂ := if i = σ j then 1 else 0
  let b (i : ι) : ℂ := if i = j then 0 else 1
  have hσ : matchingProduct a b σ = 1 := by
    unfold matchingProduct
    apply Finset.prod_eq_one
    intro k _
    by_cases hk : k = j
    · subst k
      simp [a, b]
    · have hk' : σ k ≠ σ j := fun he => hk (σ.injective he)
      simp [a, b, hk, hk']
  have hτ : matchingProduct a b τ = 0 := by
    unfold matchingProduct
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    simp [a, b, Ne.symm hj]
  refine ⟨(a, b), ?_⟩
  change matchingProduct a b σ ≠ matchingProduct a b τ
  simpa only [hσ, hτ] using (one_ne_zero : (1 : ℂ) ≠ 0)

private theorem continuous_matchingProduct_pair (σ : Equiv.Perm ι) :
    Continuous fun x : SpectrumPair ι => matchingProduct x.1 x.2 σ := by
  unfold matchingProduct
  apply continuous_finset_prod
  intro j _
  fun_prop

private theorem dense_regular_matching_products :
    Dense {x : SpectrumPair ι | (∀ i j, x.1 i + x.2 j ≠ 0) ∧
      Function.Injective (matchingProduct x.1 x.2)} := by
  classical
  let S (q : ι × ι) : Set (SpectrumPair ι) := {x | x.1 q.1 + x.2 q.2 ≠ 0}
  let T (q : {q : Equiv.Perm ι × Equiv.Perm ι // q.1 ≠ q.2}) : Set (SpectrumPair ι) :=
    {x | matchingProduct x.1 x.2 q.1.1 ≠ matchingProduct x.1 x.2 q.1.2}
  let L (a b : ℂ) : Polynomial ℂ := C a + X * C (b - a)
  have hopenS (q : ι × ι) : IsOpen (S q) :=
    isOpen_ne_fun (by fun_prop) continuous_const
  have hopenT (q : {q : Equiv.Perm ι × Equiv.Perm ι // q.1 ≠ q.2}) : IsOpen (T q) :=
    isOpen_ne_fun (continuous_matchingProduct_pair q.1.1) (continuous_matchingProduct_pair q.1.2)
  have hdenseS (q : ι × ι) : Dense (S q) := by
    apply dense_ne_zero_of_polynomial_lines (fun x => x.1 q.1 + x.2 q.2)
    · exact ⟨(fun _ => 1, fun _ => 0), by simp⟩
    · intro x y
      exact ⟨L (x.1 q.1) (y.1 q.1) + L (x.2 q.2) (y.2 q.2), fun t =>
        by simp [L, spectralLine, eval_add, eval_mul, eval_C, eval_X]⟩
  have hdenseT (q : {q : Equiv.Perm ι × Equiv.Perm ι // q.1 ≠ q.2}) : Dense (T q) := by
    have hd := dense_ne_zero_of_polynomial_lines (fun x =>
      matchingProduct x.1 x.2 q.1.1 - matchingProduct x.1 x.2 q.1.2) (by
        obtain ⟨x, hx⟩ := matchingProducts_ne_at_some_spectra q.1.1 q.1.2 q.2
        exact ⟨x, sub_ne_zero.mpr hx⟩) (by
        intro x y
        let P (σ : Equiv.Perm ι) :=
          ∏ j, (L (x.1 (σ j)) (y.1 (σ j)) + L (x.2 j) (y.2 j))
        exact ⟨P q.1.1 - P q.1.2, fun t => by
          simp [P, L, spectralLine, matchingProduct, eval_sub, eval_prod, eval_add,
            eval_mul, eval_C, eval_X]⟩)
    simpa only [T, sub_ne_zero] using hd
  apply ((dense_iInter_of_isOpen hopenS hdenseS).inter_of_isOpen_right
    (dense_iInter_of_isOpen hopenT hdenseT) (isOpen_iInter_of_finite hopenT)).mono
  intro x hx
  refine ⟨fun i j => Set.mem_iInter.mp hx.1 (i, j), ?_⟩
  intro σ τ he
  by_contra hne
  exact (Set.mem_iInter.mp hx.2 ⟨(σ, τ), hne⟩) he

/-- A fixed unitary and direction with a strict support violation admit spectra
with the same strict inequality, all spectral sums nonzero, and distinct vertices. -/
theorem exists_regular_spectra_of_support_violation (a b : ι → ℂ) (U : Matrix ι ι ℂ) (η : ℂ)
    (h : ∀ σ : Equiv.Perm ι,
      (η * matchingProduct a b σ).re < (η * determinantValue a b U).re) :
    ∃ a' b' : ι → ℂ, (∀ i j, a' i + b' j ≠ 0) ∧ Function.Injective (matchingProduct a' b') ∧
      ∀ σ : Equiv.Perm ι,
        (η * matchingProduct a' b' σ).re < (η * determinantValue a' b' U).re := by
  let O (σ : Equiv.Perm ι) : Set (SpectrumPair ι) :=
    {x | (η * matchingProduct x.1 x.2 σ).re < (η * determinantValue x.1 x.2 U).re}
  have hd : Continuous fun x : SpectrumPair ι => (η * determinantValue x.1 x.2 U).re := by
    unfold determinantValue
    fun_prop
  have ho (σ : Equiv.Perm ι) : IsOpen (O σ) := by
    have hm := continuous_matchingProduct_pair σ
    exact isOpen_lt (by fun_prop) hd
  have hmem : (a, b) ∈ ⋂ σ, O σ := Set.mem_iInter.mpr h
  obtain ⟨x, hx, hstrict⟩ :=
    dense_regular_matching_products.exists_mem_open (isOpen_iInter_of_finite ho) ⟨(a, b), hmem⟩
  exact ⟨x.1, x.2, hx.1, hx.2, Set.mem_iInter.mp hstrict⟩

/-- Checking spectra with nonzero entries in the spectral sum matrix and
pairwise distinct matching products suffices in every finite order. -/
theorem conjecture_iff_regular_matching_products :
    Conjecture ι ↔ ∀ (a b : ι → ℂ) (U : Matrix ι ι ℂ), IsUnitary U →
      (∀ i j, a i + b j ≠ 0) → Function.Injective (matchingProduct a b) → Holds a b U := by
  constructor
  · intro h a b U hU _ _
    exact h a b U hU
  · intro h a b U hU
    by_contra hfail
    rw [holds_iff_directional] at hfail
    push_neg at hfail
    obtain ⟨η, hsep⟩ := hfail
    obtain ⟨a', b', hnonzero, hinj, hsep'⟩ :=
      exists_regular_spectra_of_support_violation a b U η hsep
    obtain ⟨σ, hσ⟩ :=
      (holds_iff_directional a' b' U).mp (h a' b' U hU hnonzero hinj) η
    exact (not_le_of_gt (hsep' σ)) hσ

end

end MOC
