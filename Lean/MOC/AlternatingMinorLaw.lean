import MOC.FiniteMinorLaw
import MOC.StrongSupport
import Mathlib.Topology.Order.Basic

/-!
The determinant interface to the complementary double-dimer identity of
T. Lam, *Dimers, webs, and positroids*, DOI: 10.1112/jlms/jdv039, Theorem 3.1.
The interface assumes the complementary identities; it does not prove
Lam's planar-network theorem or its Plücker-minor identification.
-/

open BigOperators Finset Filter
open scoped Topology

namespace MOC

noncomputable section
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

/-- In a graph chart, select all coordinate columns except I and select
the mixer columns J. The two summands tag the two kinds of columns. -/
def graphBoundary (I J : Finset ι) : Finset (ι ⊕ ι) :=
  Iᶜ.disjSum J

/-- The matching joins mixer column j to coordinate column p(j). -/
def separatesGraphBoundary (p : Equiv.Perm ι) (S : Finset (ι ⊕ ι)) : Prop :=
  ∀ j, Sum.inl (p j) ∈ S ↔ Sum.inr j ∉ S

local instance (p : Equiv.Perm ι) (S : Finset (ι ⊕ ι)) :
    Decidable (separatesGraphBoundary p S) := Classical.propDecidable _

theorem separates_graphBoundary_iff (p : Equiv.Perm ι) (I J : Finset ι) :
    separatesGraphBoundary p (graphBoundary I J) ↔ J.map p.toEmbedding = I := by
  have hbridge : separatesGraphBoundary p (graphBoundary I J) ↔
      ∀ j, p j ∈ I ↔ j ∈ J := by simp [separatesGraphBoundary, graphBoundary, not_iff_not]
  rw [hbridge]
  constructor
  · intro hp
    ext i
    rw [Finset.mem_map_equiv]
    have ht := hp (p.symm i)
    rw [Equiv.apply_symm_apply] at ht
    exact ht.symm
  · intro hp j
    rw [← hp, Finset.mem_map_equiv, Equiv.symm_apply_apply]

/-- The indexed alternating complementary identity yields a probability law
for all minors and therefore one simultaneous convex combination for all spectra.
Only balanced boundary sets occur in the external identity. -/
theorem alternating_complementary_law
    (U : Matrix ι ι ℂ) (hU : IsUnitary U)
    (p : κ → Equiv.Perm ι) (c : κ → ℝ) (hc : ∀ k, 0 ≤ c k)
    (L : Finset (ι ⊕ ι) → ℝ) (m : ℝ) (hm : 0 < m)
    (hminor : ∀ I J : Finset ι, I.card = J.card →
      L (graphBoundary I J) = m * subsetMinorSq U I J)
    (hcomp : ∀ I J : Finset ι, I.card = J.card →
      L (graphBoundary I J) = ∑ k ∈ univ.filter
        (fun k => separatesGraphBoundary (p k) (graphBoundary I J)), c k) :
    ∃ w : κ → ℝ, (∀ k, 0 ≤ w k) ∧ ∑ k, w k = 1 ∧
      (∀ I J : Finset ι, subsetMinorSq U I J =
        ∑ k ∈ univ.filter (fun k => J.map (p k).toEmbedding = I), w k) ∧
      (∀ a b : ι → ℂ, Holds a b U) := by
  classical
  let w (k : κ) := c k / m
  have hnonneg (k : κ) : 0 ≤ w k := div_nonneg (hc k) hm.le
  have hlaw (I J : Finset ι) : subsetMinorSq U I J =
      ∑ k ∈ univ.filter (fun k => J.map (p k).toEmbedding = I), w k := by
    by_cases hij : I.card = J.card
    · have he := (hminor I J hij).symm.trans (hcomp I J hij)
      simp only [separates_graphBoundary_iff] at he
      simp only [w, ← Finset.sum_div, ← he]
      field_simp
    · have hn (k : κ) : J.map (p k).toEmbedding ≠ I := by
        intro hh
        have he := congrArg Finset.card hh
        exact hij (by simpa using he.symm)
      simp [subsetMinorSq, hij, hn]
  have hzero : subsetMinorSq U ∅ ∅ = 1 := by
    apply Complex.ofReal_injective
    rw [← sum_signedWeight_image_eq_subsetMinorSq U hU]
    simpa using sum_signedWeight U (det_ne_zero_of_unitary hU)
  have htotal : ∑ k, w k = 1 := by
    simpa [hzero] using (hlaw ∅ ∅).symm
  exact ⟨w, hnonneg, htotal, hlaw,
    fun a b => holds_of_indexed_minor_law a b U hU p w hnonneg htotal hlaw⟩

/-- A fixed finite list of continuous signed weights that is strictly positive
at the center is a positive law throughout a neighborhood. The function U
may parametrize complex unitary matrices, not only orthogonal matrices. -/
theorem eventually_holds_of_continuous_indexed_minor_law
    {X : Type*} [TopologicalSpace X] (x₀ : X)
    (U : X → Matrix ι ι ℂ) (hU : ∀ x, IsUnitary (U x))
    (p : κ → Equiv.Perm ι) (w : κ → X → ℝ)
    (hcont : ∀ k, ContinuousAt (w k) x₀) (hpos : ∀ k, 0 < w k x₀)
    (hm : ∀ x, ∀ I J : Finset ι, subsetMinorSq (U x) I J =
      ∑ k ∈ univ.filter (fun k => J.map (p k).toEmbedding = I), w k x) :
    ∀ᶠ x in 𝓝 x₀, (∀ k, 0 < w k x) ∧ (∀ a b : ι → ℂ, Holds a b (U x)) := by
  classical
  have he (k : κ) : ∀ᶠ x in 𝓝 x₀, 0 < w k x :=
    (hcont k).eventually (lt_mem_nhds (hpos k))
  filter_upwards [Filter.eventually_all.mpr he] with x hx
  refine ⟨hx, fun a b => ?_⟩
  have hzero : subsetMinorSq (U x) ∅ ∅ = 1 := by
    apply Complex.ofReal_injective
    rw [← sum_signedWeight_image_eq_subsetMinorSq (U x) (hU x)]
    simpa using sum_signedWeight (U x) (det_ne_zero_of_unitary (hU x))
  have htotal : ∑ k, w k x = 1 := by
    simpa [hzero] using (hm x ∅ ∅).symm
  exact holds_of_indexed_minor_law a b (U x) (hU x) p (fun k => w k x)
    (fun k => (hx k).le) htotal (hm x)

/-- A positive law on a fixed set of permutations gives strict spectral support
whenever that same set is sufficient for signed laws at every unitary. -/
theorem strict_support_of_positive_spanning_minor_law
    (a b : ι → ℂ) (U : Matrix ι ι ℂ) (hU : IsUnitary U)
    (p : κ → Equiv.Perm ι) (w : κ → ℝ) (hw : ∀ k, 0 < w k)
    (hall : ∀ V : Matrix ι ι ℂ, IsUnitary V → ∃ c : κ → ℝ,
      ∀ I J : Finset ι, subsetMinorSq V I J =
        ∑ k ∈ univ.filter (fun k => J.map (p k).toEmbedding = I), c k)
    (hm : ∀ I J : Finset ι, subsetMinorSq U I J =
      ∑ k ∈ univ.filter (fun k => J.map (p k).toEmbedding = I), w k)
    (η : ℂ) (H : ℝ)
    (hbound : ∀ σ : Equiv.Perm ι, (η * matchingProduct a b σ).re ≤ H)
    (hproper : ∃ σ : Equiv.Perm ι, (η * matchingProduct a b σ).re < H) :
    (η * determinantValue a b U).re < H := by
  classical
  let q (k : κ) : ℝ := (η * matchingProduct a b (p k)).re
  have hweight (V : Matrix ι ι ℂ) (hV : IsUnitary V) (c : κ → ℝ)
      (hc : ∀ I J : Finset ι, subsetMinorSq V I J =
        ∑ k ∈ univ.filter (fun k => J.map (p k).toEmbedding = I), c k) :
      (∑ k, c k) = 1 ∧ (η * determinantValue a b V).re = ∑ k, c k * q k := by
    constructor
    · have hz : subsetMinorSq V ∅ ∅ = 1 := by
        apply Complex.ofReal_injective
        rw [← sum_signedWeight_image_eq_subsetMinorSq V hV]
        simpa using sum_signedWeight V (det_ne_zero_of_unitary hV)
      simpa [hz] using (hc ∅ ∅).symm
    · rw [← determinantValue_eq_sum_of_indexed_minor_law a b V hV p c hc,
        Finset.mul_sum, Complex.re_sum]
      apply Finset.sum_congr rfl
      intro k _
      rw [mul_left_comm η]
      simp [q, Complex.mul_re]
  have hk : ∃ k, q k < H := by
    by_contra! hn
    have hq (k : κ) : q k = H := le_antisymm (hbound (p k)) (hn k)
    obtain ⟨σ, hσ⟩ := hproper
    obtain ⟨V, hV, he⟩ := matchingProduct_mem_determinantRange a b σ
    obtain ⟨c, hc⟩ := hall V hV
    obtain ⟨ht, hv⟩ := hweight V hV c hc
    rw [he] at hv
    simp_rw [hq, ← Finset.sum_mul, ht, one_mul] at hv
    exact (not_lt_of_ge hv.ge) hσ
  obtain ⟨ht, hv⟩ := hweight U hU w hm
  have hg : 0 < ∑ k, w k * (H - q k) := by
    apply Finset.sum_pos' (fun k _ => mul_nonneg (hw k).le (sub_nonneg.mpr (hbound (p k))))
    obtain ⟨k, hk⟩ := hk
    exact ⟨k, Finset.mem_univ _, mul_pos (hw k) (sub_pos.mpr hk)⟩
  simp_rw [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, ht, one_mul, ← hv] at hg
  exact sub_pos.mp hg

end

end MOC
