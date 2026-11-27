import MOC.FiniteSimplicialCone
import Lean.Elab.Tactic.Omega

/-! The Leray property passes to links of faces. Use augmented integral
chains and grade each simplex by its number of vertices. -/

open Finset BigOperators

namespace MOC

section

variable {α : Type*} [Fintype α] [LinearOrder α]

/-- A chain is supported on faces of the specified vertex count. -/
def IsFiniteSimplicialChain (K : Set (Finset α)) (q : ℕ) (c : Finset α → ℤ) : Prop :=
  ∀ s, c s ≠ 0 → s ∈ K ∧ s.card = q

/-- Restrict the faces of a complex to a selected set of vertices. -/
def finiteSimplicialInduced (K : Set (Finset α)) (T : Finset α) : Set (Finset α) :=
  {s | s ∈ K ∧ s ⊆ T}

/-- A face in the link is disjoint from the given face, and their union is a face. -/
def finiteSimplicialLink (K : Set (Finset α)) (F : Finset α) : Set (Finset α) :=
  {s | Disjoint s F ∧ s ∪ F ∈ K}

/-- In each induced complex, every integral cycle in reduced degree
at least `d` bounds a chain of one higher degree. -/
def IsFiniteSimplicialLeray (K : Set (Finset α)) (d : ℕ) : Prop :=
  ∀ T : Finset α, ∀ q : ℕ, d < q → ∀ c : Finset α → ℤ,
    IsFiniteSimplicialChain (finiteSimplicialInduced K T) q c →
    finiteSimplicialBoundary c = 0 →
    ∃ b : Finset α → ℤ, IsFiniteSimplicialChain (finiteSimplicialInduced K T) (q + 1) b ∧
      finiteSimplicialBoundary b = c

private theorem finiteSimplicialBoundary_sub (c b : Finset α → ℤ) :
    finiteSimplicialBoundary (c - b) = finiteSimplicialBoundary c - finiteSimplicialBoundary b := by
  funext s
  simp only [finiteSimplicialBoundary, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

private theorem finiteSimplicialBoundary_neg (c : Finset α → ℤ) :
    finiteSimplicialBoundary (-c) = -finiteSimplicialBoundary c := by
  funext s
  simp only [finiteSimplicialBoundary, Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]

private theorem finiteSimplicialSection_sub (v : α) (c b : Finset α → ℤ) :
    finiteSimplicialSection v (c - b) =
      finiteSimplicialSection v c - finiteSimplicialSection v b := by
  funext s
  by_cases h : v ∈ s <;>
    simp [finiteSimplicialSection, h, mul_sub]

private theorem finiteSimplicialSection_eq_zero (v : α) (c : Finset α → ℤ)
    (hc : ∀ s, v ∈ s → c s = 0) : finiteSimplicialSection v c = 0 := by
  funext s
  simp [finiteSimplicialSection, hc (insert v s) (mem_insert_self _ _)]

private theorem finiteSimplicialLink_down_closed {K : Set (Finset α)}
    (hK : ∀ {s t}, s ∈ K → t ⊆ s → t ∈ K) (F : Finset α) :
    ∀ {s t}, s ∈ finiteSimplicialLink K F → t ⊆ s → t ∈ finiteSimplicialLink K F := by
  intro s t hs ht
  exact ⟨hs.1.mono_left ht, hK hs.2 (union_subset_union ht (fun _ hx => hx))⟩

private theorem finiteSimplicialLink_insert {K : Set (Finset α)} (F : Finset α) (v : α)
    (hv : v ∉ F) :
    finiteSimplicialLink (finiteSimplicialLink K F) {v} =
      finiteSimplicialLink K (insert v F) := by
  ext s
  have hu : (s ∪ {v}) ∪ F = s ∪ insert v F := by
    ext a
    simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_insert, or_assoc]
  change (Disjoint s {v} ∧ Disjoint (s ∪ {v}) F ∧ (s ∪ {v}) ∪ F ∈ K) ↔
    Disjoint s (insert v F) ∧ s ∪ insert v F ∈ K
  rw [hu]
  constructor
  · rintro ⟨hs, hF, hk⟩
    refine ⟨Finset.disjoint_left.mpr ?_, hk⟩
    intro a ha h
    rcases Finset.mem_insert.mp h with he | he
    · exact Finset.disjoint_left.mp hs ha (Finset.mem_singleton.mpr he)
    · exact Finset.disjoint_left.mp hF (Finset.mem_union_left _ ha) he
  · rintro ⟨hs, hk⟩
    refine ⟨Finset.disjoint_left.mpr ?_, Finset.disjoint_left.mpr ?_, hk⟩
    · intro a ha he
      exact Finset.disjoint_left.mp hs ha (Finset.mem_insert.mpr (Or.inl (Finset.mem_singleton.mp he)))
    · intro a ha hF
      rcases Finset.mem_union.mp ha with h | h
      · exact Finset.disjoint_left.mp hs h (Finset.mem_insert_of_mem hF)
      · exact hv ((Finset.mem_singleton.mp h) ▸ hF)

/-- The link of a vertex in a Leray complex has the same Leray bound.
Fill the cycle in the deletion, subtract that filling from its cone, and
take the signed section of a filling of the resulting cycle. -/
theorem finiteSimplicialLeray_link_singleton {K : Set (Finset α)} {d : ℕ}
    (hK : ∀ {s t}, s ∈ K → t ⊆ s → t ∈ K) (hL : IsFiniteSimplicialLeray K d) (v : α) :
    IsFiniteSimplicialLeray (finiteSimplicialLink K {v}) d := by
  classical
  intro T q hq c hc hc₀
  let S := T.erase v
  let T' := insert v T
  have hcv (s : Finset α) (hs : v ∈ s) : c s = 0 := by
    by_contra hz
    have hd := (hc s hz).1.1.1
    exact Finset.disjoint_left.mp hd hs (Finset.mem_singleton_self v)
  have hcS : IsFiniteSimplicialChain (finiteSimplicialInduced K S) q c := by
    intro s hs
    obtain ⟨⟨⟨hd, hface⟩, hst⟩, hcard⟩ := hc s hs
    refine ⟨⟨hK hface (Finset.subset_union_left), ?_⟩, hcard⟩
    intro a ha
    exact Finset.mem_erase.mpr
      ⟨fun he => Finset.disjoint_left.mp hd ha (Finset.mem_singleton.mpr he), hst ha⟩
  obtain ⟨b, hb, hb₀⟩ := hL S q hq c hcS hc₀
  have hbv (s : Finset α) (hs : v ∈ s) : b s = 0 := by
    by_contra hz
    exact (Finset.not_mem_erase v T) ((hb s hz).1.2 hs)
  let z := finiteSimplicialCone v c - b
  have hcT : IsFiniteSimplicialChain (finiteSimplicialInduced K T') (q + 1)
      (finiteSimplicialCone v c) := by
    intro s hs
    have hvs : v ∈ s := by
      by_contra hv
      exact hs (by simp [finiteSimplicialCone, hv])
    have he : c (s.erase v) ≠ 0 := by
      intro h
      exact hs (by simp [finiteSimplicialCone, hvs, h])
    obtain ⟨⟨⟨_, hface⟩, hst⟩, hcard⟩ := hc _ he
    have hu : s.erase v ∪ {v} = s := by
      rw [Finset.union_comm, ← Finset.insert_eq, Finset.insert_erase hvs]
    refine ⟨⟨hu ▸ hface, ?_⟩, ?_⟩
    · rw [← hu]
      exact Finset.union_subset (hst.trans (Finset.subset_insert _ _))
        (Finset.singleton_subset_iff.mpr (Finset.mem_insert_self _ _))
    · have hcard' := Finset.card_erase_add_one hvs
      omega
  have hz : IsFiniteSimplicialChain (finiteSimplicialInduced K T') (q + 1) z := by
    intro s hs
    by_cases hh : finiteSimplicialCone v c s = 0
    · have hbs : b s ≠ 0 := by
        intro he
        exact hs (by simp [z, hh, he])
      obtain ⟨⟨hsK, hsS⟩, hcard⟩ := hb s hbs
      exact ⟨⟨hsK, hsS.trans ((Finset.erase_subset _ _).trans (Finset.subset_insert _ _))⟩, hcard⟩
    · exact hcT s hh
  have hcCone : finiteSimplicialBoundary (finiteSimplicialCone v c) = c := by
    have h := finiteSimplicialBoundary_cone_add_cone_boundary v c
    rw [hc₀] at h
    have hz₀ : finiteSimplicialCone v (0 : Finset α → ℤ) = 0 := by
      funext s
      simp [finiteSimplicialCone]
    simpa only [hz₀, add_zero] using h
  have hz₀ : finiteSimplicialBoundary z = 0 := by
    change finiteSimplicialBoundary (finiteSimplicialCone v c - b) = 0
    rw [finiteSimplicialBoundary_sub, hcCone, hb₀, sub_self]
  obtain ⟨w, hw, hw₀⟩ := hL T' (q + 1) (by omega) z hz hz₀
  refine ⟨-finiteSimplicialSection v w, ?_, ?_⟩
  · intro s hs
    have hvs : v ∉ s := by
      intro hv
      exact hs (by simp [finiteSimplicialSection, hv])
    have hws : w (insert v s) ≠ 0 := by
      intro h
      exact hs (by simp [finiteSimplicialSection, hvs, h])
    obtain ⟨⟨hface, hsub⟩, hcard⟩ := hw _ hws
    have hdis : Disjoint s {v} := by
      rw [Finset.disjoint_singleton_right]
      exact hvs
    refine ⟨⟨⟨hdis, ?_⟩, ?_⟩, ?_⟩
    · simpa only [Finset.union_comm s {v}, ← Finset.insert_eq] using hface
    · intro a ha
      have ht := hsub (Finset.mem_insert_of_mem ha)
      exact (Finset.mem_insert.mp ht).resolve_left (fun he => hvs (he ▸ ha))
    · rw [Finset.card_insert_of_not_mem hvs] at hcard
      omega
  · rw [finiteSimplicialBoundary_neg, ← finiteSimplicialSection_boundary, hw₀]
    change finiteSimplicialSection v (finiteSimplicialCone v c - b) = c
    rw [finiteSimplicialSection_sub, finiteSimplicialSection_cone v c hcv,
      finiteSimplicialSection_eq_zero v b hbv, sub_zero]

/-- The link of any face inherits the Leray bound by taking one
vertex link at a time. -/
theorem finiteSimplicialLeray_link {K : Set (Finset α)} {d : ℕ}
    (hK : ∀ {s t}, s ∈ K → t ⊆ s → t ∈ K) (hL : IsFiniteSimplicialLeray K d)
    (F : Finset α) : IsFiniteSimplicialLeray (finiteSimplicialLink K F) d := by
  classical
  induction F using Finset.induction_on with
  | empty =>
    have he : finiteSimplicialLink K (∅ : Finset α) = K := by
      ext s
      simp [finiteSimplicialLink]
    rwa [he]
  | insert v F hv ih =>
    rw [← finiteSimplicialLink_insert F v hv]
    exact finiteSimplicialLeray_link_singleton (finiteSimplicialLink_down_closed hK F) ih v

end

end MOC
