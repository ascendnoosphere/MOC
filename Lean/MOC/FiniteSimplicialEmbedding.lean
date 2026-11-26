import MOC.FiniteSimplicialCone
import Mathlib.Data.Finset.Card

/-! An order embedding of finite vertex sets extends augmented simplicial
chains by zero and preserves their boundary. -/

open Finset BigOperators

namespace MOC

variable {α β : Type*} [Fintype α] [Fintype β] [LinearOrder α] [LinearOrder β]

private theorem finiteSimplicial_map_preimage (e : α ↪o β) (t : Finset β)
    (ht : t ⊆ (Finset.univ : Finset α).map e.toEmbedding) :
    ((Finset.univ : Finset α).filter (fun a => e a ∈ t)).map e.toEmbedding = t := by
  ext v
  constructor
  · intro hv
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hv
    exact (Finset.mem_filter.mp ha).2
  · intro hv
    obtain ⟨a, ha, he⟩ := Finset.mem_map.mp (ht hv)
    change e a = v at he
    have hat : e a ∈ t := by simpa only [he] using hv
    exact Finset.mem_map.mpr ⟨a, Finset.mem_filter.mpr ⟨ha, hat⟩, he⟩

/-- Every face on the embedded vertices is the image of a face. -/
theorem finiteSimplicial_exists_map_eq_of_subset (e : α ↪o β) (t : Finset β)
    (ht : t ⊆ (Finset.univ : Finset α).map e.toEmbedding) :
    ∃ s : Finset α, s.map e.toEmbedding = t :=
  ⟨_, finiteSimplicial_map_preimage e t ht⟩

/-- Extend the chain coefficients by zero on faces outside the embedded vertices. -/
def finiteSimplicialPushChain (e : α ↪o β) (c : Finset α → ℤ) (t : Finset β) : ℤ :=
  if t ⊆ (Finset.univ : Finset α).map e.toEmbedding then
    c ((Finset.univ : Finset α).filter (fun a => e a ∈ t))
  else 0

/-- The extension preserves the coefficient of each embedded face. -/
theorem finiteSimplicialPushChain_map (e : α ↪o β) (c : Finset α → ℤ) (s : Finset α) :
    finiteSimplicialPushChain e c (s.map e.toEmbedding) = c s := by
  have hs : s.map e.toEmbedding ⊆ (Finset.univ : Finset α).map e.toEmbedding :=
    Finset.map_subset_map.mpr (Finset.subset_univ s)
  rw [finiteSimplicialPushChain, if_pos hs]
  exact congrArg c (Finset.map_injective e.toEmbedding (finiteSimplicial_map_preimage e _ hs))

/-- The extension is zero on any face with a vertex outside the image. -/
theorem finiteSimplicialPushChain_eq_zero (e : α ↪o β) (c : Finset α → ℤ) (t : Finset β)
    (ht : ¬ t ⊆ (Finset.univ : Finset α).map e.toEmbedding) :
    finiteSimplicialPushChain e c t = 0 := by
  rw [finiteSimplicialPushChain, if_neg ht]

/-- Extension sends the zero chain to the zero chain. -/
theorem finiteSimplicialPushChain_zero (e : α ↪o β) :
    finiteSimplicialPushChain e 0 = 0 := by
  funext t
  simp only [finiteSimplicialPushChain, Pi.zero_apply, ite_self]

private theorem finiteSimplicial_filter_card_map (e : α ↪o β) (s : Finset α) (v : α) :
    ((s.map e.toEmbedding).filter (fun a => a < e v)).card =
      (s.filter (fun a => a < v)).card := by
  rw [Finset.filter_map, Finset.card_map]
  congr 1
  ext a
  simp only [Finset.mem_filter, Function.comp_apply]
  change (a ∈ s ∧ e a < e v) ↔ (a ∈ s ∧ a < v)
  rw [e.lt_iff_lt]

private theorem finiteSimplicialBoundary_pushChain_map (e : α ↪o β)
    (c : Finset α → ℤ) (s : Finset α) :
    finiteSimplicialBoundary (finiteSimplicialPushChain e c) (s.map e.toEmbedding) =
      finiteSimplicialBoundary c s := by
  let f (w : β) : ℤ :=
    (-1 : ℤ) ^ ((s.map e.toEmbedding).filter (fun a => a < w)).card *
      finiteSimplicialPushChain e c (insert w (s.map e.toEmbedding))
  have hsum : (∑ w ∈ ((Finset.univ : Finset α) \ s).map e.toEmbedding, f w) =
      ∑ w ∈ (Finset.univ : Finset β) \ s.map e.toEmbedding, f w := by
    refine Finset.sum_subset ?_ ?_
    · intro w hw
      obtain ⟨v, hv, rfl⟩ := Finset.mem_map.mp hw
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun hs =>
        (Finset.mem_sdiff.mp hv).2 ((Finset.mem_map' e.toEmbedding).mp hs)⟩
    · intro w hw hnot
      have hout : w ∉ (Finset.univ : Finset α).map e.toEmbedding := by
        intro h
        obtain ⟨v, hv, rfl⟩ := Finset.mem_map.mp h
        have hvs : v ∉ s := fun hs =>
          (Finset.mem_sdiff.mp hw).2 (Finset.mem_map_of_mem e.toEmbedding hs)
        exact hnot (Finset.mem_map.mpr ⟨v, Finset.mem_sdiff.mpr ⟨hv, hvs⟩, rfl⟩)
      have hins : ¬ insert w (s.map e.toEmbedding) ⊆
          (Finset.univ : Finset α).map e.toEmbedding :=
        fun h => hout (h (Finset.mem_insert_self _ _))
      dsimp only [f]
      rw [finiteSimplicialPushChain_eq_zero e c _ hins, mul_zero]
  unfold finiteSimplicialBoundary
  change (∑ w ∈ (Finset.univ : Finset β) \ s.map e.toEmbedding, f w) = _
  rw [← hsum, Finset.sum_map]
  refine Finset.sum_congr rfl ?_
  intro v _
  change (-1 : ℤ) ^ ((s.map e.toEmbedding).filter (fun a => a < e v)).card *
      finiteSimplicialPushChain e c (insert (e v) (s.map e.toEmbedding)) =
    (-1 : ℤ) ^ (s.filter (fun a => a < v)).card * c (insert v s)
  have hins : (insert v s).map e.toEmbedding = insert (e v) (s.map e.toEmbedding) :=
    Finset.map_insert e.toEmbedding v s
  rw [finiteSimplicial_filter_card_map e s v, ← hins, finiteSimplicialPushChain_map]

/-- Extension along an order embedding commutes with the simplicial boundary. -/
theorem finiteSimplicialBoundary_pushChain (e : α ↪o β) (c : Finset α → ℤ) :
    finiteSimplicialBoundary (finiteSimplicialPushChain e c) =
      finiteSimplicialPushChain e (finiteSimplicialBoundary c) := by
  funext t
  by_cases ht : t ⊆ (Finset.univ : Finset α).map e.toEmbedding
  · obtain ⟨s, rfl⟩ := finiteSimplicial_exists_map_eq_of_subset e t ht
    rw [finiteSimplicialPushChain_map]
    exact finiteSimplicialBoundary_pushChain_map e c s
  · rw [finiteSimplicialPushChain_eq_zero e (finiteSimplicialBoundary c) t ht,
      finiteSimplicialBoundary]
    apply Finset.sum_eq_zero
    intro v _
    have hins : ¬ insert v t ⊆ (Finset.univ : Finset α).map e.toEmbedding :=
      fun h => ht ((Finset.subset_insert v t).trans h)
    rw [finiteSimplicialPushChain_eq_zero e c _ hins, mul_zero]

/-- Read the coefficients of the chain on the embedded faces. -/
def finiteSimplicialPullChain (e : α ↪o β) (b : Finset β → ℤ) (s : Finset α) : ℤ :=
  b (s.map e.toEmbedding)

/-- Reading coefficients on the embedded faces recovers the original chain. -/
theorem finiteSimplicialPullChain_pushChain (e : α ↪o β) (c : Finset α → ℤ) :
    finiteSimplicialPullChain e (finiteSimplicialPushChain e c) = c :=
  funext (finiteSimplicialPushChain_map e c)

/-- Extension recovers a chain supported on the embedded vertices. -/
theorem finiteSimplicialPushChain_pullChain (e : α ↪o β) (b : Finset β → ℤ)
    (hb : ∀ t, ¬ t ⊆ (Finset.univ : Finset α).map e.toEmbedding → b t = 0) :
    finiteSimplicialPushChain e (finiteSimplicialPullChain e b) = b := by
  funext t
  by_cases ht : t ⊆ (Finset.univ : Finset α).map e.toEmbedding
  · obtain ⟨s, rfl⟩ := finiteSimplicial_exists_map_eq_of_subset e t ht
    exact finiteSimplicialPushChain_map e (finiteSimplicialPullChain e b) s
  · rw [finiteSimplicialPushChain_eq_zero e _ t ht, hb t ht]

/-- Reading coefficients of a supported chain commutes with the boundary. -/
theorem finiteSimplicialBoundary_pullChain_of_supported (e : α ↪o β) (b : Finset β → ℤ)
    (hb : ∀ t, ¬ t ⊆ (Finset.univ : Finset α).map e.toEmbedding → b t = 0) :
    finiteSimplicialBoundary (finiteSimplicialPullChain e b) =
      finiteSimplicialPullChain e (finiteSimplicialBoundary b) := by
  have h := finiteSimplicialBoundary_pushChain e (finiteSimplicialPullChain e b)
  rw [finiteSimplicialPushChain_pullChain e b hb] at h
  rw [h, finiteSimplicialPullChain_pushChain]

/-- A filling supported on the embedded vertices gives a filling of the original chain. -/
theorem finiteSimplicialBoundary_pullChain_eq (e : α ↪o β) (b : Finset β → ℤ)
    (c : Finset α → ℤ)
    (hb : ∀ t, ¬ t ⊆ (Finset.univ : Finset α).map e.toEmbedding → b t = 0)
    (hfill : finiteSimplicialBoundary b = finiteSimplicialPushChain e c) :
    finiteSimplicialBoundary (finiteSimplicialPullChain e b) = c := by
  rw [finiteSimplicialBoundary_pullChain_of_supported e b hb, hfill,
    finiteSimplicialPullChain_pushChain]

end MOC
