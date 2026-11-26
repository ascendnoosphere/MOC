import MOC.BlockConstraintLink
import MOC.BlockJoinOrientedChains
import MOC.FiniteSimplicialEmbedding
import MOC.FiniteSimplicialLeray
import Mathlib.Data.Sum.Order

/-! The simplex-boundary joins from the block laws give lower bounds
for Leray numbers of minor-constraint nerves. -/

open Finset Matrix BigOperators

namespace MOC

noncomputable section

/-- A face of a minor-constraint nerve admits a probability law on
permutations with the specified expectations on that face. -/
def minorConstraintNerve {v ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix ι ι ℂ) (I J : v → Finset ι) : Set (Finset v) :=
  {s | ∃ w : Equiv.Perm ι → ℝ, (∀ σ, 0 ≤ w σ) ∧ (∑ σ, w σ) = 1 ∧
    ∀ i ∈ s, (∑ σ, w σ * subsetImageEvent (I i) (J i) σ) = subsetMinorSq U (I i) (J i)}

theorem minorConstraintNerve_down_closed {v ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix ι ι ℂ) (I J : v → Finset ι) {s t : Finset v}
    (h : s ∈ minorConstraintNerve U I J) (hst : t ⊆ s) : t ∈ minorConstraintNerve U I J := by
  obtain ⟨w, hw, hm, hc⟩ := h
  exact ⟨w, hw, hm, fun i hi => hc i (hst hi)⟩

variable {B : Type*} [Fintype B] [LinearOrder B]
variable {ι : B → Type*} [∀ k, Fintype (ι k)] [∀ k, DecidableEq (ι k)]

/-- Row and column indices that belong to distinct blocks. -/
abbrev CrossBlockPair (ι : B → Type*) :=
  {p : (Σ j, ι j) × (Σ j, ι j) // p.1.1 ≠ p.2.1}

/-- The vertex labels put each local probe before all cross-block constraints. -/
abbrev BlockObservationVertex (m : B → ℕ) (ι : B → Type*)
    [∀ k, Fintype (ι k)] [∀ k, DecidableEq (ι k)] :=
  Lex (OrderedBlockJoinVertex m ⊕ Fin (Fintype.card (CrossBlockPair ι)))

def blockProbeEmbedding (m : B → ℕ) (ι : B → Type*)
    [∀ k, Fintype (ι k)] [∀ k, DecidableEq (ι k)] :
    OrderedBlockJoinVertex m ↪o BlockObservationVertex m ι where
  toFun v := toLex (Sum.inl v)
  inj' := fun _ _ h => Sum.inl.inj (congrArg ofLex h)
  map_rel_iff' := Sum.Lex.inl_le_inl_iff

private def crossBlockEmbedding (m : B → ℕ) (ι : B → Type*)
    [∀ k, Fintype (ι k)] [∀ k, DecidableEq (ι k)] :
    Fin (Fintype.card (CrossBlockPair ι)) ↪ BlockObservationVertex m ι where
  toFun v := toLex (Sum.inr v)
  inj' := fun _ _ h => Sum.inr.inj (congrArg ofLex h)

/-- The face with all cross-block singleton constraints. -/
def crossBlockConstraintFace (m : B → ℕ) (ι : B → Type*)
    [∀ k, Fintype (ι k)] [∀ k, DecidableEq (ι k)] :
    Finset (BlockObservationVertex m ι) :=
  univ.map (crossBlockEmbedding m ι)

private def blockObservationRows {m : B → ℕ}
    (I : ∀ j, Fin (m j + 1) → Finset (ι j)) (v : BlockObservationVertex m ι) :
    Finset (Σ j, ι j) :=
  match ofLex v with
  | .inl p =>
    let q := ofLex p
    (I q.1 q.2).map (Function.Embedding.sigmaMk q.1)
  | .inr r => {((Fintype.equivFin (CrossBlockPair ι)).symm r).val.1}

private def blockObservationColumns {m : B → ℕ}
    (J : ∀ j, Fin (m j + 1) → Finset (ι j)) (v : BlockObservationVertex m ι) :
    Finset (Σ j, ι j) :=
  match ofLex v with
  | .inl p =>
    let q := ofLex p
    (J q.1 q.2).map (Function.Embedding.sigmaMk q.1)
  | .inr r => {((Fintype.equivFin (CrossBlockPair ι)).symm r).val.2}

/-- The minor nerve of the local observations and all cross-block singletons. -/
def blockObservationNerve {m : B → ℕ} (U : ∀ j, Matrix (ι j) (ι j) ℂ)
    (I J : ∀ j, Fin (m j + 1) → Finset (ι j)) : Set (Finset (BlockObservationVertex m ι)) :=
  minorConstraintNerve (blockDiagonal' U) (blockObservationRows I) (blockObservationColumns J)

private theorem disjoint_crossBlockConstraintFace {m : B → ℕ} (s : Finset (OrderedBlockJoinVertex m)) :
    Disjoint (s.map (blockProbeEmbedding m ι).toEmbedding) (crossBlockConstraintFace m ι) := by
  apply Finset.disjoint_left.mpr
  intro v hx hy
  obtain ⟨p, _, rfl⟩ := Finset.mem_map.mp hx
  obtain ⟨r, _, hr⟩ := Finset.mem_map.mp hy
  exact Sum.noConfusion (congrArg ofLex hr)

/-- Local probe selections belong to the link precisely when they are feasible
with the cross-block singleton probabilities set to zero. -/
theorem blockObservationNerve_link_iff {m : B → ℕ} (U : ∀ j, Matrix (ι j) (ι j) ℂ)
    (hU : ∀ j, IsUnitary (U j)) (I J : ∀ j, Fin (m j + 1) → Finset (ι j))
    (s : Finset (OrderedBlockJoinVertex m)) :
    s.map (blockProbeEmbedding m ι).toEmbedding ∈
      finiteSimplicialLink (blockObservationNerve U I J) (crossBlockConstraintFace m ι) ↔
    BlockMinorLinkFeasible U (fun j => orderedBlockJoinBlock m s j) I J := by
  classical
  let e := blockProbeEmbedding m ι
  let f := crossBlockEmbedding m ι
  let h := Fintype.equivFin (CrossBlockPair ι)
  have hprobe (j : B) (i : Fin (m j + 1)) :
      blockObservationRows I (e (toLex ⟨j, i⟩)) = (I j i).map (Function.Embedding.sigmaMk j) ∧
      blockObservationColumns J (e (toLex ⟨j, i⟩)) = (J j i).map (Function.Embedding.sigmaMk j) :=
    ⟨rfl, rfl⟩
  have hcross (p : CrossBlockPair ι) :
      blockObservationRows I (f (h p)) = {p.val.1} ∧
      blockObservationColumns J (f (h p)) = {p.val.2} := by
    change ({(h.symm (h p)).val.1} : Finset (Σ j, ι j)) = {p.val.1} ∧
      ({(h.symm (h p)).val.2} : Finset (Σ j, ι j)) = {p.val.2}
    simp only [Equiv.symm_apply_apply]
  constructor
  · rintro ⟨_, w, hw, hm, hf⟩
    refine ⟨w, hw, hm, ?_, ?_⟩
    · intro i j hij
      let p : CrossBlockPair ι := ⟨(i, j), hij⟩
      have hp : f (h p) ∈ crossBlockConstraintFace m ι := Finset.mem_map.mpr ⟨h p, mem_univ _, rfl⟩
      have hv := hf (f (h p)) (Finset.mem_union_right _ hp)
      simpa only [(hcross p).1, (hcross p).2,
        subsetMinorSq_blockDiagonal'_singleton_cross U hU i j hij] using hv
    · intro j i hi
      have hmem : toLex (⟨j, i⟩ : Σ j, Fin (m j + 1)) ∈ s :=
        (Finset.mem_filter.mp hi).2
      have hp : e (toLex ⟨j, i⟩) ∈ s.map e.toEmbedding := Finset.mem_map.mpr ⟨_, hmem, rfl⟩
      have hv := hf _ (Finset.mem_union_left _ hp)
      simpa only [(hprobe j i).1, (hprobe j i).2] using hv
  · rintro ⟨w, hw, hm, hx, hp⟩
    refine ⟨disjoint_crossBlockConstraintFace s, w, hw, hm, ?_⟩
    intro v hv
    rcases Finset.mem_union.mp hv with hv | hv
    · obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hv
      change (Σ j, Fin (m j + 1)) at a
      rcases a with ⟨j, i⟩
      have hi : i ∈ orderedBlockJoinBlock m s j := Finset.mem_filter.mpr ⟨mem_univ _, ha⟩
      simpa only [(hprobe j i).1, (hprobe j i).2] using hp j i hi
    · obtain ⟨r, _, rfl⟩ := Finset.mem_map.mp hv
      let p := h.symm r
      have hr : h p = r := Equiv.apply_symm_apply _ _
      rw [← hr, (hcross p).1, (hcross p).2,
        subsetMinorSq_blockDiagonal'_singleton_cross U hU _ _ p.property]
      exact hx p.val.1 p.val.2 p.property

/-- If each block has a simplex-boundary nerve, the combined nerve
has Leray number at least the sum of the block boundary sizes. -/
theorem blockObservationNerve_not_leray {m : B → ℕ} (U : ∀ j, Matrix (ι j) (ι j) ℂ)
    (hU : ∀ j, IsUnitary (U j)) (I J : ∀ j, Fin (m j + 1) → Finset (ι j))
    (hlocal : ∀ j (s : Finset (Fin (m j + 1))),
      s ∈ minorConstraintNerve (U j) (I j) (J j) ↔ s ≠ univ)
    {d : ℕ} (hd : d < ∑ j, m j) :
    ¬ IsFiniteSimplicialLeray (blockObservationNerve U I J) d := by
  classical
  intro hL
  let K := blockObservationNerve U I J
  let F := crossBlockConstraintFace m ι
  let e := blockProbeEmbedding m ι
  let T := (univ : Finset (OrderedBlockJoinVertex m)).map e.toEmbedding
  let q := ∑ j, m j
  have hlink : IsFiniteSimplicialLeray (finiteSimplicialLink K F) d :=
    finiteSimplicialLeray_link (minorConstraintNerve_down_closed _ _ _) hL F
  have hface (s : Finset (OrderedBlockJoinVertex m)) :
      s.map e.toEmbedding ∈ finiteSimplicialLink K F ↔ s ∈ orderedBlockJoinFaces m := by
    refine (blockObservationNerve_link_iff U hU I J s).trans
      ((blockMinorLinkFeasible_iff U hU (fun j => orderedBlockJoinBlock m s j) I J).trans ?_)
    change (∀ j, orderedBlockJoinBlock m s j ∈ minorConstraintNerve (U j) (I j) (J j)) ↔
      ∀ j, orderedBlockJoinBlock m s j ≠ univ
    exact forall_congr' fun j => hlocal j (orderedBlockJoinBlock m s j)
  obtain ⟨c, hc, hn, h₀, _⟩ := orderedBlockJoin_top_cycle_witness m
  let z := finiteSimplicialPushChain e c
  have hzChain : IsFiniteSimplicialChain (finiteSimplicialInduced (finiteSimplicialLink K F) T) q z := by
    intro t ht
    have hsub : t ⊆ T := by
      by_contra h
      exact ht (finiteSimplicialPushChain_eq_zero e c t h)
    obtain ⟨s, rfl⟩ := finiteSimplicial_exists_map_eq_of_subset e t hsub
    obtain ⟨hs, hcard⟩ := hc s (by simpa only [z, finiteSimplicialPushChain_map] using ht)
    exact ⟨⟨(hface s).mpr hs, hsub⟩, by simpa only [Finset.card_map] using hcard⟩
  have hzn : z ≠ 0 := by
    intro hz
    apply hn
    funext s
    have he := congrFun hz (s.map e.toEmbedding)
    simpa only [z, finiteSimplicialPushChain_map, Pi.zero_apply] using he
  have hz₀ : finiteSimplicialBoundary z = 0 := by
    rw [z, finiteSimplicialBoundary_pushChain, h₀]
    exact finiteSimplicialPushChain_zero e
  obtain ⟨b, hb, hboundary⟩ := hlink T q hd z hzChain hz₀
  have hb₀ : b = 0 := by
    funext t
    by_contra ht
    obtain ⟨⟨hmem, hsub⟩, hcard⟩ := hb t ht
    obtain ⟨s, rfl⟩ := finiteSimplicial_exists_map_eq_of_subset e t hsub
    have hs := orderedBlockJoinFace_card_le ((hface s).mp hmem)
    rw [Finset.card_map] at hcard
    exact (not_le_of_gt (Nat.lt_succ_self q)) (hcard ▸ hs)
  rw [hb₀] at hboundary
  have hzero : finiteSimplicialBoundary (0 : Finset (BlockObservationVertex m ι) → ℤ) = 0 := by
    funext s
    simp [finiteSimplicialBoundary]
  exact hzn (hboundary.symm.trans hzero)

end

end MOC
