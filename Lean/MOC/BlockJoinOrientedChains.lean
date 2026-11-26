import MOC.FiniteSimplicialCone
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Sigma.Order
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-! The top oriented cycle in a join of simplex boundaries of unequal sizes.
The grading counts vertices, so the empty face has augmented degree minus one. -/

open Finset BigOperators

namespace MOC

variable {B : Type*} [Fintype B] [LinearOrder B]

/-- The vertices of the join, ordered first by block and then within the block. -/
abbrev OrderedBlockJoinVertex (m : B → ℕ) := Lex (Σ j, Fin (m j + 1))

/-- The vertices of a set that belong to a fixed block. -/
def orderedBlockJoinBlock (m : B → ℕ) (s : Finset (OrderedBlockJoinVertex m)) (j : B) :
    Finset (Fin (m j + 1)) :=
  univ.filter (fun a => (⟨j, a⟩ : OrderedBlockJoinVertex m) ∈ s)

/-- The vertex set assembled from one set in each block. -/
def orderedBlockJoinVertices (m : B → ℕ) (t : ∀ j, Finset (Fin (m j + 1))) :
    Finset (OrderedBlockJoinVertex m) :=
  (univ : Finset B).sigma t

@[simp]
theorem mem_orderedBlockJoinVertices (m : B → ℕ) (t : ∀ j, Finset (Fin (m j + 1)))
    (j : B) (a : Fin (m j + 1)) :
    (⟨j, a⟩ : OrderedBlockJoinVertex m) ∈ orderedBlockJoinVertices m t ↔ a ∈ t j := by
  simp only [orderedBlockJoinVertices, Finset.mem_sigma, mem_univ, true_and]

@[simp]
theorem orderedBlockJoinBlock_vertices (m : B → ℕ) (t : ∀ j, Finset (Fin (m j + 1)))
    (j : B) : orderedBlockJoinBlock m (orderedBlockJoinVertices m t) j = t j := by
  ext a
  simp only [orderedBlockJoinBlock, mem_filter, mem_univ, true_and, mem_orderedBlockJoinVertices]

@[simp]
theorem orderedBlockJoinVertices_blocks (m : B → ℕ) (s : Finset (OrderedBlockJoinVertex m)) :
    orderedBlockJoinVertices m (orderedBlockJoinBlock m s) = s := by
  ext v
  rcases v with ⟨j, a⟩
  simp only [mem_orderedBlockJoinVertices, orderedBlockJoinBlock, mem_filter, mem_univ, true_and]

/-- A face omits a vertex of each block. -/
def orderedBlockJoinFaces (m : B → ℕ) : Set (Finset (OrderedBlockJoinVertex m)) :=
  {s | ∀ j, orderedBlockJoinBlock m s j ≠ univ}

@[simp]
theorem orderedBlockJoinVertices_mem_faces (m : B → ℕ) (t : ∀ j, Finset (Fin (m j + 1))) :
    orderedBlockJoinVertices m t ∈ orderedBlockJoinFaces m ↔ ∀ j, t j ≠ univ := by
  change (∀ j, orderedBlockJoinBlock m (orderedBlockJoinVertices m t) j ≠ univ) ↔ _
  simp only [orderedBlockJoinBlock_vertices]

theorem orderedBlockJoinFaces_subset_closed {m : B → ℕ} {s t : Finset (OrderedBlockJoinVertex m)}
    (hs : s ∈ orderedBlockJoinFaces m) (ht : t ⊆ s) : t ∈ orderedBlockJoinFaces m := by
  intro j hj
  apply hs j
  apply Finset.eq_univ_of_forall
  intro a
  have ha : a ∈ orderedBlockJoinBlock m t j := by
    rw [hj]
    exact mem_univ a
  exact Finset.mem_filter.mpr ⟨mem_univ _, ht (Finset.mem_filter.mp ha).2⟩

theorem orderedBlockJoin_card (m : B → ℕ) (s : Finset (OrderedBlockJoinVertex m)) :
    s.card = ∑ j, (orderedBlockJoinBlock m s j).card := by
  calc
    s.card = (orderedBlockJoinVertices m (orderedBlockJoinBlock m s)).card := by
      rw [orderedBlockJoinVertices_blocks]
    _ = _ := Finset.card_sigma _ _

theorem orderedBlockJoinFace_card_le {m : B → ℕ} {s : Finset (OrderedBlockJoinVertex m)}
    (hs : s ∈ orderedBlockJoinFaces m) : s.card ≤ ∑ j, m j := by
  rw [orderedBlockJoin_card]
  apply Finset.sum_le_sum
  intro j _
  have hlt := Finset.card_lt_card (Finset.ssubset_univ_iff.mpr (hs j))
  have h : (orderedBlockJoinBlock m s j).card < m j + 1 := by
    simpa only [Finset.card_univ, Fintype.card_fin] using hlt
  omega

/-- A chain of grade `q` has coefficients only on faces with `q` vertices. -/
def IsOrderedBlockJoinChain (m : B → ℕ) (q : ℕ)
    (c : Finset (OrderedBlockJoinVertex m) → ℤ) : Prop :=
  ∀ s, c s ≠ 0 → s ∈ orderedBlockJoinFaces m ∧ s.card = q

private def omittedSimplexVertices {n : ℕ} (s : Finset (Fin (n + 1))) : Finset (Fin (n + 1)) :=
  univ \ s

private def orderedSimplexBoundaryCoefficient {n : ℕ} (s : Finset (Fin (n + 1))) : ℤ :=
  ∑ a : Fin (n + 1), if omittedSimplexVertices s = {a} then (-1 : ℤ) ^ a.val else 0

private theorem orderedSimplexBoundaryCoefficient_singleton {n : ℕ} {s : Finset (Fin (n + 1))}
    {a : Fin (n + 1)} (h : omittedSimplexVertices s = {a}) :
    orderedSimplexBoundaryCoefficient s = (-1 : ℤ) ^ a.val := by
  rw [orderedSimplexBoundaryCoefficient, h]
  simp only [Finset.singleton_inj, Finset.sum_ite_eq, mem_univ, if_true]

private theorem orderedSimplexBoundaryCoefficient_zero {n : ℕ} {s : Finset (Fin (n + 1))}
    (h : (omittedSimplexVertices s).card ≠ 1) : orderedSimplexBoundaryCoefficient s = 0 := by
  unfold orderedSimplexBoundaryCoefficient
  apply Finset.sum_eq_zero
  intro a _
  have hn : omittedSimplexVertices s ≠ {a} := by
    intro he
    exact h (by rw [he, card_singleton])
  rw [if_neg hn]

private def orderedSimplexRank {n : ℕ} (s : Finset (Fin (n + 1))) (a : Fin (n + 1)) : ℕ :=
  (s.filter (· < a)).card

private theorem orderedSimplexRank_pair {n : ℕ} (s : Finset (Fin (n + 1))) (a b : Fin (n + 1))
    (hab : a < b) (h : omittedSimplexVertices s = {a, b}) :
    orderedSimplexRank s a = a.val ∧ orderedSimplexRank s b + 1 = b.val := by
  have hmem (c : Fin (n + 1)) : c ∈ s ↔ c ≠ a ∧ c ≠ b := by
    have hc : c ∉ s ↔ c ∈ ({a, b} : Finset (Fin (n + 1))) := by
      rw [← h]
      simp [omittedSimplexVertices]
    simpa only [not_not, mem_insert, mem_singleton, not_or] using not_congr hc
  have ha : s.filter (· < a) = Finset.Iio a := by
    ext c
    simp only [mem_filter, Finset.mem_Iio, hmem]
    exact ⟨fun hc => hc.2, fun hca => ⟨⟨hca.ne, (hca.trans hab).ne⟩, hca⟩⟩
  have hb : s.filter (· < b) = (Finset.Iio b).erase a := by
    ext c
    simp only [mem_filter, mem_erase, Finset.mem_Iio, hmem]
    exact ⟨fun hc => ⟨hc.1.1, hc.2⟩, fun hc => ⟨⟨hc.1, hc.2.ne⟩, hc.2⟩⟩
  constructor
  · rw [orderedSimplexRank, ha, Fin.card_Iio]
  · rw [orderedSimplexRank, hb, card_erase_add_one (Finset.mem_Iio.mpr hab), Fin.card_Iio]

private theorem orderedSimplexBoundary_pair {n : ℕ} (s : Finset (Fin (n + 1))) (a b : Fin (n + 1))
    (hab : a < b) (h : omittedSimplexVertices s = {a, b}) :
    (∑ c ∈ omittedSimplexVertices s,
      (-1 : ℤ) ^ orderedSimplexRank s c * orderedSimplexBoundaryCoefficient (insert c s)) = 0 := by
  have ha : omittedSimplexVertices (insert a s) = {b} := by
    change univ \ insert a s = _
    rw [Finset.sdiff_insert]
    change (omittedSimplexVertices s).erase a = _
    rw [h]
    simp [hab.ne]
  have hb : omittedSimplexVertices (insert b s) = {a} := by
    change univ \ insert b s = _
    rw [Finset.sdiff_insert]
    change (omittedSimplexVertices s).erase b = _
    rw [h, Finset.pair_comm]
    simp [hab.ne.symm]
  obtain ⟨hRa, hRb⟩ := orderedSimplexRank_pair s a b hab h
  rw [h, sum_insert (by simp [hab.ne]), sum_singleton,
    orderedSimplexBoundaryCoefficient_singleton ha, orderedSimplexBoundaryCoefficient_singleton hb,
    hRa, ← hRb, pow_succ]
  ring

private theorem orderedSimplexBoundary_zero {n : ℕ} (s : Finset (Fin (n + 1))) :
    (∑ a ∈ omittedSimplexVertices s,
      (-1 : ℤ) ^ orderedSimplexRank s a * orderedSimplexBoundaryCoefficient (insert a s)) = 0 := by
  by_cases hs : (omittedSimplexVertices s).card = 2
  · obtain ⟨a, b, hab, h⟩ := card_eq_two.mp hs
    rcases lt_or_gt_of_ne hab with hlt | hgt
    · exact orderedSimplexBoundary_pair s a b hlt h
    · exact orderedSimplexBoundary_pair s b a hgt (h.trans (Finset.pair_comm a b))
  · apply Finset.sum_eq_zero
    intro a ha
    have he : omittedSimplexVertices (insert a s) = (omittedSimplexVertices s).erase a :=
      Finset.sdiff_insert _ _ _
    have hz : (omittedSimplexVertices (insert a s)).card ≠ 1 := by
      rw [he, card_erase_of_mem ha]
      omega
    rw [orderedSimplexBoundaryCoefficient_zero hz, mul_zero]

private theorem orderedBlockJoin_lt_same (m : B → ℕ) (j : B) (a b : Fin (m j + 1)) :
    (⟨j, a⟩ : OrderedBlockJoinVertex m) < ⟨j, b⟩ ↔ a < b := by
  rw [Sigma.Lex.lt_def]
  simp only [lt_irrefl, false_or]
  exact ⟨fun ⟨_, ha⟩ => ha, fun ha => ⟨rfl, ha⟩⟩

private theorem orderedBlockJoin_lt_other (m : B → ℕ) {l j : B} (hl : l ≠ j)
    (b : Fin (m l + 1)) (a : Fin (m j + 1)) :
    (⟨l, b⟩ : OrderedBlockJoinVertex m) < ⟨j, a⟩ ↔ l < j := by
  rw [Sigma.Lex.lt_def]
  exact ⟨fun h => h.elim id (fun ⟨he, _⟩ => (hl he).elim), Or.inl⟩

private def orderedBlockJoinPrefix (m : B → ℕ) (s : Finset (OrderedBlockJoinVertex m)) (j : B) : ℕ :=
  ∑ l ∈ univ.erase j, if l < j then (orderedBlockJoinBlock m s l).card else 0

private theorem orderedBlockJoin_rank (m : B → ℕ) (s : Finset (OrderedBlockJoinVertex m))
    (j : B) (a : Fin (m j + 1)) :
    (s.filter (· < (⟨j, a⟩ : OrderedBlockJoinVertex m))).card =
      orderedBlockJoinPrefix m s j + orderedSimplexRank (orderedBlockJoinBlock m s j) a := by
  let t := s.filter (· < (⟨j, a⟩ : OrderedBlockJoinVertex m))
  have hj : orderedBlockJoinBlock m t j = (orderedBlockJoinBlock m s j).filter (· < a) := by
    ext b
    simp only [t, orderedBlockJoinBlock, mem_filter, mem_univ, true_and, orderedBlockJoin_lt_same]
  have hl (l : B) (hne : l ≠ j) :
      orderedBlockJoinBlock m t l = if l < j then orderedBlockJoinBlock m s l else ∅ := by
    ext b
    simp only [t, orderedBlockJoinBlock, mem_filter, mem_univ, true_and, orderedBlockJoin_lt_other m hne]
    by_cases hlt : l < j
    · simp only [hlt, and_true, if_true, mem_filter, mem_univ, true_and]
    · simp only [hlt, and_false, if_false, not_mem_empty]
  change t.card = _
  rw [orderedBlockJoin_card, ← sum_erase_add _ _ (mem_univ j), hj, orderedSimplexRank]
  unfold orderedBlockJoinPrefix
  congr 1
  apply Finset.sum_congr rfl
  intro l hlj
  rw [hl l (ne_of_mem_erase hlj)]
  by_cases hlt : l < j <;> simp only [hlt, if_true, if_false, card_empty]

private theorem orderedBlockJoin_block_insert_same (m : B → ℕ)
    (s : Finset (OrderedBlockJoinVertex m)) (j : B) (a : Fin (m j + 1)) :
    orderedBlockJoinBlock m (insert ⟨j, a⟩ s) j = insert a (orderedBlockJoinBlock m s j) := by
  ext b
  have he : (⟨j, b⟩ : OrderedBlockJoinVertex m) = ⟨j, a⟩ ↔ b = a :=
    (Function.Embedding.sigmaMk j).injective.eq_iff
  simp only [orderedBlockJoinBlock, mem_filter, mem_univ, true_and, mem_insert, he]

private theorem orderedBlockJoin_block_insert_other (m : B → ℕ)
    (s : Finset (OrderedBlockJoinVertex m)) {l j : B} (hl : l ≠ j) (a : Fin (m j + 1)) :
    orderedBlockJoinBlock m (insert ⟨j, a⟩ s) l = orderedBlockJoinBlock m s l := by
  ext b
  have hn : (⟨l, b⟩ : OrderedBlockJoinVertex m) ≠ ⟨j, a⟩ :=
    fun h => hl (congrArg (fun v : OrderedBlockJoinVertex m => (ofLex v).1) h)
  simp only [orderedBlockJoinBlock, mem_filter, mem_univ, true_and, mem_insert, hn, false_or]

/-- The product of the signed top coefficients of the block boundaries. -/
def orderedBlockJoinTopCycle (m : B → ℕ) (s : Finset (OrderedBlockJoinVertex m)) : ℤ :=
  ∏ j, orderedSimplexBoundaryCoefficient (orderedBlockJoinBlock m s j)

private theorem orderedBlockJoinTopCycle_insert (m : B → ℕ)
    (s : Finset (OrderedBlockJoinVertex m)) (j : B) (a : Fin (m j + 1)) :
    orderedBlockJoinTopCycle m (insert ⟨j, a⟩ s) =
      orderedSimplexBoundaryCoefficient (insert a (orderedBlockJoinBlock m s j)) *
        ∏ l ∈ univ.erase j, orderedSimplexBoundaryCoefficient (orderedBlockJoinBlock m s l) := by
  unfold orderedBlockJoinTopCycle
  rw [← mul_prod_erase univ _ (mem_univ j), orderedBlockJoin_block_insert_same]
  congr 1
  apply Finset.prod_congr rfl
  intro l hl
  rw [orderedBlockJoin_block_insert_other m s (ne_of_mem_erase hl)]

theorem orderedBlockJoinTopCycle_boundary_zero (m : B → ℕ) :
    finiteSimplicialBoundary (orderedBlockJoinTopCycle m) = 0 := by
  funext s
  have hmiss : (univ : Finset (OrderedBlockJoinVertex m)) \ s =
      (univ : Finset B).sigma (fun j => omittedSimplexVertices (orderedBlockJoinBlock m s j)) := by
    ext v
    rcases v with ⟨j, a⟩
    simp only [mem_sdiff, mem_univ, true_and, mem_sigma, omittedSimplexVertices,
      orderedBlockJoinBlock, mem_filter]
  unfold finiteSimplicialBoundary
  change (∑ v ∈ univ \ s, (-1 : ℤ) ^ (s.filter (· < v)).card *
    orderedBlockJoinTopCycle m (insert v s)) = 0
  rw [hmiss, Finset.sum_sigma]
  apply Finset.sum_eq_zero
  intro j _
  have he :
      (∑ a ∈ omittedSimplexVertices (orderedBlockJoinBlock m s j),
        (-1 : ℤ) ^ (s.filter (· < (⟨j, a⟩ : OrderedBlockJoinVertex m))).card *
          orderedBlockJoinTopCycle m (insert ⟨j, a⟩ s)) =
      (-1 : ℤ) ^ orderedBlockJoinPrefix m s j *
        (∑ a ∈ omittedSimplexVertices (orderedBlockJoinBlock m s j),
          (-1 : ℤ) ^ orderedSimplexRank (orderedBlockJoinBlock m s j) a *
            orderedSimplexBoundaryCoefficient (insert a (orderedBlockJoinBlock m s j))) *
        ∏ l ∈ univ.erase j, orderedSimplexBoundaryCoefficient (orderedBlockJoinBlock m s l) := by
    rw [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a _
    rw [orderedBlockJoin_rank, pow_add, orderedBlockJoinTopCycle_insert]
    ring
  rw [he, orderedSimplexBoundary_zero, mul_zero, zero_mul]

theorem orderedBlockJoinTopCycle_isChain (m : B → ℕ) :
    IsOrderedBlockJoinChain m (∑ j, m j) (orderedBlockJoinTopCycle m) := by
  intro s hs
  have hc (j : B) : (omittedSimplexVertices (orderedBlockJoinBlock m s j)).card = 1 := by
    by_contra hj
    apply hs
    exact Finset.prod_eq_zero (mem_univ j) (orderedSimplexBoundaryCoefficient_zero hj)
  have hface : s ∈ orderedBlockJoinFaces m := by
    intro j hj
    have he := hc j
    simp [omittedSimplexVertices, hj] at he
  have hcard (j : B) : (orderedBlockJoinBlock m s j).card = m j := by
    have hh := card_sdiff_add_card_eq_card (subset_univ (orderedBlockJoinBlock m s j))
    change (omittedSimplexVertices (orderedBlockJoinBlock m s j)).card +
      (orderedBlockJoinBlock m s j).card = (univ : Finset (Fin (m j + 1))).card at hh
    rw [hc j, card_univ, Fintype.card_fin] at hh
    omega
  refine ⟨hface, ?_⟩
  simp only [orderedBlockJoin_card, hcard]

/-- The coefficient is one on the face that omits the first vertex of every block. -/
theorem orderedBlockJoinTopCycle_omit_zero (m : B → ℕ) :
    orderedBlockJoinTopCycle m (orderedBlockJoinVertices m
      (fun j => (univ : Finset (Fin (m j + 1))).erase 0)) = 1 := by
  unfold orderedBlockJoinTopCycle
  have hc (j : B) : orderedSimplexBoundaryCoefficient
      ((univ : Finset (Fin (m j + 1))).erase 0) = 1 := by
    have hm : omittedSimplexVertices ((univ : Finset (Fin (m j + 1))).erase 0) =
        ({0} : Finset (Fin (m j + 1))) := Finset.sdiff_erase_self (mem_univ _)
    rw [orderedSimplexBoundaryCoefficient_singleton hm, Fin.val_zero, pow_zero]
  simp only [orderedBlockJoinBlock_vertices, hc, prod_const_one]

theorem orderedBlockJoinTopCycle_ne_zero (m : B → ℕ) : orderedBlockJoinTopCycle m ≠ 0 := by
  intro h
  have he := orderedBlockJoinTopCycle_omit_zero m
  rw [h, Pi.zero_apply] at he
  exact zero_ne_one he

/-- There are no chains with more vertices than the top grade. -/
theorem orderedBlockJoinChain_zero_of_card_lt {m : B → ℕ} {q : ℕ}
    {c : Finset (OrderedBlockJoinVertex m) → ℤ} (hq : (∑ j, m j) < q)
    (hc : IsOrderedBlockJoinChain m q c) : c = 0 := by
  funext s
  change c s = 0
  by_contra hs
  obtain ⟨hface, hcard⟩ := hc s hs
  have hle := orderedBlockJoinFace_card_le hface
  rw [hcard] at hle
  exact (not_lt_of_ge hle) hq

/-- The join has a nonzero integral top cycle with no incoming boundary. -/
theorem orderedBlockJoin_top_cycle_witness (m : B → ℕ) :
    ∃ c : Finset (OrderedBlockJoinVertex m) → ℤ,
      IsOrderedBlockJoinChain m (∑ j, m j) c ∧ c ≠ 0 ∧ finiteSimplicialBoundary c = 0 ∧
      ∀ d, IsOrderedBlockJoinChain m ((∑ j, m j) + 1) d → finiteSimplicialBoundary d ≠ c := by
  refine ⟨orderedBlockJoinTopCycle m, orderedBlockJoinTopCycle_isChain m,
    orderedBlockJoinTopCycle_ne_zero m, orderedBlockJoinTopCycle_boundary_zero m, ?_⟩
  intro d hd he
  have hz : d = 0 := orderedBlockJoinChain_zero_of_card_lt (Nat.lt_succ_self _) hd
  rw [hz] at he
  have hb : finiteSimplicialBoundary (0 : Finset (OrderedBlockJoinVertex m) → ℤ) = 0 := by
    funext s
    simp [finiteSimplicialBoundary]
  rw [hb] at he
  exact orderedBlockJoinTopCycle_ne_zero m he.symm

end MOC
