import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-! The top simplicial cycle of the join of boundaries of simplices of
dimension twelve. Chains are graded by vertex count, with the empty
face in reduced degree minus one. -/

open Finset BigOperators

namespace MOC

/-- A tuple of candidate faces, with the vertices in each block listed
separately. -/
abbrev BlockJoinTuple (k : ℕ) := Fin k → Finset (Fin 13)

/-- Every block of a face of the join omits at least one vertex. -/
def IsBlockJoinFace {k : ℕ} (s : BlockJoinTuple k) : Prop :=
  ∀ i, s i ≠ univ

/-- The finite set of labelled vertices of a face tuple. -/
def blockJoinVertices {k : ℕ} (s : BlockJoinTuple k) : Finset (Fin k × Fin 13) :=
  (univ.sigma s).map (Equiv.sigmaEquivProd (Fin k) (Fin 13)).toEmbedding

@[simp] theorem mem_blockJoinVertices {k : ℕ} (s : BlockJoinTuple k)
    (i : Fin k) (a : Fin 13) : (i, a) ∈ blockJoinVertices s ↔ a ∈ s i := by
  rw [blockJoinVertices, Finset.mem_map_equiv]
  change (⟨i, a⟩ : Σ _ : Fin k, Fin 13) ∈ univ.sigma s ↔ a ∈ s i
  simp [Finset.mem_sigma]

/-- The tuple of block restrictions of a vertex set. -/
def blockJoinTuple {k : ℕ} (V : Finset (Fin k × Fin 13)) : BlockJoinTuple k :=
  fun i => univ.filter (fun a => (i, a) ∈ V)

@[simp] theorem blockJoinTuple_vertices {k : ℕ} (s : BlockJoinTuple k) :
    blockJoinTuple (blockJoinVertices s) = s := by
  funext i
  ext a
  simp [blockJoinTuple]

@[simp] theorem blockJoinVertices_tuple {k : ℕ} (V : Finset (Fin k × Fin 13)) :
    blockJoinVertices (blockJoinTuple V) = V := by
  ext v
  rcases v with ⟨i, a⟩
  simp [blockJoinTuple]

/-- The face set of the join of the boundaries of the labelled simplices. -/
def blockJoinFaces (k : ℕ) : Set (Finset (Fin k × Fin 13)) :=
  {V | IsBlockJoinFace (blockJoinTuple V)}

@[simp] theorem blockJoinVertices_mem_faces {k : ℕ} (s : BlockJoinTuple k) :
    blockJoinVertices s ∈ blockJoinFaces k ↔ ∀ i, s i ≠ univ := by
  change IsBlockJoinFace (blockJoinTuple (blockJoinVertices s)) ↔ _
  rw [blockJoinTuple_vertices] <;> rfl

theorem empty_mem_blockJoinFaces (k : ℕ) : ∅ ∈ blockJoinFaces k := by
  intro i h
  have he : (0 : Fin 13) ∈ blockJoinTuple (∅ : Finset (Fin k × Fin 13)) i := by
    rw [h]
    exact mem_univ _
  simp [blockJoinTuple] at he

theorem blockJoinFaces_subset_closed {k : ℕ} {S T : Finset (Fin k × Fin 13)}
    (hS : S ∈ blockJoinFaces k) (hTS : T ⊆ S) : T ∈ blockJoinFaces k := by
  intro i hi
  apply hS i
  apply eq_univ_of_forall
  intro a
  have hma : a ∈ blockJoinTuple T i := by
    rw [hi]
    exact mem_univ _
  have haT : (i, a) ∈ T := (mem_filter.mp hma).2
  exact mem_filter.mpr ⟨mem_univ _, hTS haT⟩

/-- The number of vertices of a face in the join. -/
def blockJoinCard {k : ℕ} (s : BlockJoinTuple k) : ℕ :=
  ∑ i, (s i).card

@[simp] theorem card_blockJoinVertices {k : ℕ} (s : BlockJoinTuple k) :
    (blockJoinVertices s).card = blockJoinCard s := by
  rw [blockJoinVertices, card_map, card_sigma, blockJoinCard]

theorem blockJoinCard_le {k : ℕ} {s : BlockJoinTuple k} (hs : IsBlockJoinFace s) :
    blockJoinCard s ≤ 12 * k := by
  unfold blockJoinCard
  calc
    _ ≤ ∑ _ : Fin k, 12 := by
      apply Finset.sum_le_sum
      intro i _
      have hlt := Finset.card_lt_card (Finset.ssubset_univ_iff.mpr (hs i))
      have h : (s i).card < 13 := by simpa only [card_univ, Fintype.card_fin] using hlt
      omega
    _ = _ := by simp [Nat.mul_comm]

section Coefficients

variable {R : Type*} [CommRing R]

/-- A chain assigns coefficients only to faces of one vertex count.
This is the augmented simplicial grading. -/
def IsBlockJoinChain {k : ℕ} (q : ℕ) (c : BlockJoinTuple k → R) : Prop :=
  ∀ s, c s ≠ 0 → IsBlockJoinFace s ∧ blockJoinCard s = q

private def omittedVertices (s : Finset (Fin 13)) : Finset (Fin 13) :=
  univ \ s

private def oneBlockCoefficient (s : Finset (Fin 13)) : R :=
  ∑ a : Fin 13, if omittedVertices s = {a} then (-1 : R) ^ a.val else 0

private theorem oneBlockCoefficient_singleton {s : Finset (Fin 13)} {a : Fin 13}
    (h : omittedVertices s = {a}) : (oneBlockCoefficient s : R) = (-1 : R) ^ a.val := by
  rw [oneBlockCoefficient, h]
  simp only [Finset.singleton_inj, Finset.sum_ite_eq, mem_univ, if_true]

private theorem oneBlockCoefficient_zero {s : Finset (Fin 13)}
    (h : (omittedVertices s).card ≠ 1) : (oneBlockCoefficient s : R) = 0 := by
  unfold oneBlockCoefficient
  apply Finset.sum_eq_zero
  intro a _
  have hn : omittedVertices s ≠ {a} := by
    intro he
    exact h (by rw [he, card_singleton])
  rw [if_neg hn]

private def oneBlockRank (s : Finset (Fin 13)) (a : Fin 13) : ℕ :=
  (s.filter (fun b => b < a)).card

private theorem oneBlockRank_pair (s : Finset (Fin 13)) (a b : Fin 13)
    (hab : a < b) (h : omittedVertices s = {a, b}) :
    oneBlockRank s a = a.val ∧ oneBlockRank s b + 1 = b.val := by
  have hmem (c : Fin 13) : c ∈ s ↔ c ≠ a ∧ c ≠ b := by
    have hc : c ∉ s ↔ c ∈ ({a, b} : Finset (Fin 13)) := by
      rw [← h]
      simp [omittedVertices]
    simpa only [not_not, mem_insert, mem_singleton, not_or] using not_congr hc
  have ha : s.filter (fun c => c < a) = Finset.Iio a := by
    ext c
    simp only [mem_filter, Finset.mem_Iio, hmem]
    exact ⟨fun hc => hc.2, fun hca => ⟨⟨hca.ne, (hca.trans hab).ne⟩, hca⟩⟩
  have hb : s.filter (fun c => c < b) = (Finset.Iio b).erase a := by
    ext c
    simp only [mem_filter, mem_erase, Finset.mem_Iio, hmem]
    exact ⟨fun hc => ⟨hc.1.1, hc.2⟩, fun hc => ⟨⟨hc.1, hc.2.ne⟩, hc.2⟩⟩
  constructor
  · rw [oneBlockRank, ha, Fin.card_Iio]
  · rw [oneBlockRank, hb, card_erase_add_one (Finset.mem_Iio.mpr hab), Fin.card_Iio]

private theorem oneBlockBoundary_pair (s : Finset (Fin 13)) (a b : Fin 13)
    (hab : a < b) (h : omittedVertices s = {a, b}) :
    (∑ c ∈ omittedVertices s,
      (-1 : R) ^ oneBlockRank s c * oneBlockCoefficient (insert c s)) = 0 := by
  have ha : omittedVertices (insert a s) = {b} := by
    change univ \ insert a s = _
    rw [Finset.sdiff_insert]
    change (omittedVertices s).erase a = _
    rw [h]
    simp [hab.ne]
  have hb : omittedVertices (insert b s) = {a} := by
    change univ \ insert b s = _
    rw [Finset.sdiff_insert]
    change (omittedVertices s).erase b = _
    rw [h, Finset.pair_comm]
    simp [hab.ne.symm]
  obtain ⟨hRa, hRb⟩ := oneBlockRank_pair s a b hab h
  rw [h, sum_insert (by simp [hab.ne]), sum_singleton,
    oneBlockCoefficient_singleton ha, oneBlockCoefficient_singleton hb,
    hRa, ← hRb, pow_succ]
  ring

private theorem oneBlockBoundary_zero (s : Finset (Fin 13)) :
    (∑ a ∈ omittedVertices s,
      (-1 : R) ^ oneBlockRank s a * oneBlockCoefficient (insert a s)) = 0 := by
  by_cases hs : (omittedVertices s).card = 2
  · obtain ⟨a, b, hab, h⟩ := card_eq_two.mp hs
    rcases lt_or_gt_of_ne hab with hlt | hgt
    · exact oneBlockBoundary_pair s a b hlt h
    · exact oneBlockBoundary_pair s b a hgt (h.trans (Finset.pair_comm a b))
  · apply Finset.sum_eq_zero
    intro a ha
    have he : omittedVertices (insert a s) = (omittedVertices s).erase a :=
      Finset.sdiff_insert _ _ _
    have hz : (omittedVertices (insert a s)).card ≠ 1 := by
      rw [he, card_erase_of_mem ha]
      omega
    rw [oneBlockCoefficient_zero hz, mul_zero]

private def blockJoinPrefix {k : ℕ} (s : BlockJoinTuple k) (i : Fin k) : ℕ :=
  ∑ j ∈ Finset.Iio i, (s j).card

/-- The coefficient of the simplicial boundary at each face tuple.
Vertices are ordered first by block and then within their block. -/
def blockJoinBoundary {k : ℕ} (c : BlockJoinTuple k → R) (s : BlockJoinTuple k) : R :=
  ∑ i, (-1 : R) ^ blockJoinPrefix s i *
    ∑ a ∈ omittedVertices (s i),
      (-1 : R) ^ oneBlockRank (s i) a * c (Function.update s i (insert a (s i)))

/-- The signed product of the single-block simplex boundaries. -/
def blockJoinTopCycle {k : ℕ} (s : BlockJoinTuple k) : R :=
  ∏ i, oneBlockCoefficient (s i)

private theorem blockJoinTopCycle_update {k : ℕ}
    (s : BlockJoinTuple k) (i : Fin k) (t : Finset (Fin 13)) :
    (blockJoinTopCycle (Function.update s i t) : R) =
      oneBlockCoefficient t * ∏ j ∈ univ.erase i, oneBlockCoefficient (s j) := by
  unfold blockJoinTopCycle
  rw [← mul_prod_erase univ _ (mem_univ i), Function.update_self]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  rw [Function.update_of_ne (ne_of_mem_erase hj)]

theorem blockJoinTopCycle_boundary_zero (k : ℕ) :
    blockJoinBoundary (blockJoinTopCycle : BlockJoinTuple k → R) = 0 := by
  funext s
  change blockJoinBoundary (blockJoinTopCycle : BlockJoinTuple k → R) s = 0
  unfold blockJoinBoundary
  apply Finset.sum_eq_zero
  intro i _
  have he :
      (∑ a ∈ omittedVertices (s i), (-1 : R) ^ oneBlockRank (s i) a *
        blockJoinTopCycle (Function.update s i (insert a (s i)))) =
      (∑ a ∈ omittedVertices (s i), (-1 : R) ^ oneBlockRank (s i) a *
        oneBlockCoefficient (insert a (s i))) *
        ∏ j ∈ univ.erase i, oneBlockCoefficient (s j) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a _
    rw [blockJoinTopCycle_update, mul_assoc]
  rw [he, oneBlockBoundary_zero, zero_mul, mul_zero]

theorem blockJoinTopCycle_isChain (k : ℕ) :
    IsBlockJoinChain (12 * k) (blockJoinTopCycle : BlockJoinTuple k → R) := by
  intro s hs
  have hc (i : Fin k) : (omittedVertices (s i)).card = 1 := by
    by_contra h
    apply hs
    exact Finset.prod_eq_zero (mem_univ i) (oneBlockCoefficient_zero h)
  have hface (i : Fin k) : s i ≠ univ := by
    intro hi
    have he := hc i
    simp [omittedVertices, hi] at he
  have hcard (i : Fin k) : (s i).card = 12 := by
    have hi := card_sdiff_add_card_eq_card (subset_univ (s i))
    change (omittedVertices (s i)).card + (s i).card =
      (Finset.univ : Finset (Fin 13)).card at hi
    rw [hc i, card_univ, Fintype.card_fin] at hi
    omega
  exact ⟨hface, by simp [blockJoinCard, hcard, Nat.mul_comm]⟩

theorem blockJoinTopCycle_ne_zero (k : ℕ) [Nontrivial R] :
    (blockJoinTopCycle : BlockJoinTuple k → R) ≠ 0 := by
  intro h
  let s : BlockJoinTuple k := fun _ => univ.erase 0
  have he : (blockJoinTopCycle s : R) = 1 := by
    unfold blockJoinTopCycle
    have hc (i : Fin k) : (oneBlockCoefficient (s i) : R) = 1 := by
      have hm : omittedVertices (s i) = ({0} : Finset (Fin 13)) :=
        Finset.sdiff_erase_self (mem_univ (0 : Fin 13))
      rw [oneBlockCoefficient_singleton hm, Fin.val_zero, pow_zero]
    simp only [hc, prod_const_one]
  have hz : (blockJoinTopCycle s : R) = 0 := congrFun h s
  exact zero_ne_one (hz.symm.trans he)

/-- The join has no chains above vertex count twelve times the number
of blocks. -/
theorem blockJoinChain_zero_of_card_lt {k q : ℕ} {c : BlockJoinTuple k → R}
    (hq : 12 * k < q) (hc : IsBlockJoinChain q c) : c = 0 := by
  funext s
  change c s = 0
  by_contra hs
  obtain ⟨hface, hcard⟩ := hc s hs
  have hle := blockJoinCard_le hface
  rw [hcard] at hle
  exact (not_lt_of_ge hle) hq

/-- At vertex count twelve times the number of blocks, the join has a
nonzero cycle and no nonzero incoming boundaries. The coefficient ring
may be the integers or the rationals. -/
theorem blockJoin_top_cycle_witness (k : ℕ) [Nontrivial R] :
    ∃ c : BlockJoinTuple k → R, IsBlockJoinChain (12 * k) c ∧ c ≠ 0 ∧
      blockJoinBoundary c = 0 ∧
      ∀ d, IsBlockJoinChain (12 * k + 1) d → blockJoinBoundary d ≠ c := by
  refine ⟨blockJoinTopCycle, blockJoinTopCycle_isChain k, blockJoinTopCycle_ne_zero k,
    blockJoinTopCycle_boundary_zero k, ?_⟩
  intro d hd he
  have hz : d = 0 := blockJoinChain_zero_of_card_lt (Nat.lt_succ_self _) hd
  rw [hz] at he
  have hb : (blockJoinBoundary (0 : BlockJoinTuple k → R)) = 0 := by
    funext s
    simp [blockJoinBoundary]
  rw [hb] at he
  exact blockJoinTopCycle_ne_zero (R := R) k he.symm

end Coefficients

end MOC
