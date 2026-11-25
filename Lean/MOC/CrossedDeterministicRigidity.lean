import MOC.CrossedMinorBridge
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card

/-! Deterministic degree assignments surviving crossed transport are locally
rigid. The crossed transport uses Lyons's shadow method, DOI:
10.1007/s10240-003-0016-0. The combinatorial rigidity proved here is independent
of the unitary and of any numerical subset profile. -/

open Finset BigOperators

namespace MOC.CrossedDeterministic

variable {α : Type*} [DecidableEq α] {k : ℕ}

abbrev Layer (α : Type*) (k : ℕ) := {S : Finset α // S.card = k}

def replaceAt (S : Layer α k) (r : S.val) (j : α) (hj : j ∉ S.val) : Layer α k :=
  ⟨insert j (S.val.erase r), by
    rw [card_insert_of_not_mem (fun he => hj (mem_of_mem_erase he)),
      card_erase_of_mem r.property, S.property]
    have hp : 0 < #(S.val) := card_pos.mpr ⟨r.val, r.property⟩
    omega⟩

/-- Local condition forced by independently marked crossed transport:
every chosen removed row and incoming column can be paired along one
transport edge of the deterministic table. -/
def CrossedLocal (F : Layer α k → Layer α k) : Prop :=
  ∀ S (j : α) (hj : j ∉ S.val) (i : (F S).val),
    ∃ r : S.val, (F S).val \ (F (replaceAt S r j hj)).val = {i.val}

/-- For fixed source and incoming column the removed column and removed
row are in bijection. In particular every possible neighbouring column
set is sent to a set that differs by one row, with a distinct removal. -/
theorem exists_crossed_removal_bijection (F : Layer α k → Layer α k) (h : CrossedLocal F)
    (S : Layer α k) (j : α) (hj : j ∉ S.val) :
    ∃ e : (F S).val ≃ S.val, ∀ i : (F S).val,
      (F S).val \ (F (replaceAt S (e i) j hj)).val = {i.val} := by
  classical
  choose r hr using h S j hj
  have hinj : Function.Injective r := by
    intro i l he
    have hs := (hr i).symm.trans (he ▸ hr l)
    exact Subtype.ext (by simpa only [singleton_inj] using hs)
  have hcard : Fintype.card ((F S).val : Finset α) = Fintype.card (S.val : Finset α) := by
    simp only [Fintype.card_coe, (F S).property, S.property]
  have hsurj : Function.Surjective r := (Fintype.bijective_iff_injective_and_card _).mpr ⟨hinj, hcard⟩ |>.surjective
  exact ⟨Equiv.ofBijective r ⟨hinj, hsurj⟩, hr⟩

/-- A deterministic crossed assignment preserves adjacency on the graph
of k-element subsets, in the forward direction. -/
theorem crossed_removal_is_singleton (F : Layer α k → Layer α k) (h : CrossedLocal F)
    (S : Layer α k) (j : α) (hj : j ∉ S.val) (r : S.val) :
    ∃ i : (F S).val, (F S).val \ (F (replaceAt S r j hj)).val = {i.val} := by
  obtain ⟨e, he⟩ := exists_crossed_removal_bijection F h S j hj
  exact ⟨e.symm r, by simpa only [Equiv.apply_symm_apply] using he (e.symm r)⟩

private theorem eq_insert_erase_of_diff_singleton {S T : Layer α k} {i : α}
    (hi : S.val \ T.val = {i}) :
    ∃ j ∉ S.val, T.val = insert j (S.val.erase i) := by
  have himem : i ∈ S.val \ T.val := by rw [hi]; simp
  have hic : i ∈ S.val := (mem_sdiff.mp himem).1
  have hn : i ∉ T.val := (mem_sdiff.mp himem).2
  have hsub : S.val.erase i ⊆ T.val := by
    intro x hx
    by_contra hxt
    have he := mem_sdiff.mpr ⟨mem_of_mem_erase hx, hxt⟩
    rw [hi, mem_singleton] at he
    exact (mem_erase.mp hx).1 he
  have hcard : #(S.val.erase i) < #T.val := by
    rw [card_erase_of_mem hic, S.property, T.property]
    have hp : 0 < k := S.property ▸ card_pos.mpr ⟨i, hic⟩
    omega
  have hstrict : S.val.erase i ⊂ T.val := Finset.ssubset_iff_subset_ne.mpr
    ⟨hsub, fun he => hcard.ne (congrArg Finset.card he)⟩
  obtain ⟨j, hjT, hjS⟩ := exists_of_ssubset hstrict
  have hnot : j ∉ S.val := by
    intro h
    by_cases hji : j = i
    · exact hn (hji ▸ hjT)
    · exact hjS (mem_erase.mpr ⟨hji, h⟩)
  exact ⟨j, hnot, (eq_of_subset_of_card_le (insert_subset hjT hsub) (by
    rw [card_insert_of_not_mem hjS, card_erase_of_mem hic, T.property, S.property]
    have hp : 0 < k := S.property ▸ card_pos.mpr ⟨i, hic⟩
    omega)).symm⟩

private theorem replace_diff_singleton (S : Layer α k) (r : S.val) (j : α) (hj : j ∉ S.val) :
    S.val \ (replaceAt S r j hj).val = {r.val} := by
  ext t
  simp only [replaceAt, mem_sdiff, mem_insert, mem_erase, mem_singleton]
  constructor
  · rintro ⟨ht, hn⟩
    by_contra htr
    exact hn (Or.inr ⟨htr, ht⟩)
  · intro he
    subst t
    exact ⟨r.property, fun h => h.elim (fun hr => hj (hr ▸ r.property)) (fun hp => hp.1 rfl)⟩

/-- Crossed transport sends a pair of adjacent column sets to adjacent
row sets. Equal-size subsets are adjacent if one removes one label. -/
theorem crossed_assignment_preserves_adjacency
    (F : Layer α k → Layer α k) (h : CrossedLocal F) (S T : Layer α k)
    (hadj : ∃ i : α, S.val \ T.val = {i}) :
    ∃ i : α, (F S).val \ (F T).val = {i} := by
  obtain ⟨i, hi⟩ := hadj
  obtain ⟨j, hj, ht⟩ := eq_insert_erase_of_diff_singleton hi
  have hiS : i ∈ S.val := (mem_sdiff.mp (show i ∈ S.val \ T.val by rw [hi]; simp)).1
  let r : S.val := ⟨i, hiS⟩
  have he : T = replaceAt S r j hj := Subtype.ext ht
  subst T
  obtain ⟨q, hq⟩ := crossed_removal_is_singleton F h S j hj r
  exact ⟨q, hq⟩

/-- A nonzero edge of a deterministic crossed table yields the local
removal condition. All marks are chosen independently. -/
theorem crossedLocal_of_transport [Fintype α]
    (F : Layer α k → Layer α k)
    (h : ∀ i j : α, ∃ μ : Layer α k → Layer α k → ℝ,
      (∀ S, i ∈ (F S).val → j ∉ S.val → ∑ T, μ S T = 1) ∧
      ∀ S T, μ S T ≠ 0 →
        i ∉ (F T).val ∧ j ∈ T.val ∧ (F S).val.erase i ⊆ (F T).val ∧
        T.val.erase j ⊆ S.val) : CrossedLocal F := by
  classical
  intro S j hj i
  obtain ⟨μ, hrow, hμ⟩ := h i.val j
  have hm := hrow S i.property hj
  obtain ⟨T, hT⟩ : ∃ T, μ S T ≠ 0 := by
    by_contra! hn
    simp [hn] at hm
  obtain ⟨hiT, hjT, hr, hc⟩ := hμ S T hT
  have hcard : #(T.val.erase j) < #S.val := by
    rw [card_erase_of_mem hjT, T.property, S.property]
    have hp : 0 < k := T.property ▸ card_pos.mpr ⟨j, hjT⟩
    omega
  have hstrict : T.val.erase j ⊂ S.val := Finset.ssubset_iff_subset_ne.mpr
    ⟨hc, fun he => hcard.ne (congrArg Finset.card he)⟩
  obtain ⟨r, hrS, hrT⟩ := exists_of_ssubset hstrict
  have hsub : T.val.erase j ⊆ S.val.erase r := by
    intro x hx
    exact mem_erase.mpr ⟨fun he => hrT (he ▸ hx), hc hx⟩
  have hsame : T.val.erase j = S.val.erase r := eq_of_subset_of_card_le hsub (by
    rw [card_erase_of_mem hrS, card_erase_of_mem hjT, S.property, T.property])
  have hT' : T = replaceAt S ⟨r, hrS⟩ j hj := Subtype.ext (by
    change T.val = insert j (S.val.erase r)
    rw [← hsame, insert_erase hjT])
  refine ⟨⟨r, hrS⟩, ?_⟩
  rw [← hT']
  ext x
  rw [mem_sdiff, mem_singleton]
  constructor
  · rintro ⟨hx, hn⟩
    by_contra hne
    exact hn (hr (mem_erase.mpr ⟨hne, hx⟩))
  · intro he
    exact ⟨he.symm ▸ i.property, fun hxt => hiT (he ▸ hxt)⟩

/-- Even at the middle layer, composing an ordinary assignment with
complement cannot satisfy the independently marked crossed condition.
An incoming column would demand the same removed row for every edge. -/
theorem not_crossedLocal_complement_twist [Fintype α]
    (F : Layer α k → Layer α k) (e : Equiv.Perm α)
    (hF : ∀ S, (F S).val = (S.val.map e.toEmbedding)ᶜ)
    (S : Layer α k) (hk : 2 ≤ k) (j : α) (hj : j ∉ S.val) :
    ¬ CrossedLocal F := by
  intro h
  have hjF : e j ∈ (F S).val := by
    rw [hF]
    simpa only [mem_compl, mem_map_equiv, Equiv.symm_apply_apply] using hj
  let J : Finset α := (F S).val.erase (e j)
  have hJ : J.Nonempty := by
    apply card_pos.mp
    dsimp only [J]
    rw [card_erase_of_mem hjF, (F S).property]
    omega
  obtain ⟨i, hi⟩ := hJ
  have hiF : i ∈ (F S).val := mem_of_mem_erase hi
  have hiJ : i ≠ e j := (mem_erase.mp hi).1
  obtain ⟨r, hr⟩ := h S j hj ⟨i, hiF⟩
  have hdiff : (F S).val \ (F (replaceAt S r j hj)).val = {e j} := by
    rw [hF, hF]
    ext t
    let a := e.symm t
    have he : t = e a := (e.apply_symm_apply t).symm
    rw [he]
    simp only [mem_sdiff, mem_compl, not_not, mem_map_equiv, Equiv.symm_apply_apply,
      mem_singleton, e.injective.eq_iff, replaceAt, mem_insert, mem_erase]
    constructor
    · rintro ⟨hnot, h | h⟩
      · exact h
      · exact (hnot h.2).elim
    · intro h
      rw [h]
      exact ⟨hj, Or.inl rfl⟩
  exact hiJ (by simpa only [singleton_inj] using hr.symm.trans hdiff)


end MOC.CrossedDeterministic
