import MOC.RankTwoOverlap
import Mathlib.Combinatorics.Hall.Basic

open Finset

namespace MOC

/-- Number of labels of one color. -/
def colorMultiplicity {I C : Type*} [Fintype I] [DecidableEq C]
    (a : I → C) (c : C) : ℕ := (Finset.univ.filter fun i => a i = c).card

private theorem colorMultiplicity_add_complement {I C : Type*}
    [Fintype I] [DecidableEq C] (a : I → C) (c : C) :
    colorMultiplicity a c + (Finset.univ.filter fun i => a i ≠ c).card =
      Fintype.card I := by
  classical
  unfold colorMultiplicity
  rw [← Finset.card_univ, ← Finset.card_union_of_disjoint
    (show Disjoint (Finset.univ.filter (fun i => a i = c))
      (Finset.univ.filter (fun i => a i ≠ c)) by
        refine Finset.disjoint_left.mpr ?_
        intro i hi hj
        exact (Finset.mem_filter.mp hj).2 (Finset.mem_filter.mp hi).2)]
  congr 1
  ext i
  simp [em]

/-- A perfect unequal-color matching exists precisely when no common color
uses more labels, counted on the two sides together, than one side contains.
This compresses Hall’s inequalities to one per color class.
Hall, “On Representatives of Subsets”, DOI 10.1112/jlms/s1-10.37.26. -/
theorem exists_unequal_color_equiv_iff
    {I J C : Type*} [Fintype I] [Fintype J] [DecidableEq C]
    (a : I → C) (b : J → C) (hcard : Fintype.card I = Fintype.card J) :
    (∃ e : I ≃ J, ∀ i, a i ≠ b (e i)) ↔
      ∀ c, colorMultiplicity a c + colorMultiplicity b c ≤ Fintype.card I := by
  classical
  let N (s : Finset I) : Finset J := Finset.univ.filter fun j => ∃ i ∈ s, a i ≠ b j
  let P (c : C) : Finset I := Finset.univ.filter fun i => a i = c
  let Q (c : C) : Finset J := Finset.univ.filter fun j => b j ≠ c
  have hall : (∀ s : Finset I, s.card ≤ (N s).card) ↔ ∃ e : I ≃ J, ∀ i, a i ≠ b (e i) := by
    rw [show (∀ s : Finset I, s.card ≤ (N s).card) ↔
      (∃ f : I → J, Function.Injective f ∧ ∀ i, a i ≠ b (f i)) from
        Fintype.all_card_le_filter_rel_iff_exists_injective (fun i j => a i ≠ b j)]
    constructor
    · rintro ⟨f, hf, h⟩
      exact ⟨Equiv.ofBijective f ((Fintype.bijective_iff_injective_and_card f).mpr ⟨hf, hcard⟩), h⟩
    · rintro ⟨e, he⟩
      exact ⟨e, e.injective, he⟩
  rw [← hall]
  have hone (s : Finset I) (c : C) (hne : s.Nonempty) (hs : ∀ i ∈ s, a i = c) :
      N s = Q c := by
    obtain ⟨i, hi⟩ := hne
    ext j
    constructor
    · intro hj
      obtain ⟨i', hi', h'⟩ := (Finset.mem_filter.mp hj).2
      exact Finset.mem_filter.mpr ⟨mem_univ _, fun h => h' ((hs _ hi').trans h.symm)⟩
    · intro hj
      exact Finset.mem_filter.mpr ⟨mem_univ _, i, hi, by
        rw [hs i hi]
        exact (Finset.mem_filter.mp hj).2.symm⟩
  constructor
  · intro h c
    have hq := colorMultiplicity_add_complement b c
    change colorMultiplicity b c + (Q c).card = _ at hq
    by_cases hn : (P c).Nonempty
    · have hc := h (P c)
      rw [hone _ c hn (fun i hi => (Finset.mem_filter.mp hi).2)] at hc
      change colorMultiplicity a c ≤ (Q c).card at hc
      omega
    · have hc : colorMultiplicity a c = 0 := by
        change (P c).card = 0
        exact Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp hn)
      omega
  · intro h s
    by_cases hne : s.Nonempty
    · obtain ⟨i, hi⟩ := hne
      by_cases hone' : ∀ j ∈ s, a j = a i
      · rw [hone s (a i) ⟨i, hi⟩ hone']
        have hc : s.card ≤ colorMultiplicity a (a i) :=
          Finset.card_le_card (fun j hj => Finset.mem_filter.mpr ⟨mem_univ _, hone' j hj⟩)
        have hq := colorMultiplicity_add_complement b (a i)
        change colorMultiplicity b (a i) + (Q (a i)).card = _ at hq
        have hb := h (a i)
        omega
      · push_neg at hone'
        obtain ⟨i', hi', hneq⟩ := hone'
        have huniv : N s = Finset.univ := by
          ext j
          simp only [N, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
          by_cases hc : a i = b j
          · exact ⟨i', hi', fun h' => hneq (h'.trans hc.symm)⟩
          · exact ⟨i, hi, hc⟩
        rw [huniv, Finset.card_univ, ← hcard]
        exact Finset.card_le_univ s
    · have hs := Finset.not_nonempty_iff_eq_empty.mp hne
      simp [hs]


/-- Exact support nonemptiness test for additive matching profiles. -/
theorem exists_nonzero_matching_iff_colorMultiplicity {I : Type*}
    [Fintype I] [DecidableEq I] (a b : I → ℂ) :
    (∃ e : Equiv.Perm I, matchingProduct a b e ≠ 0) ↔
      ∀ c, colorMultiplicity (fun j => -b j) c + colorMultiplicity a c ≤ Fintype.card I := by
  rw [← exists_unequal_color_equiv_iff (fun j => -b j) a rfl]
  simp only [matchingProduct, Finset.prod_ne_zero_iff, Finset.mem_univ, true_implies]
  constructor
  · rintro ⟨e, he⟩
    exact ⟨e, fun i h => he i (eq_neg_iff_add_eq_zero.mp h.symm)⟩
  · rintro ⟨e, he⟩
    exact ⟨e, fun i h => he i (eq_neg_iff_add_eq_zero.mpr h).symm⟩


private theorem colorMultiplicity_subtype_le {I C : Type*}
    [Fintype I] [DecidableEq C] (a : I → C) (p : I → Prop) [DecidablePred p] (c : C) :
    colorMultiplicity (fun i : Subtype p => a i) c ≤ colorMultiplicity a c := by
  unfold colorMultiplicity
  rw [← Fintype.card_subtype (fun i : Subtype p => a i = c),
    ← Fintype.card_subtype (fun i : I => a i = c)]
  exact Fintype.card_le_of_injective
    (fun x : {i : Subtype p // a i = c} => (⟨x.1.1, x.2⟩ : {i : I // a i = c}))
    (fun _ _ h => Subtype.ext (Subtype.ext (congrArg Subtype.val h)))

/-- Under one unit of slack in each Hall inequality, every allowed pair
extends to a perfect unequal-color matching. -/
theorem exists_unequal_color_perm_at_of_slack {I C : Type*}
    [Fintype I] [DecidableEq I] [DecidableEq C] (a b : I → C) (j i : I)
    (hij : a j ≠ b i)
    (hslack : ∀ c, colorMultiplicity a c + colorMultiplicity b c < Fintype.card I) :
    ∃ σ : Equiv.Perm I, σ j = i ∧ ∀ k, a k ≠ b (σ k) := by
  classical
  have hc (k : I) : Fintype.card {x : I // x ≠ k} = Fintype.card I - 1 := by
    rw [Fintype.card_subtype_compl (fun x : I => x = k), Fintype.card_subtype_eq]
  obtain ⟨e, he⟩ := (exists_unequal_color_equiv_iff
    (fun x : {k : I // k ≠ j} => a x) (fun x : {k : I // k ≠ i} => b x)
    ((hc j).trans (hc i).symm)).mpr (fun c => by
      have ha := colorMultiplicity_subtype_le a (fun k => k ≠ j) c
      have hb := colorMultiplicity_subtype_le b (fun k => k ≠ i) c
      have hs := hslack c
      rw [hc j]
      omega)
  let pivot : {k : I // k = j} ≃ {k : I // k = i} :=
    { toFun := fun _ => ⟨i, rfl⟩
      invFun := fun _ => ⟨j, rfl⟩
      left_inv := fun k => Subtype.ext k.property.symm
      right_inv := fun k => Subtype.ext k.property.symm }
  let σ := (Equiv.sumCompl (fun k : I => k = j)).symm.trans
    ((Equiv.sumCongr pivot e).trans (Equiv.sumCompl (fun k : I => k = i)))
  have hj : σ j = i := by
    simp only [σ, Equiv.trans_apply, Equiv.sumCompl_apply_symm_of_pos _ j rfl,
      Equiv.sumCongr_apply, Sum.map_inl, Equiv.sumCompl_apply_inl] <;> rfl
  refine ⟨σ, hj, fun k => ?_⟩
  by_cases hk : k = j
  · subst k
    simpa only [hj] using hij
  · simpa only [σ, Equiv.trans_apply, Equiv.sumCompl_apply_symm_of_neg _ k hk,
      Equiv.sumCongr_apply, Sum.map_inr, Equiv.sumCompl_apply_inr] using he ⟨k, hk⟩

/-- A column has at least as many nonzero matching products, counted
with their permutations, as allowed rows when all Hall inequalities have slack. -/
theorem nonzero_matching_count_ge_allowed_partners {I : Type*}
    [Fintype I] [DecidableEq I] (a b : I → ℂ) (j : I)
    (hslack : ∀ c, colorMultiplicity (fun k => -b k) c + colorMultiplicity a c < Fintype.card I) :
    Fintype.card {i : I // a i + b j ≠ 0} ≤
      Fintype.card {σ : Equiv.Perm I // matchingProduct a b σ ≠ 0} := by
  classical
  have hp {σ : Equiv.Perm I} (hσ : matchingProduct a b σ ≠ 0) (k : I) :
      a (σ k) + b k ≠ 0 := fun hk =>
    hσ (Finset.prod_eq_zero (Finset.mem_univ k) hk)
  let partner (σ : {σ : Equiv.Perm I // matchingProduct a b σ ≠ 0}) :
      {i : I // a i + b j ≠ 0} := ⟨σ.1 j, hp σ.2 j⟩
  apply Fintype.card_le_of_surjective partner
  intro i
  have hij : -b j ≠ a i := fun h => i.2 (eq_neg_iff_add_eq_zero.mp h.symm)
  obtain ⟨σ, hσ, hmatch⟩ := exists_unequal_color_perm_at_of_slack
    (fun k => -b k) a j i hij hslack
  have hn : matchingProduct a b σ ≠ 0 := by
    unfold matchingProduct
    exact Finset.prod_ne_zero_iff.mpr (fun k _ h => hmatch k (eq_neg_iff_add_eq_zero.mpr h).symm)
  exact ⟨⟨σ, hn⟩, Subtype.ext hσ⟩

/-- Every MOC counterexample has at least three units of Hall slack at
every color, including colors which occur in just one spectrum. -/
theorem not_holds_colorMultiplicity_le_card_sub_three {I : Type*}
    [Fintype I] [DecidableEq I] (a b : I → ℂ) (U : Matrix I I ℂ)
    (hU : IsUnitary U) (h : ¬ Holds a b U) (c : ℂ) :
    colorMultiplicity (fun j => -b j) c + colorMultiplicity a c ≤ Fintype.card I - 3 := by
  have hA : spectralSupport (fun i => a i + -c) =
      Finset.univ.filter (fun i => a i ≠ c) := by
    ext i
    simp [spectralSupport, ← sub_eq_add_neg, sub_ne_zero]
  have hB : spectralSupport (fun i => b i - -c) =
      Finset.univ.filter (fun i => -b i ≠ c) := by
    ext i
    simp only [spectralSupport, mem_filter, mem_univ, true_and, sub_ne_zero]
    exact not_congr ⟨fun he => neg_eq_iff_eq_neg.mpr he, fun he => neg_eq_iff_eq_neg.mp he⟩
  have hM : ¬ ((spectralSupport (fun i => a i + -c)).card +
      (spectralSupport (fun i => b i - -c)).card ≤ Fintype.card I + 2) :=
    fun hb => h (holds_of_shifted_support_le_card_add_two a b U hU (-c) hb)
  rw [hA, hB] at hM
  have hca := colorMultiplicity_add_complement a c
  have hcb := colorMultiplicity_add_complement (fun j => -b j) c
  omega

end MOC
