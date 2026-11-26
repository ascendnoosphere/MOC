import MOC.SubsetIncidenceKernel

/-! Mixed differences across a bipartition separate harmonic functions on the middle
subset level. The proof removes one label from each class at a time. -/

open Finset

namespace MOC

variable {α K : Type*} [DecidableEq α] [Field K]

/-- The pairs of a bijection between two finite classes, in an arbitrary order. -/
inductive SubsetMatchingList : Finset α → Finset α → List (α × α) → Prop
  | nil : SubsetMatchingList ∅ ∅ []
  | cons {L R : Finset α} {l r : α} {p : List (α × α)}
      (hl : l ∉ L) (hr : r ∉ R) (hp : SubsetMatchingList L R p) :
      SubsetMatchingList (insert l L) (insert r R) ((l, r) :: p)

/-- Apply the two choices from each matched pair with opposite signs. -/
def subsetMatchingDifference : List (α × α) → (Finset α → K) → Finset α → K
  | [], f => f
  | (l, r) :: p, f => subsetMatchingDifference p (fun S => f (insert l S) - f (insert r S))

def SubsetHarmonicOn (M : Finset α) (k : ℕ) (f : Finset α → K) : Prop :=
  ∀ S ⊆ M, S.card + 1 = k → ∑ i ∈ M \ S, f (insert i S) = 0

private theorem subsetHarmonic_difference {M : Finset α} {n : ℕ} {f : Finset α → K}
    (hf : SubsetHarmonicOn M (n + 1) f) {l r : α} (hl : l ∈ M) (hr : r ∈ M)
    (hne : l ≠ r) :
    SubsetHarmonicOn ((M.erase l).erase r) n
      (fun S => f (insert l S) - f (insert r S)) := by
  intro S hS hcard
  have hsub : S ⊆ M := fun x hx => (mem_erase.mp (mem_erase.mp (hS hx)).2).2
  have hls : l ∉ S := fun h => (mem_erase.mp (mem_erase.mp (hS h)).2).1 rfl
  have hrs : r ∉ S := fun h => (mem_erase.mp (hS h)).1 rfl
  let T := ((M.erase l).erase r) \ S
  have hT (x : α) : x ∈ T ↔ x ≠ r ∧ x ≠ l ∧ x ∈ M ∧ x ∉ S := by
    simp only [T, mem_sdiff, mem_erase]
    tauto
  have hlT : l ∉ T := by simp [hT]
  have hrT : r ∉ T := by simp [hT]
  have hel : M \ insert l S = insert r T := by
    ext x
    simp only [mem_sdiff, mem_insert, hT]
    by_cases hxl : x = l <;> by_cases hxr : x = r <;> subst_vars <;> tauto
  have her : M \ insert r S = insert l T := by
    ext x
    simp only [mem_sdiff, mem_insert, hT]
    by_cases hxl : x = l <;> by_cases hxr : x = r <;> subst_vars <;> tauto
  have hL := hf (insert l S) (insert_subset_iff.mpr ⟨hl, hsub⟩)
    (by rw [card_insert_of_not_mem hls, hcard])
  have hR := hf (insert r S) (insert_subset_iff.mpr ⟨hr, hsub⟩)
    (by rw [card_insert_of_not_mem hrs, hcard])
  rw [hel, sum_insert hrT] at hL
  rw [her, sum_insert hlT, Finset.insert_comm l r] at hR
  change (∑ i ∈ T, (f (insert l (insert i S)) - f (insert r (insert i S)))) = 0
  rw [sum_sub_distrib]
  have hc (a : α) :
      (∑ i ∈ T, f (insert a (insert i S))) = ∑ i ∈ T, f (insert i (insert a S)) :=
    sum_congr rfl fun i _ => congrArg f (Finset.insert_comm a i S)
  rw [hc l, hc r]
  linear_combination hL - hR

/-- A harmonic function on the middle level that vanishes on every matching test vanishes
at every middle subset. Each class can have any finite cardinality, including zero. -/
theorem subsetHarmonic_eq_zero_of_matching_differences [CharZero K] (n : ℕ)
    (L R : Finset α) (hl : L.card = n) (hr : R.card = n) (hdis : Disjoint L R)
    (f : Finset α → K) (hf : SubsetHarmonicOn (L ∪ R) n f)
    (ht : ∀ p, SubsetMatchingList L R p → subsetMatchingDifference p f ∅ = 0)
    (T : Finset α) (hT : T ⊆ L ∪ R) (hcT : T.card = n) : f T = 0 := by
  induction n generalizing L R f T with
  | zero =>
    have hL := card_eq_zero.mp hl
    have hR := card_eq_zero.mp hr
    have hE := card_eq_zero.mp hcT
    subst L
    subst R
    subst T
    exact ht [] .nil
  | succ n ih =>
    have hcross (S : Finset α) (hS : S ⊆ L ∪ R) (hcs : S.card = n)
        (l r : α) (hlL : l ∈ L) (hrR : r ∈ R) (hls : l ∉ S) (hrs : r ∉ S) :
        f (insert l S) = f (insert r S) := by
      have hlR : l ∉ R := Finset.disjoint_left.mp hdis hlL
      have hrL : r ∉ L := Finset.disjoint_right.mp hdis hrR
      have hne : l ≠ r := by rintro rfl; exact hlR hrR
      let L' := L.erase l
      let R' := R.erase r
      have hM : L' ∪ R' = ((L ∪ R).erase l).erase r := by
        ext x
        simp only [L', R', mem_union, mem_erase]
        by_cases hxl : x = l <;> by_cases hxr : x = r <;> subst_vars <;> tauto
      let g := fun V => f (insert l V) - f (insert r V)
      have hg : SubsetHarmonicOn (L' ∪ R') n g := by
        rw [hM]
        exact subsetHarmonic_difference hf (mem_union_left _ hlL) (mem_union_right _ hrR) hne
      have htests (p) (hp : SubsetMatchingList L' R' p) :
          subsetMatchingDifference p g ∅ = 0 := by
        apply ht ((l, r) :: p)
        simpa only [L', R', insert_erase hlL, insert_erase hrR] using
          SubsetMatchingList.cons (not_mem_erase l L) (not_mem_erase r R) hp
      apply sub_eq_zero.mp
      apply ih L' R' (by simp [L', card_erase_of_mem hlL, hl])
        (by simp [R', card_erase_of_mem hrR, hr])
        (hdis.mono (erase_subset _ _) (erase_subset _ _)) g hg htests S _ hcs
      rw [hM]
      intro x hx
      exact mem_erase.mpr ⟨fun he => hrs (he ▸ hx),
        mem_erase.mpr ⟨fun he => hls (he ▸ hx), hS hx⟩⟩
    obtain ⟨z, hz⟩ := card_pos.mp (show 0 < T.card by omega)
    let S := T.erase z
    have hcs : S.card = n := by simp [S, card_erase_of_mem hz, hcT]
    have hS : S ⊆ L ∪ R := (erase_subset _ _).trans hT
    obtain ⟨l, hlL, hls⟩ : ∃ l ∈ L, l ∉ S := by
      by_contra! h
      have := card_le_card (show L ⊆ S from h)
      omega
    obtain ⟨r, hrR, hrs⟩ : ∃ r ∈ R, r ∉ S := by
      by_contra! h
      have := card_le_card (show R ⊆ S from h)
      omega
    have hval (x : α) (hx : x ∈ (L ∪ R) \ S) : f (insert x S) = f (insert r S) := by
      obtain ⟨hxM, hxS⟩ := mem_sdiff.mp hx
      rcases mem_union.mp hxM with hxL | hxR
      · exact hcross S hS hcs x r hxL hrR hxS hrs
      · exact (hcross S hS hcs l x hlL hxR hls hxS).symm.trans
          (hcross S hS hcs l r hlL hrR hls hrs)
    have hs := hf S hS (by omega)
    rw [sum_congr rfl hval, sum_const, nsmul_eq_mul] at hs
    have hz' : z ∈ (L ∪ R) \ S := mem_sdiff.mpr ⟨hT hz, not_mem_erase z T⟩
    have hpos := card_pos.mpr ⟨z, hz'⟩
    have hne : (((L ∪ R) \ S).card : K) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hpos)
    have he := (hval z hz').trans ((mul_eq_zero.mp hs).resolve_left hne)
    simpa only [S, insert_erase hz] using he

end MOC
