import MOC.FiniteMinorLaw
import Mathlib.Tactic.Linarith

/-! An order-five unitary with zero diagonal and constant off-diagonal
modulus has a common permutation law for its squared minors. -/

open BigOperators Finset Matrix
open scoped ComplexConjugate

namespace MOC

noncomputable section

private theorem fifth_label_of_four_distinct :
    ∀ i k j l : Fin 5, i ≠ k → j ≠ l → i ≠ j → i ≠ l → k ≠ j → k ≠ l →
      ∃ m : Fin 5, i ≠ m ∧ k ≠ m ∧ j ≠ m ∧ l ≠ m ∧
        (univ : Finset (Fin 5)) = {i, k, j, l, m} := by
  decide +kernel

/-- The pair minors have only two squared norms. For disjoint pairs,
three equal-modulus row inner products sum to zero and determine the norm. -/
theorem conferenceFive_pair (U : Matrix (Fin 5) (Fin 5) ℂ) (hU : IsUnitary U)
    (hdiag : ∀ i, U i i = 0)
    (hflat : ∀ i j, i ≠ j → Complex.normSq (U i j) = 1 / 4)
    {i k j l : Fin 5} (hik : i ≠ k) (hjl : j ≠ l) :
    subsetMinorSq U {i, k} {j, l} =
      if i = j ∨ i = l ∨ k = j ∨ k = l then 1 / 16 else 3 / 16 := by
  rw [subsetMinorSq_pair U hU hik hjl]
  by_cases h : i = j ∨ i = l ∨ k = j ∨ k = l
  · rw [if_pos h]
    rcases h with h | h | h | h
    · subst j
      rw [hdiag i, zero_mul, zero_sub, Complex.normSq_neg, Complex.normSq_mul,
        hflat i l hjl, hflat k i hik.symm]
      norm_num
    · subst l
      rw [hdiag i, zero_mul, sub_zero, Complex.normSq_mul, hflat i j hjl.symm,
        hflat k i hik.symm]
      norm_num
    · subst j
      rw [hdiag k, mul_zero, sub_zero, Complex.normSq_mul, hflat i k hik, hflat k l hjl]
      norm_num
    · subst l
      rw [hdiag k, mul_zero, zero_sub, Complex.normSq_neg, Complex.normSq_mul,
        hflat i k hik, hflat k j hjl.symm]
      norm_num
  rw [if_neg h]
  push_neg at h
  obtain ⟨hij, hil, hkj, hkl⟩ := h
  obtain ⟨m, him, hkm, hjm, hlm, hm⟩ := fifth_label_of_four_distinct i k j l
    hik hjl hij hil hkj hkl
  let x := U i j * conj (U k j)
  let y := U i l * conj (U k l)
  let z := U i m * conj (U k m)
  have hsum : x + y + z = 0 := by
    have ht := congrArg (fun M : Matrix (Fin 5) (Fin 5) ℂ => M i k) hU.1
    change ((U * Uᴴ) i k) = (1 : Matrix (Fin 5) (Fin 5) ℂ) i k at ht
    rw [Matrix.mul_apply, hm, Matrix.one_apply_ne hik] at ht
    simpa [Finset.sum_insert, Matrix.conjTranspose_apply, Complex.star_def,
      hik, hij, hil, him, hkj, hkl, hkm, hjl, hjm, hlm, hdiag, x, y, z, add_assoc] using ht
  have hx : Complex.normSq x = 1 / 16 := by
    dsimp only [x]
    rw [Complex.normSq_mul, Complex.normSq_conj, hflat i j hij, hflat k j hkj]
    norm_num
  have hy : Complex.normSq y = 1 / 16 := by
    dsimp only [y]
    rw [Complex.normSq_mul, Complex.normSq_conj, hflat i l hil, hflat k l hkl]
    norm_num
  have hz : Complex.normSq z = 1 / 16 := by
    dsimp only [z]
    rw [Complex.normSq_mul, Complex.normSq_conj, hflat i m him, hflat k m hkm]
    norm_num
  have hxy : x + y = -z := eq_neg_of_add_eq_zero_left hsum
  have hs : Complex.normSq (x + y) = 1 / 16 := by
    rw [hxy, Complex.normSq_neg, hz]
  rw [Complex.normSq_add, hx, hy] at hs
  calc
    Complex.normSq (U i j * U k l - U i l * U k j) = Complex.normSq (x - y) := by
      have hcross : (U i j * U k l) * conj (U i l * U k j) = x * conj y := by
        simp only [x, y, map_mul, starRingEnd_self_apply]
        ring
      simp only [Complex.normSq_sub, hcross, hx, hy, Complex.normSq_mul,
        hflat i j hij, hflat k l hkl, hflat i l hil, hflat k j hkj]
      ring
    _ = 3 / 16 := by
      rw [Complex.normSq_sub, hx, hy]
      linarith only [hs]

/- The 24 five-cycles followed by the 20 permutations with a two-cycle and
a three-cycle, in lexicographic order within each class. -/
private def conferencePermImage : Fin 44 → Fin 5 → Fin 5 :=
  ![
  ![1, 2, 3, 4, 0], ![1, 2, 4, 0, 3],
  ![1, 3, 0, 4, 2], ![1, 3, 4, 2, 0],
  ![1, 4, 0, 2, 3], ![1, 4, 3, 0, 2],
  ![2, 0, 3, 4, 1], ![2, 0, 4, 1, 3],
  ![2, 3, 1, 4, 0], ![2, 3, 4, 0, 1],
  ![2, 4, 1, 0, 3], ![2, 4, 3, 1, 0],
  ![3, 0, 1, 4, 2], ![3, 0, 4, 2, 1],
  ![3, 2, 0, 4, 1], ![3, 2, 4, 1, 0],
  ![3, 4, 0, 1, 2], ![3, 4, 1, 2, 0],
  ![4, 0, 1, 2, 3], ![4, 0, 3, 1, 2],
  ![4, 2, 0, 1, 3], ![4, 2, 3, 0, 1],
  ![4, 3, 0, 2, 1], ![4, 3, 1, 0, 2],
  ![1, 0, 3, 4, 2], ![1, 0, 4, 2, 3],
  ![1, 2, 0, 4, 3], ![1, 3, 4, 0, 2],
  ![1, 4, 3, 2, 0], ![2, 0, 1, 4, 3],
  ![2, 3, 0, 4, 1], ![2, 3, 4, 1, 0],
  ![2, 4, 0, 1, 3], ![2, 4, 3, 0, 1],
  ![3, 0, 4, 1, 2], ![3, 2, 1, 4, 0],
  ![3, 2, 4, 0, 1], ![3, 4, 0, 2, 1],
  ![3, 4, 1, 0, 2], ![4, 0, 3, 2, 1],
  ![4, 2, 1, 0, 3], ![4, 2, 3, 1, 0],
  ![4, 3, 0, 1, 2], ![4, 3, 1, 2, 0]]

private def conferencePermInverse : Fin 44 → Fin 5 → Fin 5 :=
  ![
  ![4, 0, 1, 2, 3], ![3, 0, 1, 4, 2],
  ![2, 0, 4, 1, 3], ![4, 0, 3, 1, 2],
  ![2, 0, 3, 4, 1], ![3, 0, 4, 2, 1],
  ![1, 4, 0, 2, 3], ![1, 3, 0, 4, 2],
  ![4, 2, 0, 1, 3], ![3, 4, 0, 1, 2],
  ![3, 2, 0, 4, 1], ![4, 3, 0, 2, 1],
  ![1, 2, 4, 0, 3], ![1, 4, 3, 0, 2],
  ![2, 4, 1, 0, 3], ![4, 3, 1, 0, 2],
  ![2, 3, 4, 0, 1], ![4, 2, 3, 0, 1],
  ![1, 2, 3, 4, 0], ![1, 3, 4, 2, 0],
  ![2, 3, 1, 4, 0], ![3, 4, 1, 2, 0],
  ![2, 4, 3, 1, 0], ![3, 2, 4, 1, 0],
  ![1, 0, 4, 2, 3], ![1, 0, 3, 4, 2],
  ![2, 0, 1, 4, 3], ![3, 0, 4, 1, 2],
  ![4, 0, 3, 2, 1], ![1, 2, 0, 4, 3],
  ![2, 4, 0, 1, 3], ![4, 3, 0, 1, 2],
  ![2, 3, 0, 4, 1], ![3, 4, 0, 2, 1],
  ![1, 3, 4, 0, 2], ![4, 2, 1, 0, 3],
  ![3, 4, 1, 0, 2], ![2, 4, 3, 0, 1],
  ![3, 2, 4, 0, 1], ![1, 4, 3, 2, 0],
  ![3, 2, 1, 4, 0], ![4, 3, 1, 2, 0],
  ![2, 3, 4, 1, 0], ![4, 2, 3, 1, 0]]

private theorem conferencePerm_left :
    ∀ k i, conferencePermInverse k (conferencePermImage k i) = i := by
  decide +kernel

private theorem conferencePerm_right :
    ∀ k i, conferencePermImage k (conferencePermInverse k i) = i := by
  decide +kernel

private def conferencePerm (k : Fin 44) : Equiv.Perm (Fin 5) :=
  ⟨conferencePermImage k, conferencePermInverse k, conferencePerm_left k, conferencePerm_right k⟩

private def conferenceMass (k : Fin 44) : ℕ :=
  if k.val < 24 then 1 else 2

private def conferenceWeight (k : Fin 44) : ℝ :=
  (conferenceMass k : ℝ) / 64

private def conferenceCount (I J : Finset (Fin 5)) : ℕ :=
  ∑ k ∈ univ.filter (fun k : Fin 44 => J.map (conferencePerm k).toEmbedding = I),
    conferenceMass k

private theorem conferenceCount_empty : conferenceCount ∅ ∅ = 64 := by
  decide +kernel

private theorem conferenceCount_singleton :
    ∀ i j : Fin 5, conferenceCount {i} {j} = if i = j then 0 else 16 := by
  decide +kernel

private def conferencePair : Fin 10 → Finset (Fin 5) :=
  ![{0, 1}, {0, 2}, {0, 3}, {0, 4}, {1, 2}, {1, 3}, {1, 4}, {2, 3}, {2, 4}, {3, 4}]

private theorem conferencePair_cover :
    ∀ i k : Fin 5, i ≠ k → ∃ t : Fin 10, conferencePair t = {i, k} := by
  decide +kernel

private theorem conferencePair_overlap :
    ∀ i k j l : Fin 5, (¬ Disjoint ({i, k} : Finset (Fin 5)) {j, l}) ↔
      i = j ∨ i = l ∨ k = j ∨ k = l := by
  decide +kernel

set_option maxHeartbeats 3500000 in
private theorem conferenceCount_pairs :
    ∀ t r : Fin 10, conferenceCount (conferencePair t) (conferencePair r) =
      if Disjoint (conferencePair t) (conferencePair r) then 12 else 4 := by
  decide +kernel

private theorem conferenceCount_pair :
    ∀ i k j l : Fin 5, i ≠ k → j ≠ l →
      conferenceCount {i, k} {j, l} =
        if i = j ∨ i = l ∨ k = j ∨ k = l then 4 else 12 := by
  intro i k j l hik hjl
  obtain ⟨t, ht⟩ := conferencePair_cover i k hik
  obtain ⟨r, hr⟩ := conferencePair_cover j l hjl
  have hc := conferenceCount_pairs t r
  rw [ht, hr] at hc
  by_cases hd : Disjoint ({i, k} : Finset (Fin 5)) {j, l}
  · rw [if_pos hd] at hc
    rw [if_neg (fun h => (conferencePair_overlap i k j l).mpr h hd)]
    exact hc
  · rw [if_neg hd] at hc
    rw [if_pos ((conferencePair_overlap i k j l).mp hd)]
    exact hc

private theorem conference_weighted_count (I J : Finset (Fin 5)) :
    (∑ k ∈ univ.filter (fun k : Fin 44 => J.map (conferencePerm k).toEmbedding = I),
      conferenceWeight k) = (conferenceCount I J : ℝ) / 64 := by
  simp only [conferenceWeight, conferenceCount, Nat.cast_sum, Finset.sum_div]

private theorem conferenceWeight_sum : ∑ k, conferenceWeight k = 1 := by
  have h := conference_weighted_count ∅ ∅
  rw [conferenceCount_empty] at h
  simpa using h.trans (show (↑(64 : ℕ) : ℝ) / 64 = 1 by norm_num)

private theorem conference_minor_law_small (U : Matrix (Fin 5) (Fin 5) ℂ)
    (hU : IsUnitary U) (hdiag : ∀ i, U i i = 0)
    (hflat : ∀ i j, i ≠ j → Complex.normSq (U i j) = 1 / 4)
    (I J : Finset (Fin 5)) (hIJ : I.card = J.card) (hs : I.card ≤ 2) :
    subsetMinorSq U I J =
      ∑ k ∈ univ.filter (fun k => J.map (conferencePerm k).toEmbedding = I),
        conferenceWeight k := by
  rw [conference_weighted_count]
  by_cases h0 : I.card = 0
  · have hI := Finset.card_eq_zero.mp h0
    have hJ := Finset.card_eq_zero.mp (hIJ.symm.trans h0)
    rw [hI, hJ, conferenceCount_empty]
    apply Complex.ofReal_injective
    rw [← sum_signedWeight_image_eq_subsetMinorSq U hU]
    simp [sum_signedWeight U (det_ne_zero_of_unitary hU)]
  by_cases h1 : I.card = 1
  · obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp h1
    obtain ⟨j, rfl⟩ := Finset.card_eq_one.mp (hIJ.symm.trans h1)
    rw [subsetMinorSq_singleton U hU, conferenceCount_singleton]
    by_cases h : i = j
    · subst j
      simp [hdiag, Complex.normSq_zero]
    · rw [if_neg h, hflat i j h]
      norm_num
  have h2 : I.card = 2 := by omega
  obtain ⟨i, k, hik, rfl⟩ := Finset.card_eq_two.mp h2
  obtain ⟨j, l, hjl, rfl⟩ := Finset.card_eq_two.mp (hIJ.symm.trans h2)
  rw [conferenceFive_pair U hU hdiag hflat hik hjl, conferenceCount_pair i k j l hik hjl]
  split_ifs <;> norm_num

/-- For every order-five unitary with zero diagonal and squared entry norm
(1/4) off the diagonal, one permutation law gives all squared minors. -/
theorem conferenceFive_minor_law (U : Matrix (Fin 5) (Fin 5) ℂ) (hU : IsUnitary U)
    (hdiag : ∀ i, U i i = 0) (hflat : ∀ i j, i ≠ j → Complex.normSq (U i j) = 1 / 4) :
    ∃ (p : Fin 44 → Equiv.Perm (Fin 5)) (w : Fin 44 → ℝ),
      (∀ k, 0 ≤ w k) ∧ (∑ k, w k) = 1 ∧
      ∀ I J : Finset (Fin 5), subsetMinorSq U I J =
        ∑ k ∈ univ.filter (fun k => J.map (p k).toEmbedding = I), w k := by
  refine ⟨conferencePerm, conferenceWeight, fun k => by unfold conferenceWeight; positivity,
    conferenceWeight_sum, ?_⟩
  exact indexed_minor_law_of_small U hU conferencePerm conferenceWeight (by
    intro I J hIJ hs
    exact conference_minor_law_small U hU hdiag hflat I J hIJ (by simpa using hs))

/-- The zero-diagonal, flat off-diagonal order-five mixers satisfy MOC
for all pairs of complex spectra. -/
theorem holds_conferenceFive (a b : Fin 5 → ℂ) (U : Matrix (Fin 5) (Fin 5) ℂ)
    (hU : IsUnitary U) (hdiag : ∀ i, U i i = 0)
    (hflat : ∀ i j, i ≠ j → Complex.normSq (U i j) = 1 / 4) : Holds a b U := by
  obtain ⟨p, w, hw, hs, hm⟩ := conferenceFive_minor_law U hU hdiag hflat
  exact holds_of_indexed_minor_law a b U hU p w hw hs hm

end

end MOC
