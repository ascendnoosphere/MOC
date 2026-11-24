import MOC.ContactCurveStep

/-! A complex affine profile line supplies the next contact without a
compactification or a curve normalization. -/

open Matrix Set
open scoped BigOperators

namespace MOC

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- If an affine line of realizable profiles fixes the old differences and
the determinant gap, a varying difference forces a new contact. This is an
explicit test on a candidate affine direction, not a claim that one exists
at every witness. -/
theorem StrictMatchingSupport.exists_more_contacts_of_affine_profiles
    {U : Matrix ι ι ℂ} (hU : IsUnitary U) (w : StrictMatchingSupport U)
    (d : Equiv.Perm ι → ℂ)
    (hline : ∀ t : ℂ, ∃ a b : ι → ℂ,
      ∀ q, matchingProduct a b q = matchingProduct w.a w.b q + t * d q)
    (hold : ∀ q ∈ w.contacts, d q = d w.pivot)
    (hgap : matchingProfileDetGap U w.η w.pivot d = 0)
    (hvar : ∃ q, d q ≠ d w.pivot) :
    ∃ w' : StrictMatchingSupport U, w.contacts ⊂ w'.contacts := by
  classical
  obtain ⟨q, hq⟩ := hvar
  let J : Finset (Equiv.Perm ι) := w.contactsᶜ
  have hqJ : q ∈ J := Finset.mem_compl.mpr fun h => hq (hold q h)
  have hη : w.η ≠ 0 := by
    intro he
    simpa [he] using w.strict
  let G (q : Equiv.Perm ι) : ℝ :=
    (w.η * (matchingProduct w.a w.b w.pivot - matchingProduct w.a w.b q)).re
  let slope (q : Equiv.Perm ι) : ℂ := w.η * (d w.pivot - d q)
  have hsq : slope q ≠ 0 := mul_ne_zero hη (sub_ne_zero.mpr (Ne.symm hq))
  let u : ℂ := (-((G q + 1 : ℝ) : ℂ)) / slope q
  let g (x : ℝ) (j : Equiv.Perm ι) : ℝ := G j + x * (u * slope j).re
  have hg0 (j) (hj : j ∈ J) : 0 < g 0 j := by
    have hne : (w.η * matchingProduct w.a w.b j).re ≠
        (w.η * matchingProduct w.a w.b w.pivot).re := by
      intro he
      exact (Finset.mem_compl.mp hj) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, he⟩)
    simpa only [g, G, zero_mul, add_zero, mul_sub, Complex.sub_re] using
      sub_pos.mpr (lt_of_le_of_ne (w.maximal j) hne)
  have hg1 : g 1 q < 0 := by
    have he : u * slope q = -((G q + 1 : ℝ) : ℂ) := div_mul_cancel₀ _ hsq
    simp only [g, he, Complex.neg_re, Complex.ofReal_re, one_mul]
    linarith
  let jn : J.Nonempty := ⟨q, hqJ⟩
  let m (x : ℝ) : ℝ := J.inf' jn (g x)
  have hm : Continuous m := by
    apply Continuous.finset_inf'_apply
    intro j _
    change Continuous (fun x : ℝ => G j + x * (u * slope j).re)
    fun_prop
  have hm0 : 0 < m 0 := (Finset.lt_inf'_iff jn).mpr hg0
  have hm1 : m 1 < 0 := (Finset.inf'_lt_iff jn).mpr ⟨q, hqJ, hg1⟩
  have hzero : (0 : ℝ) ∈ m '' (Set.univ : Set ℝ) :=
    ((isPreconnected_univ : IsPreconnected (Set.univ : Set ℝ)).image _ hm.continuousOn).Icc_subset
      ⟨1, Set.mem_univ _, rfl⟩ ⟨0, Set.mem_univ _, rfl⟩ ⟨hm1.le, hm0.le⟩
  obtain ⟨x, _, hx⟩ := hzero
  obtain ⟨j, hj, hmin⟩ := Finset.exists_mem_eq_inf' jn (g x)
  obtain ⟨a, b, hP⟩ := hline ((x : ℂ) * u)
  have hg (j) :
      (w.η * matchingProduct a b w.pivot).re - (w.η * matchingProduct a b j).re =
        g x j := by
    rw [hP, hP]
    have he : w.η * (matchingProduct w.a w.b w.pivot + (x : ℂ) * u * d w.pivot) -
        w.η * (matchingProduct w.a w.b j + (x : ℂ) * u * d j) =
      w.η * (matchingProduct w.a w.b w.pivot - matchingProduct w.a w.b j) +
        (x : ℂ) * (u * slope j) := by dsimp [slope]; ring
    rw [← Complex.sub_re, he, Complex.add_re, Complex.mul_re]
    simp [g, G]
  have hOld (j) (hj : j ∈ w.contacts) : g x j = 0 := by
    have hc := (Finset.mem_filter.mp hj).2
    have hs : slope j = 0 := by simp [slope, hold j hj]
    simp only [g, G, hs, mul_zero, Complex.zero_re, add_zero, mul_sub, Complex.sub_re,
      hc, sub_self]
  have hmax (j) : (w.η * matchingProduct a b j).re ≤ (w.η * matchingProduct a b w.pivot).re := by
    apply sub_nonneg.mp
    rw [hg]
    by_cases hj : j ∈ w.contacts
    · rw [hOld j hj]
    · have hjJ : j ∈ J := Finset.mem_compl.mpr hj
      have hnm : 0 ≤ m x := by rw [hx]
      exact (Finset.le_inf'_iff jn (g x)).mp hnm j hjJ
  have hgapEq : matchingProfileDetGap U w.η w.pivot (matchingProduct a b) =
      matchingProfileDetGap U w.η w.pivot (matchingProduct w.a w.b) := by
    have he (j : Equiv.Perm ι) :
        (realSignedWeight U j : ℂ) * (w.η * (matchingProduct a b j - matchingProduct a b w.pivot)) =
          (realSignedWeight U j : ℂ) * (w.η *
            (matchingProduct w.a w.b j - matchingProduct w.a w.b w.pivot)) +
          ((x : ℂ) * u) * ((realSignedWeight U j : ℂ) * (w.η * (d j - d w.pivot))) := by
      rw [hP, hP]
      ring
    unfold matchingProfileDetGap
    simp_rw [he, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [show (∑ j, (realSignedWeight U j : ℂ) * (w.η * (d j - d w.pivot))) = 0 from hgap,
      mul_zero, add_zero]
  have hstrict : (w.η * matchingProduct a b w.pivot).re <
      (w.η * determinantValue a b U).re := by
    rw [matchingProfileDetGap_matchingProduct a b U hU,
      matchingProfileDetGap_matchingProduct w.a w.b U hU] at hgapEq
    have he := congrArg Complex.re hgapEq
    simp only [mul_sub, Complex.sub_re] at he
    exact sub_pos.mp (he ▸ (sub_pos.mpr w.strict))
  let w' : StrictMatchingSupport U := ⟨a, b, w.η, w.pivot, hmax, hstrict⟩
  have hmem (j) (hj : g x j = 0) : j ∈ w'.contacts := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    exact (sub_eq_zero.mp ((hg j).trans hj)).symm
  refine ⟨w', Finset.ssubset_iff_subset_ne.mpr ⟨fun j hj => hmem j (hOld j hj), ?_⟩⟩
  intro he
  have hj0 : g x j = 0 := (hmin.symm.trans hx)
  exact (Finset.mem_compl.mp hj) (he ▸ hmem j hj0)

/-- The affine direction obtained by varying one entry of the second
spectrum. It is the product of all factors except the one at that entry. -/
def oneEntryMatchingSlope (a b : ι → ℂ) (k : ι) (p : Equiv.Perm ι) : ℂ :=
  ∏ j ∈ Finset.univ.erase k, (a (p j) + b j)

theorem matchingProduct_update_add (a b : ι → ℂ) (k : ι) (t : ℂ) (p : Equiv.Perm ι) :
    matchingProduct a (Function.update b k (b k + t)) p =
      matchingProduct a b p + t * oneEntryMatchingSlope a b k p := by
  classical
  have hk : k ∈ (Finset.univ : Finset ι) := Finset.mem_univ _
  have he : (∏ j ∈ Finset.univ.erase k, (a (p j) + Function.update b k (b k + t) j)) =
      oneEntryMatchingSlope a b k p := by
    unfold oneEntryMatchingSlope
    apply Finset.prod_congr rfl
    intro i hi
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
  unfold matchingProduct
  rw [← Finset.mul_prod_erase Finset.univ _ hk,
    ← Finset.mul_prod_erase Finset.univ (fun j => a (p j) + b j) hk,
    Function.update_self, he]
  unfold oneEntryMatchingSlope
  ring

/-- A single spectral entry gives a strict contact increase when its
coefficient preserves the original contact differences and determinant
gap, but changes at least one other difference. -/
theorem StrictMatchingSupport.exists_more_contacts_of_one_entry
    {U : Matrix ι ι ℂ} (hU : IsUnitary U) (w : StrictMatchingSupport U) (k : ι)
    (hold : ∀ q ∈ w.contacts, oneEntryMatchingSlope w.a w.b k q =
      oneEntryMatchingSlope w.a w.b k w.pivot)
    (hgap : matchingProfileDetGap U w.η w.pivot (oneEntryMatchingSlope w.a w.b k) = 0)
    (hvar : ∃ q, oneEntryMatchingSlope w.a w.b k q ≠ oneEntryMatchingSlope w.a w.b k w.pivot) :
    ∃ w' : StrictMatchingSupport U, w.contacts ⊂ w'.contacts :=
  w.exists_more_contacts_of_affine_profiles hU (oneEntryMatchingSlope w.a w.b k)
    (fun t => ⟨w.a, Function.update w.b k (w.b k + t),
      matchingProduct_update_add w.a w.b k t⟩) hold hgap hvar

end MOC
