import MOC.AffineGapCover
import Mathlib.Algebra.MvPolynomial.Equiv

/-! A polynomial family of exact matching profiles cannot preserve every
old contact difference at a maximal strict witness while varying another. -/

open Set Filter MvPolynomial Matrix
open scoped Topology BigOperators

namespace MOC

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A nonconstant polynomial motion of a projected deficit supplies
a new contact if the motion is exact and fixes old complex differences. -/
theorem StrictMatchingSupport.exists_more_contacts_on_exact_polynomial_profile [Nonempty ι]
    {U : Matrix ι ι ℂ} (hU : IsUnitary U) (w : StrictMatchingSupport U)
    (P : Equiv.Perm ι → Polynomial ℂ)
    (hbase : (fun q => (P q).eval 0) = matchingProduct w.a w.b)
    (hex : ∀ z : ℂ, ∃ a b : ι → ℂ, matchingProduct a b = fun q => (P q).eval z)
    (hold : ∀ z : ℂ, ∀ q ∈ w.contacts,
      (P w.pivot).eval z - (P q).eval z = (P w.pivot).eval 0 - (P q).eval 0)
    (hv : ∃ q, (Polynomial.C w.η * (P w.pivot - P q)).natDegree ≠ 0) :
    ∃ v : StrictMatchingSupport U, v.η = w.η ∧ v.pivot = w.pivot ∧ w.contacts ⊂ v.contacts := by
  classical
  let gp : Polynomial ℂ := ∑ q, Polynomial.C (realSignedWeight U q : ℂ) *
    (Polynomial.C w.η * (P q - P w.pivot))
  have hgp (z : ℂ) : gp.eval z =
      matchingProfileDetGap U w.η w.pivot (fun q => (P q).eval z) := by
    simp only [gp, matchingProfileDetGap, Polynomial.eval_finset_sum, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_sub]
  have hgp₀ : 0 < (gp.eval 0).re := by
    rw [hgp, hbase, matchingProfileDetGap_matchingProduct _ _ _ hU, mul_sub, Complex.sub_re]
    exact sub_pos.mpr w.strict
  have hc (q : Equiv.Perm ι) : Continuous (fun z : ℂ => (w.η *
      ((P w.pivot).eval z - (P q).eval z)).re) :=
    Complex.continuous_re.comp (continuous_const.mul ((P w.pivot).continuous.sub (P q).continuous))
  by_cases hvar : ∃ z : ℂ, gp.eval z ≠ gp.eval 0
  · let A := MvPolynomial PUnit ℂ
    let Q : Ideal A := ⊥
    letI : Q.IsPrime := Ideal.bot_prime
    let e := (MvPolynomial.pUnitAlgEquiv ℂ).symm
    let F := (e.trans (AlgEquiv.quotientBot ℂ A).symm).toAlgHom
    let g := e gp
    let t := e Polynomial.X
    have ht : Ideal.Quotient.mk Q t = F Polynomial.X := rfl
    let x (z : ℂ) : zeroLocus Q := ⟨fun _ => z, by
      intro p hp
      have he : p = 0 := Ideal.mem_bot.mp hp
      simp only [he, map_zero]⟩
    let arg (y : zeroLocus Q) : ℂ := y.val PUnit.unit
    let PQ (y : zeroLocus Q) (q : Equiv.Perm ι) : ℂ := (P q).eval (arg y)
    have hG (y : zeroLocus Q) : eval y.val g = gp.eval (arg y) := by
      change eval₂ (RingHom.id ℂ) y.val (e gp) = _
      rw [MvPolynomial.eval₂_pUnitAlgEquiv_symm]
      rfl
    have hvar' : ∃ y y' : zeroLocus Q, eval y.val g ≠ eval y'.val g := by
      obtain ⟨z,hz⟩ := hvar
      exact ⟨x z,x 0,by simpa only [hG] using hz⟩
    obtain ⟨S,s,c,hstart,hconn,hpos,hs,hsG,hhol⟩ :=
      affineGapContinuation PUnit Q F (AlgHom.Finite.of_surjective _ (e.trans (AlgEquiv.quotientBot ℂ A).symm).surjective)
        (e.trans (AlgEquiv.quotientBot ℂ A).symm).injective t g ht hvar' (x 0) (by rwa [hG])
    let T : Set (zeroLocus Q) := insert (x 0) S
    have hT : IsPreconnected T :=
      hconn.subset_closure (Set.subset_insert _ _) (insert_subset hstart subset_closure)
    have hTp (y : zeroLocus Q) (hy : y ∈ T) : 0 < (gp.eval (arg y)).re := by
      rcases hy with he | he
      · exact he.symm ▸ hgp₀
      · rw [← hG]
        exact hpos y he
    have harg : Continuous arg := (continuous_apply PUnit.unit).comp continuous_subtype_val
    obtain ⟨v,hη,hp,hv',_⟩ := w.exists_more_contacts_of_halfPlane_sheet hU hT PQ
      (fun y _ => hex (arg y)) (fun q => ((hc q).comp harg).continuousOn)
      (Set.mem_insert _ _) hbase (fun y _ => hold (arg y))
      (fun y hy => by rw [← hgp]; exact hTp y hy) s c (fun z hz => Or.inr (hs z hz))
      (fun q z hz => (P q).differentiableAt.comp_differentiableWithinAt z (hhol PUnit.unit z hz))
      (fun z hz => by rw [← hgp, ← hG]; exact hsG z hz)
    exact ⟨v,hη,hp,hv'⟩
  · obtain ⟨q,hq⟩ := hv
    let D : Polynomial ℂ := Polynomial.C w.η * (P w.pivot - P q)
    let R := D - Polynomial.C (-1)
    have hRd : R.natDegree ≠ 0 := by simpa only [R, Polynomial.natDegree_sub_C] using hq
    have hR0 : R ≠ 0 := fun h => hRd (h ▸ Polynomial.natDegree_zero)
    have hR : R.degree ≠ 0 := by
      rw [Polynomial.degree_eq_natDegree hR0]
      exact_mod_cast hRd
    obtain ⟨z,hz⟩ := IsAlgClosed.exists_root R hR
    have hneg : (w.η * ((P w.pivot).eval z - (P q).eval z)).re < 0 := by
      have hdz : D.eval z = -1 := by
        change R.eval z = 0 at hz
        simpa only [R, Polynomial.eval_sub, Polynomial.eval_C, sub_eq_zero] using hz
      have hn : (D.eval z).re < 0 := by
        rw [hdz, Complex.neg_re, Complex.one_re]
        exact neg_lt_zero.mpr zero_lt_one
      simpa only [D, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_sub] using hn
    have hgap (x : ℂ) : 0 < (gp.eval x).re := by
      have he : gp.eval x = gp.eval 0 := not_not.mp fun hn => hvar ⟨x,hn⟩
      rw [he]
      exact hgp₀
    obtain ⟨v,hη,hp,hlt,_⟩ := w.exists_more_contacts_on_connected_profiles hU
      (isPreconnected_univ (α := ℂ)) (fun z q => (P q).eval z) (fun z _ => hex z)
      (fun j => (hc j).continuousOn) (mem_univ 0) hbase
      (fun y _ j hj => by
        rw [hold y j hj, congrFun hbase, congrFun hbase, mul_sub, Complex.sub_re,
          (Finset.mem_filter.mp hj).2, sub_self])
      (fun y _ => by rw [← hgp]; exact hgap y)
      ⟨z, mem_univ _, q, hneg⟩
    exact ⟨v,hη,hp,hlt⟩


/-- A nontrivial common pivot-relative invariant cut among all contacts
can be moved by opposite translates on its two sides. The polynomial
motion preserves the contacts and forces another one. No simplicity
or nonvanishing premise is needed. -/
theorem StrictMatchingSupport.exists_more_contacts_of_common_invariant_cut
    {U : Matrix ι ι ℂ} (hU : IsUnitary U) (w : StrictMatchingSupport U)
    (I : Finset ι) (hI : I.Nonempty) (hIc : ∃ j, j ∉ I)
    (hcut : ∀ q ∈ w.contacts, ∀ j, w.pivot.symm (q j) ∈ I ↔ j ∈ I) :
    ∃ v : StrictMatchingSupport U, v.η = w.η ∧ v.pivot = w.pivot ∧ w.contacts ⊂ v.contacts := by
  classical
  obtain ⟨i,hi⟩ := hI
  obtain ⟨j,hj⟩ := hIc
  letI : Nonempty ι := ⟨i⟩
  let D (k : ι) : Polynomial ℂ := if k ∈ I then Polynomial.X else 0
  let d (z : ℂ) (k : ι) : ℂ := if k ∈ I then z else 0
  have hD (k : ι) (z : ℂ) : (D k).eval z = d z k := by
    by_cases hk : k ∈ I <;> simp [D,d,hk]
  let Cst (q : Equiv.Perm ι) (k : ι) := w.a (q k) + w.b k
  let L (q : Equiv.Perm ι) (k : ι) :=
    Polynomial.C (Cst q k) + (D (w.pivot.symm (q k)) - D k)
  let P (q : Equiv.Perm ι) := ∏ k, L q k
  have hP (z : ℂ) : (fun q => (P q).eval z) = matchingProduct
      (fun k => w.a k + d z (w.pivot.symm k)) (fun k => w.b k - d z k) := by
    funext q
    simp only [P, matchingProduct, Polynomial.eval_prod, L, Polynomial.eval_add,
      Polynomial.eval_C, Polynomial.eval_sub, hD]
    exact Finset.prod_congr rfl fun k _ => by dsimp only [Cst]; ring
  have hbase : (fun q => (P q).eval 0) = matchingProduct w.a w.b := by
    rw [hP]
    have hd (k : ι) : d 0 k = 0 := by simp [d]
    simp only [hd, add_zero, sub_zero]
  have hconst (q : Equiv.Perm ι) (k : ι) (h : w.pivot.symm (q k) ∈ I ↔ k ∈ I) :
      L q k = Polynomial.C (Cst q k) := by
    by_cases hk : k ∈ I
    · simp [L,D,hk,h.mpr hk]
    · have hr : w.pivot.symm (q k) ∉ I := fun he => hk (h.mp he)
      simp [L,D,hk,hr]
  have hLocked (q : Equiv.Perm ι) (hq : q ∈ w.contacts) :
      P q = Polynomial.C (matchingProduct w.a w.b q) := by
    change (∏ k, L q k) = Polynomial.C (∏ k, Cst q k)
    rw [map_prod]
    exact Finset.prod_congr rfl fun k _ => hconst q k (hcut q hq k)
  have hpivot : w.pivot ∈ w.contacts := by simp [StrictMatchingSupport.contacts]
  have hη : w.η ≠ 0 := by
    intro he
    have hw := w.strict
    simp [he] at hw
  have hsome : ∃ q : Equiv.Perm ι, matchingProduct w.a w.b q ≠ 0 := by
    by_contra! h
    have hdet := real_signed_determinant w.a w.b U hU
    simp only [h, mul_zero, Finset.sum_const_zero] at hdet
    have hw := w.strict
    rw [← hdet, h w.pivot, mul_zero] at hw
    exact (lt_irrefl _ hw)
  obtain ⟨s,hs⟩ := hsome
  have hsFactor (k : ι) : Cst s k ≠ 0 := Finset.prod_ne_zero_iff.mp hs k (Finset.mem_univ _)
  have hexCross : ∃ q : Equiv.Perm ι,
      (∃ k, ¬ (w.pivot.symm (q k) ∈ I ↔ k ∈ I)) ∧
      (∀ k, (w.pivot.symm (q k) ∈ I ↔ k ∈ I) → Cst q k ≠ 0) := by
    by_cases hgood : ∀ k, w.pivot.symm (s k) ∈ I ↔ k ∈ I
    · let q := s * Equiv.swap i j
      have hneq : i ≠ j := fun h => hj (h ▸ hi)
      have hqi : ¬ (w.pivot.symm (q i) ∈ I ↔ i ∈ I) := by
        rw [show q i = s j by simp [q, Equiv.Perm.mul_apply], hgood j]
        exact fun he => hj (he.mpr hi)
      have hqj : ¬ (w.pivot.symm (q j) ∈ I ↔ j ∈ I) := by
        rw [show q j = s i by simp [q, Equiv.Perm.mul_apply], hgood i]
        exact fun he => hj (he.mp hi)
      refine ⟨q, ⟨i,hqi⟩, fun k hk => ?_⟩
      have hki : k ≠ i := fun h => hqi (h ▸ hk)
      have hkj : k ≠ j := fun h => hqj (h ▸ hk)
      simpa only [Cst,q,Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hki hkj] using hsFactor k
    · exact ⟨s, not_forall.mp hgood, fun k _ => hsFactor k⟩
  obtain ⟨q,⟨k,hk⟩,huncross⟩ := hexCross
  have hOne (m : ι) (hm : ¬ (w.pivot.symm (q m) ∈ I ↔ m ∈ I)) : (L q m).natDegree = 1 := by
    by_cases hm₁ : w.pivot.symm (q m) ∈ I <;> by_cases hm₂ : m ∈ I
    · exact False.elim (hm (iff_of_true hm₁ hm₂))
    · simp [L,D,hm₁,hm₂]
    · simp [L,D,hm₁,hm₂, Polynomial.natDegree_neg]
    · exact False.elim (hm (iff_of_false hm₁ hm₂))
  have hnonzero (m : ι) (_ : m ∈ (Finset.univ : Finset ι)) : L q m ≠ 0 := by
    by_cases h : (w.pivot.symm (q m) ∈ I ↔ m ∈ I)
    · rw [hconst q m h]
      exact Polynomial.C_ne_zero.mpr (huncross m h)
    · intro hz
      have hh := hOne m h
      rw [hz, Polynomial.natDegree_zero] at hh
      exact Nat.zero_ne_one hh
  have hvar : (P q).natDegree ≠ 0 := by
    apply Nat.ne_of_gt
    change 0 < (∏ m, L q m).natDegree
    rw [Polynomial.natDegree_prod Finset.univ (L q) hnonzero]
    exact (Nat.zero_lt_one.trans_eq (hOne k hk).symm).trans_le
      (Finset.single_le_sum (f := fun m => (L q m).natDegree) (fun _ _ => Nat.zero_le _) (Finset.mem_univ k))
  apply w.exists_more_contacts_on_exact_polynomial_profile hU P hbase
    (fun z => ⟨_,_,(hP z).symm⟩)
  · intro z q hq
    simp only [hLocked _ hpivot, hLocked _ hq, Polynomial.eval_C]
  · refine ⟨q, ?_⟩
    rw [Polynomial.natDegree_C_mul hη, Polynomial.natDegree_sub, hLocked _ hpivot,
      Polynomial.natDegree_sub_C]
    exact hvar

/-- At a contact-maximal strict witness, no nontrivial cut is common to
all pivot-relative permutations. Equivalently the union of the contact
assignment edges is connected after the pivot edges identify the two
label copies. -/
theorem StrictMatchingSupport.contact_crosses_every_nontrivial_cut
    {U : Matrix ι ι ℂ} (hU : IsUnitary U) (w : StrictMatchingSupport U)
    (hmax : ∀ v : StrictMatchingSupport U, v.contacts.card ≤ w.contacts.card)
    (I : Finset ι) (hI : I.Nonempty) (hIc : ∃ j, j ∉ I) :
    ∃ q ∈ w.contacts, ∃ j, ¬ (w.pivot.symm (q j) ∈ I ↔ j ∈ I) := by
  classical
  by_contra! h
  obtain ⟨v,_,_,hv⟩ := w.exists_more_contacts_of_common_invariant_cut hU I hI hIc h
  exact (not_lt_of_ge (hmax v)) (Finset.card_lt_card hv)


end MOC
