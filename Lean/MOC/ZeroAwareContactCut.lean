import MOC.PolynomialProfileContact
import MOC.DistinctTerminalContacts

/-! A zero matching product does not lock all its assignment edges.
Opposite block translations leave it fixed if just one of its zero
factors stays within a block. This sharpens the common invariant cut
obstruction without a nonvanishing or a simple-spectrum assumption. -/

open Matrix
open scoped BigOperators

namespace MOC

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The chosen reference matching identifies the row and column copies
before taking the cut. Only nonzero matching products constrain all
their edges. For zero matching products, a single inside zero suffices. -/
theorem StrictMatchingSupport.exists_more_contacts_of_zero_aware_cut
    {U : Matrix ι ι ℂ} (hU : IsUnitary U) (w : StrictMatchingSupport U)
    (r : Equiv.Perm ι) (I : Finset ι) (hI : I.Nonempty) (hIc : ∃ j, j ∉ I)
    (hlock : ∀ q ∈ w.contacts,
      (∀ k, r.symm (q k) ∈ I ↔ k ∈ I) ∨
        ∃ k, (r.symm (q k) ∈ I ↔ k ∈ I) ∧ w.a (q k) + w.b k = 0) :
    ∃ v : StrictMatchingSupport U, v.η = w.η ∧ v.pivot = w.pivot ∧ w.contacts ⊂ v.contacts := by
  classical
  obtain ⟨i,hi⟩ := hI
  obtain ⟨j,hj⟩ := hIc
  letI : Nonempty ι := ⟨i⟩
  let D (k : ι) : Polynomial ℂ := if k ∈ I then Polynomial.X else 0
  let d (z : ℂ) (k : ι) : ℂ := if k ∈ I then z else 0
  have hD (k : ι) (z : ℂ) : (D k).eval z = d z k := by
    by_cases hk : k ∈ I <;> simp [D,d,hk]
  let A (q : Equiv.Perm ι) (k : ι) := w.a (q k) + w.b k
  let L (q : Equiv.Perm ι) (k : ι) :=
    Polynomial.C (A q k) + (D (r.symm (q k)) - D k)
  let P (q : Equiv.Perm ι) : Polynomial ℂ := ∏ k, L q k
  let inside (q : Equiv.Perm ι) (k : ι) : Prop := r.symm (q k) ∈ I ↔ k ∈ I
  have hconst (q : Equiv.Perm ι) (k : ι) (h : inside q k) :
      L q k = Polynomial.C (A q k) := by
    have h' : r.symm (q k) ∈ I ↔ k ∈ I := h
    simp [L,D,h']
  have hP (z : ℂ) : (fun q => (P q).eval z) = matchingProduct
      (fun k => w.a k + d z (r.symm k)) (fun k => w.b k - d z k) := by
    funext q
    simp only [P, matchingProduct, Polynomial.eval_prod, L, Polynomial.eval_add,
      Polynomial.eval_C, Polynomial.eval_sub, hD]
    exact Finset.prod_congr rfl fun k _ => by dsimp only [A]; ring
  have hbase : (fun q => (P q).eval 0) = matchingProduct w.a w.b := by
    rw [hP]
    have hd (k : ι) : d 0 k = 0 := by simp [d]
    simp only [hd,add_zero,sub_zero]
  have hlocked (q : Equiv.Perm ι) (hq : q ∈ w.contacts) :
      P q = Polynomial.C (matchingProduct w.a w.b q) := by
    rcases hlock q hq with hall | ⟨k,hk,hzero⟩
    · change (∏ k, L q k) = Polynomial.C (∏ k, A q k)
      rw [map_prod]
      exact Finset.prod_congr rfl fun k _ => hconst q k (hall k)
    · have hz : L q k = 0 := by simp [hconst q k hk, A, hzero]
      have hp : P q = 0 := Finset.prod_eq_zero (Finset.mem_univ k) hz
      have hmate : matchingProduct w.a w.b q = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ k) hzero
      rw [hp,hmate,map_zero]
  have hpivot : w.pivot ∈ w.contacts := by simp [StrictMatchingSupport.contacts]
  have hη : w.η ≠ 0 := by
    intro he
    have hw := w.strict
    simp [he] at hw
  have hsome : ∃ q : Equiv.Perm ι, matchingProduct w.a w.b q ≠ 0 := by
    by_contra! h
    have hdet := real_signed_determinant w.a w.b U hU
    simp only [h,mul_zero,Finset.sum_const_zero] at hdet
    have hw := w.strict
    rw [← hdet,h w.pivot,mul_zero] at hw
    exact (lt_irrefl _ hw)
  obtain ⟨s,hs⟩ := hsome
  have hsFactor (k : ι) : A s k ≠ 0 := Finset.prod_ne_zero_iff.mp hs k (Finset.mem_univ _)
  have hc : ∃ q : Equiv.Perm ι, (∃ k, ¬ inside q k) ∧
      (∀ k, inside q k → A q k ≠ 0) := by
    by_cases hgood : ∀ k, inside s k
    · let q := s * Equiv.swap i j
      have hij : i ≠ j := fun h => hj (h ▸ hi)
      have hqi : ¬ inside q i := by
        have hg : r.symm (s j) ∈ I ↔ j ∈ I := hgood j
        change ¬ (r.symm (q i) ∈ I ↔ i ∈ I)
        rw [show q i = s j by simp [q,Equiv.Perm.mul_apply],hg]
        exact fun he => hj (he.mpr hi)
      have hqj : ¬ inside q j := by
        have hg : r.symm (s i) ∈ I ↔ i ∈ I := hgood i
        change ¬ (r.symm (q j) ∈ I ↔ j ∈ I)
        rw [show q j = s i by simp [q,Equiv.Perm.mul_apply],hg]
        exact fun he => hj (he.mp hi)
      refine ⟨q,⟨i,hqi⟩,fun k hk => ?_⟩
      have hki : k ≠ i := fun h => hqi (h ▸ hk)
      have hkj : k ≠ j := fun h => hqj (h ▸ hk)
      simpa only [A,q,Equiv.Perm.mul_apply,Equiv.swap_apply_of_ne_of_ne hki hkj] using hsFactor k
    · exact ⟨s,not_forall.mp hgood,fun k _ => hsFactor k⟩
  obtain ⟨q,⟨k,hk⟩,hq⟩ := hc
  have hOne (m : ι) (hm : ¬ inside q m) : (L q m).natDegree = 1 := by
    change ¬ (r.symm (q m) ∈ I ↔ m ∈ I) at hm
    by_cases hl : r.symm (q m) ∈ I <;> by_cases hr : m ∈ I
    · exact False.elim (hm (iff_of_true hl hr))
    · simp [L,D,hl,hr]
    · simp [L,D,hl,hr,Polynomial.natDegree_neg]
    · exact False.elim (hm (iff_of_false hl hr))
  have hnonzero (m : ι) (_ : m ∈ (Finset.univ : Finset ι)) : L q m ≠ 0 := by
    by_cases h : inside q m
    · rw [hconst q m h]
      exact Polynomial.C_ne_zero.mpr (hq m h)
    · intro hz
      have hh := hOne m h
      rw [hz,Polynomial.natDegree_zero] at hh
      exact Nat.zero_ne_one hh
  have hv : (P q).natDegree ≠ 0 := by
    apply Nat.ne_of_gt
    change 0 < (∏ m, L q m).natDegree
    rw [Polynomial.natDegree_prod Finset.univ (L q) hnonzero]
    exact (Nat.zero_lt_one.trans_eq (hOne k hk).symm).trans_le
      (Finset.single_le_sum (f := fun m => (L q m).natDegree)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ k))
  apply w.exists_more_contacts_on_exact_polynomial_profile hU P hbase
    (fun z => ⟨_,_,(hP z).symm⟩)
  · intro z q hq
    simp only [hlocked _ hpivot,hlocked _ hq,Polynomial.eval_C]
  · refine ⟨q,?_⟩
    rw [Polynomial.natDegree_C_mul hη, Polynomial.natDegree_sub, hlocked _ hpivot,
      Polynomial.natDegree_sub_C]
    exact hv

/-- Every balanced cut either meets a nonzero contact edge or completely
severs the vanishing factors of a zero contact. Unlike the full-edge
test, this notices when a crossing zero contact is still identically
zero along the block translation. -/
theorem StrictMatchingSupport.nonzero_contact_or_unprotected_zero_crosses_cut
    {U : Matrix ι ι ℂ} (hU : IsUnitary U) (w : StrictMatchingSupport U)
    (hmax : ∀ v : StrictMatchingSupport U, v.contacts.card ≤ w.contacts.card)
    (r : Equiv.Perm ι) (I : Finset ι) (hI : I.Nonempty) (hIc : ∃ j, j ∉ I) :
    (∃ q ∈ w.contacts, matchingProduct w.a w.b q ≠ 0 ∧
      ∃ k, ¬ (r.symm (q k) ∈ I ↔ k ∈ I)) ∨
    (∃ q ∈ w.contacts, matchingProduct w.a w.b q = 0 ∧
      ∀ k, w.a (q k) + w.b k = 0 → ¬ (r.symm (q k) ∈ I ↔ k ∈ I)) := by
  classical
  by_contra h
  have hl (q : Equiv.Perm ι) (hq : q ∈ w.contacts) :
      (∀ k, r.symm (q k) ∈ I ↔ k ∈ I) ∨
        ∃ k, (r.symm (q k) ∈ I ↔ k ∈ I) ∧ w.a (q k) + w.b k = 0 := by
    by_cases hz : matchingProduct w.a w.b q = 0
    · right
      by_contra hh
      apply h
      right
      exact ⟨q,hq,hz,fun k hk hi => hh ⟨k,hi,hk⟩⟩
    · left
      intro k
      by_contra hh
      exact h (Or.inl ⟨q,hq,hz,k,hh⟩)
  obtain ⟨v,_,_,hv⟩ := w.exists_more_contacts_of_zero_aware_cut hU r I hI hIc hl
  exact (not_lt_of_ge (hmax v)) (Finset.card_lt_card hv)


/-- Zero-aware additive rigidity. Given one chosen preserved vanishing
factor per zero contact, the associated contact-incidence equations have
only the global translation as a solution. This is the component
statement without introducing a separate graph representation. -/
theorem StrictMatchingSupport.additive_rigidity_of_maximal_contacts [Nonempty ι]
    {U : Matrix ι ι ℂ} (hU : IsUnitary U) (w : StrictMatchingSupport U)
    (hmax : ∀ v : StrictMatchingSupport U, v.contacts.card ≤ w.contacts.card)
    (x y : ι → ℂ)
    (hlock : ∀ q ∈ w.contacts,
      (∀ k, x (q k) + y k = 0) ∨
        ∃ k, x (q k) + y k = 0 ∧ w.a (q k) + w.b k = 0) :
    ∃ c : ℂ, (∀ k, x k = c) ∧ (∀ k, y k = -c) := by
  classical
  obtain ⟨r,hr,hrnz⟩ := w.exists_nonzero_contact_of_maximal_count hU hmax
  have hrlock (k : ι) : x (r k) + y k = 0 := by
    rcases hlock r hr with h | ⟨j,_,hj⟩
    · exact h k
    · exact False.elim (hrnz (Finset.prod_eq_zero (Finset.mem_univ j) hj))
  have hk {q : Equiv.Perm ι} {k : ι} (h : x (q k) + y k = 0) :
      y (r.symm (q k)) = y k := by
    have hr' := hrlock (r.symm (q k))
    rw [Equiv.apply_symm_apply] at hr'
    exact add_left_cancel (hr'.trans h.symm)
  obtain ⟨i⟩ := (inferInstance : Nonempty ι)
  have hconst (k : ι) : y k = y i := by
    by_contra hn
    let I := Finset.univ.filter fun j => y j = y i
    have hi : i ∈ I := by simp [I]
    have hki : k ∉ I := by simp [I,hn]
    obtain ⟨v,_,_,hv⟩ := w.exists_more_contacts_of_zero_aware_cut hU r I
      ⟨i,hi⟩ ⟨k,hki⟩ (by
        intro q hq
        rcases hlock q hq with he | ⟨j,hj,hzero⟩
        · exact Or.inl (fun j => by simp only [I,Finset.mem_filter,Finset.mem_univ,true_and,hk (he j)])
        · exact Or.inr ⟨j,by simp only [I,Finset.mem_filter,Finset.mem_univ,true_and,hk hj],hzero⟩)
    exact (not_lt_of_ge (hmax v)) (Finset.card_lt_card hv)
  refine ⟨-y i,fun j => ?_,fun j => by rw [neg_neg,hconst j]⟩
  have h := hrlock (r.symm j)
  simpa only [Equiv.apply_symm_apply,hconst (r.symm j),add_eq_zero_iff_eq_neg] using h

end MOC
