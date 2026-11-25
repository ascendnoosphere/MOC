import MOC.ZhengRectangleContact

/-! A symbolic paired-block support certificate for the eight-label
branch of Zheng's Section 5 (preprint DOI: 10.13140/RG.2.2.36790.25923).
We use complementary pairs, not a list of facets or permutations. -/

open Matrix BigOperators

namespace MOC
namespace ZhengPairedContacts

abbrev Bit4 := Bool × Bool
abbrev Bits := Bool → Bool
abbrev Perm := Equiv.Perm Bit4

def flip (f : Bits) : Perm where
  toFun x := (x.1, if f x.1 then !x.2 else x.2)
  invFun x := (x.1, if f x.1 then !x.2 else x.2)
  left_inv := by rintro ⟨i,j⟩; cases h : f i <;> simp [h]
  right_inv := by rintro ⟨i,j⟩; cases h : f i <;> simp [h]

def exchange : Perm where
  toFun x := (!x.1, x.2)
  invFun x := (!x.1, x.2)
  left_inv := by rintro ⟨i,j⟩; simp
  right_inv := by rintro ⟨i,j⟩; simp

def cross : Perm := Equiv.prodComm Bool Bool

def within (p : Perm) : Prop := ∀ x, (p x).1 = x.1
def across (p : Perm) : Prop := ∀ x, (p x).1 = !x.1

@[simp] theorem flip_fst (f : Bits) (x : Bit4) : (flip f x).1 = x.1 := rfl
@[simp] theorem flip_snd (f : Bits) (x : Bit4) :
    (flip f x).2 = (if f x.1 then !x.2 else x.2) := rfl

@[simp] theorem exchange_fst (x : Bit4) : (exchange x).1 = !x.1 := rfl
@[simp] theorem flip_self (f : Bits) : flip f * flip f = 1 := by
  apply Equiv.ext
  exact (flip f).left_inv

def xor (f g : Bits) : Bits := fun i => if f i then !g i else g i

@[simp] theorem flip_mul (f g : Bits) : flip f * flip g = flip (xor f g) := by
  apply Equiv.ext
  rintro ⟨i,j⟩
  cases hf : f i <;> cases hg : g i <;>
    simp [Equiv.Perm.mul_apply, flip, xor, hf, hg]

theorem flip_comm (f g : Bits) : flip f * flip g = flip g * flip f := by
  rw [flip_mul, flip_mul]
  congr 1
  funext i
  cases hf : f i <;> cases hg : g i <;> simp [xor,hf,hg]

theorem exists_flip_of_within (p : Perm) (hp : within p) : ∃ f, p = flip f := by
  let f (i : Bool) := (p (i,false)).2
  refine ⟨f,?_⟩
  apply Equiv.ext
  rintro ⟨i,j⟩
  refine Prod.ext (by simpa only [flip_fst] using hp (i,j)) ?_
  cases j
  · cases hf : f i <;> simp [flip, hf, f] at hf ⊢
  · have hn : (p (i,true)).2 ≠ (p (i,false)).2 := by
      intro h
      have he := p.injective (Prod.ext ((hp (i,true)).trans (hp (i,false)).symm) h)
      exact Bool.noConfusion (congrArg Prod.snd he)
    change (p (i,true)).2 = if f i then false else true
    change (p (i,true)).2 ≠ f i at hn
    cases hf : f i <;> cases hh : (p (i,true)).2 <;> simp_all

theorem exists_exchange_flip_of_across (p : Perm) (hp : across p) :
    ∃ f, p = exchange * flip f := by
  have he : exchange * exchange = 1 := by
    apply Equiv.ext
    exact exchange.left_inv
  obtain ⟨f,hf⟩ := exists_flip_of_within (exchange * p) (by
    intro x
    simp [Equiv.Perm.mul_apply, hp x])
  exact ⟨f,by rw [← hf, ← mul_assoc, he, one_mul]⟩

/-- If one block maps into one block, its complement maps into the
complementary block, by injectivity. -/
private theorem unmixed (p : Perm) (i : Bool)
    (h : (p (i,false)).1 = (p (i,true)).1) : within p ∨ across p := by
  let c := (p (i,false)).1
  have hi (j : Bool) : (p (i,j)).1 = c := by
    cases j
    · rfl
    · exact h.symm
  have ho (j : Bool) : (p (!i,j)).1 = !c := by
    have hn : (p (!i,j)).1 ≠ c := by
      intro hh
      have hbits : (p (i,false)).2 ≠ (p (i,true)).2 := by
        intro he
        exact Bool.noConfusion (congrArg Prod.snd (p.injective (Prod.ext h he)))
      have h₂ : (p (!i,j)).2 = (p (i,false)).2 ∨
          (p (!i,j)).2 = (p (i,true)).2 := by
        cases hu : (p (i,false)).2 <;> cases hv : (p (i,true)).2 <;>
          cases hw : (p (!i,j)).2 <;> simp_all
      rcases h₂ with he | he
      · have hi' := congrArg Prod.fst (p.injective (Prod.ext (hh.trans (hi false).symm) he))
        cases i <;> contradiction
      · have hi' := congrArg Prod.fst (p.injective (Prod.ext (hh.trans (hi true).symm) he))
        cases i <;> contradiction
    cases hc : c <;> cases hp : (p (!i,j)).1 <;> simp_all
  have hh (k : Bool) : k = i ∨ k = !i := by cases k <;> cases i <;> simp
  by_cases hc : c = i
  · left
    rintro ⟨k,j⟩
    rcases hh k with he | he
    · subst k; exact (hi j).trans hc
    · subst k; exact (ho j).trans (congrArg Bool.not hc)
  · right
    have hc' : c = !i := by
      clear hi ho
      cases i <;> cases h' : c <;> simp_all
    rintro ⟨k,j⟩
    rcases hh k with he | he
    · subst k; exact (hi j).trans hc'
    · subst k; exact (ho j).trans (congrArg Bool.not hc')

/-- A mixed assignment has the two-sided normal form: select one flip
per source block, apply the central exchange, then one per target
block. The construction uses injectivity, not permutation enumeration. -/
theorem normal_form (p : Perm) :
    within p ∨ across p ∨ ∃ f g, p = flip f * cross * flip g := by
  by_cases h : ∃ i, (p (i,false)).1 = (p (i,true)).1
  · obtain ⟨i,hi⟩ := h
    exact (unmixed p i hi).imp id Or.inl
  push_neg at h
  let g (i : Bool) := (p (i,false)).1
  have hg (i j : Bool) : (p (flip g (i,j))).1 = j := by
    have hi := h i
    change g i ≠ (p (i,true)).1 at hi
    cases hg' : g i <;> cases hj : j <;>
      simp_all [flip, g]
  let f (j : Bool) := (p (flip g (false,j))).2
  have hf (i j : Bool) : (flip f (p (flip g (i,j)))).2 = i := by
    rw [flip_snd, hg]
    cases i
    · change (if f j then !(f j) else f j) = false
      cases f j <;> rfl
    · have hn : (p (flip g (true,j))).2 ≠ f j := by
        intro hn
        have he := (flip g).injective (p.injective (Prod.ext ((hg true j).trans (hg false j).symm) hn))
        exact Bool.noConfusion (congrArg Prod.fst he)
      cases hh : f j <;> cases hk : (p (flip g (true,j))).2 <;> simp_all
  have he : flip f * p * flip g = cross := by
    apply Equiv.ext
    rintro ⟨i,j⟩
    change flip f (p (flip g (i,j))) = (j,i)
    exact Prod.ext (hg i j) (hf i j)
  right; right
  refine ⟨f,g,?_⟩
  calc
    p = (flip f * flip f) * p * (flip g * flip g) := by simp only [flip_self, one_mul, mul_one]
    _ = flip f * cross * flip g := by rw [← he]; simp only [mul_assoc]

def axis (i : Bool) : Bits := fun k => k == i

def repair (i j : Bool) : Perm := cross * Equiv.swap (j,!i) (!j,i)

/-- The two missing assignments are exchanged so that the selected
source block maps to the selected target block. -/
private theorem repair_block (i j : Bool) : within (repair i j) ∨ across (repair i j) := by
  by_cases h : i = j
  · left
    subst j
    rintro ⟨k,l⟩
    cases i <;> cases k <;> cases l <;>
      simp [repair, cross, Equiv.Perm.mul_apply, Equiv.swap_apply_def]
  · right
    rintro ⟨k,l⟩
    cases i <;> cases j <;> cases k <;> cases l <;>
      simp_all [repair, cross, Equiv.Perm.mul_apply, Equiv.swap_apply_def]

/-- A mixed difference across the two independent flips is a difference
of block-permuting products. Only two independent bit indices occur. -/
private theorem mixed_identity (a b : Bit4 → ℂ) (i j : Bool) :
    matchingProduct a b cross -
      matchingProduct a b (flip (axis i) * cross) -
      matchingProduct a b (cross * flip (axis j)) +
      matchingProduct a b (flip (axis i) * cross * flip (axis j)) =
    matchingProduct a b (repair i j) -
      matchingProduct a b (flip (axis i) * repair i j) := by
  cases i <;> cases j <;>
    simp [matchingProduct, Fintype.prod_prod_type, Fintype.prod_bool, flip, axis, cross,
      repair, Equiv.Perm.mul_apply, Equiv.swap_apply_def] <;> ring

private theorem matchingProduct_comp (a b : Bit4 → ℂ) (f p g : Perm) :
    matchingProduct a b (f * p * g) = matchingProduct (a ∘ f) (b ∘ g.symm) p := by
  simp only [matchingProduct, Equiv.Perm.mul_apply, Function.comp_apply]
  exact Fintype.prod_equiv g _ _ (fun x => by rw [Equiv.symm_apply_apply])

private theorem flip_membership_left (f : Bits) (p : Perm)
    (h : within p ∨ across p) : within (flip f * p) ∨ across (flip f * p) := by
  simpa only [within, across, Equiv.Perm.mul_apply, flip_fst] using h

private theorem flip_membership_right (p : Perm) (g : Bits)
    (h : within p ∨ across p) : within (p * flip g) ∨ across (p * flip g) := by
  rcases h with h | h
  · exact Or.inl (fun x => (h (flip g x)).trans (flip_fst g x))
  · exact Or.inr (fun x => (h (flip g x)).trans (congrArg Bool.not (flip_fst g x)))

-- A table entry is indexed by the two independent block flips.
private def table (a b : Bit4 → ℂ) (η : ℂ) (H : ℝ) (f g : Bits) : ℝ :=
  H - (η * matchingProduct a b (flip f * cross * flip g)).re

private theorem table_adjacent (a b : Bit4 → ℂ) (η : ℂ) (H : ℝ)
    (hD : ∀ p : Perm, within p ∨ across p → (η * matchingProduct a b p).re = H)
    (f g : Bits) (i j : Bool) :
    table a b η H f g - table a b η H (xor f (axis i)) g -
      table a b η H f (xor (axis j) g) +
      table a b η H (xor f (axis i)) (xor (axis j) g) = 0 := by
  let a' := a ∘ flip f
  let b' := b ∘ (flip g).symm
  have hwrap (p : Perm) : matchingProduct a' b' p =
      matchingProduct a b (flip f * p * flip g) := (matchingProduct_comp a b _ p _).symm
  have hD' (p : Perm) (hp : within p ∨ across p) : (η * matchingProduct a' b' p).re = H := by
    rw [hwrap]
    exact hD _ (flip_membership_right _ _ (flip_membership_left _ _ hp))
  have hp := repair_block i j
  have h := congrArg (fun z => (η * z).re) (mixed_identity a' b' i j)
  simp only [mul_sub, mul_add, Complex.sub_re, Complex.add_re,
    hD' _ hp, hD' _ (flip_membership_left _ _ hp), sub_self] at h
  simp only [table, ← flip_mul, mul_assoc, hwrap] at *
  linarith

private theorem xor_comm (f g : Bits) : xor f g = xor g f := by
  funext i
  cases hf : f i <;> cases hg : g i <;> simp [xor,hf,hg]

private theorem eq_of_flip_invariance {R : Type*} (F : Bits → R)
    (h : ∀ g j, F g = F (xor (axis j) g)) (f g : Bits) : F f = F g := by
  let m (i : Bool) := if i then f true else g false
  have h₀ : F f = F m := by
    by_cases he : f false = g false
    · congr 1
      funext i
      cases i <;> simp [m,he]
    · rw [h f false]
      congr 1
      funext i
      cases i
      · cases ha : f false <;> cases hb : g false <;>
          simp [m,axis,xor,ha,hb] at he ⊢
      · simp [m,axis,xor]
  have h₁ : F m = F g := by
    by_cases he : f true = g true
    · congr 1
      funext i
      cases i <;> simp [m,he]
    · rw [h m true]
      congr 1
      funext i
      cases i
      · simp [m,axis,xor]
      · cases ha : f true <;> cases hb : g true <;>
          simp [m,axis,xor,ha,hb] at he ⊢
  exact h₀.trans h₁

private theorem table_rectangle (a b : Bit4 → ℂ) (η : ℂ) (H : ℝ)
    (hD : ∀ p : Perm, within p ∨ across p → (η * matchingProduct a b p).re = H)
    (f f' g g' : Bits) :
    table a b η H f g - table a b η H f' g -
      table a b η H f g' + table a b η H f' g' = 0 := by
  let C := table a b η H
  have hf (f : Bits) (i : Bool) :
      C f g - C (xor (axis i) f) g = C f g' - C (xor (axis i) f) g' := by
    apply eq_of_flip_invariance (fun k => C f k - C (xor (axis i) f) k) _ g g'
    intro k j
    have h := table_adjacent a b η H hD f k i j
    change C f k - C (xor f (axis i)) k -
      C f (xor (axis j) k) + C (xor f (axis i)) (xor (axis j) k) = 0 at h
    rw [xor_comm f (axis i)] at h
    change C f k - C (xor (axis i) f) k = C f (xor (axis j) k) - C (xor (axis i) f) (xor (axis j) k)
    linarith
  have he : C f g - C f g' = C f' g - C f' g' := by
    apply eq_of_flip_invariance (fun k => C k g - C k g') _ f f'
    intro k i
    change C k g - C k g' = C (xor (axis i) k) g - C (xor (axis i) k) g'
    linarith [hf k i]
  change C f g - C f' g - C f g' + C f' g' = 0
  linarith

def block : Finset Bit4 := {(false,false),(false,true)}
def mixedSet (f : Bits) : Finset Bit4 := Finset.univ.image (fun i : Bool => (i,f i))

private theorem mem_block (x : Bit4) : x ∈ block ↔ x.1 = false := by
  obtain ⟨i,j⟩ := x
  cases i <;> cases j <;> simp [block]

private theorem mem_mixedSet (f : Bits) (x : Bit4) : x ∈ mixedSet f ↔ x.2 = f x.1 := by
  obtain ⟨i,j⟩ := x
  cases i <;> simp [mixedSet, Prod.mk.injEq, eq_comm]

private theorem mixedSet_injective : Function.Injective mixedSet := by
  intro f g h
  funext i
  have hm : (i,f i) ∈ mixedSet g := by
    rw [← h, mem_mixedSet]
  exact (mem_mixedSet g (i,f i)).mp hm

private theorem map_of_preserves (p : Perm) (hp : within p ∨ across p) :
    (block.map p.toEmbedding = block ∨ block.map p.toEmbedding = blockᶜ) ∧
      ∀ f : Bits, (mixedSet f).map p.toEmbedding ≠ block := by
  have he (x : Bit4) : x ∈ block.map p.toEmbedding ↔ (p.symm x).1 = false := by
    rw [Finset.mem_map_equiv, mem_block]
  rcases hp with hp | hp
  · refine ⟨Or.inl ?_,?_⟩
    · ext x
      rw [he, mem_block, ← hp (p.symm x), p.apply_symm_apply]
    · intro f h
      have ht : p (true, f true) ∈ block := h ▸ Finset.mem_map.mpr
        ⟨_, (mem_mixedSet f _).mpr rfl, rfl⟩
      rw [mem_block, hp] at ht
      contradiction
  · refine ⟨Or.inr ?_,?_⟩
    · ext x
      have hpx := hp (p.symm x)
      rw [p.apply_symm_apply] at hpx
      rw [he, Finset.mem_compl, mem_block, hpx]
      cases (p.symm x).1 <;> simp
    · intro f h
      have ht : p (false, f false) ∈ block := h ▸ Finset.mem_map.mpr
        ⟨_, (mem_mixedSet f _).mpr rfl, rfl⟩
      rw [mem_block, hp] at ht
      contradiction

private theorem mixedSet_ne_block (f : Bits) : mixedSet f ≠ block := by
  simpa using (map_of_preserves 1 (Or.inl (fun _ => rfl))).2 f

private theorem mixedSet_ne_compl (f : Bits) : mixedSet f ≠ blockᶜ := by
  intro h
  have ht : (false, f false) ∈ blockᶜ := h ▸ (mem_mixedSet f _).mpr rfl
  exact (Finset.mem_compl.mp ht) ((mem_block _).mpr rfl)

private theorem map_block_mixed (f g : Bits) :
    block.map (flip f * cross * flip g).toEmbedding = mixedSet f := by
  ext ⟨i,j⟩
  rw [mem_mixedSet]
  constructor
  · intro h
    obtain ⟨⟨k,l⟩,hk,he⟩ := Finset.mem_map.mp h
    have hk' := (mem_block (k,l)).mp hk
    cases hk'
    simp [flip, cross, Equiv.Perm.mul_apply] at he
    obtain ⟨rfl,rfl⟩ := he
    rfl
  · intro h
    change j = f i at h
    subst j
    refine Finset.mem_map.mpr ⟨(false,if g false then !i else i),(mem_block _).mpr rfl,?_⟩
    cases hg : g false <;> simp [flip, cross, Equiv.Perm.mul_apply,hg]

private theorem map_mixed_eq_block_iff (f g k : Bits) :
    (mixedSet k).map (flip f * cross * flip g).toEmbedding = block ↔ k = g := by
  let p : Perm := flip f * cross * flip g
  have hflip (z : Bits) : (flip z)⁻¹ = flip z := inv_eq_of_mul_eq_one_right (flip_self z)
  have hcross : cross⁻¹ = cross := by
    apply inv_eq_of_mul_eq_one_right
    apply Equiv.ext
    rintro ⟨i,j⟩
    rfl
  have hp : p⁻¹ = flip g * cross * flip f := by
    simp only [p, _root_.mul_inv_rev, hflip, hcross, mul_assoc]
  have hleft : p.toEmbedding.trans (p⁻¹).toEmbedding = Function.Embedding.refl _ := by
    apply Function.Embedding.ext
    intro x
    exact p.symm_apply_apply x
  have hright : (p⁻¹).toEmbedding.trans p.toEmbedding = Function.Embedding.refl _ := by
    apply Function.Embedding.ext
    intro x
    exact p.apply_symm_apply x
  have h := map_block_mixed g f
  rw [← hp] at h
  change (mixedSet k).map p.toEmbedding = block ↔ _
  constructor
  · intro he
    have hh := congrArg (Finset.map (p⁻¹).toEmbedding) he
    rw [h] at hh
    have hh' : mixedSet k = mixedSet g := by
      simpa only [Finset.map_map, hleft, Finset.map_refl] using hh
    exact mixedSet_injective hh'
  · rintro rfl
    rw [← h]
    simp only [Finset.map_map, hright, Finset.map_refl]

/-- If all block-preserving and block-exchanging assignments are on
an exposed line, the whole gap function has a nonnegative minor
decomposition. This statement allows an arbitrary complex unitary. -/
theorem support_of_block_contacts (a b : Bit4 → ℂ) (η : ℂ) (H : ℝ)
    (U : Matrix Bit4 Bit4 ℂ) (hU : IsUnitary U)
    (hD : ∀ p : Perm, within p ∨ across p → (η * matchingProduct a b p).re = H)
    (hmax : ∀ p : Perm, (η * matchingProduct a b p).re ≤ H) :
    (η * determinantValue a b U).re ≤ H := by
  classical
  let C := table a b η H
  have hC (f g : Bits) : 0 ≤ C f g := sub_nonneg.mpr (hmax _)
  obtain ⟨m,_,hm⟩ := Finset.exists_min_image (Finset.univ : Finset (Bits × Bits))
    (fun fg => C fg.1 fg.2) ⟨(fun _ => false,fun _ => false),Finset.mem_univ _⟩
  let u (f : Bits) := C f m.2 - C m.1 m.2
  let v (g : Bits) := C m.1 g
  let I : Bits ⊕ Bits → Finset Bit4 := Sum.elim mixedSet (fun _ => block)
  let J : Bits ⊕ Bits → Finset Bit4 := Sum.elim (fun _ => block) mixedSet
  let w : Bits ⊕ Bits → ℝ := Sum.elim u v
  have hw (k : Bits ⊕ Bits) : 0 ≤ w k := by
    cases k with
    | inl f => exact sub_nonneg.mpr (hm (f,m.2) (Finset.mem_univ _))
    | inr g => exact hC _ _
  have hdecomp (p : Perm) : H - (η * matchingProduct a b p).re =
      ∑ k, if (J k).map p.toEmbedding = I k then w k else 0 := by
    rw [Fintype.sum_sum_type]
    change _ = (∑ f, if block.map p.toEmbedding = mixedSet f then u f else 0) +
      ∑ g, if (mixedSet g).map p.toEmbedding = block then v g else 0
    rcases normal_form p with hp | hp | ⟨f,g,rfl⟩
    · have ⟨hb,hmix⟩ := map_of_preserves p (Or.inl hp)
      have hn (i : Bits) : block.map p.toEmbedding ≠ mixedSet i :=
        hb.elim (fun h he => mixedSet_ne_block i (he.symm.trans h))
          (fun h he => mixedSet_ne_compl i (he.symm.trans h))
      simp [hD p (Or.inl hp), hn, hmix]
    · have ⟨hb,hmix⟩ := map_of_preserves p (Or.inr hp)
      have hn (i : Bits) : block.map p.toEmbedding ≠ mixedSet i :=
        hb.elim (fun h he => mixedSet_ne_block i (he.symm.trans h))
          (fun h he => mixedSet_ne_compl i (he.symm.trans h))
      simp [hD p (Or.inr hp), hn, hmix]
    · rw [map_block_mixed]
      simp_rw [mixedSet_injective.eq_iff, map_mixed_eq_block_iff]
      simp only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      change C f g = C f m.2 - C m.1 m.2 + C m.1 g
      have he := table_rectangle a b η H hD f m.1 g m.2
      change C f g - C m.1 g - C f m.2 + C m.1 m.2 = 0 at he
      linarith
  have hs := support_of_minor_gap_decomposition a b (-η) (-H) U hU I J w hw (fun p => by
    simpa only [neg_mul, Complex.neg_re, neg_sub_neg] using hdecomp p)
  simpa only [neg_mul, Complex.neg_re, neg_le_neg_iff] using hs

private def label : Fin 4 ≃ Bit4 where
  toFun := ![(false,false),(true,false),(false,true),(true,true)]
  invFun x := if x.2 then (if x.1 then 3 else 2) else (if x.1 then 1 else 0)
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by rintro ⟨i,j⟩; cases i <;> cases j <;> rfl

open ZhengRectangleContact

private theorem marked_exchange : label.symm.permCongr exchange = s₇ := by
  apply Equiv.ext
  intro i
  fin_cases i <;> rfl

private theorem marked_flip (f : Bits) :
    label.symm.permCongr (flip f) =
      (if f false then s₁₄ else 1) * (if f true then s₅ else 1) := by
  apply Equiv.ext
  intro i
  fin_cases i <;>
    cases hf : f false <;> cases ht : f true <;>
    simp [Equiv.permCongr_apply, label, flip, hf, ht, Equiv.Perm.mul_apply,
      s₁₄, s₅, Equiv.swap_apply_def]

private theorem matchingProduct_label (a b : Fin 4 → ℂ) (p : Perm) :
    matchingProduct (a ∘ label.symm) (b ∘ label.symm) p =
      matchingProduct a b (label.symm.permCongr p) := by
  simp only [matchingProduct, Function.comp_apply]
  exact Fintype.prod_equiv label.symm _ _ (fun x => by simp only [Equiv.permCongr_apply,
    Equiv.symm_symm, Equiv.apply_symm_apply])

/-- The paired branch of Zheng's T85 pattern cannot be a strict witness.
The certificate uses only the eight supporting labels and works for
complex unitary mixers as well as real orthogonal ones. -/
theorem not_paired_witness {U : Matrix (Fin 4) (Fin 4) ℂ} (hU : IsUnitary U)
    (w : StrictMatchingSupport U) (hT : Pattern w) (h₂₃ : s₂₃ ∈ w.contacts) : False := by
  classical
  have ⟨hp,h₅,h₇,h₉,h₁₄,h₁₈⟩ := hT
  have h₁₆ := ((collision_or_paired_contact w hT).resolve_left (fun h => h.1 h₂₃)).2
  have hid : (1 : Perm4) ∈ w.contacts := by simp [StrictMatchingSupport.contacts,hp]
  have hm (p : Perm) (h : within p ∨ across p) : label.symm.permCongr p ∈ w.contacts := by
    have hmul (x y : Perm) :
        label.symm.permCongr (x*y) =
          label.symm.permCongr x * label.symm.permCongr y := by
      apply Equiv.ext
      intro i
      simp only [Equiv.permCongr_apply, Equiv.Perm.mul_apply, Equiv.symm_apply_apply]
    have h7_5 : s₇ * s₅ = s₁₈ := by
      apply Equiv.ext; intro i; fin_cases i <;> rfl
    have h7_14 : s₇ * s₁₄ = s₉ := by
      apply Equiv.ext; intro i; fin_cases i <;> rfl
    have h7_16 : s₇ * s₁₆ = s₂₃ := by
      apply Equiv.ext; intro i; fin_cases i <;> rfl
    rcases h with h | h
    · obtain ⟨f,rfl⟩ := exists_flip_of_within p h
      rw [marked_flip]
      cases hf : f false <;> cases ht : f true <;>
        simp only [hf,ht,Bool.false_eq_true,if_false,if_true,mul_one,one_mul]
      · exact hid
      · exact h₅
      · exact h₁₄
      · exact h₁₆
    · obtain ⟨f,rfl⟩ := exists_exchange_flip_of_across p h
      rw [hmul, marked_exchange, marked_flip]
      cases hf : f false <;> cases ht : f true <;>
        simp only [hf,ht,Bool.false_eq_true,if_false,if_true,mul_one,one_mul,
          h7_5,h7_14]
      · exact h₇
      · exact h₁₈
      · exact h₉
      · exact h7_16.symm ▸ h₂₃
  have hs := support_of_block_contacts (w.a ∘ label.symm) (w.b ∘ label.symm) w.η
    (w.η * matchingProduct w.a w.b w.pivot).re
    (U.submatrix label.symm label.symm) (unitary_reindex label.symm label.symm hU)
    (fun p h => by rw [matchingProduct_label]; exact (Finset.mem_filter.mp (hm p h)).2)
    (fun p => by rw [matchingProduct_label]; exact w.maximal _)
  rw [determinantValue_reindex] at hs
  exact (not_lt_of_ge hs) w.strict

/-- The entire six-label problem reduces to at least eight contacts at
positive upper height. The branch reduction makes no conditional use
of the supplementary tables. -/
theorem reduce_to_positive_eight {U : Matrix (Fin 4) (Fin 4) ℂ} (hU : IsUnitary U)
    (w : StrictMatchingSupport U) (hT : Pattern w) :
    ∃ v : StrictMatchingSupport U, Pattern v ∧ 8 ≤ v.contacts.card ∧
      s₂₃ ∉ v.contacts ∧ 0 < (v.η * matchingProduct v.a v.b 1).re ∧
      matchingProduct v.a v.b s₇ = matchingProduct v.a v.b 1 := by
  obtain ⟨v,hV,hcard⟩ := exists_eight_contacts hU w hT
  have hinactive : s₂₃ ∉ v.contacts := not_paired_witness hU v hV
  have hcollision := ((collision_or_paired_contact v hV).resolve_right
    (fun h => hinactive h.1)).2
  exact ⟨v,hV,hcard,hinactive,positive_height_of_inactive_23 hU v hV hinactive,
    sub_eq_zero.mp hcollision⟩

end ZhengPairedContacts
end MOC
