import MOC.ZhengRectangleContact

/-! Symbolic block certificates and the one-defect reduction for Zheng's
Section 5 (preprint DOI: 10.13140/RG.2.2.36790.25923).
Subset-image evaluation uses the squared-minor identity (Merikoski and
Virtanen, DOI: 10.1016/0024-3795(89)90709-X).
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

-- Every matching-product gap obeys the same local relation, including at zero factors.
private def BlockLaw (F : Perm → ℝ) : Prop :=
  ∀ f g : Bits, ∀ i j : Bool,
    F (flip f * cross * flip g) - F (flip (xor f (axis i)) * cross * flip g) -
      F (flip f * cross * flip (xor (axis j) g)) +
      F (flip (xor f (axis i)) * cross * flip (xor (axis j) g)) =
    F (flip f * repair i j * flip g) - F (flip f * flip (axis i) * repair i j * flip g)

private theorem gap_blockLaw (a b : Bit4 → ℂ) (η : ℂ) (H : ℝ) :
    BlockLaw (fun p => H - (η * matchingProduct a b p).re) := by
  intro f g i j
  let a' := a ∘ flip f
  let b' := b ∘ (flip g).symm
  have hwrap (p : Perm) : matchingProduct a' b' p =
      matchingProduct a b (flip f * p * flip g) := (matchingProduct_comp a b _ p _).symm
  have h := congrArg (fun z => (η * z).re) (mixed_identity a' b' i j)
  simp only [mul_sub, mul_add, Complex.sub_re, Complex.add_re, hwrap] at h
  simp only [← flip_mul, mul_assoc] at h ⊢
  linarith

private theorem BlockLaw.sub_mul {F E : Perm → ℝ} (hF : BlockLaw F) (hE : BlockLaw E)
    (d : ℝ) : BlockLaw (fun p => F p - d * E p) := by
  intro f g i j
  dsimp only
  linear_combination (hF f g i j) - d * (hE f g i j)

def event (K J : Finset Bit4) (p : Perm) : ℝ :=
  if K.map p.toEmbedding = J then 1 else 0

private theorem event_blockLaw (K J : Finset Bit4) (hcard : K.card = J.card) :
    BlockLaw (event K J) := by
  classical
  let a (i : Bit4) : ℂ := if i ∈ J then 1 else 0
  let b (j : Bit4) : ℂ := if j ∈ K then 0 else 1
  have hprod (p : Perm) : (matchingProduct a b p).re = event K J p := by
    by_cases hp : K.map p.toEmbedding = J
    · have hmem (j : Bit4) : p j ∈ J ↔ j ∈ K := by
        rw [← hp, Finset.mem_map_equiv, Equiv.symm_apply_apply]
      have hone (j : Bit4) : a (p j) + b j = 1 := by
        by_cases hj : j ∈ K
        · simp [a,b,hj,(hmem j).mpr hj]
        · simp [a,b,hj,mt (hmem j).mp hj]
      simp [matchingProduct, hone, event, hp]
    · have hmissing : ∃ j ∈ K, p j ∉ J := by
        by_contra! hn
        apply hp
        apply Finset.eq_of_subset_of_card_le
        · intro i hi
          obtain ⟨j,hj,rfl⟩ := Finset.mem_map.mp hi
          exact hn j hj
        · simp [hcard]
      obtain ⟨j,hj,hpj⟩ := hmissing
      have hz : a (p j) + b j = 0 := by simp [a,b,hj,hpj]
      have hzero : matchingProduct a b p = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ j) hz
      simp [hzero,event,hp]
  have h := gap_blockLaw a b (-1) 0
  simpa only [neg_one_mul, Complex.neg_re, zero_sub, neg_neg, hprod] using h

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

private theorem table_rectangle_of_blockLaw (F : Perm → ℝ) (hF : BlockLaw F)
    (hD : ∀ p : Perm, within p ∨ across p → F p = 0)
    (f f' g g' : Bits) :
    F (flip f * cross * flip g) - F (flip f' * cross * flip g) -
      F (flip f * cross * flip g') + F (flip f' * cross * flip g') = 0 := by
  let C (f g : Bits) := F (flip f * cross * flip g)
  have adjacent (f g : Bits) (i j : Bool) :
      C f g - C (xor f (axis i)) g - C f (xor (axis j) g) +
        C (xor f (axis i)) (xor (axis j) g) = 0 := by
    have hp := repair_block i j
    have h₁ := hD (flip f * repair i j * flip g)
      (flip_membership_right _ _ (flip_membership_left _ _ hp))
    have h₂ := hD (flip f * flip (axis i) * repair i j * flip g)
      (flip_membership_right _ _ (by
        rw [mul_assoc]
        exact flip_membership_left _ _ (flip_membership_left _ _ hp)))
    have h := hF f g i j
    rw [h₁,h₂,sub_self] at h
    exact h
  have hf (f : Bits) (i : Bool) :
      C f g - C (xor (axis i) f) g = C f g' - C (xor (axis i) f) g' := by
    apply eq_of_flip_invariance (fun k => C f k - C (xor (axis i) f) k) _ g g'
    intro k j
    have h := adjacent f k i j
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

private def blockTarget : Bits ⊕ Bits → Finset Bit4 := Sum.elim mixedSet (fun _ => block)
private def blockSource : Bits ⊕ Bits → Finset Bit4 := Sum.elim (fun _ => block) mixedSet

private theorem nonnegative_block_decomposition (F : Perm → ℝ) (hF : BlockLaw F)
    (hD : ∀ p : Perm, within p ∨ across p → F p = 0)
    (hC : ∀ f g : Bits, 0 ≤ F (flip f * cross * flip g)) :
    ∃ w : Bits ⊕ Bits → ℝ, (∀ k, 0 ≤ w k) ∧
      ∀ p : Perm, F p = ∑ k,
        if (blockSource k).map p.toEmbedding = blockTarget k then w k else 0 := by
  classical
  let C (f g : Bits) := F (flip f * cross * flip g)
  obtain ⟨m,_,hm⟩ := Finset.exists_min_image (Finset.univ : Finset (Bits × Bits))
    (fun fg => C fg.1 fg.2) ⟨(fun _ => false,fun _ => false),Finset.mem_univ _⟩
  let u (f : Bits) := C f m.2 - C m.1 m.2
  let v (g : Bits) := C m.1 g
  let w : Bits ⊕ Bits → ℝ := Sum.elim u v
  have hw (k : Bits ⊕ Bits) : 0 ≤ w k := by
    cases k with
    | inl f => exact sub_nonneg.mpr (hm (f,m.2) (Finset.mem_univ _))
    | inr g => exact hC _ _
  have hdecomp (p : Perm) : F p =
      ∑ k, if (blockSource k).map p.toEmbedding = blockTarget k then w k else 0 := by
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
      have he := table_rectangle_of_blockLaw F hF hD f m.1 g m.2
      change C f g - C m.1 g - C f m.2 + C m.1 m.2 = 0 at he
      linarith
  exact ⟨w, hw, hdecomp⟩

/-- A single two-subset image event can account for nonzero block gaps.
If subtracting it leaves all crossing gaps nonnegative, there is a
nonnegative minor certificate for the original support direction. -/
theorem support_of_single_block_defect (a b : Bit4 → ℂ) (η : ℂ) (H : ℝ)
    (U : Matrix Bit4 Bit4 ℂ) (hU : IsUnitary U) (K J : Finset Bit4)
    (hcard : K.card = J.card) (d : ℝ) (hd : 0 ≤ d)
    (hD : ∀ p : Perm, within p ∨ across p →
      H - (η * matchingProduct a b p).re = d * event K J p)
    (hC : ∀ f g : Bits, let p := flip f * cross * flip g
      d * event K J p ≤ H - (η * matchingProduct a b p).re) :
    (η * determinantValue a b U).re ≤ H := by
  classical
  let F (p : Perm) := H - (η * matchingProduct a b p).re - d * event K J p
  have hF : BlockLaw F := (gap_blockLaw a b η H).sub_mul (event_blockLaw K J hcard) d
  obtain ⟨w,hw,hdec⟩ := nonnegative_block_decomposition F hF
    (fun p hp => sub_eq_zero.mpr (hD p hp)) (fun f g => sub_nonneg.mpr (hC f g))
  let I : (Bits ⊕ Bits) ⊕ Unit → Finset Bit4 := Sum.elim blockTarget (fun _ => J)
  let J' : (Bits ⊕ Bits) ⊕ Unit → Finset Bit4 := Sum.elim blockSource (fun _ => K)
  let w' : (Bits ⊕ Bits) ⊕ Unit → ℝ := Sum.elim w (fun _ => d)
  have hw' (k : (Bits ⊕ Bits) ⊕ Unit) : 0 ≤ w' k := by
    cases k with
    | inl x => exact hw x
    | inr _ => exact hd
  have hs := support_of_minor_gap_decomposition a b (-η) (-H) U hU I J' w' hw'
    (fun p => by
      simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, I, J', w',
        Finset.univ_unique, Finset.sum_singleton, neg_mul, Complex.neg_re, neg_sub_neg]
      have he := hdec p
      change H - (η * matchingProduct a b p).re - d * event K J p = _ at he
      rw [Fintype.sum_sum_type] at he
      by_cases hm : K.map p.toEmbedding = J
      · simp only [event, hm, if_true, mul_one] at he ⊢
        linarith
      · simp only [event, hm, if_false, mul_zero, sub_zero, add_zero] at he ⊢
        exact he)
  simpa only [neg_mul, Complex.neg_re, neg_le_neg_iff] using hs

/-- The gap table after removing the common block defect is additive. -/
theorem single_block_defect_rectangle (a b : Bit4 → ℂ) (η : ℂ) (H : ℝ)
    (K J : Finset Bit4) (hcard : K.card = J.card) (d : ℝ)
    (hD : ∀ p : Perm, within p ∨ across p →
      H - (η * matchingProduct a b p).re = d * event K J p) :
    let R (f g : Bits) := let p := flip f * cross * flip g
      H - (η * matchingProduct a b p).re - d * event K J p
    ∀ f f' g g', R f g - R f' g - R f g' + R f' g' = 0 := by
  exact table_rectangle_of_blockLaw _ ((gap_blockLaw a b η H).sub_mul (event_blockLaw K J hcard) d)
    (fun p hp => sub_eq_zero.mpr (hD p hp))

/-- If all block-permuting assignments are contacts, take the block defect to be zero. -/
theorem support_of_block_contacts (a b : Bit4 → ℂ) (η : ℂ) (H : ℝ)
    (U : Matrix Bit4 Bit4 ℂ) (hU : IsUnitary U)
    (hD : ∀ p : Perm, within p ∨ across p → (η * matchingProduct a b p).re = H)
    (hmax : ∀ p : Perm, (η * matchingProduct a b p).re ≤ H) :
    (η * determinantValue a b U).re ≤ H := by
  apply support_of_single_block_defect a b η H U hU block block rfl 0 le_rfl
  · intro p hp
    simp [hD p hp]
  · intro f g
    simpa using sub_nonneg.mpr (hmax (flip f * cross * flip g))

def label : Fin 4 ≃ Bit4 where
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

def innerLow : Finset Bit4 := {(false,false),(true,false)}
def innerHigh : Finset Bit4 := {(false,true),(true,true)}

private theorem mem_innerLow (x : Bit4) : x ∈ innerLow ↔ x.2 = false := by
  obtain ⟨i,j⟩ := x
  cases i <;> cases j <;> simp [innerLow]

private theorem mem_innerHigh (x : Bit4) : x ∈ innerHigh ↔ x.2 = true := by
  obtain ⟨i,j⟩ := x
  cases i <;> cases j <;> simp [innerHigh]

private theorem inner_card : innerLow.card = innerHigh.card := by
  simp [innerLow, innerHigh]

private theorem inner_event_iff (p : Perm) :
    innerLow.map p.toEmbedding = innerHigh ↔ ∀ x : Bit4, (p x).2 = !x.2 := by
  constructor
  · intro h x
    have hm : (p x).2 = true ↔ x.2 = false := by
      rw [← mem_innerHigh, ← h, Finset.mem_map_equiv, p.symm_apply_apply, mem_innerLow]
    cases hx : x.2
    · exact hm.mpr hx
    · have hn : (p x).2 ≠ true := fun he => Bool.noConfusion (hx.symm.trans (hm.mp he))
      cases hy : (p x).2 <;> simp_all
  · intro h
    ext x
    rw [Finset.mem_map_equiv, mem_innerLow, mem_innerHigh]
    have he := h (p.symm x)
    rw [p.apply_symm_apply] at he
    cases hx : (p.symm x).2 <;> simp_all

private theorem inner_flip_iff (f : Bits) :
    innerLow.map (flip f).toEmbedding = innerHigh ↔ f false = true ∧ f true = true := by
  rw [inner_event_iff]
  constructor
  · intro h
    have h₀ := h (false,false)
    have h₁ := h (true,false)
    simpa [flip] using And.intro h₀ h₁
  · rintro ⟨h₀,h₁⟩ ⟨i,j⟩
    cases i <;> simp [flip,h₀,h₁]

private theorem inner_exchange_iff (f : Bits) :
    innerLow.map (exchange * flip f).toEmbedding = innerHigh ↔ f false = true ∧ f true = true := by
  rw [inner_event_iff, ← inner_flip_iff, inner_event_iff]
  rfl

/-- The two inactive block assignments of Zheng's unpaired branch are the
restriction of a single two-subset image event to the block group. -/
private theorem t85_block_defect {U : Matrix (Fin 4) (Fin 4) ℂ} (w : StrictMatchingSupport U)
    (hT : Pattern w) (p : Perm) (hb : within p ∨ across p) :
    (w.η * matchingProduct w.a w.b w.pivot).re -
      (w.η * matchingProduct (w.a ∘ label.symm) (w.b ∘ label.symm) p).re =
      ((w.η * matchingProduct w.a w.b w.pivot).re -
        (w.η * matchingProduct w.a w.b s₂₃).re) * event innerLow innerHigh p := by
  classical
  obtain ⟨hp,h₅,h₇,h₉,h₁₄,h₁₈⟩ := hT
  have contact (q : Perm4) (hq : q ∈ w.contacts) :
      (w.η * matchingProduct w.a w.b w.pivot).re -
        (w.η * matchingProduct w.a w.b q).re = 0 :=
    sub_eq_zero.mpr (Finset.mem_filter.mp hq).2.symm
  have h16 : (w.η * matchingProduct w.a w.b s₁₆).re =
      (w.η * matchingProduct w.a w.b s₂₃).re := by
    have he := same_projected_gap w ⟨hp,h₅,h₇,h₉,h₁₄,h₁₈⟩
    simp only [diff, mul_sub, Complex.sub_re] at he
    linarith
  have hmul (x y : Perm) :
      label.symm.permCongr (x*y) = label.symm.permCongr x * label.symm.permCongr y := by
    apply Equiv.ext
    intro i
    simp only [Equiv.permCongr_apply, Equiv.Perm.mul_apply, Equiv.symm_apply_apply]
  have h7_5 : s₇ * s₅ = s₁₈ := by
    apply Equiv.ext; intro i; fin_cases i <;> rfl
  have h7_14 : s₇ * s₁₄ = s₉ := by
    apply Equiv.ext; intro i; fin_cases i <;> rfl
  have h7_16 : s₇ * s₁₆ = s₂₃ := by
    apply Equiv.ext; intro i; fin_cases i <;> rfl
  rcases hb with hb | hb
  · obtain ⟨f,rfl⟩ := exists_flip_of_within p hb
    rw [matchingProduct_label, marked_flip]
    simp only [event, inner_flip_iff]
    cases hf : f false <;> cases ht : f true <;>
      simp only [hf,ht,Bool.false_eq_true,true_and,false_and,if_true,if_false,
        one_mul,mul_one,mul_zero]
    · rw [← hp, sub_self]
    · exact contact _ h₅
    · exact contact _ h₁₄
    · change _ - (w.η * matchingProduct w.a w.b s₁₆).re = _
      rw [h16]
  · obtain ⟨f,rfl⟩ := exists_exchange_flip_of_across p hb
    rw [matchingProduct_label, hmul, marked_exchange, marked_flip]
    simp only [event, inner_exchange_iff]
    cases hf : f false <;> cases ht : f true <;>
      simp only [hf,ht,Bool.false_eq_true,true_and,false_and,if_true,if_false,
        one_mul,mul_one,mul_zero,h7_5,h7_14]
    · exact contact _ h₇
    · exact contact _ h₁₈
    · exact contact _ h₉
    · change _ - (w.η * matchingProduct w.a w.b (s₇ * s₁₆)).re = _
      rw [h7_16]

/-- For a strict T85 witness, one of the two crossing assignments of the
defect event must have a strictly smaller deficit than the block defect. -/
theorem crossing_below_block_defect {U : Matrix (Fin 4) (Fin 4) ℂ}
    (hU : IsUnitary U) (w : StrictMatchingSupport U) (hT : Pattern w) :
    ∃ f g : Bits, let p := flip f * cross * flip g
      innerLow.map p.toEmbedding = innerHigh ∧
      (w.η * matchingProduct w.a w.b s₂₃).re <
        (w.η * matchingProduct w.a w.b (label.symm.permCongr p)).re := by
  let H := (w.η * matchingProduct w.a w.b w.pivot).re
  let d := H - (w.η * matchingProduct w.a w.b s₂₃).re
  by_contra! hn
  have hs := support_of_single_block_defect (w.a ∘ label.symm) (w.b ∘ label.symm) w.η H
    (U.submatrix label.symm label.symm) (unitary_reindex label.symm label.symm hU)
    innerLow innerHigh inner_card d (sub_nonneg.mpr (w.maximal _)) (t85_block_defect w hT)
    (fun f g => by
      dsimp only
      rw [matchingProduct_label]
      by_cases he : innerLow.map (flip f * cross * flip g).toEmbedding = innerHigh
      · simp only [event, he, if_true, mul_one, d]
        exact sub_le_sub_left (le_of_not_gt (fun hlt => hn f g ⟨he,hlt⟩)) _
      · simp only [event, he, if_false, mul_zero]
        exact sub_nonneg.mpr (w.maximal _))
  rw [determinantValue_reindex] at hs
  exact (not_lt_of_ge hs) w.strict

/-- In the crossing table the defect event selects exactly two cells,
in different rows and different columns. -/
theorem inner_cross_iff (f g : Bits) :
    innerLow.map (flip f * cross * flip g).toEmbedding = innerHigh ↔
      f = axis (g false) ∧ g true = !(g false) := by
  rw [inner_event_iff]
  constructor
  · intro h
    have h₀ := h (false,false)
    have h₁ := h (false,true)
    have h₂ := h (true,false)
    have ha : f = axis (g false) := by
      funext i
      cases hg : g false <;> cases i
      · simpa [flip, cross, Equiv.Perm.mul_apply, axis, hg] using h₀
      · simpa [flip, cross, Equiv.Perm.mul_apply, axis, hg] using h₁
      · simpa [flip, cross, Equiv.Perm.mul_apply, axis, hg] using h₁
      · simpa [flip, cross, Equiv.Perm.mul_apply, axis, hg] using h₀
    refine ⟨ha,?_⟩
    rw [ha] at h₂
    cases hg : g false <;> cases ht : g true <;>
      simp_all [flip, cross, Equiv.Perm.mul_apply, axis]
  · rintro ⟨rfl,ht⟩ ⟨i,j⟩
    cases hg : g false <;> cases i <;> cases j <;>
      simp_all [flip,cross,Equiv.Perm.mul_apply,axis]

private theorem inner_cross_same_row {f g g' : Bits}
    (h : innerLow.map (flip f * cross * flip g).toEmbedding = innerHigh)
    (h' : innerLow.map (flip f * cross * flip g').toEmbedding = innerHigh) : g = g' := by
  obtain ⟨hf,ht⟩ := (inner_cross_iff f g).mp h
  obtain ⟨hf',ht'⟩ := (inner_cross_iff f g').mp h'
  have he : g false = g' false := by
    have he := congrFun (hf.symm.trans hf') false
    cases h₀ : g false <;> cases h₁ : g' false <;> simp_all [axis]
  funext i
  cases i
  · exact he
  · rw [ht,ht',he]

private theorem inner_cross_same_col {f f' g : Bits}
    (h : innerLow.map (flip f * cross * flip g).toEmbedding = innerHigh)
    (h' : innerLow.map (flip f' * cross * flip g).toEmbedding = innerHigh) : f = f' :=
  ((inner_cross_iff f g).mp h).1.trans ((inner_cross_iff f' g).mp h').1.symm

/-- The crossing indicator and the two kinds of crossing marginals use only
two-subset images. -/
def crossingEvent (p : Perm) : ℝ :=
  1 - event block block p - event block blockᶜ p

def rowEvent (f : Bits) (p : Perm) : ℝ := event block (mixedSet f) p

def colEvent (g : Bits) (p : Perm) : ℝ := event (mixedSet g) block p

/-- Up to index relabeling, the only possibly negative signed contribution. -/
def starObjective (f₀ g₀ : Bits) (p : Perm) : ℝ :=
  event innerLow innerHigh p + crossingEvent p - rowEvent f₀ p - colEvent g₀ p

/-- Exact decomposition of the whole gap, not just its zero set. Once a
marked cell is below the block gap, every coefficient in this decomposition
is nonnegative. Only the indicated star objective may evaluate negatively. -/
theorem gap_eq_marked_star_sum {U : Matrix (Fin 4) (Fin 4) ℂ}
    (w : StrictMatchingSupport U) (hT : Pattern w) (f₀ g₀ : Bits)
    (hm : innerLow.map (flip f₀ * cross * flip g₀).toEmbedding = innerHigh) :
    let D : Perm → ℝ := fun p => (w.η * matchingProduct w.a w.b w.pivot).re -
      (w.η * matchingProduct w.a w.b (label.symm.permCongr p)).re
    let C : Bits → Bits → ℝ := fun f g => D (flip f * cross * flip g)
    let d := (w.η * matchingProduct w.a w.b w.pivot).re -
      (w.η * matchingProduct w.a w.b s₂₃).re
    ∀ p : Perm, D p = C f₀ g₀ * event innerLow innerHigh p +
      (d - C f₀ g₀) * starObjective f₀ g₀ p +
      (∑ f : Bits, if f = f₀ then 0 else C f g₀ * rowEvent f p) +
      (∑ g : Bits, if g = g₀ then 0 else C f₀ g * colEvent g p) := by
  classical
  intro D C d p
  have hD (p : Perm) (hb : within p ∨ across p) : D p = d * event innerLow innerHigh p := by
    simpa only [D,d,matchingProduct_label] using t85_block_defect w hT p hb
  have rect (f g : Bits) :
      C f g - d * event innerLow innerHigh (flip f * cross * flip g) -
        (C f₀ g - d * event innerLow innerHigh (flip f₀ * cross * flip g)) -
        (C f g₀ - d * event innerLow innerHigh (flip f * cross * flip g₀)) +
        (C f₀ g₀ - d * event innerLow innerHigh (flip f₀ * cross * flip g₀)) = 0 := by
    simpa only [C,D,d,matchingProduct_label] using
      single_block_defect_rectangle (w.a ∘ label.symm) (w.b ∘ label.symm) w.η
        ((w.η * matchingProduct w.a w.b w.pivot).re) innerLow innerHigh inner_card d
        (t85_block_defect w hT) f f₀ g g₀
  by_cases hb : within p ∨ across p
  · obtain ⟨hmap,hcol⟩ := map_of_preserves p hb
    have hrow (f : Bits) : block.map p.toEmbedding ≠ mixedSet f :=
      hmap.elim (fun h he => mixedSet_ne_block f (he.symm.trans h))
        (fun h he => mixedSet_ne_compl f (he.symm.trans h))
    have hX : crossingEvent p = 0 := by
      rcases hmap with hh | hh
      · have hne : block.map p.toEmbedding ≠ blockᶜ := by
          rw [hh]
          intro he
          have h₀ : (false, false) ∈ block := by simp [block]
          exact (Finset.mem_compl.mp (he ▸ h₀)) h₀
        simp [crossingEvent,event,hh,hne]
      · have hne : block.map p.toEmbedding ≠ block := by
          rw [hh]
          intro he
          have h₀ : (false, false) ∈ block := by simp [block]
          exact (Finset.mem_compl.mp (he.symm ▸ h₀)) h₀
        simp [crossingEvent,event,hh,hne]
    rw [hD p hb]
    simp [starObjective,hX,rowEvent,colEvent,event,hrow,hcol]
    split_ifs <;> ring
  · obtain ⟨f,g,rfl⟩ := (normal_form p).resolve_left (fun h => hb (Or.inl h)) |>
      (fun h => h.resolve_left (fun h => hb (Or.inr h)))
    have hX : crossingEvent (flip f * cross * flip g) = 1 := by
      simp [crossingEvent,event,map_block_mixed,mixedSet_ne_block,mixedSet_ne_compl]
    have hrow (j : Bits) : rowEvent j (flip f * cross * flip g) = if f = j then 1 else 0 := by
      simp [rowEvent,event,map_block_mixed,mixedSet_injective.eq_iff]
    have hcol (j : Bits) : colEvent j (flip f * cross * flip g) = if j = g then 1 else 0 := by
      simp [colEvent,event,map_mixed_eq_block_iff]
    have hs₁ : (∑ j : Bits, if j = f₀ then 0 else C j g₀ * rowEvent j (flip f * cross * flip g)) =
        if f = f₀ then 0 else C f g₀ := by
      calc
        _ = ∑ j : Bits, if f = j then (if j = f₀ then 0 else C j g₀) else 0 := by
          apply Finset.sum_congr rfl
          intro j _
          rw [hrow]
          by_cases h : f = j <;> by_cases h' : j = f₀ <;> simp [h,h']
        _ = _ := by simp
    have hs₂ : (∑ j : Bits, if j = g₀ then 0 else C f₀ j * colEvent j (flip f * cross * flip g)) =
        if g = g₀ then 0 else C f₀ g := by
      calc
        _ = ∑ j : Bits, if j = g then (if j = g₀ then 0 else C f₀ j) else 0 := by
          apply Finset.sum_congr rfl
          intro j _
          rw [hcol]
          by_cases h : j = g <;> by_cases h' : j = g₀ <;> simp [h,h']
        _ = _ := by simp
    rw [hs₁,hs₂]
    simp only [starObjective,hX,hrow,hcol]
    change C f g = _
    by_cases hf : f = f₀ <;> by_cases hg : g = g₀
    · subst f; subst g
      simp [event,hm]
    · subst f
      have hnot : innerLow.map (flip f₀ * cross * flip g).toEmbedding ≠ innerHigh :=
        fun h => hg (inner_cross_same_row h hm)
      simp [event,hnot,hg,Ne.symm hg]
    · subst g
      have hnot : innerLow.map (flip f * cross * flip g₀).toEmbedding ≠ innerHigh :=
        fun h => hf (inner_cross_same_col h hm)
      simp [event,hnot,hf]
    · have hnot₁ : innerLow.map (flip f₀ * cross * flip g).toEmbedding ≠ innerHigh :=
        fun h => hg (inner_cross_same_row h hm)
      have hnot₂ : innerLow.map (flip f * cross * flip g₀).toEmbedding ≠ innerHigh :=
        fun h => hf (inner_cross_same_col h hm)
      have he := rect f g
      have hE₁ : event innerLow innerHigh (flip f₀ * cross * flip g) = 0 := if_neg hnot₁
      have hE₂ : event innerLow innerHigh (flip f * cross * flip g₀) = 0 := if_neg hnot₂
      have hE₀ : event innerLow innerHigh (flip f₀ * cross * flip g₀) = 1 := if_pos hm
      simp only [hE₁,hE₂,hE₀,mul_zero,mul_one,sub_zero] at he
      simp only [hf,hg,Ne.symm hg,if_false,sub_zero]
      linear_combination he

/-- Every remaining T85 witness has a crossing row and column containing
all its crossing contacts. Off that row and column the gap is bounded
below by the positive deficit shortfall at their intersection. -/
theorem crossing_contacts_confined {U : Matrix (Fin 4) (Fin 4) ℂ}
    (hU : IsUnitary U) (w : StrictMatchingSupport U) (hT : Pattern w) :
    let gap := fun f g : Bits => (w.η * matchingProduct w.a w.b w.pivot).re -
      (w.η * matchingProduct w.a w.b (label.symm.permCongr (flip f * cross * flip g))).re
    let d := (w.η * matchingProduct w.a w.b w.pivot).re -
      (w.η * matchingProduct w.a w.b s₂₃).re
    ∃ f₀ g₀ : Bits, innerLow.map (flip f₀ * cross * flip g₀).toEmbedding = innerHigh ∧
      gap f₀ g₀ < d ∧
      ∀ f g : Bits, f ≠ f₀ → g ≠ g₀ → d - gap f₀ g₀ ≤ gap f g := by
  dsimp only
  obtain ⟨f₀,g₀,hm,hlt⟩ := crossing_below_block_defect hU w hT
  let H := (w.η * matchingProduct w.a w.b w.pivot).re
  let d := H - (w.η * matchingProduct w.a w.b s₂₃).re
  let z (f g : Bits) := (w.η * matchingProduct w.a w.b
     (label.symm.permCongr (flip f * cross * flip g))).re
  let E (f g : Bits) := event innerLow innerHigh (flip f * cross * flip g)
  have hz (f g : Bits) : z f g ≤ H := w.maximal _
  have hd : 0 ≤ d := sub_nonneg.mpr (w.maximal _)
  refine ⟨f₀,g₀,hm,?_,?_⟩
  · exact sub_lt_sub_left hlt _
  intro f g hf hg
  have hm₁ : innerLow.map (flip f * cross * flip g₀).toEmbedding ≠ innerHigh :=
    fun h => hf (inner_cross_same_col h hm)
  have hm₂ : innerLow.map (flip f₀ * cross * flip g).toEmbedding ≠ innerHigh :=
    fun h => hg (inner_cross_same_row h hm)
  have hr := single_block_defect_rectangle (w.a ∘ label.symm) (w.b ∘ label.symm) w.η H
    innerLow innerHigh inner_card d (t85_block_defect w hT) f f₀ g g₀
  simp only [matchingProduct_label] at hr
  change H - z f g - d * E f g - (H - z f₀ g - d * E f₀ g) -
    (H - z f g₀ - d * E f g₀) + (H - z f₀ g₀ - d * E f₀ g₀) = 0 at hr
  have hE : 0 ≤ E f g := by dsimp [E,event]; split_ifs <;> positivity
  have hE₁ : E f g₀ = 0 := if_neg hm₁
  have hE₂ : E f₀ g = 0 := if_neg hm₂
  have hE₀ : E f₀ g₀ = 1 := if_pos hm
  simp only [hE₁,hE₂,hE₀,mul_zero,mul_one,sub_zero] at hr
  change d - (H - z f₀ g₀) ≤ H - z f g
  linarith [hz f g₀, hz f₀ g, mul_nonneg hd hE]

/-- The paired branch of Zheng's T85 pattern cannot be a strict witness.
The certificate uses only the eight supporting labels and works for
complex unitary mixers as well as real orthogonal ones. -/
theorem not_paired_witness {U : Matrix (Fin 4) (Fin 4) ℂ} (hU : IsUnitary U)
    (w : StrictMatchingSupport U) (hT : Pattern w) (h₂₃ : s₂₃ ∈ w.contacts) : False := by
  obtain ⟨f,g,hm,hlt⟩ := crossing_below_block_defect hU w hT
  have hheight := (Finset.mem_filter.mp h₂₃).2
  rw [hheight] at hlt
  exact (not_lt_of_ge (w.maximal _)) hlt

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
