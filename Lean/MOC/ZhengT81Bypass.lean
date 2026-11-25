import MOC.ZhengPairedContacts

/-! The eight-contact star reduction bypasses Zheng's T81 dependency
in the proof of T85 (preprint DOI: 10.13140/RG.2.2.36790.25923, Table 3).
The two arms arise by independent transpositions of the two blocks. -/

namespace MOC
namespace ZhengT81Bypass

open Matrix ZhengPairedContacts ZhengRectangleContact Equiv.Perm

abbrev P := Equiv.Perm (Fin 4)

def rowsCols (f g : Bits) : P :=
  label.symm.permCongr (ZhengPairedContacts.flip f * cross * ZhengPairedContacts.flip g)

/-- The center with paper label 17, using inverse assignment convention. -/
def center₁₇ : P := rowsCols (axis true) (axis false)

private def pull (p : Perm) : P := label.symm.permCongr p

private theorem pull_mul (p q : Perm) : pull (p*q) = pull p * pull q := by
  apply Equiv.ext
  intro i
  simp only [pull, Equiv.permCongr_apply, Equiv.Perm.mul_apply, Equiv.symm_apply_apply]

private theorem pull_inv (p : Perm) : pull p⁻¹ = (pull p)⁻¹ := by
  symm
  apply inv_eq_of_mul_eq_one_left
  rw [← pull_mul, inv_mul_cancel]
  apply Equiv.ext
  simp [pull]

private theorem flip_pull (f : Bits) :
    pull (ZhengPairedContacts.flip f) = (if f false then s₁₄ else 1) * (if f true then s₅ else 1) := by
  apply Equiv.ext
  intro i
  fin_cases i <;>
    cases hf : f false <;> cases ht : f true <;>
    simp [pull, Equiv.permCongr_apply, label, ZhengPairedContacts.flip, hf, ht, Equiv.Perm.mul_apply,
      s₁₄, s₅, Equiv.swap_apply_def]

private theorem exchange_pull : pull exchange = s₇ := by
  apply Equiv.ext
  intro i
  fin_cases i <;> rfl

private theorem cross_inv : cross⁻¹ = cross := by rfl
private theorem flip_inv (f : Bits) : (ZhengPairedContacts.flip f)⁻¹ = ZhengPairedContacts.flip f := by rfl

private theorem rowsCols_inv (f g : Bits) : (rowsCols f g)⁻¹ = rowsCols g f := by
  change (pull _)⁻¹ = pull _
  rw [← pull_inv]
  simp only [_root_.mul_inv_rev, cross_inv, flip_inv, mul_assoc]

/-- The two marked centers are inverse permutations. -/
theorem center_or_inverse (f g : Bits)
    (h : innerLow.map (ZhengPairedContacts.flip f * cross * ZhengPairedContacts.flip g).toEmbedding = innerHigh) :
    rowsCols f g = center₁₇ ∨ rowsCols f g = center₁₇⁻¹ := by
  obtain ⟨hf,hg⟩ := (inner_cross_iff f g).mp h
  cases hx : g false
  · right
    have he : g = axis true := by funext i; cases i <;> simp [axis,hx,hg]
    rw [hf,hx,he,center₁₇,rowsCols_inv]
  · left
    have he : g = axis false := by funext i; cases i <;> simp [axis,hx,hg]
    rw [hf,hx,he,center₁₇]

private theorem block_labels (p : Perm) (h : within p ∨ across p) :
    pull p ∈ ({1,s₅,s₇,s₉,s₁₄,s₁₈,s₁₆,s₂₃} : Finset P) := by
  have h75 : s₇ * s₅ = s₁₈ := by apply Equiv.ext; intro i; fin_cases i <;> rfl
  have h714 : s₇ * s₁₄ = s₉ := by apply Equiv.ext; intro i; fin_cases i <;> rfl
  have h716 : s₇ * s₁₆ = s₂₃ := by apply Equiv.ext; intro i; fin_cases i <;> rfl
  have hFlip : s₁₄ * s₅ = s₁₆ := rfl
  rcases h with h | h
  · obtain ⟨f,rfl⟩ := exists_flip_of_within p h
    rw [flip_pull]
    cases hf : f false <;> cases hg : f true <;> simp [hf,hg,hFlip]
  · obtain ⟨f,rfl⟩ := exists_exchange_flip_of_across p h
    rw [pull_mul, exchange_pull, flip_pull]
    cases hf : f false <;> cases hg : f true <;>
      simp [hf,hg,hFlip,h75,h714,h716]

/-- Multiplying by any nontrivial within-block ZhengPairedContacts.flip gives an arm label. -/
def Arm (m q : P) : Prop :=
  ∃ k ∈ ({s₅,s₁₄,s₁₆} : Finset P), q = m*k ∨ q = k*m

private theorem pull_flip_mem (f : Bits) (h : pull (ZhengPairedContacts.flip f) ≠ 1) :
    pull (ZhengPairedContacts.flip f) ∈ ({s₅,s₁₄,s₁₆} : Finset P) := by
  rw [flip_pull] at h ⊢
  cases hf : f false <;> cases hg : f true <;> simp_all [show s₁₄ * s₅ = s₁₆ from rfl]

private theorem arm_of_row {f g g₀ : Bits} (h : rowsCols f g ≠ rowsCols f g₀) :
    Arm (rowsCols f g₀) (rowsCols f g) := by
  let k := ZhengPairedContacts.flip g₀ * ZhengPairedContacts.flip g
  have hk : rowsCols f g = rowsCols f g₀ * pull k := by
    change pull (ZhengPairedContacts.flip f * cross * ZhengPairedContacts.flip g) = pull (ZhengPairedContacts.flip f * cross * ZhengPairedContacts.flip g₀) * pull k
    rw [← pull_mul]
    congr 1
    dsimp [k]
    simp only [mul_assoc, ← mul_assoc (ZhengPairedContacts.flip g₀) (ZhengPairedContacts.flip g₀), flip_self,one_mul]
  have hne : pull k ≠ 1 := fun he => h (by simpa only [he,mul_one] using hk)
  have hn' : pull (ZhengPairedContacts.flip (xor g₀ g)) ≠ 1 := by
    simpa only [k,flip_mul] using hne
  have hk' := pull_flip_mem (xor g₀ g) hn'
  exact ⟨pull k, by simpa only [k,flip_mul] using hk', Or.inl hk⟩

private theorem arm_of_col {f f₀ g : Bits} (h : rowsCols f g ≠ rowsCols f₀ g) :
    Arm (rowsCols f₀ g) (rowsCols f g) := by
  let k := ZhengPairedContacts.flip f * ZhengPairedContacts.flip f₀
  have hk : rowsCols f g = pull k * rowsCols f₀ g := by
    change pull (ZhengPairedContacts.flip f * cross * ZhengPairedContacts.flip g) = pull k * pull (ZhengPairedContacts.flip f₀ * cross * ZhengPairedContacts.flip g)
    rw [← pull_mul]
    congr 1
    dsimp [k]
    simp only [mul_assoc, ← mul_assoc (ZhengPairedContacts.flip f₀) (ZhengPairedContacts.flip f₀), flip_self,one_mul]
  have hne : pull k ≠ 1 := fun he => h (by simpa only [he,one_mul] using hk)
  have hn' : pull (ZhengPairedContacts.flip (xor f f₀)) ≠ 1 := by
    simpa only [k,flip_mul] using hne
  have hk' := pull_flip_mem (xor f f₀) hn'
  exact ⟨pull k, by simpa only [k,flip_mul] using hk', Or.inr hk⟩

private theorem blockFlip_inv (k : P) (hk : k ∈ ({s₅,s₁₄,s₁₆} : Finset P)) :
    k⁻¹ = k := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hk
  rcases hk with rfl | rfl | rfl <;> apply Equiv.ext <;> intro i <;>
    fin_cases i <;> rfl

private theorem arm_inverse {m q : P} (h : Arm m⁻¹ q) : Arm m q⁻¹ := by
  obtain ⟨k,hk,h | h⟩ := h
  · refine ⟨k,hk,Or.inr ?_⟩
    rw [h,_root_.mul_inv_rev,inv_inv,blockFlip_inv k hk]
  · refine ⟨k,hk,Or.inl ?_⟩
    rw [h,_root_.mul_inv_rev,inv_inv,blockFlip_inv k hk]


/-- The six original T85 contacts. -/
def core : Finset P := {1,s₅,s₇,s₉,s₁₄,s₁₈}

private theorem core_card_le : core.card ≤ 6 := by
  unfold core
  have h6 := Finset.card_insert_le s₁₄ ({s₁₈} : Finset P)
  have h5 := Finset.card_insert_le s₉ ({s₁₄,s₁₈} : Finset P)
  have h4 := Finset.card_insert_le s₇ ({s₉,s₁₄,s₁₈} : Finset P)
  have h3 := Finset.card_insert_le s₅ ({s₇,s₉,s₁₄,s₁₈} : Finset P)
  have h2 := Finset.card_insert_le (1 : P) ({s₅,s₇,s₉,s₁₄,s₁₈} : Finset P)
  rw [Finset.card_singleton] at h6
  omega

/-- All contacts come from the six original contacts or the selected star. -/
theorem every_contact_in_core_or_star {U : Matrix (Fin 4) (Fin 4) ℂ}
    (hU : IsUnitary U) (w : StrictMatchingSupport U) (hT : Pattern w) :
    ∃ m : P, (m = center₁₇ ∨ m = center₁₇⁻¹) ∧
      ∀ q ∈ w.contacts, q ∈ core ∨ q = m ∨ Arm m q := by
  classical
  obtain ⟨f₀,g₀,hm,hlt,hstar⟩ := crossing_contacts_confined hU w hT
  let q₀ := rowsCols f₀ g₀
  refine ⟨q₀,center_or_inverse f₀ g₀ hm,?_⟩
  intro q hq
  by_cases hc : q ∈ core
  · exact Or.inl hc
  by_cases hne : q = q₀
  · exact Or.inr (Or.inl hne)
  right
  right
  have hinactive : s₂₃ ∉ w.contacts := not_paired_witness hU w hT
  have h16 : s₁₆ ∉ w.contacts := by
    intro h
    have he := same_projected_gap w hT
    let H := (w.η * matchingProduct w.a w.b w.pivot).re
    let Z := fun p => (w.η * matchingProduct w.a w.b p).re
    have hh : Z s₁₆ = H := (Finset.mem_filter.mp h).2
    have he' : Z s₁₆ - Z 1 = Z s₂₃ - Z 1 := by
      simpa only [diff, mul_sub, Complex.sub_re] using he
    have hx : Z s₂₃ = H := by linarith
    exact hinactive (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hx⟩)
  let p := label.permCongr q
  have hp : pull p = q := by
    apply Equiv.ext
    intro i
    simp [pull, p, Equiv.permCongr_apply]
  have hout : ¬(within p ∨ across p) := by
    intro h
    have hi := block_labels p h
    rw [hp] at hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hc (by simp [core])
    · exact hc (by simp [core])
    · exact hc (by simp [core])
    · exact hc (by simp [core])
    · exact hc (by simp [core])
    · exact hc (by simp [core])
    · exact h16 hq
    · exact hinactive hq
  obtain ⟨f,g,hfg⟩ := (normal_form p).resolve_left (fun he => hout (Or.inl he))
    |>.resolve_left (fun he => hout (Or.inr he))
  have hqfg : q = rowsCols f g := hp.symm.trans (congrArg pull hfg)
  have hline : f = f₀ ∨ g = g₀ := by
    by_cases hf : f = f₀
    · exact Or.inl hf
    by_cases hg : g = g₀
    · exact Or.inr hg
    exfalso
    have hs := hstar f g hf hg
    have hz := (Finset.mem_filter.mp hq).2
    dsimp only at hs hlt
    change _ - _ ≤ _ - (w.η * matchingProduct w.a w.b (rowsCols f g)).re at hs
    rw [← hqfg, hz, sub_self] at hs
    linarith
  rw [hqfg] at hne ⊢
  rcases hline with rfl | rfl
  · exact arm_of_row hne
  · exact arm_of_col hne

/-- At eight or more supporting labels, a T85 witness reaches a noncentral
arm, in one of the two inverse orientations. In paper labels the arm is
{1,4,6,11,12,15}; the exceptional label 17 is not needed. -/
theorem exists_noncentral_contact {U : Matrix (Fin 4) (Fin 4) ℂ}
    (hU : IsUnitary U) (w : StrictMatchingSupport U) (hT : Pattern w)
    (hcard : 8 ≤ w.contacts.card) :
    ∃ q ∈ w.contacts, Arm center₁₇ q ∨ Arm center₁₇ q⁻¹ := by
  classical
  obtain ⟨m,hm,hh⟩ := every_contact_in_core_or_star hU w hT
  have hs : (insert m core).card ≤ 7 :=
    (Finset.card_insert_le _ _).trans (by have := core_card_le; omega)
  have hn : ¬ w.contacts ⊆ insert m core := fun hsub => by
    have h := Finset.card_le_card hsub
    omega
  obtain ⟨q,hq,hnq⟩ := Finset.not_subset.mp hn
  have harm : Arm m q := by
    rcases hh q hq with h | h | h
    · exact (hnq (Finset.mem_insert_of_mem h)).elim
    · exact (hnq (h.symm ▸ Finset.mem_insert_self _ _)).elim
    · exact h
  rcases hm with hc | hc
  · exact ⟨q,hq,Or.inl (hc ▸ harm)⟩
  · exact ⟨q,hq,Or.inr (arm_inverse (hc ▸ harm))⟩

/-- The transferable version: every strict T85 witness produces a strict
witness with the same mixer and an arm contact. -/
theorem reduce_t85_to_noncentral_contact {U : Matrix (Fin 4) (Fin 4) ℂ}
    (hU : IsUnitary U) (w : StrictMatchingSupport U) (hT : Pattern w) :
    ∃ v : StrictMatchingSupport U, Pattern v ∧
      ∃ q ∈ v.contacts, Arm center₁₇ q ∨ Arm center₁₇ q⁻¹ := by
  obtain ⟨v,hV,hcard,_,_,_⟩ := reduce_to_positive_eight hU w hT
  exact ⟨v,hV,exists_noncentral_contact hU v hV hcard⟩

/-- Paper label 17 in the forward, row-to-column convention. -/
theorem center17_paper : (⇑(center₁₇⁻¹) : Fin 4 → Fin 4) = ![2,3,1,0] := by
  funext i
  fin_cases i <;> rfl

/-- The right and left arms of the normalized star are the six substitutions
of one of the two transpositions, or their product, in the center tuple. -/
theorem arm_paper_labels (q : P) (hq : Arm center₁₇ q) :
    (⇑q⁻¹ : Fin 4 → Fin 4) = ![0,1,3,2] ∨
    (⇑q⁻¹ : Fin 4 → Fin 4) = ![0,3,1,2] ∨
    (⇑q⁻¹ : Fin 4 → Fin 4) = ![1,0,2,3] ∨
    (⇑q⁻¹ : Fin 4 → Fin 4) = ![1,3,2,0] ∨
    (⇑q⁻¹ : Fin 4 → Fin 4) = ![2,0,1,3] ∨
    (⇑q⁻¹ : Fin 4 → Fin 4) = ![2,1,3,0] := by
  obtain ⟨k,hk,he⟩ := hq
  simp only [Finset.mem_insert, Finset.mem_singleton] at hk
  rcases hk with rfl | rfl | rfl <;> rcases he with rfl | rfl
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by funext i; fin_cases i <;> rfl)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by funext i; fin_cases i <;> rfl)))))
  · exact Or.inr (Or.inl (by funext i; fin_cases i <;> rfl))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (by funext i; fin_cases i <;> rfl))))
  · exact Or.inl (by funext i; fin_cases i <;> rfl)
  · exact Or.inr (Or.inr (Or.inl (by funext i; fin_cases i <;> rfl)))

/-- The four arm labels whose boundary is a T55 relabeling. -/
def T55Arm (q : P) : Prop :=
  (⇑q⁻¹ : Fin 4 → Fin 4) = ![0,3,1,2] ∨
  (⇑q⁻¹ : Fin 4 → Fin 4) = ![1,3,2,0] ∨
  (⇑q⁻¹ : Fin 4 → Fin 4) = ![2,0,1,3] ∨
  (⇑q⁻¹ : Fin 4 → Fin 4) = ![2,1,3,0]

private theorem arm_split (q : P) (h : Arm center₁₇ q) :
    T55Arm q ∨ q = Equiv.swap 2 3 ∨ q = Equiv.swap 0 1 := by
  have hswap1 : (⇑((Equiv.swap (2 : Fin 4) 3)⁻¹) : Fin 4 → Fin 4) =
      ![0,1,3,2] := by funext i; fin_cases i <;> rfl
  have hswap6 : (⇑((Equiv.swap (0 : Fin 4) 1)⁻¹) : Fin 4 → Fin 4) =
      ![1,0,2,3] := by funext i; fin_cases i <;> rfl
  have hperm {p r : P} (he : (⇑p⁻¹ : Fin 4 → Fin 4) = ⇑r⁻¹) : p = r :=
    inv_injective (Equiv.ext (congrFun he))
  rcases arm_paper_labels q h with h1 | h4 | h6 | h11 | h12 | h15
  · exact Or.inr (Or.inl (hperm (h1.trans hswap1.symm)))
  · exact Or.inl (Or.inl h4)
  · exact Or.inr (Or.inr (hperm (h6.trans hswap6.symm)))
  · exact Or.inl (Or.inr (Or.inl h11))
  · exact Or.inl (Or.inr (Or.inr (Or.inl h12)))
  · exact Or.inl (Or.inr (Or.inr (Or.inr h15)))

private theorem two_extras_of_card (C : Finset P) (p q : P) (hbig : 8 ≤ C.card)
    (hsub : C ⊆ insert p (insert q core)) : p ∈ C ∧ q ∈ C := by
  classical
  have hsmall (r : P) : (insert r core).card ≤ 7 :=
    (Finset.card_insert_le _ _).trans (by have := core_card_le; omega)
  constructor
  · by_contra hp
    have hs : C ⊆ insert q core := fun r hr =>
      (Finset.mem_insert.mp (hsub hr)).resolve_left (fun he => hp (he ▸ hr))
    have h := (Finset.card_le_card hs).trans (hsmall q)
    omega
  · by_contra hq
    have hs : C ⊆ insert p core := by
      intro r hr
      rcases Finset.mem_insert.mp (hsub hr) with he | he
      · exact Finset.mem_insert.mpr (Or.inl he)
      rcases Finset.mem_insert.mp he with he | he
      · exact (hq (he ▸ hr)).elim
      · exact Finset.mem_insert_of_mem he
    have h := (Finset.card_le_card hs).trans (hsmall p)
    omega

/-- If no T55 arm appears in the chosen orientation, eight contacts
force its center and exactly one of the two T40 splits. -/
theorem narrow_t85_cases_at_eight {U : Matrix (Fin 4) (Fin 4) ℂ}
    (hU : IsUnitary U) (w : StrictMatchingSupport U) (hT : Pattern w)
    (hcard : 8 ≤ w.contacts.card) :
    ∃ m : P, (m = center₁₇ ∨ m = center₁₇⁻¹) ∧
      ((∃ q ∈ w.contacts,
        (m = center₁₇ ∧ T55Arm q) ∨ (m = center₁₇⁻¹ ∧ T55Arm q⁻¹)) ∨
      (w.contacts.card = 8 ∧ m ∈ w.contacts ∧
        ((Equiv.swap (2 : Fin 4) 3 ∈ w.contacts ∧ Equiv.swap (0 : Fin 4) 1 ∉ w.contacts) ∨
         (Equiv.swap (0 : Fin 4) 1 ∈ w.contacts ∧ Equiv.swap (2 : Fin 4) 3 ∉ w.contacts)))) := by
  classical
  obtain ⟨m,hm,hcover⟩ := every_contact_in_core_or_star hU w hT
  refine ⟨m,hm,?_⟩
  by_cases h55 : ∃ q ∈ w.contacts,
      (m = center₁₇ ∧ T55Arm q) ∨ (m = center₁₇⁻¹ ∧ T55Arm q⁻¹)
  · exact Or.inl h55
  right
  let l₁ : P := Equiv.swap 2 3
  let l₆ : P := Equiv.swap 0 1
  have hself1 : l₁⁻¹ = l₁ := by apply Equiv.ext; intro i; fin_cases i <;> rfl
  have hself6 : l₆⁻¹ = l₆ := by apply Equiv.ext; intro i; fin_cases i <;> rfl
  have hc (q : P) (hq : q ∈ w.contacts) : q ∈ core ∨ q = m ∨ q = l₁ ∨ q = l₆ := by
    rcases hcover q hq with he | he | he
    · exact Or.inl he
    · exact Or.inr (Or.inl he)
    right; right
    rcases hm with hm | hm
    · rcases arm_split q (hm ▸ he) with he | he
      · exact (h55 ⟨q,hq,Or.inl ⟨hm,he⟩⟩).elim
      · exact he
    · rcases arm_split q⁻¹ (arm_inverse (hm ▸ he)) with he | he | he
      · exact (h55 ⟨q,hq,Or.inr ⟨hm,he⟩⟩).elim
      · have he' : q⁻¹ = l₁ := he
        exact Or.inl (by rw [← hself1, ← he', inv_inv])
      · have he' : q⁻¹ = l₆ := he
        exact Or.inr (by rw [← hself6, ← he', inv_inv])
  have hcount (l : P) (hsub : w.contacts ⊆ insert m (insert l core)) : w.contacts.card = 8 := by
    have hc := Finset.card_le_card hsub
    have hA := Finset.card_insert_le m (insert l core)
    have hB := Finset.card_insert_le l core
    have hC := core_card_le
    omega
  rcases one_split_inactive_of_inactive_23 hU w hT (not_paired_witness hU w hT) with h6 | h1
  · have hsub : w.contacts ⊆ insert m (insert l₁ core) := by
      intro q hq
      rcases hc q hq with h | h | h | h
      · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h)
      · exact Finset.mem_insert.mpr (Or.inl h)
      · exact Finset.mem_insert_of_mem (Finset.mem_insert.mpr (Or.inl h))
      · exact ((show l₆ ∉ w.contacts from h6) (h ▸ hq)).elim
    obtain ⟨hm,hl⟩ := two_extras_of_card _ m l₁ hcard hsub
    exact ⟨hcount l₁ hsub,hm,Or.inl ⟨hl,h6⟩⟩
  · have hsub : w.contacts ⊆ insert m (insert l₆ core) := by
      intro q hq
      rcases hc q hq with h | h | h | h
      · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h)
      · exact Finset.mem_insert.mpr (Or.inl h)
      · exact ((show l₁ ∉ w.contacts from h1) (h ▸ hq)).elim
      · exact Finset.mem_insert_of_mem (Finset.mem_insert.mpr (Or.inl h))
    obtain ⟨hm,hl⟩ := two_extras_of_card _ m l₆ hcard hsub
    exact ⟨hcount l₆ hsub,hm,Or.inr ⟨hl,h1⟩⟩

private theorem matching_swap (a b : Fin 4 → ℂ) (q : P) :
    matchingProduct b a q = matchingProduct a b q⁻¹ := by
  change matchingProduct b a q = matchingProduct a b q.symm
  rw [matchingProduct_inverse]
  simp [matchingProduct, add_comm]

private theorem determinant_swap (a b : Fin 4 → ℂ) {U : Matrix (Fin 4) (Fin 4) ℂ}
    (hU : IsUnitary U) :
    determinantValue b a Uᴴ = determinantValue a b U := by
  simpa [determinantValue, add_comm] using
    (determinantValue_relative b a U (1 : Matrix (Fin 4) (Fin 4) ℂ) hU).symm

def adjointWitness {U : Matrix (Fin 4) (Fin 4) ℂ} (hU : IsUnitary U)
    (w : StrictMatchingSupport U) : StrictMatchingSupport Uᴴ where
  a := w.b
  b := w.a
  η := w.η
  pivot := w.pivot⁻¹
  maximal q := by
    rw [matching_swap w.a w.b q, matching_swap w.a w.b w.pivot⁻¹,inv_inv]
    exact w.maximal _
  strict := by
    rw [matching_swap w.a w.b w.pivot⁻¹,inv_inv,determinant_swap w.a w.b hU]
    exact w.strict

private theorem adjoint_contact {U : Matrix (Fin 4) (Fin 4) ℂ} (hU : IsUnitary U)
    (w : StrictMatchingSupport U) (q : P) :
    q ∈ (adjointWitness hU w).contacts ↔ q⁻¹ ∈ w.contacts := by
  simp only [StrictMatchingSupport.contacts, Finset.mem_filter, Finset.mem_univ, true_and]
  change (w.η * matchingProduct w.b w.a q).re =
    (w.η * matchingProduct w.b w.a w.pivot⁻¹).re ↔ _
  rw [matching_swap w.a w.b q, matching_swap w.a w.b w.pivot⁻¹,inv_inv]

private theorem adjoint_pattern {U : Matrix (Fin 4) (Fin 4) ℂ} (hU : IsUnitary U)
    (w : StrictMatchingSupport U) (hT : Pattern w) : Pattern (adjointWitness hU w) := by
  obtain ⟨hp,h5,h7,h9,h14,h18⟩ := hT
  have I5 : s₅⁻¹ = s₅ := by apply Equiv.ext; intro i; fin_cases i <;> rfl
  have I7 : s₇⁻¹ = s₇ := by apply Equiv.ext; intro i; fin_cases i <;> rfl
  have I9 : s₉⁻¹ = s₁₈ := by apply Equiv.ext; intro i; fin_cases i <;> rfl
  have I14 : s₁₄⁻¹ = s₁₄ := by apply Equiv.ext; intro i; fin_cases i <;> rfl
  have I18 : s₁₈⁻¹ = s₉ := by apply Equiv.ext; intro i; fin_cases i <;> rfl
  refine ⟨by simp [adjointWitness,hp], ?_, ?_, ?_, ?_, ?_⟩
  · exact (adjoint_contact hU w _).mpr (I5 ▸ h5)
  · exact (adjoint_contact hU w _).mpr (I7 ▸ h7)
  · exact (adjoint_contact hU w _).mpr (I9 ▸ h18)
  · exact (adjoint_contact hU w _).mpr (I14 ▸ h14)
  · exact (adjoint_contact hU w _).mpr (I18 ▸ h9)

/-- To prove the full Zheng T85 support inequality it suffices to rule out
its six noncentral arm contacts in one orientation, without any T81 branch. -/
theorem t85_of_one_orientation_arm_cases
    (harm : ∀ (U : Matrix (Fin 4) (Fin 4) ℂ) (_hU : IsUnitary U)
      (w : StrictMatchingSupport U), Pattern w → ∀ q ∈ w.contacts, Arm center₁₇ q → False)
    (U : Matrix (Fin 4) (Fin 4) ℂ) (hU : IsUnitary U)
    (w : StrictMatchingSupport U) (hT : Pattern w) : False := by
  obtain ⟨v,hV,q,hq,hu | hu⟩ := reduce_t85_to_noncentral_contact hU w hT
  · exact harm U hU v hV q hq hu
  · have hU' : IsUnitary Uᴴ := by
      simpa only [IsUnitary, Matrix.conjTranspose_conjTranspose] using And.intro hU.2 hU.1
    have hq' : q⁻¹ ∈ (adjointWitness hU v).contacts :=
      (adjoint_contact hU v _).mpr (by simpa only [inv_inv] using hq)
    exact harm Uᴴ hU' (adjointWitness hU v) (adjoint_pattern hU v hV) q⁻¹ hq' hu

end ZhengT81Bypass
end MOC
