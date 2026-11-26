import MOC.FiniteMinorLaw

/-! Switch assignments, subset events, and occupation counts on an alternating cycle. -/

open BigOperators Finset

namespace MOC

noncomputable section

variable {κ : Type*} [Fintype κ]

def switchSign (b : Bool) : ℝ := if b then -1 else 1

def switchParity (x : κ → Bool) : ℝ := ∏ k, switchSign (x k)

theorem switchSign_not (b : Bool) : switchSign (!b) = -switchSign b := by
  cases b <;> norm_num [switchSign]

def toggleSwitch [DecidableEq κ] (k : κ) : (κ → Bool) ≃ (κ → Bool) where
  toFun x i := if i = k then !(x i) else x i
  invFun x i := if i = k then !(x i) else x i
  left_inv x := by
    funext i
    by_cases h : i = k <;> simp [h]
  right_inv x := by
    funext i
    by_cases h : i = k <;> simp [h]

theorem switchParity_toggle [DecidableEq κ] (k : κ) (x : κ → Bool) :
    switchParity (toggleSwitch k x) = -switchParity x := by
  unfold switchParity
  rw [← Finset.prod_erase_mul _ _ (mem_univ k), ← Finset.prod_erase_mul _ _ (mem_univ k)]
  have he : (∏ i ∈ univ.erase k, switchSign (toggleSwitch k x i)) =
      ∏ i ∈ univ.erase k, switchSign (x i) := by
    apply Finset.prod_congr rfl
    intro i hi
    simp [toggleSwitch, (Finset.mem_erase.mp hi).1]
  rw [he]
  simp only [toggleSwitch, Equiv.coe_fn_mk, if_true, switchSign_not, mul_neg]

theorem sum_switchParity_eq_zero [DecidableEq κ] (k : κ) (S : Finset (κ → Bool))
    (hS : ∀ x, toggleSwitch k x ∈ S ↔ x ∈ S) :
    ∑ x ∈ S, switchParity x = 0 := by
  classical
  have he : (∑ x ∈ S, switchParity x) = ∑ x ∈ S, -switchParity x := by
    apply Finset.sum_equiv (toggleSwitch k)
    · exact fun x => (hS x).symm
    · intro x _
      rw [switchParity_toggle, neg_neg]
  rw [Finset.sum_neg_distrib] at he
  linarith

theorem switchParity_compl (x : κ → Bool) (hκ : Even (Fintype.card κ)) :
    switchParity (fun k => !(x k)) = switchParity x := by
  unfold switchParity
  have hsign (b : Bool) : switchSign (!b) = (-1) * switchSign b := by
    rw [switchSign_not, neg_one_mul]
  simp_rw [hsign]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, hκ.neg_one_pow, one_mul]

theorem sum_switchParity_pair (x : κ → Bool) (hκ : Even (Fintype.card κ))
    [Nonempty κ] :
    (∑ y ∈ ({x, fun k => !(x k)} : Finset (κ → Bool)), switchParity y) =
      2 * switchParity x := by
  classical
  have hne : x ≠ fun k => !(x k) := by
    intro he
    obtain ⟨k⟩ := ‹Nonempty κ›
    have hk := congrFun he k
    cases h : x k <;> simp [h] at hk
  rw [Finset.sum_pair hne, switchParity_compl x hκ]
  ring

def cyclicSwitchWeight (c : ℝ) (x : κ → Bool) : ℝ :=
  (1 + c * switchParity x) / 2 ^ Fintype.card κ

theorem switchParity_eq_one_or_neg (x : κ → Bool) :
    switchParity x = 1 ∨ switchParity x = -1 := by
  classical
  unfold switchParity
  induction (Finset.univ : Finset κ) using Finset.induction_on with
  | empty => simp
  | insert k S hk ih =>
    rw [Finset.prod_insert hk]
    rcases ih with h | h <;> rw [h] <;> cases hb : x k <;> norm_num [switchSign, hb]

theorem cyclicSwitchWeight_nonneg (c : ℝ) (hc : |c| ≤ 1) (x : κ → Bool) :
    0 ≤ cyclicSwitchWeight c x := by
  have hl := (abs_le.mp hc).1
  have hu := (abs_le.mp hc).2
  unfold cyclicSwitchWeight
  apply div_nonneg _ (by positivity)
  rcases switchParity_eq_one_or_neg x with h | h <;> rw [h] <;> linarith

theorem sum_cyclicSwitchWeight [DecidableEq κ] (c : ℝ) [Nonempty κ] :
    ∑ x : κ → Bool, cyclicSwitchWeight c x = 1 := by
  classical
  obtain ⟨k⟩ := ‹Nonempty κ›
  have hs := sum_switchParity_eq_zero k univ (fun x => by simp)
  unfold cyclicSwitchWeight
  rw [← Finset.sum_div, Finset.sum_add_distrib, ← Finset.mul_sum, hs, mul_zero, add_zero]
  simp [Fintype.card_fun, div_self (by positivity : (2 : ℝ)^Fintype.card κ ≠ 0)]

theorem sum_cyclicSwitchWeight_event (c : ℝ) (S : Finset (κ → Bool)) :
    (∑ x ∈ S, cyclicSwitchWeight c x) =
      (S.card + c * (∑ x ∈ S, switchParity x)) / 2 ^ Fintype.card κ := by
  unfold cyclicSwitchWeight
  rw [← Finset.sum_div, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
    nsmul_eq_mul, mul_one]

end

end MOC

namespace MOC

noncomputable section

variable {κ ι : Type*}

/-- Switch the two positions of each block when its switch is true. -/
def blockSwitch (e : κ × Bool ≃ ι) (x : κ → Bool) : Equiv.Perm ι where
  toFun i := e ((e.symm i).1, if x (e.symm i).1 then !(e.symm i).2 else (e.symm i).2)
  invFun i := e ((e.symm i).1, if x (e.symm i).1 then !(e.symm i).2 else (e.symm i).2)
  left_inv i := by
    by_cases h : x (e.symm i).1 <;> simp [h]
  right_inv i := by
    by_cases h : x (e.symm i).1 <;> simp [h]

@[simp] theorem blockSwitch_symm (e : κ × Bool ≃ ι) (x : κ → Bool) :
    (blockSwitch e x).symm = blockSwitch e x := rfl

theorem blockSwitch_apply (e : κ × Bool ≃ ι) (x : κ → Bool) (k : κ) (b : Bool) :
    blockSwitch e x (e (k, b)) = e (k, if x k then !b else b) := by
  simp [blockSwitch]

theorem mem_map_blockSwitch (e : κ × Bool ≃ ι) (x : κ → Bool) (S : Finset ι)
    (k : κ) (b : Bool) :
    e (k, b) ∈ S.map (blockSwitch e x).toEmbedding ↔
      e (k, if x k then !b else b) ∈ S := by
  rw [Finset.mem_map_equiv, blockSwitch_symm, blockSwitch_apply]

/-- Every block contains exactly one element of the set. -/
def BlockTransversal (e : κ × Bool ≃ ι) (S : Finset ι) : Prop :=
  ∀ k, e (k, false) ∈ S ↔ e (k, true) ∉ S

theorem blockTransversal_map (e : κ × Bool ≃ ι) (x : κ → Bool) (S : Finset ι)
    (hS : BlockTransversal e S) :
    BlockTransversal e (S.map (blockSwitch e x).toEmbedding) := by
  intro k
  simp only [mem_map_blockSwitch]
  by_cases h : x k
  · simpa [h] using not_congr (hS k).symm
  · simpa [h] using hS k

theorem map_blockSwitch_eq_of_flip [DecidableEq ι] (e : κ × Bool ≃ ι) (x y : κ → Bool) (S : Finset ι)
    (k : κ) (hxy : ∀ j, j ≠ k → x j = y j)
    (hS : e (k, false) ∈ S ↔ e (k, true) ∈ S) :
    S.map (blockSwitch e x).toEmbedding = S.map (blockSwitch e y).toEmbedding := by
  ext i
  obtain ⟨⟨j,b⟩, rfl⟩ := e.surjective i
  simp only [mem_map_blockSwitch]
  by_cases hj : j = k
  · subst j
    cases b <;> cases hx : x k <;> cases hy : y k <;> simp [hx, hy, hS]
  · rw [hxy j hj]

/-- The permutation for independent switch assignments in the two block charts. -/
def twoLayerSwitch (eL eR : κ × Bool ≃ ι) (x : κ ⊕ κ → Bool) : Equiv.Perm ι :=
  blockSwitch eL (x ∘ Sum.inl) * blockSwitch eR (x ∘ Sum.inr)

theorem twoLayerSwitch_event_iff (eL eR : κ × Bool ≃ ι) (x : κ ⊕ κ → Bool)
    (I J : Finset ι) :
    J.map (twoLayerSwitch eL eR x).toEmbedding = I ↔
      J.map (blockSwitch eR (x ∘ Sum.inr)).toEmbedding =
        I.map (blockSwitch eL (x ∘ Sum.inl)).toEmbedding := by
  have himage {p q : Equiv.Perm ι} :
      J.map (p * q).toEmbedding = (J.map q.toEmbedding).map p.toEmbedding := by
    rw [Finset.map_map]
    rfl
  rw [twoLayerSwitch, himage]
  generalize J.map (blockSwitch eR (x ∘ Sum.inr)).toEmbedding = K
  let p := blockSwitch eL (x ∘ Sum.inl)
  have hp : (p.toEmbedding.trans p.toEmbedding) = Function.Embedding.refl ι := by
    ext i
    exact (p.left_inv i)
  change K.map p.toEmbedding = I ↔ K = I.map p.toEmbedding
  constructor
  · intro h
    rw [← h, Finset.map_map, hp, Finset.map_refl]
  · intro h
    rw [h, Finset.map_map, hp, Finset.map_refl]

theorem twoLayerSwitch_event_toggle_left [DecidableEq κ] [DecidableEq ι]
    (eL eR : κ × Bool ≃ ι) (I J : Finset ι) (k : κ)
    (hI : eL (k, false) ∈ I ↔ eL (k, true) ∈ I) :
    ∀ x, J.map (twoLayerSwitch eL eR (toggleSwitch (Sum.inl k) x)).toEmbedding = I ↔
      J.map (twoLayerSwitch eL eR x).toEmbedding = I := by
  intro x
  rw [twoLayerSwitch_event_iff, twoLayerSwitch_event_iff]
  have hr : (toggleSwitch (Sum.inl k) x ∘ Sum.inr : κ → Bool) = x ∘ Sum.inr := by
    funext j
    simp [toggleSwitch]
  rw [hr]
  rw [map_blockSwitch_eq_of_flip eL (toggleSwitch (Sum.inl k) x ∘ Sum.inl)
    (x ∘ Sum.inl) I k (by intro j hj; simp [toggleSwitch, hj]) hI]

theorem twoLayerSwitch_event_toggle_right [DecidableEq κ] [DecidableEq ι]
    (eL eR : κ × Bool ≃ ι) (I J : Finset ι) (k : κ)
    (hJ : eR (k, false) ∈ J ↔ eR (k, true) ∈ J) :
    ∀ x, J.map (twoLayerSwitch eL eR (toggleSwitch (Sum.inr k) x)).toEmbedding = I ↔
      J.map (twoLayerSwitch eL eR x).toEmbedding = I := by
  intro x
  rw [twoLayerSwitch_event_iff, twoLayerSwitch_event_iff]
  have hl : (toggleSwitch (Sum.inr k) x ∘ Sum.inl : κ → Bool) = x ∘ Sum.inl := by
    funext j
    simp [toggleSwitch]
  rw [hl]
  rw [map_blockSwitch_eq_of_flip eR (toggleSwitch (Sum.inr k) x ∘ Sum.inr)
    (x ∘ Sum.inr) J k (by intro j hj; simp [toggleSwitch, hj]) hJ]

end

end MOC

namespace MOC

noncomputable section

variable {κ ι : Type*} [DecidableEq ι]

theorem map_blockSwitch_injective_of_transversal (e : κ × Bool ≃ ι) (S : Finset ι)
    (hS : BlockTransversal e S) {x y : κ → Bool}
    (hxy : S.map (blockSwitch e x).toEmbedding = S.map (blockSwitch e y).toEmbedding) :
    x = y := by
  funext k
  have he : e (k, false) ∈ S.map (blockSwitch e x).toEmbedding ↔
      e (k, false) ∈ S.map (blockSwitch e y).toEmbedding := by rw [hxy]
  simp only [mem_map_blockSwitch] at he
  have ht := hS k
  cases hx : x k <;> cases hy : y k <;> simp [hx, hy, blockSwitch_apply] at he ⊢ <;> tauto

theorem map_blockSwitch_complement_assignment [Fintype ι]
    (e : κ × Bool ≃ ι) (S : Finset ι) (hS : BlockTransversal e S) (x : κ → Bool) :
    S.map (blockSwitch e (fun k => !(x k))).toEmbedding =
      (S.map (blockSwitch e x).toEmbedding)ᶜ := by
  ext i
  obtain ⟨⟨k,b⟩, rfl⟩ := e.surjective i
  simp only [Finset.mem_compl, mem_map_blockSwitch]
  have hf := hS k
  have ht : e (k, true) ∈ S ↔ e (k, false) ∉ S := by
    simpa only [not_not] using not_congr hf.symm
  cases h : x k <;> cases b <;> simp [h, blockSwitch_apply] <;> assumption

theorem twoLayerSwitch_event_complement [Fintype ι]
    (eL eR : κ × Bool ≃ ι) (I J : Finset ι)
    (hI : BlockTransversal eL I) (hJ : BlockTransversal eR J)
    (x : κ ⊕ κ → Bool) :
    J.map (twoLayerSwitch eL eR (fun z => !(x z))).toEmbedding = I ↔
      J.map (twoLayerSwitch eL eR x).toEmbedding = I := by
  rw [twoLayerSwitch_event_iff, twoLayerSwitch_event_iff]
  change (J.map (blockSwitch eR (fun k => !(x (Sum.inr k)))).toEmbedding =
    I.map (blockSwitch eL (fun k => !(x (Sum.inl k)))).toEmbedding) ↔ _
  rw [map_blockSwitch_complement_assignment eL I hI,
    map_blockSwitch_complement_assignment eR J hJ, compl_inj_iff]
  rfl

end

end MOC

namespace MOC

noncomputable section

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- The second block contains the false position at k and the true position at s(k). -/
def cyclicRightChart (s : Equiv.Perm κ) : κ × Bool ≃ κ × Bool where
  toFun z := (if z.2 then s z.1 else z.1, z.2)
  invFun z := (if z.2 then s.symm z.1 else z.1, z.2)
  left_inv z := by
    rcases z with ⟨k,b⟩
    cases b <;> simp
  right_inv z := by
    rcases z with ⟨k,b⟩
    cases b <;> simp

omit [Fintype κ] [DecidableEq κ] in
private theorem cyclic_transversal_mem_next (s : Equiv.Perm κ) (K : Finset (κ × Bool))
    (hL : BlockTransversal (Equiv.refl _) K) (hR : BlockTransversal (cyclicRightChart s) K)
    (k : κ) : (s k, false) ∈ K ↔ (k, false) ∈ K :=
  (hL (s k)).trans (hR k).symm

omit [Fintype κ] [DecidableEq κ] in
theorem cyclic_transversal_mem_iff (s : Equiv.Perm κ)
    (hs : ∀ k l : κ, ∃ n : ℕ, (s ^ n) k = l) (K : Finset (κ × Bool))
    (hL : BlockTransversal (Equiv.refl _) K) (hR : BlockTransversal (cyclicRightChart s) K)
    (k l : κ) : (l, false) ∈ K ↔ (k, false) ∈ K := by
  obtain ⟨n, rfl⟩ := hs k l
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, cyclic_transversal_mem_next s K hL hR, ih]

theorem cyclic_transversal_eq_or_compl (s : Equiv.Perm κ)
    (hs : ∀ k l : κ, ∃ n : ℕ, (s ^ n) k = l) [Nonempty κ]
    (K H : Finset (κ × Bool))
    (hKL : BlockTransversal (Equiv.refl _) K) (hKR : BlockTransversal (cyclicRightChart s) K)
    (hHL : BlockTransversal (Equiv.refl _) H) (hHR : BlockTransversal (cyclicRightChart s) H) :
    H = K ∨ H = Kᶜ := by
  obtain ⟨k⟩ := ‹Nonempty κ›
  have hfalseK := cyclic_transversal_mem_iff s hs K hKL hKR k
  have hfalseH := cyclic_transversal_mem_iff s hs H hHL hHR k
  have htrueK (j : κ) : (j, true) ∈ K ↔ (k, false) ∉ K := by
    simpa only [Equiv.refl_apply, not_not] using not_congr ((hKL j).symm.trans (hfalseK j))
  have htrueH (j : κ) : (j, true) ∈ H ↔ (k, false) ∉ H := by
    simpa only [Equiv.refl_apply, not_not] using not_congr ((hHL j).symm.trans (hfalseH j))
  by_cases he : (k, false) ∈ H ↔ (k, false) ∈ K
  · refine Or.inl (Finset.ext fun ⟨j,b⟩ => ?_)
    cases b
    · exact (hfalseH j).trans (he.trans (hfalseK j).symm)
    · exact (htrueH j).trans ((not_congr he).trans (htrueK j).symm)
  · have hn : (k, false) ∈ H ↔ (k, false) ∉ K := by tauto
    refine Or.inr (Finset.ext fun ⟨j,b⟩ => ?_)
    rw [Finset.mem_compl]
    cases b
    · exact (hfalseH j).trans (hn.trans (not_congr (hfalseK j)).symm)
    · exact (htrueH j).trans ((not_congr hn).trans (not_congr (htrueK j)).symm)

end

end MOC

namespace MOC

noncomputable section

variable {κ ι : Type*} [Fintype κ] [DecidableEq κ] [DecidableEq ι]

theorem twoLayerSwitch_parity_eq_zero_of_not_transversal
    (eL eR : κ × Bool ≃ ι) (I J : Finset ι)
    (h : ¬ BlockTransversal eL I ∨ ¬ BlockTransversal eR J) :
    (∑ x ∈ univ.filter (fun x => J.map (twoLayerSwitch eL eR x).toEmbedding = I),
      switchParity x) = 0 := by
  classical
  rcases h with h | h
  · obtain ⟨k, hk⟩ := not_forall.mp h
    apply sum_switchParity_eq_zero (Sum.inl k)
    intro x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact twoLayerSwitch_event_toggle_left eL eR I J k (by tauto) x
  · obtain ⟨k, hk⟩ := not_forall.mp h
    apply sum_switchParity_eq_zero (Sum.inr k)
    intro x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact twoLayerSwitch_event_toggle_right eL eR I J k (by tauto) x

theorem cyclic_switch_event_eq_pair (s : Equiv.Perm κ)
    (hs : ∀ k l : κ, ∃ n : ℕ, (s ^ n) k = l) [Nonempty κ]
    (I J : Finset (κ × Bool))
    (hI : BlockTransversal (Equiv.refl _) I) (hJ : BlockTransversal (cyclicRightChart s) J)
    (x : κ ⊕ κ → Bool)
    (hx : J.map (twoLayerSwitch (Equiv.refl _) (cyclicRightChart s) x).toEmbedding = I) :
    univ.filter (fun y => J.map
      (twoLayerSwitch (Equiv.refl _) (cyclicRightChart s) y).toEmbedding = I) =
        {x, fun z => !(x z)} := by
  classical
  let eL : κ × Bool ≃ κ × Bool := Equiv.refl _
  let eR := cyclicRightChart s
  change _ = ({x, fun z => !(x z)} : Finset (κ ⊕ κ → Bool))
  have hq {y z : κ ⊕ κ → Bool}
      (hyl : I.map (blockSwitch eL (y ∘ Sum.inl)).toEmbedding =
        I.map (blockSwitch eL (z ∘ Sum.inl)).toEmbedding)
      (hyr : J.map (blockSwitch eR (y ∘ Sum.inr)).toEmbedding =
        J.map (blockSwitch eR (z ∘ Sum.inr)).toEmbedding) : y = z := by
    have hl := map_blockSwitch_injective_of_transversal eL I hI hyl
    have hr := map_blockSwitch_injective_of_transversal eR J hJ hyr
    funext b
    cases b with
    | inl k => exact congrFun hl k
    | inr k => exact congrFun hr k
  have hxe := (twoLayerSwitch_event_iff eL eR x I J).mp hx
  ext y
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
    Finset.mem_singleton]
  change (J.map (twoLayerSwitch eL eR y).toEmbedding = I) ↔ _
  constructor
  · intro hy
    have hye := (twoLayerSwitch_event_iff eL eR y I J).mp hy
    let K := I.map (blockSwitch eL (x ∘ Sum.inl)).toEmbedding
    let H := I.map (blockSwitch eL (y ∘ Sum.inl)).toEmbedding
    have hKR : BlockTransversal eR K := by
      change BlockTransversal eR (I.map _)
      rw [← hxe]
      exact blockTransversal_map eR _ J hJ
    have hHR : BlockTransversal eR H := by
      change BlockTransversal eR (I.map _)
      rw [← hye]
      exact blockTransversal_map eR _ J hJ
    rcases cyclic_transversal_eq_or_compl s hs K H
        (blockTransversal_map eL _ I hI) hKR (blockTransversal_map eL _ I hI) hHR with hh | hh
    · exact Or.inl (hq hh (hye.trans (hh.trans hxe.symm)))
    · refine Or.inr (hq ?_ ?_)
      · change H = I.map (blockSwitch eL (fun k => !(x (Sum.inl k)))).toEmbedding
        rw [map_blockSwitch_complement_assignment eL I hI]
        exact hh
      · change _ = J.map (blockSwitch eR (fun k => !(x (Sum.inr k)))).toEmbedding
        rw [map_blockSwitch_complement_assignment eR J hJ, hye]
        change H = (J.map (blockSwitch eR (x ∘ Sum.inr)).toEmbedding)ᶜ
        rw [hxe]
        exact hh
  · rintro (rfl | rfl)
    · exact hx
    · exact (twoLayerSwitch_event_complement eL eR I J hI hJ x).mpr hx

end

end MOC

namespace MOC

noncomputable section

variable {κ ι : Type*} [DecidableEq ι]

/-- The switch assignment that moves each selected label to the false position. -/
def switchToFalse (e : κ × Bool ≃ ι) (S : Finset ι) (k : κ) : Bool :=
  decide (e (k, true) ∈ S)

theorem mem_map_switchToFalse (e : κ × Bool ≃ ι) (S : Finset ι)
    (hS : BlockTransversal e S) (k : κ) (b : Bool) :
    e (k, b) ∈ S.map (blockSwitch e (switchToFalse e S)).toEmbedding ↔ b = false := by
  rw [mem_map_blockSwitch]
  have h := hS k
  by_cases hs : e (k, true) ∈ S <;> cases b <;> simp [switchToFalse, hs, h]

variable {κ : Type*} [DecidableEq κ]

/-- The assignment that moves both transversals to the common false positions. -/
def cyclicSwitchToFalse (s : Equiv.Perm κ) (I J : Finset (κ × Bool)) : κ ⊕ κ → Bool :=
  Sum.elim (switchToFalse (Equiv.refl _) I) (switchToFalse (cyclicRightChart s) J)

theorem cyclicSwitchToFalse_event (s : Equiv.Perm κ) (I J : Finset (κ × Bool))
    (hI : BlockTransversal (Equiv.refl _) I) (hJ : BlockTransversal (cyclicRightChart s) J) :
    J.map (twoLayerSwitch (Equiv.refl _) (cyclicRightChart s)
      (cyclicSwitchToFalse s I J)).toEmbedding = I := by
  rw [twoLayerSwitch_event_iff]
  change J.map (blockSwitch (cyclicRightChart s) (switchToFalse (cyclicRightChart s) J)).toEmbedding =
    I.map (blockSwitch (Equiv.refl _) (switchToFalse (Equiv.refl _) I)).toEmbedding
  ext i
  obtain ⟨⟨k,b⟩, rfl⟩ := (cyclicRightChart s).surjective i
  rw [mem_map_switchToFalse _ _ hJ]
  change (b = false) ↔
    (Equiv.refl (κ × Bool)) ((if b then s k else k), b) ∈
      I.map (blockSwitch (Equiv.refl _) (switchToFalse (Equiv.refl _) I)).toEmbedding
  rw [mem_map_switchToFalse _ _ hI]

/-- The occupancy of a given position is either zero or one. -/
def positionOccupancy {ι : Type*} [DecidableEq ι] (S : Finset ι) (i : ι) : ℤ :=
  if i ∈ S then 1 else 0

/-- The number of selected positions of a block, viewed as an integer. -/
def blockOccupancy {ι : Type*} [DecidableEq ι]
    (e : κ × Bool ≃ ι) (S : Finset ι) (k : κ) : ℤ :=
  positionOccupancy S (e (k, false)) + positionOccupancy S (e (k, true))

theorem positionOccupancy_mem_iff {ι : Type*} [DecidableEq ι]
    (S T : Finset ι) (i : ι) :
    positionOccupancy S i = positionOccupancy T i ↔ (i ∈ S ↔ i ∈ T) := by
  by_cases hS : i ∈ S <;> by_cases hT : i ∈ T <;> simp [positionOccupancy, hS, hT]

omit [DecidableEq κ] in
theorem blockOccupancy_eq_one_iff {ι : Type*} [DecidableEq ι]
    (e : κ × Bool ≃ ι) (S : Finset ι) (k : κ) :
    blockOccupancy e S k = 1 ↔ (e (k, false) ∈ S ↔ e (k, true) ∉ S) := by
  by_cases ha : e (k, false) ∈ S <;> by_cases hb : e (k, true) ∈ S <;>
    norm_num [blockOccupancy, positionOccupancy, ha, hb]

private theorem positionOccupancy_eq_of_pair {ι : Type*} [DecidableEq ι]
    (S T : Finset ι) (i j : ι) (h : i ∈ S ↔ j ∈ S) (he :
      positionOccupancy S i + positionOccupancy S j =
        positionOccupancy T i + positionOccupancy T j) :
    positionOccupancy S i = positionOccupancy T i := by
  have h1 : 0 ≤ positionOccupancy T i ∧ positionOccupancy T i ≤ 1 := by
    by_cases hi : i ∈ T <;> simp [positionOccupancy, hi]
  have h2 : 0 ≤ positionOccupancy T j ∧ positionOccupancy T j ≤ 1 := by
    by_cases hj : j ∈ T <;> simp [positionOccupancy, hj]
  by_cases hi : i ∈ S
  · simp only [positionOccupancy, if_pos hi, if_pos (h.mp hi)] at he
    rw [show positionOccupancy S i = 1 from if_pos hi]
    change 1 + 1 = positionOccupancy T i + positionOccupancy T j at he
    omega
  · simp only [positionOccupancy, if_neg hi, if_neg (mt h.mpr hi)] at he
    rw [show positionOccupancy S i = 0 from if_neg hi]
    change 0 + 0 = positionOccupancy T i + positionOccupancy T j at he
    omega

theorem cyclic_middle_eq_of_nontransversal (s : Equiv.Perm κ)
    (hs : ∀ k l : κ, ∃ n : ℕ, (s ^ n) k = l)
    (S T : Finset (κ × Bool))
    (hl : ∀ k, blockOccupancy (Equiv.refl _) S k = blockOccupancy (Equiv.refl _) T k)
    (hr : ∀ k, blockOccupancy (cyclicRightChart s) S k = blockOccupancy (cyclicRightChart s) T k)
    (hn : ¬ BlockTransversal (Equiv.refl _) S ∨ ¬ BlockTransversal (cyclicRightChart s) S) :
    S = T := by
  classical
  let d (k : κ) := positionOccupancy S (k, false) - positionOccupancy T (k, false)
  have hstep (k : κ) : d (s k) = d k := by
    have hleft := hl (s k)
    have hright := hr k
    change positionOccupancy S (s k, false) + positionOccupancy S (s k, true) =
      positionOccupancy T (s k, false) + positionOccupancy T (s k, true) at hleft
    change positionOccupancy S (k, false) + positionOccupancy S (s k, true) =
      positionOccupancy T (k, false) + positionOccupancy T (s k, true) at hright
    dsimp only [d]
    omega
  have hall (k l : κ) : d l = d k := by
    obtain ⟨n, rfl⟩ := hs k l
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ', Equiv.Perm.mul_apply, hstep, ih]
  have hzero : ∃ k, d k = 0 := by
    rcases hn with hn | hn
    · obtain ⟨k, hk⟩ := not_forall.mp hn
      have ho := positionOccupancy_eq_of_pair S T (k, false) (k, true) (by tauto) (hl k)
      exact ⟨k, sub_eq_zero.mpr ho⟩
    · obtain ⟨k, hk⟩ := not_forall.mp hn
      have ho := positionOccupancy_eq_of_pair S T (k, false) (s k, true) (by tauto) (hr k)
      exact ⟨k, sub_eq_zero.mpr ho⟩
  obtain ⟨k, hk⟩ := hzero
  have hfalse (j : κ) : positionOccupancy S (j, false) = positionOccupancy T (j, false) :=
    sub_eq_zero.mp ((hall k j).trans hk)
  ext ⟨j,b⟩
  apply (positionOccupancy_mem_iff S T _).mp
  cases b
  · exact hfalse j
  · have hleft := hl j
    change positionOccupancy S (j, false) + positionOccupancy S (j, true) =
      positionOccupancy T (j, false) + positionOccupancy T (j, true) at hleft
    rw [hfalse j] at hleft
    omega

end

end MOC

namespace MOC

noncomputable section

variable {κ ι : Type*} [DecidableEq ι]

/-- The Boolean position used by a transversal is the switch sending it to false. -/
theorem transversal_mem_iff_switchToFalse (e : κ × Bool ≃ ι) (S : Finset ι)
    (hS : BlockTransversal e S) (k : κ) (b : Bool) :
    e (k,b) ∈ S ↔ b = switchToFalse e S k := by
  have h := hS k
  by_cases hs : e (k, true) ∈ S <;> cases b <;> simp [switchToFalse, h, hs]

/-- The selected positions of a transversal have one label per block. -/
def blockTransversalEquiv (e : κ × Bool ≃ ι) (S : Finset ι) (hS : BlockTransversal e S) :
    κ ≃ S :=
  Equiv.ofBijective (fun k => ⟨e (k, switchToFalse e S k),
    (transversal_mem_iff_switchToFalse e S hS k _).mpr rfl⟩) (by
    constructor
    · intro k l he
      exact congrArg Prod.fst (e.injective (congrArg Subtype.val he))
    · rintro ⟨i,hi⟩
      obtain ⟨⟨k,b⟩, rfl⟩ := e.surjective i
      exact ⟨k, Subtype.ext (congrArg (fun c => e (k,c))
        ((transversal_mem_iff_switchToFalse e S hS k b).mp hi).symm)⟩)

theorem blockTransversalEquiv_apply (e : κ × Bool ≃ ι) (S : Finset ι)
    (hS : BlockTransversal e S) (k : κ) :
    (blockTransversalEquiv e S hS k).val = e (k, switchToFalse e S k) := rfl

end

end MOC
