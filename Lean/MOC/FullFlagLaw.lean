import MOC.NestedContactObjective

/-! Finite flag gluing for squared-minor laws. Background on projection
determinantal measures: R. Lyons, DOI 10.1007/s10240-003-0016-0. The
proof only uses the checked adjacent transport, including its zero masses. -/

open Finset BigOperators Matrix
namespace MOC
noncomputable section

private theorem flagFiber_sum {A B : Type*} [Fintype A] [Fintype B] [DecidableEq B]
    (f : A → B) (w : A → ℝ) (g : B → ℝ) :
    ∑ x, w x * g (f x) = ∑ y, (∑ x ∈ univ.filter (fun x => f x = y), w x) * g y := by
  rw [← Finset.sum_fiberwise univ f]
  apply Finset.sum_congr rfl
  intro y _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x hx
  rw [(Finset.mem_filter.mp hx).2]

private theorem flagFiber_sum_ite {A B : Type*} [Fintype A] [DecidableEq B]
    (f : A → B) (w : A → ℝ) (y : B) :
    ∑ x ∈ univ.filter (fun x => f x = y), w x =
      ∑ x, if f x = y then w x else 0 := by
  rw [Finset.sum_filter]

private theorem flag_extend_perm {n : ℕ} (J : Finset (Fin n)) (j : Fin n) (hj : j ∉ J)
    (σ : Equiv.Perm (Fin n)) (L : Finset (Fin n))
    (hsub : J.map σ.toEmbedding ⊆ L) (hcard : L.card = J.card + 1) :
    ∃ τ : Equiv.Perm (Fin n), (∀ K ⊆ J, K.map τ.toEmbedding = K.map σ.toEmbedding) ∧
      (insert j J).map τ.toEmbedding = L := by
  let I := J.map σ.toEmbedding
  have hIcard : I.card = J.card := Finset.card_map _
  have hdiff : (L \ I).card = 1 := by
    rw [Finset.card_sdiff hsub, hcard, hIcard]
    omega
  obtain ⟨y, hy⟩ := Finset.card_eq_one.mp hdiff
  have hy' : y ∈ L \ I := by rw [hy]; simp
  have hyL := (Finset.mem_sdiff.mp hy').1
  have hyI := (Finset.mem_sdiff.mp hy').2
  have hσj : σ j ∉ I := by simpa [I, Finset.mem_map_equiv] using hj
  let τ := σ.trans (Equiv.swap (σ j) y)
  have hfix (x : Fin n) (hx : x ∈ J) : τ x = σ x := by
    have hm : σ x ∈ I := Finset.mem_map.mpr ⟨x, hx, rfl⟩
    exact Equiv.swap_apply_of_ne_of_ne (fun h => hσj (h ▸ hm)) (fun h => hyI (h ▸ hm))
  have hmap (K : Finset (Fin n)) (hK : K ⊆ J) :
      K.map τ.toEmbedding = K.map σ.toEmbedding := by
    ext x
    simp only [Finset.mem_map, Equiv.toEmbedding_apply]
    constructor <;> rintro ⟨z, hz, rfl⟩
    · exact ⟨z, hz, (hfix z (hK hz)).symm⟩
    · exact ⟨z, hz, hfix z (hK hz)⟩
  refine ⟨τ, hmap, ?_⟩
  rw [Finset.map_insert, hmap J (Finset.Subset.refl _)]
  change insert ((Equiv.swap (σ j) y) (σ j)) I = L
  rw [Equiv.swap_apply_left]
  apply Finset.eq_of_subset_of_card_le
  · exact Finset.insert_subset hyL hsub
  · rw [Finset.card_insert_of_not_mem hyI, hcard, hIcard]

private theorem flag_joint_marginals {A B : Type*} [Fintype A] [Fintype B] [DecidableEq B]
    (f : A → B) (w : A → ℝ) (p : B → B → ℝ) (m m' : B → ℝ)
    (hw : ∀ x, 0 ≤ w x) (hp : ∀ y z, 0 ≤ p y z)
    (hf : ∀ y, (∑ x ∈ univ.filter (fun x => f x = y), w x) = m y)
    (hr : ∀ y, ∑ z, p y z = m y) (hc : ∀ z, ∑ y, p y z = m' z) :
    let q := fun x z => w x * p (f x) z / m (f x)
    (∀ x z, 0 ≤ q x z) ∧ (∀ x, ∑ z, q x z = w x) ∧ (∀ z, ∑ x, q x z = m' z) := by
  intro q
  have hm (y : B) : 0 ≤ m y := by rw [← hr]; exact Finset.sum_nonneg fun z _ => hp y z
  have hwzero (x : A) (h : m (f x) = 0) : w x = 0 := by
    have he := (hf (f x)).trans h
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun x _ => hw x)).mp he x (by simp)
  have hpzero (y z : B) (h : m y = 0) : p y z = 0 := by
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun z _ => hp y z)).mp ((hr y).trans h) z (by simp)
  refine ⟨fun x z => div_nonneg (mul_nonneg (hw x) (hp (f x) z)) (hm (f x)), ?_, ?_⟩
  · intro x
    change (∑ z, w x * p (f x) z / m (f x)) = w x
    rw [← Finset.sum_div, ← Finset.mul_sum, hr]
    by_cases he : m (f x) = 0
    · simp [he, hwzero x he]
    · exact mul_div_cancel_right₀ _ he
  · intro z
    change (∑ x, w x * p (f x) z / m (f x)) = m' z
    simp_rw [mul_div_assoc]
    rw [flagFiber_sum f w (fun y => p y z / m y), ← hc]
    apply Finset.sum_congr rfl
    intro y _
    rw [hf, ← mul_div_assoc, mul_comm]
    by_cases he : m y = 0
    · simp [he, hpzero y z he]
    · exact mul_div_cancel_right₀ _ he

private theorem flag_push_expectation {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A]
    (F : A → B → A) (q : A → B → ℝ) (g : A → ℝ) :
    (∑ τ, (∑ σ, ∑ y, if F σ y = τ then q σ y else 0) * g τ) =
      ∑ σ, ∑ y, q σ y * g (F σ y) := by
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro σ _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  classical
  simp_rw [ite_mul, zero_mul]
  simp


/-- Extend a permutation law from one subset to an adjacent larger subset,
while preserving all old subset-image marginals. -/
theorem extend_flag_minor_law {n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ) (hU : IsUnitary U)
    (J : Finset (Fin n)) (j : Fin n) (hj : j ∉ J)
    (w : Equiv.Perm (Fin n) → ℝ) (hw : ∀ σ, 0 ≤ w σ)
    (hwJ : ∀ I, (∑ σ ∈ univ.filter (fun σ : Equiv.Perm (Fin n) =>
      J.map σ.toEmbedding = I), w σ) = subsetMinorSq U I J) :
    ∃ w' : Equiv.Perm (Fin n) → ℝ,
      (∀ σ, 0 ≤ w' σ) ∧ (∑ σ, w' σ) = ∑ σ, w σ ∧
      (∀ K ⊆ J, ∀ I, (∑ σ ∈ univ.filter (fun σ : Equiv.Perm (Fin n) =>
        K.map σ.toEmbedding = I), w' σ) =
        ∑ σ ∈ univ.filter (fun σ : Equiv.Perm (Fin n) =>
          K.map σ.toEmbedding = I), w σ) ∧
      (∀ I, (∑ σ ∈ univ.filter (fun σ : Equiv.Perm (Fin n) =>
        (insert j J).map σ.toEmbedding = I), w' σ) = subsetMinorSq U I (insert j J)) := by
  classical
  let A := Equiv.Perm (Fin n)
  let B := Finset (Fin n)
  let f (σ : A) : B := J.map σ.toEmbedding
  let m (I : B) := subsetMinorSq U I J
  let m' (I : B) := subsetMinorSq U I (insert j J)
  obtain ⟨p, hp, hn, hpR, hpC⟩ := exists_adjacent_minor_transport U hU J j hj
  let q (σ : A) (L : B) := w σ * p (f σ) L / m (f σ)
  obtain ⟨hq, hqR, hqC⟩ := flag_joint_marginals f w p m m' hw hp hwJ hpR hpC
  change (∀ σ L, 0 ≤ q σ L) at hq
  change (∀ σ, ∑ L, q σ L = w σ) at hqR
  change (∀ L, ∑ σ, q σ L = m' L) at hqC
  have hchoose (σ : A) (L : B) : ∃ τ : A, q σ L ≠ 0 →
      (∀ K ⊆ J, K.map τ.toEmbedding = K.map σ.toEmbedding) ∧
      (insert j J).map τ.toEmbedding = L := by
    by_cases he : q σ L = 0
    · exact ⟨σ, fun h => False.elim (h he)⟩
    have hp' : p (f σ) L ≠ 0 := fun h => he (by simp [q, h])
    have hpos : 0 < m' L := lt_of_lt_of_le (lt_of_le_of_ne (hp _ _) hp'.symm) (by
      unfold m'
      rw [← hpC]
      exact Finset.single_le_sum (fun I _ => hp I L) (mem_univ (f σ)))
    have hcard : L.card = J.card + 1 := by
      rw [← Finset.card_insert_of_not_mem hj]
      by_contra h
      simp [m', subsetMinorSq, h] at hpos
    obtain ⟨τ, hτ⟩ := flag_extend_perm J j hj σ L (hn _ _ hp') hcard
    exact ⟨τ, fun _ => hτ⟩
  choose F hF using hchoose
  let w' (τ : A) := ∑ σ : A, ∑ L : B, if F σ L = τ then q σ L else 0
  have hpush (g : A → ℝ) :
      (∑ τ, w' τ * g τ) = ∑ σ, ∑ L, q σ L * g (F σ L) :=
    flag_push_expectation F q g
  refine ⟨w', ?_, ?_, ?_, ?_⟩
  · intro τ
    unfold w'
    apply Finset.sum_nonneg
    intro σ _
    apply Finset.sum_nonneg
    intro L _
    split_ifs
    · exact hq σ L
    · exact le_rfl
  · simpa only [mul_one, hqR] using hpush (fun _ => 1)
  · intro K hK I
    let g (τ : A) : ℝ := if K.map τ.toEmbedding = I then 1 else 0
    simp only [flagFiber_sum_ite]
    calc
      _ = ∑ τ, w' τ * g τ := by simp only [g, mul_ite, mul_one, mul_zero]; rfl
      _ = ∑ σ, ∑ L, q σ L * g (F σ L) := hpush g
      _ = ∑ σ, ∑ L, q σ L * g σ := by
        apply Finset.sum_congr rfl
        intro σ _
        apply Finset.sum_congr rfl
        intro L _
        by_cases he : q σ L = 0
        · simp [he]
        simp only [g, (hF σ L he).1 K hK]
      _ = _ := by
        simp_rw [← Finset.sum_mul, hqR]
        simp only [g, mul_ite, mul_one, mul_zero]; rfl
  · intro I
    let g (τ : A) : ℝ := if (insert j J).map τ.toEmbedding = I then 1 else 0
    rw [flagFiber_sum_ite]
    calc
      _ = ∑ τ, w' τ * g τ := by simp only [g, mul_ite, mul_one, mul_zero]; rfl
      _ = ∑ σ, ∑ L, q σ L * g (F σ L) := hpush g
      _ = ∑ σ, ∑ L, q σ L * (if L = I then 1 else 0) := by
        apply Finset.sum_congr rfl
        intro σ _
        apply Finset.sum_congr rfl
        intro L _
        by_cases he : q σ L = 0
        · simp [he]
        simp only [g, (hF σ L he).2]
      _ = _ := by
        simp_rw [mul_ite, mul_one, mul_zero]
        rw [Finset.sum_comm]
        simp_rw [Finset.sum_ite_irrel, hqC, Finset.sum_const_zero]
        rw [Finset.sum_eq_single I (fun b _ hb => if_neg hb) (by simp)]
        simp [m']

/-- One positive law realizes every squared-minor marginal along a column
flag. This law depends on the flag, not the scores. -/
theorem exists_full_flag_minor_law {n d : ℕ} (U : Matrix (Fin n) (Fin n) ℂ)
    (hU : IsUnitary U) (J : ℕ → Finset (Fin n)) (hzero : J 0 = ∅)
    (hstep : ∀ k < d, ∃ j ∉ J k, J (k + 1) = insert j (J k)) :
    ∃ w : Equiv.Perm (Fin n) → ℝ, (∀ σ, 0 ≤ w σ) ∧ (∑ σ, w σ) = 1 ∧
      ∀ k ≤ d, ∀ I, (∑ σ ∈ univ.filter (fun σ : Equiv.Perm (Fin n) =>
        (J k).map σ.toEmbedding = I), w σ) = subsetMinorSq U I (J k) := by
  classical
  induction d with
  | zero =>
    let w (σ : Equiv.Perm (Fin n)) : ℝ := if σ = 1 then 1 else 0
    refine ⟨w, fun σ => by unfold w; split_ifs <;> positivity, by simp [w], ?_⟩
    intro k hk I
    have he : k = 0 := by omega
    subst k
    rw [hzero]
    have h : subsetMinorSq U ∅ ∅ = 1 := by
      have hs := sum_subsetMinorSq U hU (∅ : Finset (Fin n))
      rw [Finset.sum_eq_single (∅ : Finset (Fin n))] at hs
      · exact hs
      · intro s _ hne
        have hc : s.card ≠ (∅ : Finset (Fin n)).card :=
          fun he => hne (Finset.card_eq_zero.mp (he.trans Finset.card_empty))
        unfold subsetMinorSq
        rw [dif_neg hc]
      · simp
    by_cases hI : I = ∅
    · simp [hI, h, w]
    · have hc : I.card ≠ (∅ : Finset (Fin n)).card :=
        fun he => hI (Finset.card_eq_zero.mp (he.trans Finset.card_empty))
      unfold subsetMinorSq
      rw [dif_neg hc]
      simp [Ne.symm hI]
  | succ d ih =>
    obtain ⟨w, hw, hmass, hm⟩ := ih (fun k hk => hstep k (by omega))
    obtain ⟨j, hj, he⟩ := hstep d (Nat.lt_succ_self d)
    obtain ⟨w', hw', hmass', hp, hlast⟩ := extend_flag_minor_law U hU (J d) j hj w hw
      (hm d le_rfl)
    refine ⟨w', hw', hmass'.trans hmass, ?_⟩
    intro k hk I
    by_cases hkd : k = d + 1
    · simpa only [hkd, he] using hlast I
    have hk' : k ≤ d := by omega
    have hsub (l : ℕ) (hkl : k ≤ l) (hl : l ≤ d) : J k ⊆ J l := by
      induction l, hkl using Nat.le_induction with
      | base => exact Finset.Subset.refl _
      | succ l hkl ih =>
        obtain ⟨t, _, hot⟩ := hstep l (by omega)
        exact (ih (by omega)).trans (hot.symm ▸ Finset.subset_insert _ _)
    rw [hp (J k) (hsub d hk' le_rfl) I, hm k hk']

/-- A flag law preserves the signed expectation of every real additive
score on that flag, with the same positive law for all choices of scores. -/
theorem exists_full_flag_score_law {n d : ℕ} (U : Matrix (Fin n) (Fin n) ℂ)
    (hU : IsUnitary U) (J : ℕ → Finset (Fin n)) (hzero : J 0 = ∅)
    (hstep : ∀ k < d, ∃ j ∉ J k, J (k + 1) = insert j (J k)) :
    ∃ w : Equiv.Perm (Fin n) → ℝ, (∀ σ, 0 ≤ w σ) ∧ (∑ σ, w σ) = 1 ∧
      ∀ g : ℕ → Finset (Fin n) → ℝ,
        (∑ σ : Equiv.Perm (Fin n), w σ *
          ∑ k ∈ Finset.range (d + 1), g k ((J k).map σ.toEmbedding)) =
        ∑ σ : Equiv.Perm (Fin n), realSignedWeight U σ *
          ∑ k ∈ Finset.range (d + 1), g k ((J k).map σ.toEmbedding) := by
  classical
  obtain ⟨w, hw, hmass, hm⟩ := exists_full_flag_minor_law U hU J hzero hstep
  refine ⟨w, hw, hmass, fun g => ?_⟩
  have hsing (k : ℕ) (hk : k ∈ Finset.range (d + 1)) :
      (∑ σ : Equiv.Perm (Fin n), w σ * g k ((J k).map σ.toEmbedding)) =
        ∑ σ : Equiv.Perm (Fin n), realSignedWeight U σ * g k ((J k).map σ.toEmbedding) := by
    rw [flagFiber_sum (fun σ : Equiv.Perm (Fin n) => (J k).map σ.toEmbedding) w (g k),
      flagFiber_sum (fun σ : Equiv.Perm (Fin n) => (J k).map σ.toEmbedding)
        (realSignedWeight U) (g k)]
    apply Finset.sum_congr rfl
    intro I _
    rw [hm k (by have := Finset.mem_range.mp hk; omega) I]
    have he := congrArg Complex.re (sum_signedWeight_image_eq_subsetMinorSq U hU I (J k))
    simp only [Complex.re_sum, Complex.ofReal_re, realSignedWeight] at he ⊢
    rw [he]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm, Finset.sum_comm (s := univ)]
  exact Finset.sum_congr rfl hsing

/-- The signed expectation of a pointwise nonnegative additive flag
score is nonnegative, even when the individual layer scores have signs. -/
theorem signed_expectation_nonneg_of_full_flag_score {n d : ℕ}
    (U : Matrix (Fin n) (Fin n) ℂ) (hU : IsUnitary U)
    (J : ℕ → Finset (Fin n)) (hzero : J 0 = ∅)
    (hstep : ∀ k < d, ∃ j ∉ J k, J (k + 1) = insert j (J k))
    (g : ℕ → Finset (Fin n) → ℝ)
    (hnonneg : ∀ σ : Equiv.Perm (Fin n),
      0 ≤ ∑ k ∈ Finset.range (d + 1), g k ((J k).map σ.toEmbedding)) :
    0 ≤ ∑ σ : Equiv.Perm (Fin n), realSignedWeight U σ *
      ∑ k ∈ Finset.range (d + 1), g k ((J k).map σ.toEmbedding) := by
  obtain ⟨w, hw, _, he⟩ := exists_full_flag_score_law U hU J hzero hstep
  rw [← he g]
  exact Finset.sum_nonneg fun σ _ => mul_nonneg (hw σ) (hnonneg σ)

/-- A support gap certified by a positive sum of separately nonnegative
flag scores has nonnegative signed expectation. Each summand may use a
different chain; no coupling of those chains is required. -/
theorem support_bound_of_nonnegative_flag_sum {n : ℕ} {β : Type*} [Fintype β]
    (a b : Fin n → ℂ) (U : Matrix (Fin n) (Fin n) ℂ) (hU : IsUnitary U)
    (η : ℂ) (r : Equiv.Perm (Fin n)) (d : β → ℕ)
    (J : β → ℕ → Finset (Fin n)) (hzero : ∀ c, J c 0 = ∅)
    (hstep : ∀ c k, k < d c → ∃ j ∉ J c k, J c (k + 1) = insert j (J c k))
    (g : β → ℕ → Finset (Fin n) → ℝ)
    (hnonneg : ∀ (c : β) (σ : Equiv.Perm (Fin n)),
      0 ≤ ∑ k ∈ Finset.range (d c + 1), g c k ((J c k).map σ.toEmbedding))
    (hgap : ∀ σ : Equiv.Perm (Fin n), matchingGap a b η r σ =
      ∑ c, ∑ k ∈ Finset.range (d c + 1), g c k ((J c k).map σ.toEmbedding)) :
    (η * determinantValue a b U).re ≤ (η * matchingProduct a b r).re := by
  rw [← sub_nonneg, support_gap_eq a b U hU η r]
  have hterm (σ : Equiv.Perm (Fin n)) :
      realSignedWeight U σ * matchingGap a b η r σ =
        ∑ c, realSignedWeight U σ *
          (∑ k ∈ Finset.range (d c + 1), g c k ((J c k).map σ.toEmbedding)) := by
    rw [hgap, Finset.mul_sum]
  simp_rw [hterm]
  rw [Finset.sum_comm]
  exact Finset.sum_nonneg fun c _ =>
    signed_expectation_nonneg_of_full_flag_score U hU (J c) (hzero c) (hstep c) (g c) (hnonneg c)

/-- The full-chain law proves the projected support comparison whenever the
score is additive across the images of any initial segment of a column flag. -/
theorem projected_hull_of_full_flag_scores {n d : ℕ} (a b : Fin n → ℂ)
    (U : Matrix (Fin n) (Fin n) ℂ) (hU : IsUnitary U) (η : ℂ)
    (J : ℕ → Finset (Fin n)) (hzero : J 0 = ∅)
    (hstep : ∀ k < d, ∃ j ∉ J k, J (k + 1) = insert j (J k))
    (g : ℕ → Finset (Fin n) → ℝ)
    (hscore : ∀ σ : Equiv.Perm (Fin n), (η * matchingProduct a b σ).re =
      ∑ k ∈ Finset.range (d + 1), g k ((J k).map σ.toEmbedding)) :
    (η * determinantValue a b U).re ∈
      convexHull ℝ (Set.range (fun σ : Equiv.Perm (Fin n) =>
        (η * matchingProduct a b σ).re)) := by
  classical
  obtain ⟨w, hw, hmass, he⟩ := exists_full_flag_score_law U hU J hzero hstep
  have heq :
      (∑ σ : Equiv.Perm (Fin n), w σ * (η * matchingProduct a b σ).re) =
        (η * determinantValue a b U).re := by
    rw [← real_signed_determinant a b U hU, Finset.mul_sum, Complex.re_sum]
    simp_rw [mul_left_comm η, Complex.re_ofReal_mul, hscore]
    exact he g
  rw [← heq]
  exact (convex_convexHull ℝ _).sum_mem (fun σ _ => hw σ) hmass
    (fun σ _ => subset_convexHull ℝ _ ⟨σ, rfl⟩)

/-- An exact decomposition of the complex matching product by any
column flag proves the full complex hull inclusion, not just one projection. -/
theorem holds_of_full_flag_complex_scores {n d : ℕ} (a b : Fin n → ℂ)
    (U : Matrix (Fin n) (Fin n) ℂ) (hU : IsUnitary U)
    (J : ℕ → Finset (Fin n)) (hzero : J 0 = ∅)
    (hstep : ∀ k < d, ∃ j ∉ J k, J (k + 1) = insert j (J k))
    (g : ℕ → Finset (Fin n) → ℂ)
    (hscore : ∀ σ : Equiv.Perm (Fin n), matchingProduct a b σ =
      ∑ k ∈ Finset.range (d + 1), g k ((J k).map σ.toEmbedding)) :
    Holds a b U := by
  rw [holds_iff_directional]
  intro η
  have h := projected_hull_of_full_flag_scores a b U hU η J hzero hstep
    (fun k I => (η * g k I).re) (fun σ => by
      rw [hscore σ, Finset.mul_sum, Complex.re_sum])
  by_contra! hn
  have hsub : Set.range (fun σ : Equiv.Perm (Fin n) => (η * matchingProduct a b σ).re) ⊆
      Set.Iio (η * determinantValue a b U).re := by
    rintro _ ⟨σ, rfl⟩
    exact hn σ
  have hh : (η * determinantValue a b U).re < (η * determinantValue a b U).re :=
    convexHull_min hsub (convex_Iio (𝕜 := ℝ) _) h
  exact (lt_irrefl _) hh

end
end MOC
