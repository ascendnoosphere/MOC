import MOC.FourRealification
import MOC.HermitianByNormal
import MOC.OrderFourGivens

/-! Changing the basis within a repeated eigenspace can concentrate a row
before sparse deletion. The smaller partner spectrum uses only old values. -/

open Matrix

namespace MOC

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem rotateRows_entry (U : Matrix ι ι ℂ) {j k : ι} (hjk : j ≠ k)
    (c s : ℝ) (l m : ι) :
    rotateRows U j k c s l m =
      if l = j then (c : ℂ) * U j m + (s : ℂ) * U k m else
      if l = k then (c : ℂ) * U k m - (s : ℂ) * U j m else U l m := by
  change ((U.updateRow j ((c : ℂ) • U j + (s : ℂ) • U k)).updateRow k
    ((c : ℂ) • U k + (-(s : ℂ)) • U j)) l m = _
  by_cases hlj : l = j
  · subst l
    simp [Matrix.updateRow_apply, hjk, Pi.smul_apply, smul_eq_mul]
  · by_cases hlk : l = k
    · subst l
      simp [Matrix.updateRow_apply, hlj, Pi.smul_apply, smul_eq_mul, sub_eq_add_neg]
    · simp [Matrix.updateRow_apply, hlj, hlk]

private theorem rotateRows_eq_left_mul (U : Matrix ι ι ℂ) {j k : ι} (hjk : j ≠ k)
    (c s : ℝ) : rotateRows U j k c s = rotateRows 1 j k c s * U := by
  ext l m : 1
  rw [rotateRows_entry U hjk, Matrix.mul_apply]
  simp only [rotateRows_entry (1 : Matrix ι ι ℂ) hjk]
  by_cases hlj : l = j
  · simp only [if_pos hlj, add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]
    simp [Matrix.one_apply, ite_mul, Finset.sum_ite_eq]
  · by_cases hlk : l = k
    · simp only [if_neg hlj, if_pos hlk, sub_mul, Finset.sum_sub_distrib,
        mul_assoc, ← Finset.mul_sum]
      simp [Matrix.one_apply, ite_mul, Finset.sum_ite_eq]
    · simp [hlj, hlk, Matrix.one_apply, ite_mul, Finset.sum_ite_eq]

private theorem rotateRows_commutes_with_diagonal (b : ι → ℂ) {j k : ι} (hjk : j ≠ k)
    (hb : b j = b k) (c s : ℝ) :
    rotateRows 1 j k c s * diagonal b = diagonal b * rotateRows 1 j k c s := by
  ext l m : 1
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, rotateRows_entry _ hjk]
  by_cases hlm : l = m
  · subst m
    exact mul_comm _ _
  · by_cases hlj : l = j
    · subst l
      by_cases hkm : k = m
      · subst m
        rw [hb]
        exact mul_comm _ _
      · simp [Matrix.one_apply, hlm, hkm]
    · by_cases hlk : l = k
      · subst l
        by_cases hjm : j = m
        · subst m
          rw [hb]
          exact mul_comm _ _
        · simp [Matrix.one_apply, hlj, hlm, hjm]
      · simp [Matrix.one_apply, hlj, hlk, hlm]

private theorem rotateColumns_entry (U : Matrix ι ι ℂ) {j k : ι} (hjk : j ≠ k)
    (c s : ℝ) (i l : ι) :
    (rotateRows Uᴴ j k c s)ᴴ i l =
      if l = j then (c : ℂ) * U i j + (s : ℂ) * U i k else
      if l = k then (c : ℂ) * U i k - (s : ℂ) * U i j else U i l := by
  rw [Matrix.conjTranspose_apply, rotateRows_entry _ hjk]
  by_cases hlj : l = j
  · simp [hlj, Matrix.conjTranspose_apply, Complex.star_def]
  · by_cases hlk : l = k
    · simp [hlj, hlk, Matrix.conjTranspose_apply, Complex.star_def]
    · simp [hlj, hlk, Matrix.conjTranspose_apply]

private theorem exists_equal_value_pivots (b : ι → ℂ) (S : Finset ι) (x y : ℂ)
    (hS : 2 < S.card) (hvalues : ∀ j ∈ S, b j = x ∨ b j = y) :
    ∃ j ∈ S, ∃ k ∈ S, j ≠ k ∧ b j = b k := by
  classical
  by_contra h
  have hinj : Set.InjOn b (S : Set ι) := by
    intro j hj k hk he
    by_contra hjk
    exact h ⟨j, hj, k, hk, hjk, he⟩
  have hs : S.image b ⊆ {x, y} := by
    intro z hz
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hz
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hvalues j hj
  have hc := (Finset.card_image_of_injOn hinj).symm.trans_le (Finset.card_le_card hs)
  have hp : ({x, y} : Finset ℂ).card ≤ 2 := by
    simpa only [Finset.card_singleton] using Finset.card_insert_le x ({y} : Finset ℂ)
  exact (not_le_of_gt hS) (hc.trans hp)

/-- If a row meets at most two partner values, deletion needs only lower-order
pairs whose partner values come from the original spectrum. -/
theorem holds_of_row_meeting_two_spectral_values {n : ℕ}
    (a b : Fin (n + 1) → ℂ) (U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (hU : IsUnitary U) (i : Fin (n + 1)) (x y : ℂ)
    (hvalues : ∀ j, U i j ≠ 0 → b j = x ∨ b j = y)
    (hSmall : ∀ (a' b' : Fin n → ℂ) (V : Matrix (Fin n) (Fin n) ℂ),
      IsUnitary V → Set.range b' ⊆ Set.range b → Holds a' b' V) : Holds a b U := by
  classical
  let S (V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) := supportColumns V {i}
  have hmem (V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (j : Fin (n + 1)) :
      j ∈ S V ↔ V i j ≠ 0 := by simp [S, supportColumns]
  let P (m : ℕ) : Prop := ∀ (V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ),
    IsUnitary V → (∀ j, ((V i j).re : ℂ) = V i j) →
    (∀ j, V i j ≠ 0 → b j = x ∨ b j = y) → (S V).card = m → Holds a b V
  have hP (m : ℕ) : P m := by
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro V hV hreal hsupport hm
      by_cases hsmall : (S V).card ≤ 2
      · obtain ⟨j, k, hjk⟩ := exists_row_support_pair i hsmall
        apply holds_of_two_supported_row_of_minors a b hV i j k hjk
        intro p _ hminor
        apply hSmall _ _ _ hminor
        rintro _ ⟨l, rfl⟩
        exact ⟨p.succAbove l, rfl⟩
      · obtain ⟨j, hj, k, hk, hjk, hb⟩ := exists_equal_value_pivots b (S V) x y
          (lt_of_not_ge hsmall) fun l hl => hsupport l ((hmem V l).mp hl)
        let u := (V i j).re
        let v := (V i k).re
        let r := Real.sqrt (u ^ 2 + v ^ 2)
        have hu : u ≠ 0 := by
          intro hz
          exact (hmem V j).mp hj ((hreal j).symm.trans (by change (u : ℂ) = 0; simp [hz]))
        have hr0 : 0 < u ^ 2 + v ^ 2 := add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero hu) (sq_nonneg v)
        have hr : r ≠ 0 := (Real.sqrt_pos.2 hr0).ne'
        have hrr : r ^ 2 = u ^ 2 + v ^ 2 := Real.sq_sqrt hr0.le
        let c := v / r
        let s := -u / r
        have hcs : c ^ 2 + s ^ 2 = 1 := by
          change (v / r) ^ 2 + (-u / r) ^ 2 = 1
          rw [div_pow, div_pow, neg_sq, ← add_div, add_comm (v ^ 2), ← hrr,
            div_self (pow_ne_zero _ hr)]
        let R := rotateRows (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) j k c s
        let W := (rotateRows Vᴴ j k c s)ᴴ
        have hR : IsUnitary R := isUnitary_rotateRows _ isUnitary_one j k hjk c s hcs
        have hVadj : IsUnitary Vᴴ := ⟨by simpa using hV.2, by simpa using hV.1⟩
        have hWadj := isUnitary_rotateRows _ hVadj j k hjk c s hcs
        have hW : IsUnitary W := ⟨by simpa [W] using hWadj.2, by simpa [W] using hWadj.1⟩
        have hWrot : W = V * Rᴴ := by
          dsimp only [W, R]
          rw [rotateRows_eq_left_mul Vᴴ hjk, Matrix.conjTranspose_mul,
            Matrix.conjTranspose_conjTranspose]
        have hdiag : Rᴴ * diagonal b * R = diagonal b := by
          have hcomm : R * diagonal b = diagonal b * R :=
            rotateRows_commutes_with_diagonal b hjk hb c s
          rw [Matrix.mul_assoc, ← hcomm, ← Matrix.mul_assoc, hR.2, Matrix.one_mul]
        have hdet : determinantValue a b W = determinantValue a b V := by
          have hh : (V * Rᴴ) * diagonal b * (R * Vᴴ) = V * (Rᴴ * diagonal b * R) * Vᴴ := by
            simp only [Matrix.mul_assoc]
          unfold determinantValue
          rw [hWrot, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hh, hdiag]
        have hentry (l : Fin (n + 1)) : W i l =
            if l = j then (c : ℂ) * V i j + (s : ℂ) * V i k else
            if l = k then (c : ℂ) * V i k - (s : ℂ) * V i j else V i l :=
          rotateColumns_entry V hjk c s i l
        have hz : W i j = 0 := by
          have hzero : c * u + s * v = 0 := by
            dsimp only [c, s]
            field_simp [hr] <;> ring
          rw [hentry, if_pos rfl, ← hreal j, ← hreal k]
          exact_mod_cast hzero
        have hout (l : Fin (n + 1)) (hlj : l ≠ j) (hlk : l ≠ k) : W i l = V i l := by
          rw [hentry, if_neg hlj, if_neg hlk]
        have hsub : S W ⊆ (S V).erase j := by
          intro l hl
          have hlj : l ≠ j := by
            intro he
            subst l
            exact (hmem W j).mp hl hz
          refine Finset.mem_erase.mpr ⟨hlj, ?_⟩
          by_cases hlk : l = k
          · exact hlk.symm ▸ hk
          · exact (hmem V l).mpr fun he => (hmem W l).mp hl ((hout l hlj hlk).trans he)
        have hlt : (S W).card < m := by
          rw [← hm]
          exact (Finset.card_le_card hsub).trans_lt (Finset.card_erase_lt_of_mem hj)
        have hWreal (l : Fin (n + 1)) : ((W i l).re : ℂ) = W i l := by
          have he : ∃ t : ℝ, W i l = (t : ℂ) := by
            by_cases hlj : l = j
            · exact ⟨0, by simpa [hlj] using hz⟩
            · by_cases hlk : l = k
              · refine ⟨c * v - s * u, ?_⟩
                rw [hentry, if_neg hlj, if_pos hlk, ← hreal j, ← hreal k]
                push_cast <;> rfl
              · exact ⟨(V i l).re, (hout l hlj hlk).trans (hreal l).symm⟩
          obtain ⟨t, ht⟩ := he
          rw [ht, Complex.ofReal_re]
        have hWsupport (l : Fin (n + 1)) (hl : W i l ≠ 0) : b l = x ∨ b l = y :=
          hsupport l ((hmem V l).mp (Finset.mem_erase.mp (hsub ((hmem W l).mpr hl))).2)
        have hholds := ih (S W).card hlt W hW hWreal hWsupport rfl
        unfold Holds at hholds ⊢
        rwa [hdet] at hholds
  obtain ⟨V, hV, hrow, hminors⟩ := exists_unitary_with_real_row U hU i
  have hreal (j : Fin (n + 1)) : ((V i j).re : ℂ) = V i j := by
    rw [hrow, Complex.ofReal_re]
  have hsupport (j : Fin (n + 1)) (hj : V i j ≠ 0) : b j = x ∨ b j = y := by
    apply hvalues j
    intro hz
    exact hj (by simp [hrow, hz])
  have he : determinantValue a b V = determinantValue a b U := by
    rw [determinantValue_eq_sum_subsetMinors a b V hV,
      determinantValue_eq_sum_subsetMinors a b U hU]
    simp only [hminors]
  have hholds := hP (S V).card V hV hreal hsupport rfl
  unfold Holds at hholds ⊢
  rwa [he] at hholds

/-- To prove the all-order three-value case, it suffices to treat mixers
whose every row meets three distinct values in the grouped spectrum. -/
theorem three_value_hull_iff_every_row_meets_three_values :
    (∀ (n : ℕ) (a b : Fin n → ℂ) (U : Matrix (Fin n) (Fin n) ℂ),
      IsUnitary U → Nat.card (Set.range b) ≤ 3 → Holds a b U) ↔
    (∀ (n : ℕ) (a b : Fin n → ℂ) (U : Matrix (Fin n) (Fin n) ℂ),
      IsUnitary U → Nat.card (Set.range b) ≤ 3 →
      (∀ (i : Fin n) (x y : ℂ), ∃ j, U i j ≠ 0 ∧ b j ≠ x ∧ b j ≠ y) → Holds a b U) := by
  classical
  constructor
  · intro h n a b U hU hcard _
    exact h n a b U hU hcard
  · intro h n
    induction n with
    | zero => intro a b U hU _; exact conjecture_zero a b U hU
    | succ n ih =>
      intro a b U hU hcard
      by_cases hrow : ∃ (i : Fin (n + 1)) (x y : ℂ),
          ∀ j, U i j ≠ 0 → b j = x ∨ b j = y
      · obtain ⟨i, x, y, hi⟩ := hrow
        apply holds_of_row_meeting_two_spectral_values a b U hU i x y hi
        intro a' b' V hV hsub
        apply ih a' b' V hV
        rw [Set.Nat.card_coe_set_eq] at hcard ⊢
        exact (Set.ncard_le_ncard hsub (Set.finite_range b)).trans hcard
      · apply h (n + 1) a b U hU hcard
        intro i x y
        by_contra hmiss
        apply hrow
        refine ⟨i, x, y, fun j hj => ?_⟩
        by_contra! hne
        exact hmiss ⟨j, hj, hne⟩

/-- A partner column that meets at most two Hermitian eigenvalues permits
deletion using only the smaller Hermitian–normal inclusion. -/
theorem holds_hermitian_of_column_meeting_two_spectral_values {n : ℕ}
    (hSmall : HermitianByNormal (Fin n)) (a : Fin (n + 1) → ℝ) (b : Fin (n + 1) → ℂ)
    (U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (hU : IsUnitary U)
    (j : Fin (n + 1)) (x y : ℂ)
    (hvalues : ∀ i, U i j ≠ 0 → (a i : ℂ) = x ∨ (a i : ℂ) = y) :
    Holds (fun i => (a i : ℂ)) b U := by
  let A : Fin (n + 1) → ℂ := fun i => a i
  have hUadj : IsUnitary Uᴴ := ⟨by simpa using hU.2, by simpa using hU.1⟩
  apply (holds_swap_iff A b hU).mp
  apply holds_of_row_meeting_two_spectral_values b A Uᴴ hUadj j x y
  · intro i hi
    apply hvalues i
    intro hz
    exact hi (by simp only [Matrix.conjTranspose_apply, hz, star_zero])
  · intro b' a' V hV hsub
    have ha' : (fun i => ((a' i).re : ℂ)) = a' := by
      funext i
      obtain ⟨k, hk⟩ := hsub (Set.mem_range_self i)
      calc
        ((a' i).re : ℂ) = ((A k).re : ℂ) := congrArg (fun z : ℂ => (z.re : ℂ)) hk.symm
        _ = A k := by simp only [A, Complex.ofReal_re]
        _ = a' i := hk
    have hVadj : IsUnitary Vᴴ := ⟨by simpa using hV.2, by simpa using hV.1⟩
    have hh := hSmall (fun i => (a' i).re) b' Vᴴ hVadj
    rw [ha'] at hh
    simpa only [Matrix.conjTranspose_conjTranspose] using (holds_swap_iff a' b' hVadj).mpr hh

end

end MOC
