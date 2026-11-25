import MOC.MobiusRigidity
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-! The trace balance quantizes the two cluster sizes near an antipodal
pair. A sufficiently close antipodal approximation has exactly half its
entries of each sign. -/

open BigOperators

namespace MOC

noncomputable section

variable {J : Type*} [Fintype J]

/-- An unbalanced antipodal approximation to a zero-sum vector has squared
error at least $1/n^2$, at the unit-energy radius $1/sqrt{2n}$. -/
theorem antipodal_approximation_card_eq_of_close
    (n : ℕ) (hn : 0 < n) (hcard : Fintype.card J = 2 * n)
    (x : J → ℂ) (htrace : ∑ j, x j = 0) (s : J → ℝ)
    (hs : ∀ j, s j = Real.sqrt (1 / (2 * (n : ℝ))) ∨
      s j = - Real.sqrt (1 / (2 * (n : ℝ))))
    (hclose : (∑ j, Complex.normSq (x j - (s j : ℂ))) < 1 / (n : ℝ) ^ 2) :
    (Finset.univ.filter fun j => s j = Real.sqrt (1 / (2 * (n : ℝ)))).card = n := by
  classical
  let r : ℝ := Real.sqrt (1 / (2 * (n : ℝ)))
  let S : Finset J := Finset.univ.filter fun j => s j = r
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hn₂ : 0 < 2 * (n : ℝ) := mul_pos two_pos hnR
  have hr : 0 < r := Real.sqrt_pos_of_pos (one_div_pos.mpr hn₂)
  have hr₂ : r ^ 2 = 1 / (2 * (n : ℝ)) := Real.sq_sqrt (one_div_nonneg.mpr hn₂.le)
  have he (j : J) : s j + r = if s j = r then 2 * r else 0 := by
    split_ifs with h
    · rw [h]; ring
    · rw [(hs j).resolve_left h]; ring
  have hs' : (∑ j, s j) = 2 * r * ((S.card : ℝ) - (n : ℝ)) := by
    have h : (∑ j, (s j + r)) = (S.card : ℝ) * (2 * r) := by
      simp_rw [he, ← Finset.sum_filter]
      simp only [S, Finset.sum_const, nsmul_eq_mul]
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul] at h
    push_cast at h
    linarith only [h]
  have hsum : (∑ j, (x j - (s j : ℂ)).re) = -(∑ j, s j) := by
    simp only [Complex.sub_re, Complex.ofReal_re, Finset.sum_sub_distrib, ← Complex.re_sum,
      htrace, Complex.zero_re, zero_sub]
  have hc : (∑ j, s j) ^ 2 ≤ (2 * (n : ℝ)) * ∑ j, Complex.normSq (x j - (s j : ℂ)) := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun _ : J => (1 : ℝ)) (fun j => (x j - (s j : ℂ)).re)
    simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at h
    rw [hsum, neg_sq, hcard] at h
    push_cast at h
    refine h.trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => ?_) hn₂.le)
    rw [Complex.normSq_apply, pow_two]
    exact le_add_of_nonneg_right (mul_self_nonneg _)
  change S.card = n
  by_cases hne : S.card = n
  · exact hne
  exfalso
  have hz : ((S.card : ℤ) - (n : ℤ)) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hne)
  have hsq : (1 : ℝ) ≤ ((S.card : ℝ) - (n : ℝ)) ^ 2 := by
    exact_mod_cast ((one_le_sq_iff_one_le_abs _).mpr (Int.one_le_abs hz))
  have hb : 4 * r ^ 2 ≤ (∑ j, s j) ^ 2 := by
    rw [hs', mul_pow, mul_pow]
    nlinarith only [mul_le_mul_of_nonneg_left hsq (show 0 ≤ 4 * r ^ 2 by positivity)]
  have ht := (hb.trans hc).trans_lt (mul_lt_mul_of_pos_left hclose hn₂)
  rw [hr₂] at ht
  have hfrac : 4 * (1 / (2 * (n : ℝ))) = 2 * (n : ℝ) * (1 / (n : ℝ) ^ 2) := by
    field_simp [hnR.ne']
    ring
  rw [hfrac] at ht
  exact (lt_irrefl _ ht)


variable {ι : Type*} [Fintype ι]

/-- At a trace-balanced terminal optimizer, a sufficiently small angular
deficit forces the antipodal approximation to have exactly balanced signs. -/
theorem MobiusMomentBound.exists_balanced_antipodal_approximation [Nonempty ι] {a b : ι → ℂ}
    (hmoment : MobiusMomentBound a b) (hE : spectralEnergy a b = 1)
    (htrace : (∑ i, a i) = ∑ i, b i)
    (hC : (∑ i, (Complex.normSq (a i) : ℂ) * a i) =
      ∑ i, (Complex.normSq (b i) : ℂ) * b i)
    (hnearly : let x : ι ⊕ ι → ℂ := Sum.elim a (fun i => -b i)
      let n := Fintype.card ι
      let d := 1 - ‖∑ j, x j ^ 2‖
      (4 * (n : ℝ) + 3 / 2) * d - 2 * d ^ 2 < 1 / (n : ℝ) ^ 2) :
    let x : ι ⊕ ι → ℂ := Sum.elim a (fun i => -b i)
    let n := Fintype.card ι
    let d := 1 - ‖∑ j, x j ^ 2‖
    let r := Real.sqrt (1 / (2 * (n : ℝ)))
    ∃ (p : ℂ) (s : (ι ⊕ ι) → ℝ), Complex.normSq p = 1 ∧
      (∀ j, s j = r ∨ s j = -r) ∧
      (Finset.univ.filter fun j => s j = r).card = n ∧
      (∑ j, Complex.normSq (p * x j - (s j : ℂ))) ≤ (4 * (n : ℝ) + 3 / 2) * d - 2 * d ^ 2 := by
  intro x n d r
  obtain ⟨p,s,hp,hs,_,hclose⟩ := hmoment.exists_antipodal_approximation hE hC
  have hsum : ∑ j, p * x j = 0 := by
    rw [← Finset.mul_sum]
    simp only [x, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
      Finset.sum_neg_distrib, htrace, add_neg_cancel, mul_zero]
  exact ⟨p, s, hp, hs, antipodal_approximation_card_eq_of_close n Fintype.card_pos
    (by simp [n, Fintype.card_sum, two_mul]) _ hsum s hs (hclose.trans_lt hnearly), hclose⟩

/-- For two sign lists with equal positive multiplicity, a matching cannot
disagree at exactly one column. At the signed-pair center it follows that
a nonleading matching has at least two zero factors. -/
theorem exists_second_binary_mismatch [DecidableEq ι] (a b : ι → Bool)
    (heq : (∑ i, if a i then (1 : ℕ) else 0) = ∑ i, if b i then (1 : ℕ) else 0)
    (σ : Equiv.Perm ι) (j : ι) (hj : a (σ j) ≠ b j) :
    ∃ k, k ≠ j ∧ a (σ k) ≠ b k := by
  classical
  by_contra! h
  let A (k : ι) : ℕ := if a (σ k) then 1 else 0
  let B (k : ι) : ℕ := if b k then 1 else 0
  let T : Finset ι := Finset.univ.erase j
  have hsum : ∑ k, A k = ∑ k, B k :=
    (Equiv.sum_comp σ (fun k => if a k then (1 : ℕ) else 0)).trans heq
  have hrest : ∑ k ∈ T, A k = ∑ k ∈ T, B k := by
    apply Finset.sum_congr rfl
    intro k hk
    dsimp only [A, B]
    rw [h k (Finset.ne_of_mem_erase hk)]
  have hA := Finset.sum_erase_add Finset.univ A (Finset.mem_univ j)
  have hB := Finset.sum_erase_add Finset.univ B (Finset.mem_univ j)
  change (∑ k ∈ T, A k) + A j = ∑ k, A k at hA
  change (∑ k ∈ T, B k) + B j = ∑ k, B k at hB
  rw [hrest, hsum, ← hB] at hA
  have hval : A j = B j := Nat.add_left_cancel hA
  apply hj
  cases ha : a (σ j) <;> cases hb : b j <;> simp_all [A, B]


/-- At a balanced two-sign center, any nonleading matching contributes
at least a quadratic term along every affine spectral perturbation. -/
theorem X_sq_dvd_offleading_antipodal_matching [DecidableEq ι]
    (r : ℂ) (a b : ι → Bool) (da db : ι → ℂ)
    (heq : (∑ i, if a i then (1 : ℕ) else 0) = ∑ i, if b i then (1 : ℕ) else 0)
    (σ : Equiv.Perm ι) (j : ι) (hj : a (σ j) ≠ b j) :
    (Polynomial.X : Polynomial ℂ) ^ 2 ∣
      ∏ k, (Polynomial.C ((if a (σ k) then r else -r) + (if b k then r else -r)) +
        Polynomial.X * Polynomial.C (da (σ k) + db k)) := by
  obtain ⟨k, hkj, hk⟩ := exists_second_binary_mismatch a b heq σ j hj
  let S : Finset ι := Finset.univ.erase j
  let P (k : ι) : Polynomial ℂ :=
    Polynomial.C ((if a (σ k) then r else -r) + (if b k then r else -r)) +
      Polynomial.X * Polynomial.C (da (σ k) + db k)
  have hz (l : ι) (hl : a (σ l) ≠ b l) :
      P l = Polynomial.X * Polynomial.C (da (σ l) + db l) := by
    cases ha : a (σ l) <;> cases hb : b l <;> simp_all [P]
  have hm : k ∈ S := Finset.mem_erase.mpr ⟨hkj, Finset.mem_univ k⟩
  change (Polynomial.X : Polynomial ℂ) ^ 2 ∣ ∏ l, P l
  rw [← Finset.prod_erase_mul Finset.univ P (Finset.mem_univ j)]
  change (Polynomial.X : Polynomial ℂ) ^ 2 ∣ (∏ l ∈ S, P l) * P j
  rw [← Finset.prod_erase_mul S P hm, hz j hj, hz k hk]
  refine ⟨(∏ l ∈ S.erase k, P l) * Polynomial.C (da (σ k) + db k) *
    Polynomial.C (da (σ j) + db j), ?_⟩
  ring

end

end MOC
