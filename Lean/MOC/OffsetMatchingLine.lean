import MOC.MatchingQuartet
import MOC.Small
import MOC.Weights
import Mathlib.Logic.Equiv.Fintype

/-! An affine line missing the origin can contain all matching products only
when one spectrum is constant off a single label. -/

open Matrix

namespace MOC

private def fourEmbedding {α : Type*} (i j k l : α)
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) : Fin 4 ↪ α where
  toFun := ![i, j, k, l]
  inj' := by
    intro p q he
    fin_cases p <;> fin_cases q <;>
      simp_all [hij.symm, hik.symm, hil.symm, hjk.symm, hjl.symm, hkl.symm]

private theorem exception_or_disjoint_unequal_pairs {n : ℕ} (hn : 4 ≤ n) (f : Fin n → ℂ) :
    (∃ i c, ∀ j, j ≠ i → f j = c) ∨
      ∃ e : Fin 4 ↪ Fin n, f (e 0) ≠ f (e 1) ∧ f (e 2) ≠ f (e 3) := by
  classical
  by_cases h : ∃ i j, f i ≠ f j
  · obtain ⟨i, j, hf⟩ := h
    have hij : i ≠ j := fun he => hf (congrArg f he)
    let R : Finset (Fin n) := ({i, j} : Finset (Fin n))ᶜ
    have hR : 1 < R.card := by
      dsimp only [R]
      rw [Finset.card_compl, Finset.card_pair hij, Fintype.card_fin]
      omega
    have hout (k : Fin n) (hk : k ∈ R) : k ≠ i ∧ k ≠ j := by
      simpa [R, not_or] using Finset.mem_compl.mp hk
    by_cases hdiff : ∃ k ∈ R, ∃ l ∈ R, f k ≠ f l
    · obtain ⟨k, hk, l, hl, hkl⟩ := hdiff
      exact Or.inr ⟨fourEmbedding i j k l hij (hout k hk).1.symm (hout l hl).1.symm
        (hout k hk).2.symm (hout l hl).2.symm (fun he => hkl (congrArg f he)), hf, hkl⟩
    obtain ⟨k, hk, l, hl, hkl⟩ := Finset.one_lt_card.mp hR
    have hsame (p : Fin n) (hp : p ∈ R) : f p = f k :=
      Classical.byContradiction fun he => hdiff ⟨p, hp, k, hk, he⟩
    by_cases hi : f i = f k
    · refine Or.inl ⟨j, f k, fun p hp => ?_⟩
      by_cases he : p = i
      · simpa only [he] using hi
      · exact hsame p (by simp [R, he, hp])
    by_cases hj : f j = f k
    · refine Or.inl ⟨i, f k, fun p hp => ?_⟩
      by_cases he : p = j
      · simpa only [he] using hj
      · exact hsame p (by simp [R, he, hp])
    refine Or.inr ⟨fourEmbedding i k j l (hout k hk).1.symm hij (hout l hl).1.symm
      (hout k hk).2 hkl (hout l hl).2.symm, hi, ?_⟩
    change f j ≠ f l
    rw [hsame l hl]
    exact hj
  · let i₀ : Fin n := ⟨0, by omega⟩
    exact Or.inl ⟨i₀, f i₀, fun j _ => Classical.byContradiction fun he => h ⟨j, i₀, he⟩⟩

/-- If a line missing zero contains every matching product, then one summand
has at most one eigenvalue different from a common value. -/
theorem one_exception_of_matching_line_off_origin {n : ℕ} (hn : 4 ≤ n) (a b : Fin n → ℂ)
    (η : ℂ) (H : ℝ) (hH : H ≠ 0)
    (hline : ∀ σ, (η * matchingProduct a b σ).re = H) :
    (∃ i c, ∀ j, j ≠ i → a j = c) ∨ (∃ i c, ∀ j, j ≠ i → b j = c) := by
  classical
  have hη : η ≠ 0 := by
    intro h
    exact hH (by simpa only [h, zero_mul, Complex.zero_re] using (hline 1).symm)
  have hnz (i j : Fin n) : a i + b j ≠ 0 := by
    intro h
    have hp : matchingProduct a b (Equiv.swap j i) = 0 := by
      unfold matchingProduct
      exact Finset.prod_eq_zero (Finset.mem_univ j)
        (by simpa only [Equiv.swap_apply_left] using h)
    exact hH (by simpa only [hp, mul_zero, Complex.zero_re] using (hline (Equiv.swap j i)).symm)
  rcases exception_or_disjoint_unequal_pairs hn a with ha | ⟨ea, ha₀, ha₁⟩
  · exact Or.inl ha
  rcases exception_or_disjoint_unequal_pairs hn b with hb | ⟨eb, hb₀, hb₁⟩
  · exact Or.inr hb
  let E := eb.toEquivRange.symm.trans ea.toEquivRange
  let σ := E.extendSubtype
  have he (k : Fin 4) : σ (eb k) = ea k := by
    dsimp only [σ]
    rw [Equiv.extendSubtype_apply_of_mem _ _ (Set.mem_range_self k)]
    change (E (eb.toEquivRange k) : Fin n) = ea k
    simp [E]
  have hneq {i j : Fin 4} (hij : i ≠ j) : eb i ≠ eb j := eb.injective.ne hij
  have hz := matchingProduct_disjoint_swaps_common_height_eq_zero_of_unequal_pairs
    a b σ (eb 0) (eb 1) (eb 2) (eb 3)
    (hneq (by decide)) (hneq (by decide)) (hneq (by decide))
    (hneq (by decide)) (hneq (by decide)) (hneq (by decide))
    (by simpa only [he] using ha₀) (by simpa only [he] using ha₁)
    hb₀ hb₁ hnz hη (hline _) (hline _) (hline _) (hline _)
  exact (hH hz).elim

/-- A matching line missing zero implies the determinant inclusion, with
arbitrary spectral multiplicities. -/
theorem holds_of_collinear_matching_products_off_origin {n : ℕ} (a b : Fin n → ℂ)
    (η : ℂ) (H : ℝ) (hH : H ≠ 0) (hline : ∀ σ, (η * matchingProduct a b σ).re = H)
    (U : Matrix (Fin n) (Fin n) ℂ) (hU : IsUnitary U) : Holds a b U := by
  by_cases hn : n ≤ 3
  · exact conjecture_le_three hn a b U hU
  rcases one_exception_of_matching_line_off_origin (by omega) a b η H hH hline with
    ⟨i, c, ha⟩ | ⟨j, c, hb⟩
  · have hUs : IsUnitary Uᴴ := ⟨by simpa using hU.2, by simpa using hU.1⟩
    exact (holds_swap_iff a b hU).mp (holds_one_exception b a Uᴴ hUs i c ha)
  · exact holds_one_exception a b U hU j c hb

end MOC
