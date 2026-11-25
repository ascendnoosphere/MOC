import MOC.SparseRow
import MOC.SupportDegreeBalance

/-! Induction for unitary matrices with at most three nonzero entries in each
row and column. -/

open Matrix

namespace MOC

noncomputable section

/-- Every row and column has at most three nonzero entries. -/
def SupportDegreeLEThree {n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  (∀ i, (supportColumns U {i}).card ≤ 3) ∧
    (∀ j, (supportColumns Uᴴ {j}).card ≤ 3)

private theorem supportColumns_singleton_card_le_of_embed {m n : ℕ}
    {V : Matrix (Fin m) (Fin m) ℂ} {U : Matrix (Fin n) (Fin n) ℂ}
    (i : Fin m) (j : Fin n) (e : Fin m ↪ Fin n)
    (hnz : ∀ l, V i l ≠ 0 → U j (e l) ≠ 0) :
    (supportColumns V {i}).card ≤ (supportColumns U {j}).card := by
  classical
  rw [← Finset.card_map e]
  apply Finset.card_le_card
  intro l hl
  obtain ⟨p, hp, rfl⟩ := Finset.mem_map.mp hl
  have hp' : V i p ≠ 0 := by simpa [supportColumns] using hp
  simpa [supportColumns] using hnz p hp'

private theorem normalizedSparseRowMinor_entry_eq_zero {n : ℕ}
    {U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (i j k : Fin (n + 1))
    (r s : Fin n) (hz : U (i.succAbove r) (j.succAbove s) = 0) :
    normalizedSparseRowMinor U i j k r s = 0 := by
  rw [normalizedSparseRowMinor, Matrix.mul_diagonal, Matrix.submatrix_apply]
  exact mul_eq_zero_of_left hz _

private theorem rowSupportDegree_normalizedSparseRowMinor_le {n : ℕ}
    {U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (i j k : Fin (n + 1)) (r : Fin n) :
    (supportColumns (normalizedSparseRowMinor U i j k) {r}).card ≤
      (supportColumns U {i.succAbove r}).card :=
  supportColumns_singleton_card_le_of_embed r (i.succAbove r) j.succAboveEmb
    (fun s hn hz => hn (normalizedSparseRowMinor_entry_eq_zero i j k r s hz))

private theorem columnSupportDegree_normalizedSparseRowMinor_le {n : ℕ}
    {U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (i j k : Fin (n + 1)) (s : Fin n) :
    (supportColumns (normalizedSparseRowMinor U i j k)ᴴ {s}).card ≤
      (supportColumns Uᴴ {j.succAbove s}).card := by
  apply supportColumns_singleton_card_le_of_embed s (j.succAbove s) i.succAboveEmb
  intro r hn hz
  simp only [Matrix.conjTranspose_apply] at hn hz
  exact hn (star_eq_zero.mpr
    (normalizedSparseRowMinor_entry_eq_zero i j k r s (star_eq_zero.mp hz)))

/-- A normalized row minor preserves the upper bound on both support degrees. -/
theorem supportDegreeLEThree_normalizedSparseRowMinor {n : ℕ}
    {U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (h : SupportDegreeLEThree U)
    (i j k : Fin (n + 1)) : SupportDegreeLEThree (normalizedSparseRowMinor U i j k) :=
  ⟨fun r => (rowSupportDegree_normalizedSparseRowMinor_le i j k r).trans (h.1 _),
    fun s => (columnSupportDegree_normalizedSparseRowMinor_le i j k s).trans (h.2 _)⟩

/-- The conjecture restricted to matrices with row and column support degree at most three. -/
def SupportDegreeLEThreeConjecture (n : ℕ) : Prop :=
  ∀ (a b : Fin n → ℂ) (U : Matrix (Fin n) (Fin n) ℂ),
    IsUnitary U → SupportDegreeLEThree U → Holds a b U

private theorem holds_of_row_degree_le_two_of_minors {n : ℕ}
    (a b : Fin (n + 1) → ℂ) {U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hU : IsUnitary U) (i : Fin (n + 1)) (hc : (supportColumns U {i}).card ≤ 2)
    (hSmall : ∀ p q, IsUnitary (normalizedSparseRowMinor U i p q) →
      Holds (a ∘ i.succAbove) (b ∘ p.succAbove) (normalizedSparseRowMinor U i p q)) :
    Holds a b U := by
  classical
  let S := supportColumns U {i}
  have hmem (l : Fin (n + 1)) : l ∈ S ↔ U i l ≠ 0 := by simp [S, supportColumns]
  have hpair (j k : Fin (n + 1)) (hzero : ∀ l, l ≠ j → l ≠ k → U i l = 0) :
      Holds a b U :=
    holds_of_two_supported_row_of_minors a b hU i j k hzero
      (fun p _ hV => hSmall p _ hV)
  by_cases h1 : S.card ≤ 1
  · obtain ⟨j, hj⟩ := Finset.card_le_one_iff_subset_singleton.mp h1
    apply hpair j j
    intro l hl _
    by_contra hn
    exact hl (Finset.mem_singleton.mp (hj ((hmem l).mpr hn)))
  · have h2 : S.card = 2 := by change S.card ≤ 2 at hc; omega
    obtain ⟨j, k, _, hk⟩ := Finset.card_eq_two.mp h2
    apply hpair j k
    intro l hlj hlk
    by_contra hn
    have hl := (hmem l).mpr hn
    rw [hk] at hl
    exact (Finset.mem_insert.mp hl).elim hlj (fun h => hlk (Finset.mem_singleton.mp h))

private theorem unitary_adjoint {n : ℕ} {U : Matrix (Fin n) (Fin n) ℂ}
    (hU : IsUnitary U) : IsUnitary Uᴴ := by
  simpa only [IsUnitary, Matrix.conjTranspose_conjTranspose] using hU.symm

/-- If all rows have at most three nonzero entries, either a low-degree row
or column reduces the problem to smaller matrices with the same row bound,
or every row and column has exactly three nonzero entries. -/
theorem holds_of_rowSupportDegreeLEThree_of_exact_three
    (hExact : ∀ n, (∀ m < n, SupportDegreeLEThreeConjecture m) →
      ∀ (a b : Fin n → ℂ) (U : Matrix (Fin n) (Fin n) ℂ), IsUnitary U →
        (∀ i, (supportColumns U {i}).card = 3) →
        (∀ j, (supportColumns Uᴴ {j}).card = 3) → Holds a b U) :
    ∀ n (a b : Fin n → ℂ) (U : Matrix (Fin n) (Fin n) ℂ), IsUnitary U →
      (∀ i, (supportColumns U {i}).card ≤ 3) → Holds a b U := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro a b U hU hdeg
    cases n with
    | zero => exact conjecture_zero a b U hU
    | succ n =>
      by_cases hrow : ∃ i, (supportColumns U {i}).card ≤ 2
      · obtain ⟨i, hi⟩ := hrow
        apply holds_of_row_degree_le_two_of_minors a b hU i hi
        intro p q hV
        exact ih n (Nat.lt_succ_self n) _ _ _ hV fun r =>
          (rowSupportDegree_normalizedSparseRowMinor_le i p q r).trans (hdeg _)
      by_cases hcol : ∃ j, (supportColumns Uᴴ {j}).card ≤ 2
      · obtain ⟨j, hj⟩ := hcol
        apply (holds_swap_iff a b hU).mp
        apply holds_of_row_degree_le_two_of_minors b a (unitary_adjoint hU) j hj
        intro p q hV
        apply (holds_swap_iff _ _ hV).mp
        apply ih n (Nat.lt_succ_self n) _ _ _ (unitary_adjoint hV)
        intro s
        have hs := columnSupportDegree_normalizedSparseRowMinor_le (U := Uᴴ) j p q s
        rw [Matrix.conjTranspose_conjTranspose] at hs
        exact hs.trans (hdeg _)
      have hcol' (j : Fin (n + 1)) : 3 ≤ (supportColumns Uᴴ {j}).card := by
        have hnot : ¬ (supportColumns Uᴴ {j}).card ≤ 2 := fun h => hcol ⟨j, h⟩
        omega
      obtain ⟨hrow', hcol'⟩ := supportDegrees_eq_of_row_le_of_column_ge 3 hdeg hcol'
      exact hExact (n + 1) (fun m hm a' b' V hV hd => ih m hm a' b' V hV hd.1)
        a b U hU hrow' hcol'

/-- The restriction to matrices with both support degree bounds follows from
the exact-degree-three case with smaller bounded orders available. -/
theorem holds_of_supportDegreeLEThree_of_exact_three
    (hExact : ∀ n, (∀ m < n, SupportDegreeLEThreeConjecture m) →
      ∀ (a b : Fin n → ℂ) (U : Matrix (Fin n) (Fin n) ℂ), IsUnitary U →
        (∀ i, (supportColumns U {i}).card = 3) →
        (∀ j, (supportColumns Uᴴ {j}).card = 3) → Holds a b U) :
    ∀ n, SupportDegreeLEThreeConjecture n :=
  fun n a b U hU hd => holds_of_rowSupportDegreeLEThree_of_exact_three hExact n a b U hU hd.1

end

end MOC
