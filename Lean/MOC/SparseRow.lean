import MOC.SupportBlocks
import Mathlib.Algebra.BigOperators.Fin

/-! Deleting a nonzero pivot in a row supported on two columns gives a
smaller unitary after rescaling the surviving support column. -/

open BigOperators Matrix

namespace MOC

noncomputable section

private def rowDeletionScale {n : ℕ} (U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (i j k : Fin (n + 1)) (l : Fin n) : ℂ :=
  if j.succAbove l = k then (U i j)⁻¹ else 1

/-- Delete the row and pivot column, then divide the other support column
by the pivot entry if that column survives. -/
def normalizedSparseRowMinor {n : ℕ} (U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (i j k : Fin (n + 1)) : Matrix (Fin n) (Fin n) ℂ :=
  U.submatrix i.succAbove j.succAbove * diagonal (rowDeletionScale U i j k)

/-- A nonzero pivot from a row supported on `{j,k}` has a unitary normalized minor. -/
theorem unitary_normalizedSparseRowMinor {n : ℕ}
    {U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (hU : IsUnitary U)
    (i j k : Fin (n + 1)) (hj : U i j ≠ 0)
    (hzero : ∀ l, l ≠ j → l ≠ k → U i l = 0) :
    IsUnitary (normalizedSparseRowMinor U i j k) := by
  classical
  let M := U.submatrix i.succAbove j.succAbove
  let d := rowDeletionScale U i j k
  have hpair (hjk : j ≠ k) : star (U i j) * U i j + star (U i k) * U i k = 1 := by
    have hrow : (∑ l, star (U i l) * U i l) = 1 := by
      have h := congrArg (fun W : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ => W i i) hU.1
      simpa only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply_eq, mul_comm]
        using h
    calc
      _ = ∑ l ∈ ({j, k} : Finset (Fin (n + 1))), star (U i l) * U i l := by
        rw [Finset.sum_pair hjk]
      _ = ∑ l, star (U i l) * U i l := by
        apply Finset.sum_subset (Finset.subset_univ _)
        intro l _ hl
        have h : l ≠ j ∧ l ≠ k := by
          simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using hl
        rw [hzero l h.1 h.2, mul_zero]
      _ = 1 := hrow
  have hgram (l m : Fin n) : (Mᴴ * M) l m =
      (1 : Matrix (Fin n) (Fin n) ℂ) l m -
        star (U i (j.succAbove l)) * U i (j.succAbove m) := by
    have h := congrArg (fun W : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ =>
      W (j.succAbove l) (j.succAbove m)) hU.2
    change (Uᴴ * U) (j.succAbove l) (j.succAbove m) = _ at h
    rw [Matrix.mul_apply, Fin.sum_univ_succAbove _ i] at h
    apply (eq_sub_iff_add_eq).2
    rw [add_comm]
    simpa only [M, Matrix.mul_apply, Matrix.submatrix_apply, Matrix.conjTranspose_apply,
      Matrix.one_apply, Fin.succAbove_right_inj] using h
  have hi : (M * diagonal d)ᴴ * (M * diagonal d) = 1 := by
    have hmul : (M * diagonal d)ᴴ * (M * diagonal d) =
        diagonal (star d) * (Mᴴ * M) * diagonal d := by
      simp only [Matrix.conjTranspose_mul, Matrix.diagonal_conjTranspose, Matrix.mul_assoc]
    rw [hmul]
    ext l m : 1
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul, hgram]
    change star (d l) * ((1 : Matrix (Fin n) (Fin n) ℂ) l m -
      star (U i (j.succAbove l)) * U i (j.succAbove m)) * d m = _
    by_cases hlm : l = m
    · subst m
      rw [Matrix.one_apply_eq]
      by_cases hk : j.succAbove l = k
      · have hjk : j ≠ k := fun h => j.succAbove_ne l (hk.trans h.symm)
        have heq : 1 - star (U i k) * U i k = star (U i j) * U i j :=
          ((eq_sub_iff_add_eq).2 (hpair hjk)).symm
        rw [show d l = (U i j)⁻¹ from if_pos hk, hk, heq, star_inv₀]
        calc
          _ = ((star (U i j))⁻¹ * star (U i j)) * (U i j * (U i j)⁻¹) := by ring
          _ = 1 := by
            rw [inv_mul_cancel₀ (star_ne_zero.mpr hj), mul_inv_cancel₀ hj, one_mul]
      · have hz := hzero (j.succAbove l) (j.succAbove_ne l) hk
        simp [d, rowDeletionScale, hk, hz]
    · have hz : star (U i (j.succAbove l)) * U i (j.succAbove m) = 0 := by
        by_cases hk : j.succAbove l = k
        · have hk' : j.succAbove m ≠ k := fun hm =>
            hlm (Fin.succAbove_right_injective (hk.trans hm.symm))
          rw [hzero _ (j.succAbove_ne m) hk', mul_zero]
        · rw [hzero _ (j.succAbove_ne l) hk, star_zero, zero_mul]
      simp only [Matrix.one_apply_ne hlm, hz, sub_zero, mul_zero, zero_mul]
  exact ⟨Matrix.mul_eq_one_comm.mp hi, hi⟩

private def weightedEntries {ι : Type*} (a b : ι → ℂ) (U : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  Matrix.of fun i j => (a i + b j) * U i j

private theorem det_weightedEntries {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a b : ι → ℂ) (U : Matrix ι ι ℂ) (hU : IsUnitary U) :
    (weightedEntries a b U).det = determinantValue a b U * U.det := by
  have h : (diagonal a + U * diagonal b * Uᴴ) * U = weightedEntries a b U := by
    rw [Matrix.add_mul, Matrix.mul_assoc (U * diagonal b), hU.2, Matrix.mul_one]
    ext i j : 1
    simp only [weightedEntries, Matrix.of_apply, Matrix.add_apply,
      Matrix.diagonal_mul, Matrix.mul_diagonal]
    ring
  change (weightedEntries a b U).det = (diagonal a + U * diagonal b * Uᴴ).det * U.det
  rw [← h, Matrix.det_mul]

private theorem det_weightedEntries_deleted {n : ℕ}
    (a b : Fin (n + 1) → ℂ) (U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (i j k : Fin (n + 1)) (hj : U i j ≠ 0)
    (hV : IsUnitary (normalizedSparseRowMinor U i j k)) :
    ((weightedEntries a b U).submatrix i.succAbove j.succAbove).det =
      determinantValue (a ∘ i.succAbove) (b ∘ j.succAbove) (normalizedSparseRowMinor U i j k) *
        (U.submatrix i.succAbove j.succAbove).det := by
  let D := diagonal (rowDeletionScale U i j k)
  have hD : D.det ≠ 0 := by
    change (diagonal (rowDeletionScale U i j k)).det ≠ 0
    rw [Matrix.det_diagonal]
    apply Finset.prod_ne_zero_iff.mpr
    intro l _
    by_cases hl : j.succAbove l = k <;> simp [rowDeletionScale, hl, hj]
  have hscale :
      weightedEntries (a ∘ i.succAbove) (b ∘ j.succAbove) (normalizedSparseRowMinor U i j k) =
        (weightedEntries a b U).submatrix i.succAbove j.succAbove * D := by
    ext l m : 1
    simp only [weightedEntries, normalizedSparseRowMinor, D, Matrix.of_apply,
      Matrix.mul_diagonal, Matrix.submatrix_apply, Function.comp_apply, mul_assoc]
  apply mul_right_cancel₀ hD
  rw [← Matrix.det_mul, ← hscale, det_weightedEntries _ _ _ hV]
  change _ * ((U.submatrix i.succAbove j.succAbove) * D).det = _
  rw [Matrix.det_mul, mul_assoc]

private theorem cofactor_mul_eq_normSq {n : ℕ}
    {U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (hU : IsUnitary U)
    (i j : Fin (n + 1)) :
    (-1 : ℂ) ^ (i + j : ℕ) * U i j * (U.submatrix i.succAbove j.succAbove).det =
      (Complex.normSq (U i j) : ℂ) * U.det := by
  have h := congrArg (fun W : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ => W j i)
    (adjugate_unitary U hU)
  change U.adjugate j i = (U.det • Uᴴ) j i at h
  rw [Matrix.adjugate_fin_succ_eq_det_submatrix, Matrix.smul_apply, smul_eq_mul,
    Matrix.conjTranspose_apply] at h
  rw [Complex.normSq_eq_conj_mul_self]
  change _ = (star (U i j) * U i j) * U.det
  calc
    _ = ((-1 : ℂ) ^ (i + j : ℕ) * (U.submatrix i.succAbove j.succAbove).det) * U i j := by ring
    _ = _ := by rw [h]; ring

/-- Extend a matching of a row and column minor by the deleted pivot. -/
def extendSparseRowMatching {n : ℕ} (i j : Fin (n + 1)) (σ : Equiv.Perm (Fin n)) :
    Equiv.Perm (Fin (n + 1)) :=
  ((finSuccEquiv' j).trans (Equiv.optionCongr σ)).trans (finSuccEquiv' i).symm

theorem matchingProduct_extendSparseRowMatching {n : ℕ} (a b : Fin (n + 1) → ℂ)
    (i j : Fin (n + 1)) (σ : Equiv.Perm (Fin n)) :
    matchingProduct a b (extendSparseRowMatching i j σ) =
      (a i + b j) * matchingProduct (a ∘ i.succAbove) (b ∘ j.succAbove) σ := by
  let τ := extendSparseRowMatching i j σ
  have hj : τ j = i := by simp [τ, extendSparseRowMatching, Equiv.optionCongr]
  have hs (l : Fin n) : τ (j.succAbove l) = i.succAbove (σ l) := by
    simp [τ, extendSparseRowMatching, Equiv.optionCongr]
  change matchingProduct a b τ = _
  unfold matchingProduct
  rw [Fin.prod_univ_succAbove (fun l => a (τ l) + b l) j, hj]
  simp_rw [hs, Function.comp_apply]

private theorem mul_mem_matchingHull_of_deleted {n : ℕ} (a b : Fin (n + 1) → ℂ)
    (i j : Fin (n + 1)) {z : ℂ}
    (hz : z ∈ convexHull ℝ (Set.range (matchingProduct (a ∘ i.succAbove) (b ∘ j.succAbove)))) :
    (a i + b j) * z ∈ convexHull ℝ (Set.range (matchingProduct a b)) := by
  let f : ℂ →ₗ[ℝ] ℂ := LinearMap.mulLeft ℝ (a i + b j)
  change f z ∈ convexHull ℝ (Set.range (matchingProduct a b))
  apply convexHull_min ?_ ((convex_convexHull ℝ _).linear_preimage f) hz
  rintro _ ⟨σ, rfl⟩
  change (a i + b j) * matchingProduct (a ∘ i.succAbove) (b ∘ j.succAbove) σ ∈
    convexHull ℝ (Set.range (matchingProduct a b))
  rw [← matchingProduct_extendSparseRowMatching]
  exact matchingProduct_mem_hull a b _

/-- The normalized minor at a nonzero pivot in a row supported on two columns is unitary. -/
theorem unitary_normalizedSparseRowMinor_at_pivot {n : ℕ}
    {U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (hU : IsUnitary U)
    (i j k p : Fin (n + 1)) (hzero : ∀ l, l ≠ j → l ≠ k → U i l = 0)
    (hp : U i p ≠ 0) :
    IsUnitary (normalizedSparseRowMinor U i p (if p = j then k else j)) := by
  apply unitary_normalizedSparseRowMinor hU _ _ _ hp
  by_cases hpj : p = j
  · subst p
    simpa only [if_pos rfl] using hzero
  · have hpk : p = k := by
      by_contra hpk
      exact hp (hzero p hpj hpk)
    intro l hl hl'
    exact hzero l (by simpa only [if_neg hpj] using hl') (by simpa only [hpk] using hl)

/-- The squared magnitudes of the nonzero pivots in a unitary row sum to one. -/
theorem sum_normSq_sparseRow_pivots {n : ℕ}
    {U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (hU : IsUnitary U) (i : Fin (n + 1)) :
    (∑ p ∈ Finset.univ.filter (fun p => U i p ≠ 0), Complex.normSq (U i p)) = 1 := by
  classical
  have h := sum_col_of_mem_doublyStochastic (normSq_transpose_doublyStochastic U hU) i
  change (∑ p, Complex.normSq (U i p)) = 1 at h
  rw [← h]
  apply Finset.sum_subset (Finset.subset_univ _)
  intro p _ hp
  have hp' : U i p = 0 := by simpa using hp
  rw [hp', map_zero]

/-- Laplace expansion over the nonzero pivots of a row supported on two columns. -/
theorem determinantValue_two_supported_row {n : ℕ}
    (a b : Fin (n + 1) → ℂ) {U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hU : IsUnitary U) (i j k : Fin (n + 1)) (hzero : ∀ l, l ≠ j → l ≠ k → U i l = 0) :
    determinantValue a b U =
      ∑ p ∈ Finset.univ.filter (fun p => U i p ≠ 0), Complex.normSq (U i p) •
        ((a i + b p) * determinantValue (a ∘ i.succAbove) (b ∘ p.succAbove)
          (normalizedSparseRowMinor U i p (if p = j then k else j))) := by
  classical
  let S := Finset.univ.filter (fun p => U i p ≠ 0)
  let other (p : Fin (n + 1)) := if p = j then k else j
  let V (p : Fin (n + 1)) := normalizedSparseRowMinor U i p (other p)
  have hmem (p : Fin (n + 1)) : p ∈ S ↔ U i p ≠ 0 := by simp [S]
  have hLaplace : (weightedEntries a b U).det =
      ∑ p ∈ S, (-1 : ℂ) ^ (i + p : ℕ) * weightedEntries a b U i p *
        ((weightedEntries a b U).submatrix i.succAbove p.succAbove).det := by
    rw [Matrix.det_succ_row _ i]
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro p _ hp
    have hp' : U i p = 0 := not_ne_iff.mp (fun hn => hp ((hmem p).mpr hn))
    simp [weightedEntries, hp']
  change determinantValue a b U = ∑ p ∈ S, Complex.normSq (U i p) •
    ((a i + b p) * determinantValue (a ∘ i.succAbove) (b ∘ p.succAbove) (V p))
  apply mul_right_cancel₀ (det_ne_zero_of_unitary hU)
  rw [← det_weightedEntries _ _ _ hU, hLaplace, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro p hp
  have hnz := (hmem p).mp hp
  have hminor := det_weightedEntries_deleted a b U i p (other p) hnz
    (unitary_normalizedSparseRowMinor_at_pivot hU i j k p hzero hnz)
  change _ = determinantValue (a ∘ i.succAbove) (b ∘ p.succAbove) (V p) *
    (U.submatrix i.succAbove p.succAbove).det at hminor
  rw [hminor]
  simp only [weightedEntries, Matrix.of_apply, Complex.real_smul]
  calc
    _ = ((-1 : ℂ) ^ (i + p : ℕ) * U i p * (U.submatrix i.succAbove p.succAbove).det) *
        ((a i + b p) * determinantValue (a ∘ i.succAbove) (b ∘ p.succAbove) (V p)) := by ring
    _ = _ := by rw [cofactor_mul_eq_normSq hU i p]; ring

/-- A row supported on two columns reduces the determinant inclusion to the
normalized minors obtained at its nonzero pivots. -/
theorem holds_of_two_supported_row_of_minors {n : ℕ}
    (a b : Fin (n + 1) → ℂ) {U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hU : IsUnitary U) (i j k : Fin (n + 1)) (hzero : ∀ l, l ≠ j → l ≠ k → U i l = 0)
    (hSmall : ∀ p, U i p ≠ 0 → IsUnitary (normalizedSparseRowMinor U i p (if p = j then k else j)) →
      Holds (a ∘ i.succAbove) (b ∘ p.succAbove)
        (normalizedSparseRowMinor U i p (if p = j then k else j))) :
    Holds a b U := by
  classical
  unfold Holds
  rw [determinantValue_two_supported_row a b hU i j k hzero]
  apply (convex_convexHull ℝ _).sum_mem
    (fun _ _ => Complex.normSq_nonneg _) (sum_normSq_sparseRow_pivots hU i)
  intro p hp
  have hnz : U i p ≠ 0 := (Finset.mem_filter.mp hp).2
  exact mul_mem_matchingHull_of_deleted a b i p
    (hSmall p hnz (unitary_normalizedSparseRowMinor_at_pivot hU i j k p hzero hnz))

/-- A row supported on two columns reduces the determinant inclusion to the
conjecture in order one smaller. -/
theorem holds_of_two_supported_row {n : ℕ} (hSmall : Conjecture (Fin n))
    (a b : Fin (n + 1) → ℂ) {U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hU : IsUnitary U) (i j k : Fin (n + 1)) (hzero : ∀ l, l ≠ j → l ≠ k → U i l = 0) :
    Holds a b U :=
  holds_of_two_supported_row_of_minors a b hU i j k hzero fun _ _ hV => hSmall _ _ _ hV

/-- An upper-Hessenberg relative unitary satisfies the determinant inclusion
for arbitrary spectra in every finite order. -/
theorem holds_of_upper_hessenberg {n : ℕ} (a b : Fin n → ℂ)
    {U : Matrix (Fin n) (Fin n) ℂ} (hU : IsUnitary U)
    (hHess : ∀ i j : Fin n, j.val + 1 < i.val → U i j = 0) : Holds a b U := by
  induction n with
  | zero => exact conjecture_zero _ _ _ hU
  | succ n ih =>
    cases n with
    | zero => exact conjecture_one _ _ _ hU
    | succ n =>
      let i := Fin.last (n + 1)
      let k := (Fin.last n).castSucc
      have hzero (l : Fin (n + 2)) (hli : l ≠ i) (hlk : l ≠ k) : U i l = 0 := by
        apply hHess
        have hi : l.val ≠ n + 1 := fun h => hli (Fin.ext h)
        have hk : l.val ≠ n := fun h => hlk (Fin.ext h)
        have hb := l.isLt
        change l.val + 1 < n + 1
        omega
      apply holds_of_two_supported_row_of_minors a b hU i i k hzero
      intro p hp hV
      apply ih _ _ hV
      intro l m hlm
      have hpbound : n ≤ p.val := by
        by_contra! hlt
        exact hp (hHess i p (by change p.val + 1 < n + 1; omega))
      have hmp : m.castSucc < p := by
        have hb := l.isLt
        change m.val < p.val
        omega
      rw [normalizedSparseRowMinor, Matrix.mul_diagonal, Matrix.submatrix_apply,
        show i.succAbove l = l.castSucc from Fin.succAbove_last_apply l,
        Fin.succAbove_of_castSucc_lt _ _ hmp,
        hHess l.castSucc m.castSucc hlm, zero_mul]

/-- Rows and columns may be independently relabeled before checking the
upper-Hessenberg condition. -/
theorem holds_of_reindexed_upper_hessenberg {ι : Type*} [Fintype ι] [DecidableEq ι]
    {n : ℕ} (eRow eCol : Fin n ≃ ι) (a b : ι → ℂ) {U : Matrix ι ι ℂ} (hU : IsUnitary U)
    (hHess : ∀ i j : Fin n, j.val + 1 < i.val → U (eRow i) (eCol j) = 0) : Holds a b U :=
  (holds_reindex_iff eRow eCol a b U).mp
    (holds_of_upper_hessenberg _ _ (unitary_reindex eRow eCol hU) hHess)

/-- The support of a row of degree at most two lies in a pair of columns. -/
theorem exists_row_support_pair {n : ℕ} {U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (i : Fin (n + 1)) (hc : (supportColumns U {i}).card ≤ 2) :
    ∃ j k, ∀ l, l ≠ j → l ≠ k → U i l = 0 := by
  classical
  let S := supportColumns U {i}
  have hmem (l : Fin (n + 1)) : l ∈ S ↔ U i l ≠ 0 := by simp [S, supportColumns]
  by_cases h1 : S.card ≤ 1
  · obtain ⟨j, hj⟩ := Finset.card_le_one_iff_subset_singleton.mp h1
    refine ⟨j, j, ?_⟩
    intro l hl _
    by_contra hn
    exact hl (Finset.mem_singleton.mp (hj ((hmem l).mpr hn)))
  · have h2 : S.card = 2 := by change S.card ≤ 2 at hc; omega
    obtain ⟨j, k, _, hk⟩ := Finset.card_eq_two.mp h2
    refine ⟨j, k, ?_⟩
    intro l hlj hlk
    by_contra hn
    have hl := (hmem l).mpr hn
    rw [hk] at hl
    exact (Finset.mem_insert.mp hl).elim hlj (fun h => hlk (Finset.mem_singleton.mp h))

theorem holds_of_row_degree_le_two {n : ℕ} (hSmall : Conjecture (Fin n))
    (a b : Fin (n + 1) → ℂ) {U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hU : IsUnitary U) (i : Fin (n + 1)) (hc : (supportColumns U {i}).card ≤ 2) :
    Holds a b U := by
  obtain ⟨j, k, hjk⟩ := exists_row_support_pair i hc
  exact holds_of_two_supported_row hSmall a b hU i j k hjk

theorem holds_of_column_degree_le_two {n : ℕ} (hSmall : Conjecture (Fin n))
    (a b : Fin (n + 1) → ℂ) {U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hU : IsUnitary U) (j : Fin (n + 1)) (hc : (supportColumns Uᴴ {j}).card ≤ 2) :
    Holds a b U := by
  have hU' : IsUnitary Uᴴ := by
    constructor
    · simpa only [Matrix.conjTranspose_conjTranspose] using hU.2
    · simpa only [Matrix.conjTranspose_conjTranspose] using hU.1
  exact (holds_swap_iff a b hU).mp (holds_of_row_degree_le_two hSmall b a hU' j hc)

/-- It suffices to treat relative eigenbases with at least three nonzero entries
in every row and column. -/
theorem mocIsTrue_iff_support_degree_at_least_three :
    MOCIsTrue ↔ ∀ (n : ℕ), 4 ≤ n → ∀ (a b : Fin n → ℂ)
      (U : Matrix (Fin n) (Fin n) ℂ), IsUnitary U →
      (∀ i, 3 ≤ (supportColumns U {i}).card) →
      (∀ j, 3 ≤ (supportColumns Uᴴ {j}).card) → Holds a b U := by
  constructor
  · intro h n _ a b U hU _ _
    exact h n a b U hU
  · intro h
    by_contra hfail
    obtain ⟨n, hn, hnot, hbelow⟩ := exists_least_bad_order hfail
    cases n with
    | zero => omega
    | succ n =>
      unfold Conjecture at hnot
      push_neg at hnot
      obtain ⟨a, b, U, hU, hbad⟩ := hnot
      have hSmall := hbelow n (Nat.lt_succ_self n)
      refine hbad (h (n + 1) hn a b U hU ?_ ?_)
      · intro i
        by_contra hi
        exact hbad (holds_of_row_degree_le_two hSmall a b hU i (by omega))
      · intro j
        by_contra hj
        exact hbad (holds_of_column_degree_le_two hSmall a b hU j (by omega))

end

end MOC
