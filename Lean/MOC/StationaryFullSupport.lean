import MOC.Weights
import Mathlib.Analysis.Convex.Birkhoff

/-! Symbolic full-support pivot tests. A nonnegative corrected singleton
table admits a probability law supported on the pivot face. -/

open BigOperators Matrix Finset

namespace MOC.StationaryFullSupport

variable {ι : Type*} [DecidableEq ι]

/-- Full corrected singleton table, with the anchor row replaced by its delta. -/
noncomputable def corrected (U : Matrix ι ι ℝ) (i j : ι) : Matrix ι ι ℝ :=
  fun r s => if r = i then (if s = j then 1 else 0)
    else U r s * (U r s - U r j * U i s / U i j)

/-- Every rectangle through a nonzero pivot gives this denominator-free
test. No sign convention on the entries is required. -/
theorem corrected_nonneg_iff (U : Matrix ι ι ℝ) {i j r s : ι}
    (hp : U i j ≠ 0) (hr : r ≠ i) :
    0 ≤ corrected U i j r s ↔
      0 ≤ (U i j * U r s) * (U i j * U r s - U r j * U i s) := by
  have heq : U i j ^ 2 * corrected U i j r s =
      (U i j * U r s) * (U i j * U r s - U r j * U i s) := by
    simp only [corrected, if_neg hr]
    field_simp
    ring
  rw [← heq]
  exact (mul_nonneg_iff_of_pos_left (sq_pos_of_ne_zero hp)).symm

/-- A same-sign cross product must not be larger in magnitude than the
direct product. Opposite signs impose no constraint. -/
theorem corrected_nonneg_iff_same_sign (U : Matrix ι ι ℝ) {i j r s : ι}
    (hp : U i j ≠ 0) (hr : r ≠ i) :
    0 ≤ corrected U i j r s ↔
      0 < (U i j * U r s) * (U r j * U i s) →
        |U r j * U i s| ≤ |U i j * U r s| := by
  rw [corrected_nonneg_iff U hp hr]
  generalize U i j * U r s = x
  generalize U r j * U i s = y
  rcases le_total 0 x with hx | hx <;> rcases le_total 0 y with hy | hy
  · rw [abs_of_nonneg hx, abs_of_nonneg hy]
    constructor
    · intro h hs
      have hx' : 0 < x := by
        by_contra! h
        have : x = 0 := le_antisymm h hx
        simp [this] at hs
      exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_left hx').mp h)
    · intro h
      by_cases hs : 0 < x * y
      · exact mul_nonneg hx (sub_nonneg.mpr (h hs))
      · have hz : x * y = 0 := le_antisymm (le_of_not_gt hs) (mul_nonneg hx hy)
        nlinarith [sq_nonneg x]
  · constructor
    · intro _ hs
      exact False.elim ((not_lt_of_ge (mul_nonpos_of_nonneg_of_nonpos hx hy)) hs)
    · intro _
      exact mul_nonneg hx (sub_nonneg.mpr (hy.trans hx))
  · constructor
    · intro _ hs
      exact False.elim ((not_lt_of_ge (mul_nonpos_of_nonpos_of_nonneg hx hy)) hs)
    · intro _
      exact mul_nonneg_of_nonpos_of_nonpos hx (sub_nonpos.mpr (hx.trans hy))
  · rw [abs_of_nonpos hx, abs_of_nonpos hy]
    constructor
    · intro h hs
      have hx' : x < 0 := lt_of_le_of_ne hx (by intro h; simp [h] at hs)
      have hxy : x - y ≤ 0 := by
        by_contra! hn
        exact (not_lt_of_ge h) (mul_neg_of_neg_of_pos hx' hn)
      exact neg_le_neg (sub_nonpos.mp hxy)
    · intro h
      by_cases hs : 0 < x * y
      · exact mul_nonneg_of_nonpos_of_nonpos hx
          (sub_nonpos.mpr (neg_le_neg_iff.mp (h hs)))
      · have hz : x * y = 0 := le_antisymm (le_of_not_gt hs)
          (mul_nonneg_of_nonpos_of_nonpos hx hy)
        nlinarith [sq_nonneg x]

/-- A quantitative dense regime: uniformly small entries in the pivot's
arms are allowed if the surviving entries are bounded below in magnitude.
The matrix need not be sparse and the assumption is only local to the
selected row and column and the magnitudes in their complement. -/
theorem corrected_nonneg_of_amplitude (U : Matrix ι ι ℝ) {i j : ι}
    {κ δ ε : ℝ} (hκ : 0 < κ) (hδ : 0 ≤ δ) (hε : 0 ≤ ε)
    (hp : κ ≤ |U i j|) (hgap : δ ^ 2 ≤ κ * ε)
    (hr : ∀ r, r ≠ i → |U r j| ≤ δ)
    (hs : ∀ s, s ≠ j → |U i s| ≤ δ)
    (hinside : ∀ r s, r ≠ i → s ≠ j → ε ≤ |U r s|) :
    ∀ r s, 0 ≤ corrected U i j r s := by
  have hp' : U i j ≠ 0 := by intro hz; simp [hz] at hp; linarith
  intro r s
  by_cases hri : r = i
  · subst r
    simp only [corrected, if_pos rfl]
    split_ifs <;> norm_num
  by_cases hsj : s = j
  · subst s
    simp [corrected, hri, hp', mul_div_cancel_right₀]
  apply (corrected_nonneg_iff_same_sign U hp' hri).mpr
  intro _
  rw [abs_mul, abs_mul]
  calc
    |U r j| * |U i s| ≤ δ * δ := mul_le_mul (hr r hri) (hs s hsj) (abs_nonneg _) hδ
    _ ≤ κ * ε := by simpa [pow_two] using hgap
    _ ≤ |U i j| * |U r s| := mul_le_mul hp (hinside r s hri hsj) hε (abs_nonneg _)


variable [Fintype ι]

/-- Row orthogonality and unit row norms preserve every row sum. -/
theorem corrected_row_sum (U : Matrix ι ι ℝ) (i j r : ι)
    (hU : U * U.transpose = 1) :
    ∑ s, corrected U i j r s = 1 := by
  by_cases hri : r = i
  · subst r
    simp [corrected]
  have hnorm := congrArg (fun M : Matrix ι ι ℝ => M r r) hU
  have horth := congrArg (fun M : Matrix ι ι ℝ => M r i) hU
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply_eq] at hnorm
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply_ne hri] at horth
  simp only [corrected, if_neg hri]
  calc
    (∑ s, U r s * (U r s - U r j * U i s / U i j)) =
        ∑ s, (U r s * U r s - (U r j / U i j) * (U r s * U i s)) := by
      apply Finset.sum_congr rfl
      intro s _
      rw [mul_div_assoc, div_mul_eq_mul_div]
      ring
    _ = 1 := by rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hnorm, horth, mul_zero, sub_zero]

/-- Column orthogonality and unit column norms preserve every column sum. -/
theorem corrected_col_sum (U : Matrix ι ι ℝ) {i j : ι} (s : ι)
    (hp : U i j ≠ 0) (hU : U.transpose * U = 1) :
    ∑ r, corrected U i j r s = 1 := by
  have ha : corrected U i j i s =
      (if s = j then 1 else 0) +
        (U i s * U i s - (U i s / U i j) * (U i s * U i j)) := by
    simp only [corrected, if_pos rfl]
    field_simp
    ring
  calc
    (∑ r, corrected U i j r s) =
        ∑ r, ((if r = i then (if s = j then 1 else 0) else 0) +
          (U r s * U r s - (U i s / U i j) * (U r s * U r j))) := by
      apply Finset.sum_congr rfl
      intro r _
      by_cases h : r = i
      · subst r
        simpa using ha
      · simp only [corrected, if_neg h, zero_add]
        rw [mul_div_assoc, div_mul_eq_mul_div]
        ring
    _ = 1 := by
      have hnorm := congrArg (fun M : Matrix ι ι ℝ => M s s) hU
      have horth := congrArg (fun M : Matrix ι ι ℝ => M s j) hU
      simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] at hnorm horth
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
      simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
      simp only [if_true] at hnorm
      rw [hnorm, horth]
      split_ifs with h
      · subst s
        rw [div_self hp]
        ring
      · ring

theorem corrected_mem_doublyStochastic (U : Matrix ι ι ℝ) {i j : ι}
    (hp : U i j ≠ 0) (hU : U * U.transpose = 1) (hUt : U.transpose * U = 1)
    (hn : ∀ r s, 0 ≤ corrected U i j r s) :
    corrected U i j ∈ doublyStochastic ℝ ι := by
  rw [mem_doublyStochastic_iff_sum]
  exact ⟨hn, fun r => corrected_row_sum U i j r hU, fun s => corrected_col_sum U s hp hUt⟩


/-- Birkhoff realizes the stationary singleton correction on the pivot face.
The orientation here is row-to-column, so the surviving permutations fix
the assignment `σ i = j`. -/
theorem exists_supported_law (U : Matrix ι ι ℝ) {i j : ι}
    (hp : U i j ≠ 0) (hU : U * U.transpose = 1) (hUt : U.transpose * U = 1)
    (hn : ∀ r s, 0 ≤ corrected U i j r s) :
    ∃ w : Equiv.Perm ι → ℝ, (∀ σ, 0 ≤ w σ) ∧ (∑ σ, w σ = 1) ∧
      (∀ σ, σ i ≠ j → w σ = 0) ∧
      ∀ r s, (∑ σ, if σ r = s then w σ else 0) = corrected U i j r s := by
  obtain ⟨w, hw, hsum, hm⟩ := exists_eq_sum_perm_of_mem_doublyStochastic
    (corrected_mem_doublyStochastic U hp hU hUt hn)
  have hentry (r s : ι) : (∑ σ, if σ r = s then w σ else 0) =
      corrected U i j r s := by
    have he := congrArg (fun M : Matrix ι ι ℝ => M r s) hm
    simpa [Matrix.sum_apply, Matrix.smul_apply, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply,
      mul_ite, eq_comm] using he
  refine ⟨w, hw, hsum, ?_, hentry⟩
  intro σ hσ
  have hzero := hentry i (σ i)
  simp only [corrected, if_true, if_neg hσ] at hzero
  have hle : (if σ i = σ i then w σ else 0) ≤
      ∑ τ : Equiv.Perm ι, if τ i = σ i then w τ else 0 :=
    Finset.single_le_sum (f := fun τ : Equiv.Perm ι => if τ i = σ i then w τ else 0)
      (fun τ _ => by dsimp; split_ifs <;> simp [hw]) (Finset.mem_univ σ)
  rw [hzero, if_pos rfl] at hle
  exact le_antisymm hle (hw σ)


omit [Fintype ι] in
/-- The affine corrected square of the anchored oriented two-minor.
Here the tangent changes the anchor row toward the unit pivot and changes
the other row by a multiple of the anchor. The contribution from the
other row cancels in the determinant by alternation. -/
theorem anchored_pair_affine_correction (U : Matrix ι ι ℝ) {i j r s t : ι}
    (hp : U i j ≠ 0) (hr : r ≠ i) (hst : s ≠ t) :
    let D := U i s * U r t - U i t * U r s
    let toward := fun k => (if k = j then 1 / U i j else 0) - U i k
    let Ddot := toward s / 2 * U r t - toward t / 2 * U r s +
      U i s * (-(U r j / (2 * U i j)) * U i t) -
      U i t * (-(U r j / (2 * U i j)) * U i s)
    D ^ 2 + 2 * D * Ddot =
      if s = j then corrected U i j r t
      else if t = j then corrected U i j r s else 0 := by
  dsimp
  by_cases hs : s = j
  · subst s
    have ht : t ≠ j := Ne.symm hst
    simp only [if_true, if_neg ht, corrected, if_neg hr]
    field_simp
    ring
  by_cases ht : t = j
  · subst t
    simp only [if_true, if_neg hs, corrected, if_neg hr]
    field_simp
    ring
  simp only [if_neg hs, if_neg ht]
  ring


/-- Transfer a stationary pivot score to a matching bound. The hypotheses
are the affine evaluation at the corrected pivot and its expression on
the pivot face. In order four the deleted three-row matching expansion
is of this form. The separate analytic stationarity bridge is not used
as an axiom here. -/
theorem score_le_of_pivot_affine (U : Matrix ι ι ℝ) {i j : ι}
    (hp : U i j ≠ 0) (hU : U * U.transpose = 1) (hUt : U.transpose * U = 1)
    (hn : ∀ r s, 0 ≤ corrected U i j r s)
    (score : Equiv.Perm ι → ℝ) (c v B : ℝ) (f : ι → ι → ℝ)
    (hv : v = c + ∑ r, ∑ s, corrected U i j r s * f r s)
    (hf : ∀ σ : Equiv.Perm ι, σ i = j → score σ = c + ∑ r, f r (σ r))
    (hB : ∀ σ : Equiv.Perm ι, σ i = j → score σ ≤ B) :
    v ≤ B := by
  obtain ⟨w, hw, hs, hsupport, hm⟩ := exists_supported_law U hp hU hUt hn
  have heval (r : ι) :
      (∑ s, corrected U i j r s * f r s) = ∑ σ, w σ * f r (σ r) := by
    simp_rw [← hm, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro σ _
    simp [ite_mul, eq_comm]
  have hv' : v = ∑ σ, w σ * score σ := by
    calc
      v = c + ∑ r, ∑ σ, w σ * f r (σ r) := by simp_rw [hv, heval]
      _ = ∑ σ, w σ * (c + ∑ r, f r (σ r)) := by
        simp_rw [mul_add, Finset.mul_sum, Finset.sum_add_distrib, ← Finset.sum_mul, hs, one_mul]
        rw [Finset.sum_comm]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro σ _
        by_cases h : σ i = j
        · rw [hf σ h]
        · simp [hsupport σ h]
  rw [hv', ← one_mul B, ← hs, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro σ _
  by_cases h : σ i = j
  · exact mul_le_mul_of_nonneg_left (hB σ h) (hw σ)
  · simp [hsupport σ h]

end MOC.StationaryFullSupport
