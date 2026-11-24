import MOC.SparseRow
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Matrix BigOperators

namespace MOC

noncomputable section

private def pairRotation {ι : Type*} [DecidableEq ι] (x y : ι) (c s : ℂ) :
    Matrix ι ι ℂ := of fun i j =>
  if i = x then (if j = x then star c else if j = y then -s else 0)
  else if i = y then (if j = x then star s else if j = y then c else 0)
  else if i = j then 1 else 0

private theorem rotateSum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ι → ℂ) {x y : ι} (hxy : x ≠ y) (h : ∀ k, k ≠ x → k ≠ y → f k = 0) :
    ∑ i, f i = f x + f y := by
  have he : ∑ i ∈ ({x,y} : Finset ι), f i = ∑ i, f i := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro i _ hi
    have hk : i ≠ x ∧ i ≠ y := by simpa using hi
    exact h i hk.1 hk.2
  simpa [hxy] using he.symm

private theorem pairRotation_unitary {ι : Type*} [Fintype ι] [DecidableEq ι]
    {x y : ι} (hxy : x ≠ y) {c s : ℂ}
    (hn : (Complex.normSq c : ℂ) + (Complex.normSq s : ℂ) = 1) :
    IsUnitary (pairRotation x y c s) := by
  let R := pairRotation x y c s
  have hrow (i j : ι) (hi : i ≠ x) (hj : i ≠ y) :
      R i j = if i = j then 1 else 0 := by simp [R, pairRotation, hi, hj]
  have hx (j : ι) : R x j = if j = x then star c else if j = y then -s else 0 := by
    simp [R, pairRotation]
  have hy (j : ι) : R y j = if j = x then star s else if j = y then c else 0 := by
    simp [R, pairRotation, Ne.symm hxy]
  have hc : star c * c = (Complex.normSq c : ℂ) := Complex.normSq_eq_conj_mul_self.symm
  have hs : star s * s = (Complex.normSq s : ℂ) := Complex.normSq_eq_conj_mul_self.symm
  have hRR : R * Rᴴ = 1 := by
    ext i j
    rw [Matrix.mul_apply]
    simp only [Matrix.conjTranspose_apply]
    by_cases hi : i = x ∨ i = y
    · rw [rotateSum _ hxy (by
        intro k hkx hky
        rcases hi with rfl | rfl
        · simp [hx, hkx, hky]
        · simp [hy, hkx, hky])]
      rcases hi with hi | hi <;> subst i
      · by_cases hjx : j = x
        · subst j
          simpa [hx, hxy, Ne.symm hxy, ← hc, ← hs, mul_comm] using hn
        · by_cases hjy : j = y
          · subst j
            simp [hx, hy, hxy, Ne.symm hxy]
            ring
          · simp [hx, hrow j _ hjx hjy, hjx, hjy, Ne.symm hjx, Ne.symm hjy]
      · by_cases hjx : j = x
        · subst j
          simp [hx, hy, hxy, Ne.symm hxy]
          ring
        · by_cases hjy : j = y
          · subst j
            simpa [hy, Ne.symm hxy, ← hc, ← hs, mul_comm, add_comm] using hn
          · simp [hy, hrow j _ hjx hjy, hjx, hjy, Ne.symm hjx, Ne.symm hjy]
    · have hh : i ≠ x ∧ i ≠ y := not_or.mp hi
      simp_rw [hrow i _ hh.1 hh.2, Matrix.one_apply]
      rw [Finset.sum_eq_single i]
      · by_cases hj : i = j
        · subst j
          simp [hrow i i hh.1 hh.2]
        · by_cases hjx : j = x
          · subst j
            simp [hx, hh.1, hh.2]
          · by_cases hjy : j = y
            · subst j
              simp [hy, hh.1, hh.2]
            · simp [hrow j i hjx hjy, hj, Ne.symm hj]
      · intro k _ hk
        simp [Ne.symm hk]
      · simp
  exact ⟨hRR, mul_eq_one_comm.mp hRR⟩

/-- Spectral collisions are usable even if the original basis has a genuinely
three-supported row. Rotate only the two equal-label columns, merge their
entries in that row, then invoke the verified two-supported-row reduction. -/
theorem holds_of_three_supported_row_spectral_collision {n : ℕ}
    (hSmall : Conjecture (Fin n)) (a b : Fin (n+1) → ℂ)
    {U : Matrix (Fin (n+1)) (Fin (n+1)) ℂ} (hU : IsUnitary U)
    (i x y z : Fin (n+1)) (hxy : x ≠ y) (hby : b x = b y)
    (hzero : ∀ j, j ≠ x → j ≠ y → j ≠ z → U i j = 0) :
    Holds a b U := by
  classical
  by_cases hy : U i y = 0
  · apply holds_of_two_supported_row hSmall a b hU i x z
    intro j hjx hjz
    by_cases hjy : j = y
    · simpa [hjy] using hy
    · exact hzero j hjx hjy hjz
  let q : ℝ := Complex.normSq (U i x) + Complex.normSq (U i y)
  let r : ℝ := Real.sqrt q
  have hq : 0 < q := add_pos_of_nonneg_of_pos (Complex.normSq_nonneg _)
    (lt_of_le_of_ne (Complex.normSq_nonneg _) (Ne.symm (mt Complex.normSq_eq_zero.mp hy)))
  have hr : r ^ 2 = q := Real.sq_sqrt hq.le
  have hrnz : (r : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr hq).ne'
  let c := U i x / (r : ℂ)
  let s := U i y / (r : ℂ)
  have hnorm : (Complex.normSq c : ℂ) + (Complex.normSq s : ℂ) = 1 := by
    have hrn : Complex.normSq (r : ℂ) = q := by
      rw [Complex.normSq_ofReal, ← pow_two, hr]
    suffices Complex.normSq c + Complex.normSq s = 1 by exact_mod_cast this
    rw [show Complex.normSq c = Complex.normSq (U i x) / Complex.normSq (r : ℂ)
          from map_div₀ Complex.normSq _ _,
        show Complex.normSq s = Complex.normSq (U i y) / Complex.normSq (r : ℂ)
          from map_div₀ Complex.normSq _ _,
        ← add_div, hrn]
    exact div_self hq.ne'
  let R := pairRotation x y c s
  have hR : IsUnitary R := pairRotation_unitary hxy hnorm
  have hUR : IsUnitary (U * R) :=
    by simpa using relative_unitary (Uᴴ) R ⟨by simpa using hU.2, by simpa using hU.1⟩ hR
  have hcomm : R * diagonal b = diagonal b * R := by
    ext p q
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    by_cases hp : p = x
    · subst p
      by_cases hx : q = x
      · subst q
        ring
      · by_cases hb : q = y
        · subst q
          rw [hby]
          ring
        · simp [R, pairRotation, hx, hb]
    · by_cases hp' : p = y
      · subst p
        by_cases hx : q = x
        · subst q
          rw [hby]
          ring
        · by_cases hb : q = y
          · subst q
            ring
          · simp [R, pairRotation, hp, hx, hb]
      · by_cases he : p = q
        · subst q
          ring
        · simp [R, pairRotation, hp, hp', he]
  have hd : determinantValue a b (U * R) = determinantValue a b U := by
    unfold determinantValue
    rw [Matrix.conjTranspose_mul]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc R (diagonal b), hcomm, Matrix.mul_assoc, ← Matrix.mul_assoc R,
      hR.1, Matrix.one_mul]
  unfold Holds
  rw [← hd]
  apply holds_of_two_supported_row hSmall a b hUR i x z
  intro j hjx hjz
  rw [Matrix.mul_apply]
  by_cases hjy : j = y
  · subst j
    rw [rotateSum _ hxy (by intro k hkx hky; simp [R, pairRotation, hkx, hky])]
    simp [R, pairRotation, hxy, Ne.symm hxy, c, s]
    ring
  · have hentry (k : Fin (n+1)) : R k j = if k = j then 1 else 0 := by
      by_cases hkx : k = x
      · subst k
        simp [R, pairRotation, hjx, hjy, Ne.symm hjx]
      · by_cases hky : k = y
        · subst k
          simp [R, pairRotation, hkx, hjx, hjy, Ne.symm hjy]
        · simp [R, pairRotation, hkx, hky]
    simp_rw [hentry]
    rw [Finset.sum_eq_single j]
    · simp [hzero j hjx hjy hjz]
    · intro k _ hk
      simp [hk]
    · simp

/-- A genuine rotation between different spectral labels cannot keep the
second summand fixed. In particular a degree-reducing rotation alone is not
a reduction for an overlap of distinct labels. -/
theorem diagonal_conjugation_ne_of_nonzero_between_distinct_labels
    {ι : Type*} [Fintype ι] [DecidableEq ι] {R : Matrix ι ι ℂ}
    (hR : IsUnitary R) (b : ι → ℂ) {x y : ι}
    (hb : b x ≠ b y) (hxy : R x y ≠ 0) :
    R * diagonal b * Rᴴ ≠ diagonal b := by
  intro h
  have he := congrArg (fun D : Matrix ι ι ℂ => D * R) h
  have hc : R * diagonal b = diagonal b * R := by
    simpa only [Matrix.mul_assoc, hR.2, Matrix.mul_one] using he
  have hx := congrArg (fun D : Matrix ι ι ℂ => D x y) hc
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul] at hx
  apply hb
  rw [mul_comm (R x y) (b y)] at hx
  exact (mul_right_cancel₀ hxy hx).symm

end

end MOC
