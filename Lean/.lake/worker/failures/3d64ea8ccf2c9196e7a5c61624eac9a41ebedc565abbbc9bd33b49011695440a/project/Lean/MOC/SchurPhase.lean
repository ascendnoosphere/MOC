import MOC.PhaseMove
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-! A phase at the first vector of a Schur basis. The first column of the
initial sum has zero entries below its pivot, but the first row can couple
to the remaining block. -/

open BigOperators Matrix

namespace MOC

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The scalar phase at the first vector in a one-dimensional block split. -/
def schurPivotPhase (z : ℂ) : Matrix (Unit ⊕ ι) (Unit ⊕ ι) ℂ :=
  diagonal (Sum.elim (fun _ : Unit => z) (fun _ : ι => 1))

private theorem mul_star_eq_one_of_normSq {z : ℂ} (hz : Complex.normSq z = 1) :
    z * star z = 1 := by
  rw [Complex.star_def, Complex.mul_conj, hz, Complex.ofReal_one]

theorem isUnitary_schurPivotPhase {z : ℂ} (hz : Complex.normSq z = 1) :
    IsUnitary (schurPivotPhase (ι := ι) z) := by
  let d := Sum.elim (fun _ : Unit => z) (fun _ : ι => (1 : ℂ))
  have h (i : Unit ⊕ ι) : d i * star (d i) = 1 := by
    cases i <;> simp [d, mul_star_eq_one_of_normSq hz]
  have h' (i : Unit ⊕ ι) : star (d i) * d i = 1 := (mul_comm _ _).trans (h i)
  change IsUnitary (diagonal d)
  constructor
  · rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    exact congrArg Matrix.diagonal (funext h)
  · rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    exact congrArg Matrix.diagonal (funext h')

/-- The explicitly phased sum, with the original upper right block `p`. -/
def schurPhaseSum (x : ℂ) (p v : Matrix Unit ι ℂ) (w : Matrix ι Unit ℂ)
    (T : Matrix ι ι ℂ) (z : ℂ) : Matrix (Unit ⊕ ι) (Unit ⊕ ι) ℂ :=
  fromBlocks (fun _ _ => x) (p + (z - 1) • v) ((star z - 1) • w) T

theorem schurPhaseSum_eq_unitary_orbit (x : ℂ) (p : Matrix Unit ι ℂ)
    (T : Matrix ι ι ℂ) (B : Matrix (Unit ⊕ ι) (Unit ⊕ ι) ℂ)
    {z : ℂ} (hz : Complex.normSq z = 1) :
    let C := fromBlocks (fun _ _ : Unit => x) p 0 T
    let R := schurPivotPhase (ι := ι) z
    C - B + R * B * Rᴴ = schurPhaseSum x p B.toBlocks₁₂ B.toBlocks₂₁ T z := by
  have hz' := mul_star_eq_one_of_normSq hz
  dsimp only [schurPhaseSum, schurPivotPhase]
  ext i j : 1
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.diagonal_conjTranspose,
    Matrix.mul_diagonal, Matrix.diagonal_mul, Pi.star_apply]
  rcases i with (⟨⟩ | i) <;> rcases j with (⟨⟩ | j)
  · simp only [Sum.elim_inl, Matrix.fromBlocks_apply₁₁]
    rw [mul_right_comm z, hz', one_mul, sub_add_cancel]
  · simp only [Sum.elim_inl, Sum.elim_inr, Matrix.fromBlocks_apply₁₂,
      Matrix.add_apply, Matrix.toBlocks₁₂, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul,
      star_one, mul_one]
    ring
  · simp only [Sum.elim_inl, Sum.elim_inr, Matrix.fromBlocks_apply₂₁,
      Matrix.zero_apply, Matrix.toBlocks₂₁, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul,
      one_mul]
    ring
  · simp only [Sum.elim_inr, Matrix.fromBlocks_apply₂₂, star_one, one_mul, mul_one,
      sub_add_cancel]

/-- In the Schur complement, the original row produces a term linear in the
conjugate phase, in addition to the quadratic term from the two moving blocks. -/
theorem det_schurPhaseSum (x : ℂ) (p v : Matrix Unit ι ℂ) (w : Matrix ι Unit ℂ)
    (T : Matrix ι ι ℂ) (hT : T.det ≠ 0) (z : ℂ) :
    (schurPhaseSum x p v w T z).det =
      T.det * (x + (1 - star z) * (p * T⁻¹ * w) () () -
        ((z - 1) * (star z - 1)) * (v * T⁻¹ * w) () ()) := by
  letI : Invertible T.det := invertibleOfNonzero hT
  letI : Invertible T := T.invertibleOfDetInvertible
  rw [schurPhaseSum, Matrix.det_fromBlocks₂₂, Matrix.invOf_eq_nonsing_inv, Matrix.det_unique]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  ring

/-- The exact real support along the unit circle. Both coefficients can be
computed from solves against the lower right block. -/
theorem support_schurPhaseSum (x : ℂ) (p v : Matrix Unit ι ℂ) (w : Matrix ι Unit ℂ)
    (T : Matrix ι ι ℂ) (hT : T.det ≠ 0) (η z : ℂ) (hz : Complex.normSq z = 1) :
    let P := η * T.det * (p * T⁻¹ * w) () ()
    let Q := η * T.det * (v * T⁻¹ * w) () ()
    (η * (schurPhaseSum x p v w T z).det).re =
      (η * (T.det * x)).re + (1 - z.re) * (P.re - 2 * Q.re) - z.im * P.im := by
  intro P Q
  have hzz := mul_star_eq_one_of_normSq hz
  have hp : (z - 1) * (star z - 1) = (2 : ℂ) * (1 - (z.re : ℂ)) := by
    calc
      _ = 2 - (z + star z) := by linear_combination hzz
      _ = _ := by rw [Complex.star_def, Complex.add_conj, Complex.ofReal_mul]; ring
  rw [det_schurPhaseSum x p v w T hT z, hp]
  have he : η * (T.det * (x + (1 - star z) * (p * T⁻¹ * w) () () -
      (2 * (1 - (z.re : ℂ))) * (v * T⁻¹ * w) () ())) =
      η * (T.det * x) + (1 - star z) * P - (2 * (1 - (z.re : ℂ))) * Q := by
    dsimp only [P, Q]
    ring
  rw [he]
  norm_num [Complex.add_re, Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
    Complex.star_def] <;> ring

private theorem phase_support_coefficients {a b : ℝ}
    (h : ∀ z : ℂ, Complex.normSq z = 1 → a * (1 - z.re) + b * z.im ≤ 0) :
    a ≤ 0 ∧ b = 0 := by
  have ha := h (-1) (by norm_num [Complex.normSq_neg, Complex.normSq_one])
  norm_num [Complex.neg_re, Complex.neg_im] at ha
  refine ⟨by linarith only [ha], ?_⟩
  by_contra hb
  let d := (1 - a)^2 + b^2
  have hd : 0 < d := add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_ne_zero hb)
  let z : ℂ := ⟨((1 - a)^2 - b^2) / d, (2 * (1 - a) * b) / d⟩
  have hz : Complex.normSq z = 1 := by
    simp only [z, Complex.normSq_mk]
    field_simp [hd.ne']
    dsimp only [d]
    ring
  have hv : a * (1 - z.re) + b * z.im = 2 * b^2 / d := by
    dsimp only [z]
    field_simp [hd.ne']
    dsimp only [d]
    ring
  have hpos : 0 < 2 * b^2 / d := div_pos (mul_pos (by norm_num) (sq_pos_of_ne_zero hb)) hd
  have hzmax := h z hz
  rw [hv] at hzmax
  exact (not_lt_of_ge hzmax) hpos

/-- A support maximum at phase one has zero sine coefficient and a
nonpositive coefficient of `1 - Re z`. -/
theorem schurPhase_support_coefficients (x : ℂ) (p v : Matrix Unit ι ℂ)
    (w : Matrix ι Unit ℂ) (T : Matrix ι ι ℂ) (hT : T.det ≠ 0) (η : ℂ)
    (hmax : ∀ z : ℂ, Complex.normSq z = 1 →
      (η * (schurPhaseSum x p v w T z).det).re ≤ (η * (schurPhaseSum x p v w T 1).det).re) :
    let P := η * T.det * (p * T⁻¹ * w) () ()
    let Q := η * T.det * (v * T⁻¹ * w) () ()
    P.re - 2 * Q.re ≤ 0 ∧ P.im = 0 := by
  intro P Q
  have hbase := support_schurPhaseSum x p v w T hT η 1 Complex.normSq_one
  norm_num at hbase
  have h (z : ℂ) (hz : Complex.normSq z = 1) :
      (P.re - 2 * Q.re) * (1 - z.re) + (-P.im) * z.im ≤ 0 := by
    have hle := hmax z hz
    have hform := support_schurPhaseSum x p v w T hT η z hz
    change (η * (schurPhaseSum x p v w T z).det).re =
      (η * (T.det * x)).re + (1 - z.re) * (P.re - 2 * Q.re) - z.im * P.im at hform
    rw [hform, hbase] at hle
    linarith only [hle]
  obtain ⟨ha, hb⟩ := phase_support_coefficients h
  exact ⟨ha, neg_eq_zero.mp hb⟩

omit [DecidableEq ι] in
private theorem pivot_normSq_balance (M : Matrix (Unit ⊕ ι) (Unit ⊕ ι) ℂ)
    (hM : M * Mᴴ = Mᴴ * M) :
    (∑ j, Complex.normSq (M (Sum.inl ()) (Sum.inr j))) =
      ∑ i, Complex.normSq (M (Sum.inr i) (Sum.inl ())) := by
  have hleft (z : ℂ) : (z * star z).re = Complex.normSq z :=
    congrArg Complex.re (Complex.mul_conj z)
  have hright (z : ℂ) : (star z * z).re = Complex.normSq z := by rw [mul_comm, hleft]
  have h := congrArg (fun X : Matrix (Unit ⊕ ι) (Unit ⊕ ι) ℂ => (X (Sum.inl ()) (Sum.inl ())).re) hM
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.re_sum, hleft, hright,
    Fintype.sum_sum_type, Fintype.sum_unique] at h
  exact add_left_cancel h

omit [DecidableEq ι] in
private theorem sum_normSq_fromBlocks (x : ℂ) (p : Matrix Unit ι ℂ)
    (w : Matrix ι Unit ℂ) (T : Matrix ι ι ℂ) :
    (∑ i, ∑ j, Complex.normSq (fromBlocks (fun _ _ => x) p w T i j)) =
      Complex.normSq x + (∑ j, Complex.normSq (p () j)) +
      (∑ i, Complex.normSq (w i ())) + ∑ i, ∑ j, Complex.normSq (T i j) := by
  simp only [Fintype.sum_sum_type, Fintype.sum_unique, Matrix.fromBlocks_apply₁₁,
    Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
    Finset.sum_add_distrib]
  ring

omit [DecidableEq ι] in
/-- For normal summands, reflection at the pivot gains exactly twice the
squared norm of the new upper right block. No normality of the sum is used. -/
theorem schurPhase_reflection_frobenius (x : ℂ) (p : Matrix Unit ι ℂ)
    (T : Matrix ι ι ℂ) (B : Matrix (Unit ⊕ ι) (Unit ⊕ ι) ℂ)
    (hB : B * Bᴴ = Bᴴ * B)
    (hA : let A := fromBlocks (fun _ _ : Unit => x) p 0 T - B
      A * Aᴴ = Aᴴ * A) :
    let v := B.toBlocks₁₂
    let w := B.toBlocks₂₁
    let S := schurPhaseSum x p v w T
    (∑ i, ∑ j, Complex.normSq (S (-1) i j)) =
      (∑ i, ∑ j, Complex.normSq (S 1 i j)) +
      2 * (∑ j, Complex.normSq ((p - (2 : ℂ) • v) () j)) := by
  intro v w S
  have hrow := pivot_normSq_balance B hB
  change (∑ j, Complex.normSq (v () j)) = ∑ i, Complex.normSq (w i ()) at hrow
  have hrow' := pivot_normSq_balance (fromBlocks (fun _ _ : Unit => x) p 0 T - B) hA
  change (∑ j, Complex.normSq (p () j - v () j)) =
    ∑ i, Complex.normSq (0 - w i ()) at hrow'
  simp only [zero_sub, Complex.normSq_neg] at hrow'
  have hpar :
      (∑ j, Complex.normSq ((p - (2 : ℂ) • v) () j)) +
        (∑ j, Complex.normSq (p () j)) =
      2 * (∑ j, Complex.normSq (p () j - v () j)) + 2 * (∑ j, Complex.normSq (v () j)) := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    norm_num [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Complex.normSq_apply,
      Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im] <;> ring
  have hone : S 1 = fromBlocks (fun _ _ : Unit => x) p 0 T := by
    simp [S, schurPhaseSum]
  have hm : (-1 : ℂ) - 1 = -2 := by norm_num
  have hminus : S (-1) = fromBlocks (fun _ _ : Unit => x) (p - (2 : ℂ) • v) ((-2 : ℂ) • w) T := by
    simp only [S, schurPhaseSum, star_neg, star_one, hm, neg_smul, sub_eq_add_neg]
  have hcol : (∑ i, Complex.normSq (((-2 : ℂ) • w) i ())) =
      4 * (∑ i, Complex.normSq (w i ())) := by
    simp only [Matrix.smul_apply, smul_eq_mul, Complex.normSq_mul, Complex.normSq_neg,
      Complex.normSq_ofNat, ← Finset.mul_sum]
    norm_num
  rw [hminus, hone, sum_normSq_fromBlocks, sum_normSq_fromBlocks, hcol]
  simp only [Matrix.zero_apply, Complex.normSq_zero, Finset.sum_const_zero, add_zero]
  linarith only [hrow, hrow', hpar]

/-- At a phase support maximum with maximal squared Frobenius norm on ties,
either the support forbids the reflection or its new upper right block is zero. -/
theorem schurPhase_support_frobenius_condition (x : ℂ) (p : Matrix Unit ι ℂ)
    (T : Matrix ι ι ℂ) (hT : T.det ≠ 0) (B : Matrix (Unit ⊕ ι) (Unit ⊕ ι) ℂ) (η : ℂ)
    (hB : B * Bᴴ = Bᴴ * B)
    (hA : let A := fromBlocks (fun _ _ : Unit => x) p 0 T - B
      A * Aᴴ = Aᴴ * A) :
    let v := B.toBlocks₁₂
    let w := B.toBlocks₂₁
    let S := schurPhaseSum x p v w T
    (∀ z : ℂ, Complex.normSq z = 1 → (η * (S z).det).re ≤ (η * (S 1).det).re) →
    ((η * (S (-1)).det).re = (η * (S 1).det).re →
      (∑ i, ∑ j, Complex.normSq (S (-1) i j)) ≤ ∑ i, ∑ j, Complex.normSq (S 1 i j)) →
    (η * T.det * (p * T⁻¹ * w) () ()).re -
      2 * (η * T.det * (v * T⁻¹ * w) () ()).re < 0 ∨ p = (2 : ℂ) • v := by
  intro v w S hmax htie
  obtain ⟨ha, _⟩ := schurPhase_support_coefficients x p v w T hT η hmax
  rcases lt_or_eq_of_le ha with hlt | he
  · exact Or.inl hlt
  · right
    have hplus := support_schurPhaseSum x p v w T hT η 1 Complex.normSq_one
    have hminus := support_schurPhaseSum x p v w T hT η (-1) (by norm_num [Complex.normSq_one])
    dsimp only at hplus hminus
    rw [he] at hminus
    norm_num [Complex.neg_re, Complex.neg_im] at hplus hminus
    have hnorm := htie (hminus.trans hplus.symm)
    have hgain := schurPhase_reflection_frobenius x p T B hB hA
    change (∑ i, ∑ j, Complex.normSq (S (-1) i j)) =
      (∑ i, ∑ j, Complex.normSq (S 1 i j)) +
      2 * (∑ j, Complex.normSq ((p - (2 : ℂ) • v) () j)) at hgain
    rw [hgain] at hnorm
    have hz : (∑ j, Complex.normSq ((p - (2 : ℂ) • v) () j)) = 0 :=
      le_antisymm (by linarith only [hnorm]) (Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _)
    ext i j : 1
    cases i
    have hj := (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => Complex.normSq_nonneg _)).mp
      hz j (Finset.mem_univ j)
    exact sub_eq_zero.mp (Complex.normSq_eq_zero.mp hj)

end

end MOC
