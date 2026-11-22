import MOC.Variational
import Mathlib.Tactic.LinearCombination

/-! The relative unitary at an irreducible concentric-circle extremum has
at most two distinct eigenvalues. -/

open BigOperators Matrix

namespace MOC

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The ratio of two distinct positive radii gives a nonsingular relative sum. -/
theorem normSq_phase_denominator_ne_zero (t : ℝ) (ht : 0 < t) (hlt : t < 1)
    (z : ℂ) (hz : Complex.normSq z = 1) : 1 + (t : ℂ) * z ≠ 0 := by
  intro h
  have he : (t : ℂ) * z = -1 := by linear_combination h
  have hnorm := congrArg Complex.normSq he
  rw [Complex.normSq_mul, Complex.normSq_ofReal, hz, mul_one,
    Complex.normSq_neg, Complex.normSq_one] at hnorm
  nlinarith only [hnorm, mul_pos (sub_pos.mpr hlt) (show 0 < 1 + t by linarith)]

/-- The determinant derivative coefficients lie on the image circle. -/
theorem relative_phase_norm (t : ℝ) (z : ℂ) (hz : Complex.normSq z = 1)
    (hnz : 1 + (t : ℂ) * z ≠ 0) :
    let p := (t : ℂ) * z / (1 + (t : ℂ) * z)
    Complex.normSq p = t ^ 2 * Complex.normSq (1 - p) := by
  intro p
  have he : 1 - p = 1 / (1 + (t : ℂ) * z) := by
    dsimp only [p]
    field_simp [hnz] <;> ring
  rw [he]
  dsimp only [p]
  simp only [Complex.normSq_div, Complex.normSq_mul, Complex.normSq_ofReal, hz, mul_one,
    Complex.normSq_one, pow_two, div_eq_mul_inv, one_mul]

private theorem three_phase_points_not_distinct (t : ℝ) (ht : 0 < t) (hlt : t < 1)
    (p q r ω : ℂ) (hω : ω ≠ 0)
    (hp : Complex.normSq p = t ^ 2 * Complex.normSq (1 - p))
    (hq : Complex.normSq q = t ^ 2 * Complex.normSq (1 - q))
    (hr : Complex.normSq r = t ^ 2 * Complex.normSq (1 - r))
    (hpq : (ω * p).im = (ω * q).im) (hpr : (ω * p).im = (ω * r).im) :
    p = q ∨ p = r ∨ q = r := by
  have ht₂ : 1 - t ^ 2 ≠ 0 := by
    have h := mul_pos (sub_pos.mpr hlt) (show 0 < 1 + t by linarith)
    exact (show 0 < 1 - t ^ 2 by nlinarith only [h]).ne'
  have hfact (x : ℂ) (hx : Complex.normSq x = t ^ 2 * Complex.normSq (1 - x)) :
      Complex.normSq (ω * x) = t ^ 2 * Complex.normSq (ω - ω * x) := by
    rw [← mul_one_sub, Complex.normSq_mul, Complex.normSq_mul, hx]
    ring
  have hp' := hfact p hp
  have hpair (x : ℂ) (hx : Complex.normSq x = t ^ 2 * Complex.normSq (1 - x))
      (hi : (ω * p).im = (ω * x).im) (hn : p ≠ x) :
      (1 - t ^ 2) * ((ω * p).re + (ω * x).re) + 2 * t ^ 2 * ω.re = 0 := by
    have hx' := hfact x hx
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, ← hi] at hx' hp'
    have hz : ((ω * p).re - (ω * x).re) *
        ((1 - t ^ 2) * ((ω * p).re + (ω * x).re) + 2 * t ^ 2 * ω.re) = 0 := by
      linear_combination hp' - hx'
    exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr fun he =>
      hn (mul_left_cancel₀ hω (Complex.ext he hi)))
  by_cases hpq' : p = q
  · exact Or.inl hpq'
  by_cases hpr' : p = r
  · exact Or.inr (Or.inl hpr')
  have hzero : (1 - t ^ 2) * ((ω * q).re - (ω * r).re) = 0 := by
    linear_combination (hpair q hq hpq hpq') - (hpair r hr hpr hpr')
  have he := sub_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_left ht₂)
  exact Or.inr (Or.inr (mul_left_cancel₀ hω (Complex.ext he (hpq.symm.trans hpr))))

/-- In a basis diagonalizing the product of the first unitary's adjoint and
the second unitary, stationarity makes all transformed eigenvalues have the
same imaginary projection, so the relative spectrum has at most two values. -/
theorem relative_phase_values_of_support_maximum (U : Matrix ι ι ℂ) (hU : IsUnitary U)
    (w : ι → ℂ) (hw : ∀ i, Complex.normSq (w i) = 1)
    (t : ℝ) (ht : 0 < t) (hlt : t < 1) (η : ℂ) (hη : η ≠ 0)
    (hcomm : ∀ Y : Matrix ι ι ℂ, Commute U Y → Commute (diagonal w) Y →
      ∃ c : ℂ, Y = c • (1 : Matrix ι ι ℂ))
    (hmax : ∀ V : Matrix ι ι ℂ, IsUnitary V →
      (η * (U + V * ((t : ℂ) • (U * diagonal w)) * Vᴴ).det).re ≤
        (η * (U + (t : ℂ) • (U * diagonal w)).det).re) :
    let p (i : ι) := (t : ℂ) * w i / (1 + (t : ℂ) * w i)
    let ω := η * (U + (t : ℂ) • (U * diagonal w)).det
    (∀ i j, (ω * p i).im = (ω * p j).im) ∧
      ∀ i j k, w i = w j ∨ w i = w k ∨ w j = w k := by
  intro p ω
  let B : Matrix ι ι ℂ := (t : ℂ) • (U * diagonal w)
  let d (i : ι) := 1 + (t : ℂ) * w i
  let e (i : ι) := (d i)⁻¹
  let P := diagonal p
  have hd (i : ι) : d i ≠ 0 := normSq_phase_denominator_ne_zero t ht hlt (w i) (hw i)
  have hC : U + B = U * diagonal d := by
    calc
      _ = U * (1 + (t : ℂ) • diagonal w) := by simp [B, Matrix.mul_add, Matrix.mul_smul]
      _ = _ := by
        rw [← Matrix.diagonal_one, ← Matrix.diagonal_smul, ← Matrix.diagonal_add]
        rfl
  have hInv : (U + B)⁻¹ = diagonal e * Uᴴ := by
    apply Matrix.inv_eq_left_inv
    rw [hC, Matrix.mul_assoc, ← Matrix.mul_assoc Uᴴ U, hU.2, Matrix.one_mul,
      Matrix.diagonal_mul_diagonal]
    simp [e, Pi.mul_apply, inv_mul_cancel₀, hd]
  have hdet : (U + B).det ≠ 0 := by
    rw [hC, Matrix.det_mul, Matrix.det_diagonal]
    exact mul_ne_zero (det_ne_zero_of_unitary hU) (Finset.prod_ne_zero_iff.mpr (fun i _ => hd i))
  have hpDiag : (t : ℂ) • (diagonal w * diagonal e) = P := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_smul]
    change diagonal ((t : ℂ) • (w * e)) = diagonal p
    apply congrArg diagonal
    funext i
    simp only [p, Pi.smul_apply, Pi.mul_apply, smul_eq_mul, div_eq_mul_inv, e, d, mul_assoc]
  have hpe : diagonal e * diagonal w = diagonal w * diagonal e := by
    rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    exact congrArg diagonal (funext fun i => mul_comm (e i) (w i))
  have hBP : B * (U + B)⁻¹ = U * P * Uᴴ := by
    calc
      _ = U * ((t : ℂ) • (diagonal w * diagonal e)) * Uᴴ := by
        simp only [B, hInv, Matrix.mul_assoc, Matrix.smul_mul, Matrix.mul_smul]
      _ = _ := by rw [hpDiag]
  have hPB : (U + B)⁻¹ * B = P := by
    simp only [B, hInv, Matrix.mul_assoc, Matrix.mul_smul]
    rw [← Matrix.mul_assoc Uᴴ U, hU.2, Matrix.one_mul, hpe, hpDiag]
  let S := ω • P
  have hHerm : (U * S * Uᴴ - S)ᴴ = U * S * Uᴴ - S := by
    have h := support_maximum_inverse_commutator U B η hdet hmax
    change (ω • (B * (U + B)⁻¹ - (U + B)⁻¹ * B))ᴴ = _ at h
    simpa only [hBP, hPB, S, smul_sub, Matrix.mul_smul, Matrix.smul_mul] using h
  rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, ← Matrix.mul_assoc U Sᴴ Uᴴ] at hHerm
  let J := S - Sᴴ
  have hconj : U * J * Uᴴ - J = 0 := by
    calc
      _ = (U * S * Uᴴ - S) - (U * Sᴴ * Uᴴ - Sᴴ) := by
        simp only [J, Matrix.mul_sub, Matrix.sub_mul]
        abel
      _ = 0 := sub_eq_zero.mpr hHerm.symm
  have hUJ : Commute U J := by
    change U * J = J * U
    have h := congrArg (fun M : Matrix ι ι ℂ => M * U) (sub_eq_zero.mp hconj)
    simpa only [Matrix.mul_assoc, hU.2, Matrix.mul_one] using h
  have hJ : J = diagonal (fun i => ω * p i - star (ω * p i)) := by
    change ω • diagonal p - (ω • diagonal p)ᴴ = _
    rw [← Matrix.diagonal_smul, Matrix.diagonal_conjTranspose, ← Matrix.diagonal_sub] <;> rfl
  have hdiag : Commute (diagonal w) J := by
    change diagonal w * J = J * diagonal w
    rw [hJ, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    exact congrArg diagonal (funext fun i => mul_comm _ _)
  obtain ⟨c, hc⟩ := hcomm J hUJ hdiag
  have him (i : ι) : 2 * (ω * p i).im = c.im := by
    have h := congrArg (fun M : Matrix ι ι ℂ => (M i i).im) hc
    simp only [hJ, Matrix.diagonal_apply_eq, Matrix.smul_apply, smul_eq_mul,
      Matrix.one_apply_eq, mul_one, Complex.sub_im, Complex.star_def, Complex.conj_im] at h
    linarith only [h]
  have hsame (i j : ι) : (ω * p i).im = (ω * p j).im := by linarith only [him i, him j]
  refine ⟨hsame, fun i j k => ?_⟩
  have hω : ω ≠ 0 := mul_ne_zero hη hdet
  have hp (i : ι) : Complex.normSq (p i) = t ^ 2 * Complex.normSq (1 - p i) :=
    relative_phase_norm t (w i) (hw i) (hd i)
  have hinj (i j : ι) (h : p i = p j) : w i = w j := by
    have h' := (div_eq_div_iff (hd i) (hd j)).mp h
    have hcancel : (t : ℂ) * w i = (t : ℂ) * w j := by
      dsimp only [d] at h'
      linear_combination h'
    exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr ht.ne') hcancel
  rcases three_phase_points_not_distinct t ht hlt (p i) (p j) (p k) ω hω
    (hp i) (hp j) (hp k) (hsame i j) (hsame i k) with h | h | h
  · exact Or.inl (hinj i j h)
  · exact Or.inr (Or.inl (hinj i k h))
  · exact Or.inr (Or.inr (hinj j k h))

end MOC
