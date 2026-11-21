import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Data.Complex.BigOperators
import Mathlib.Tactic.Linarith

/-! A rectangular Gram matrix dominated by a scalar identity plus one
rank-one term has a Frobenius bound depending on its number of rows. -/

open BigOperators Matrix
open scoped ComplexOrder

namespace MOC

noncomputable section

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]

private theorem dot_self_eq_normSq_sum {α : Type*} [Fintype α] (v : α → ℂ) :
    star v ⬝ᵥ v = ((∑ i, Complex.normSq (v i)) : ℝ) := by
  simp only [dotProduct, Pi.star_apply, Complex.ofReal_sum, Complex.normSq_eq_conj_mul_self,
    starRingEnd_apply]

private theorem normSq_mulVec_le_of_contraction (W : Matrix ι κ ℂ)
    (hW : ((1 : Matrix κ κ ℂ) - Wᴴ * W).PosSemidef) (v : κ → ℂ) :
    (∑ i, Complex.normSq ((W *ᵥ v) i)) ≤ ∑ j, Complex.normSq (v j) := by
  have hgram : star v ⬝ᵥ (Wᴴ * W) *ᵥ v = star (W *ᵥ v) ⬝ᵥ (W *ᵥ v) := by
    rw [← Matrix.mulVec_mulVec, Matrix.star_mulVec, Matrix.dotProduct_mulVec]
  have h := hW.re_dotProduct_nonneg v
  change 0 ≤ (star v ⬝ᵥ ((1 : Matrix κ κ ℂ) - Wᴴ * W) *ᵥ v).re at h
  rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.one_mulVec, hgram, dot_self_eq_normSq_sum,
     dot_self_eq_normSq_sum, Complex.sub_re, Complex.ofReal_re, Complex.ofReal_re] at h
  exact sub_nonneg.mp h

theorem gram_diagonal_re (W : Matrix ι κ ℂ) (i : ι) :
    ((W * Wᴴ) i i).re = ∑ j, Complex.normSq (W i j) := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [mul_comm, ← starRingEnd_apply, ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re]

/-- The trace of a rectangular Gram matrix below `pI + vᴴv`
is at most `p` times the row count plus the squared norm of `v`. -/
theorem normSq_sum_le_of_rankOne_gram_bound (X : Matrix ι κ ℂ) (v : Matrix Unit κ ℂ)
    (p : ℝ) (hp : 0 < p) (hX : ((p : ℂ) • (1 : Matrix κ κ ℂ) + vᴴ * v - Xᴴ * X).PosSemidef) :
    (∑ i, ∑ j, Complex.normSq (X i j)) ≤
      p * (Fintype.card ι : ℝ) + ∑ j, Complex.normSq (v () j) := by
  classical
  let A : Matrix κ κ ℂ := (p : ℂ) • 1 + vᴴ * v
  have hpI : ((p : ℂ) • (1 : Matrix κ κ ℂ)).PosDef := by
    rw [← Matrix.diagonal_one, ← Matrix.diagonal_smul, Matrix.posDef_diagonal_iff]
    intro j
    simpa only [Pi.smul_apply, smul_eq_mul, mul_one] using Complex.zero_lt_real.mpr hp
  have hA : A.PosDef := hpI.add_posSemidef (Matrix.posSemidef_conjTranspose_mul_self v)
  let S := hA.posSemidef.sqrt
  let W := X * S⁻¹
  have hSS : S * S = A := hA.posSemidef.sqrt_mul_self
  have hSH : Sᴴ = S := hA.posSemidef.posSemidef_sqrt.isHermitian.eq
  have hSdet : IsUnit S.det := isUnit_iff_ne_zero.mpr (fun hz => by
    have hd := congrArg Matrix.det hSS
    rw [Matrix.det_mul, hz, zero_mul] at hd
    exact hA.det_pos.ne' hd.symm)
  have hSIH : (S⁻¹)ᴴ = S⁻¹ := by rw [Matrix.conjTranspose_nonsing_inv, hSH]
  have hW : W * S = X := by
    simp only [W, Matrix.mul_assoc, S.nonsing_inv_mul hSdet, Matrix.mul_one]
  have hAW : S⁻¹ * A * S⁻¹ = 1 := by
    rw [← hSS, ← Matrix.mul_assoc S⁻¹ S S, S.nonsing_inv_mul hSdet,
      Matrix.one_mul, S.mul_nonsing_inv hSdet]
  have hcontract : ((1 : Matrix κ κ ℂ) - Wᴴ * W).PosSemidef := by
    have h := hX.conjTranspose_mul_mul_same (S⁻¹)
    change ((S⁻¹)ᴴ * (A - Xᴴ * X) * S⁻¹).PosSemidef at h
    rw [Matrix.mul_sub, Matrix.sub_mul, hSIH, hAW] at h
    simpa only [W, Matrix.conjTranspose_mul, hSIH, Matrix.mul_assoc] using h
  have hrow (i : ι) : (∑ j, Complex.normSq (W i j)) ≤ 1 := by
    let x (j : κ) := star (W i j)
    let r : ℝ := ∑ j, Complex.normSq (W i j)
    have he : (W *ᵥ x) i = (r : ℂ) := by
      simp only [Matrix.mulVec, dotProduct, x, r, Complex.ofReal_sum,
        Complex.normSq_eq_conj_mul_self, starRingEnd_apply, mul_comm]
    have hr : r * r ≤ r := by
      have h := Finset.single_le_sum (f := fun k => Complex.normSq ((W *ᵥ x) k))
        (fun k _ => Complex.normSq_nonneg _) (Finset.mem_univ i)
      have hh := h.trans (normSq_mulVec_le_of_contraction W hcontract x)
      change Complex.normSq ((W *ᵥ x) i) ≤ ∑ j, Complex.normSq (x j) at hh
      rw [he] at hh
      simpa only [Complex.normSq_ofReal, pow_two, x, Complex.normSq_conj,
        Complex.star_def, r] using hh
    change r ≤ 1
    by_cases hr0 : r = 0
    · simp [hr0]
    · have hrp : 0 < r := lt_of_le_of_ne (Finset.sum_nonneg (fun j _ => Complex.normSq_nonneg _))
        (Ne.symm hr0)
      rw [← mul_le_mul_right hrp, one_mul]
      exact hr
  have hXX : X * Xᴴ = (p : ℂ) • (W * Wᴴ) + (W * vᴴ) * (W * vᴴ)ᴴ := calc
    _ = W * A * Wᴴ := by
      rw [← hSS, ← hW]
      simp only [Matrix.conjTranspose_mul, hSH, Matrix.mul_assoc]
    _ = _ := by
      simp only [A, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
        Matrix.mul_one, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  have hdiag (i : ι) : (∑ j, Complex.normSq (X i j)) =
      p * (∑ j, Complex.normSq (W i j)) + Complex.normSq ((W * vᴴ) i ()) := by
    have hi := congrArg (fun M : Matrix ι ι ℂ => (M i i).re) hXX
    simpa only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Complex.add_re,
      Complex.re_ofReal_mul, gram_diagonal_re, Fintype.sum_unique] using hi
  have hv : (∑ i, Complex.normSq ((W * vᴴ) i ())) ≤ ∑ j, Complex.normSq (v () j) := by
    simpa only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.mulVec, dotProduct,
      Complex.star_def, Complex.normSq_conj] using
      normSq_mulVec_le_of_contraction W hcontract (fun j => star (v () j))
  simp_rw [hdiag, Finset.sum_add_distrib, ← Finset.mul_sum]
  refine add_le_add (mul_le_mul_of_nonneg_left ?_ hp.le) hv
  simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] using
    Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hrow i)

/-- Every rectangle satisfies the Frobenius cut inequality when the column
Gram is a scalar identity plus a rank-one matrix. -/
theorem rectangle_normSq_le_of_rankOne_gram [DecidableEq ι]
    (T : Matrix ι κ ℂ) (v : Matrix Unit κ ℂ) (p : ℝ) (hp : 0 < p)
    (hT : Tᴴ * T = (p : ℂ) • (1 : Matrix κ κ ℂ) + vᴴ * v)
    (I : Finset ι) (J : Finset κ) :
    (∑ i ∈ I, ∑ j ∈ J, Complex.normSq (T i j)) ≤
      p * (I.card : ℝ) + ∑ j ∈ J, Complex.normSq (v () j) := by
  let X : Matrix I J ℂ := fun i j => T i j
  let Y : Matrix (↥(Iᶜ)) J ℂ := fun i j => T i j
  let vJ : Matrix Unit J ℂ := fun i j => v i j
  have hsplit : (p : ℂ) • (1 : Matrix J J ℂ) + vJᴴ * vJ = Xᴴ * X + Yᴴ * Y := by
    ext j k : 1
    calc
      _ = (Tᴴ * T) (j : κ) (k : κ) := by
        rw [hT]
        simp [vJ, Matrix.add_apply, Matrix.smul_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
          Matrix.one_apply, Subtype.coe_inj]
      _ = _ := by
        simp only [X, Y, Matrix.add_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
        let f (i : ι) := star (T i j) * T i k
        change (∑ i, f i) = (∑ i : I, f i) + ∑ i : ↥(Iᶜ), f i
        rw [Finset.sum_coe_sort I f, Finset.sum_coe_sort (Iᶜ) f, Finset.sum_add_sum_compl]
  have hX : ((p : ℂ) • (1 : Matrix J J ℂ) + vJᴴ * vJ - Xᴴ * X).PosSemidef := by
    rw [hsplit, add_sub_cancel_left]
    exact Matrix.posSemidef_conjTranspose_mul_self Y
  have h := normSq_sum_le_of_rankOne_gram_bound X vJ p hp hX
  change (∑ i : I, ∑ j : J, Complex.normSq (T i j)) ≤
    p * (Fintype.card I : ℝ) + ∑ j : J, Complex.normSq (v () j) at h
  have hj (i : ι) : (∑ j : J, Complex.normSq (T i j)) = ∑ j ∈ J, Complex.normSq (T i j) :=
    Finset.sum_coe_sort J (fun j => Complex.normSq (T i j))
  simp_rw [hj] at h
  have hi := Finset.sum_coe_sort I (fun i => ∑ j ∈ J, Complex.normSq (T i j))
  have hv := Finset.sum_coe_sort J (fun j => Complex.normSq (v () j))
  rw [hi, hv, Fintype.card_coe] at h
  exact h

end

end MOC
