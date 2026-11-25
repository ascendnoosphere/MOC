import MOC.Jacobi
import Mathlib.Analysis.Calculus.Deriv.Mul

/-! At an invertible antipodal center, a change commuting with either
signed spectrum has a determinant derivative independent of the relative
eigenbasis except for the existing determinant factor. -/

open BigOperators Matrix

namespace MOC

noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The inverse of the sum of two involutions has a fixed anticommutator
with either summand. This is an algebraic identity, not a positivity assertion. -/
theorem inv_add_involutions_anticommutator (J K : Matrix ι ι ℂ)
    (hJ : J * J = 1) (hK : K * K = 1) (hdet : (J + K).det ≠ 0) :
    let S := J + K
    S⁻¹ * J + J * S⁻¹ = 1 := by
  intro S
  have hu : IsUnit S.det := isUnit_iff_ne_zero.mpr hdet
  have hL := S.nonsing_inv_mul hu
  have hR := S.mul_nonsing_inv hu
  have hsum : J * S + S * J = S * S := by
    simp only [S, Matrix.mul_add, Matrix.add_mul, hJ, hK]
    abel
  have he := congrArg (fun T : Matrix ι ι ℂ => S⁻¹ * T * S⁻¹) hsum
  change S⁻¹ * (J * S + S * J) * S⁻¹ = S⁻¹ * (S * S) * S⁻¹ at he
  rw [Matrix.mul_add, Matrix.add_mul, ← Matrix.mul_assoc S⁻¹ J S,
    Matrix.mul_assoc (S⁻¹ * J) S S⁻¹, hR, Matrix.mul_one,
    ← Matrix.mul_assoc S⁻¹ S J, hL, Matrix.one_mul,
    ← Matrix.mul_assoc S⁻¹ S S, hL, Matrix.one_mul, hR] at he
  exact he

/-- A variation commuting with the first involution contributes half its
signed trace to Jacobi's logarithmic determinant derivative. -/
theorem trace_inv_add_involutions_mul_of_commute (J K V : Matrix ι ι ℂ)
    (hJ : J * J = 1) (hK : K * K = 1) (hdet : (J + K).det ≠ 0)
    (hV : Commute J V) :
    ((J + K)⁻¹ * V).trace = (J * V).trace / 2 := by
  let S := J + K
  have hanti : S⁻¹ * J + J * S⁻¹ = 1 :=
    inv_add_involutions_anticommutator J K hJ hK hdet
  have he := congrArg (fun T : Matrix ι ι ℂ => (T * (J * V)).trace) hanti
  change ((S⁻¹ * J + J * S⁻¹) * (J * V)).trace = ((1 : Matrix ι ι ℂ) * (J * V)).trace at he
  have hleft : S⁻¹ * J * (J * V) = S⁻¹ * V := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc J J V, hJ, Matrix.one_mul]
  have hright : (J * S⁻¹ * (J * V)).trace = (S⁻¹ * V).trace := by
    rw [Matrix.mul_assoc, Matrix.trace_mul_comm J (S⁻¹ * (J * V)),
      Matrix.mul_assoc, Matrix.mul_assoc J V J, ← hV.eq,
      ← Matrix.mul_assoc J J V, hJ, Matrix.one_mul]
  rw [Matrix.add_mul, Matrix.trace_add, hleft, hright, Matrix.one_mul] at he
  change (S⁻¹ * V).trace = _
  apply (eq_div_iff (two_ne_zero : (2 : ℂ) ≠ 0)).mpr
  linear_combination he

/-- The exact first variation for two independent spectral changes at an
invertible involution center. Each change only needs to commute with its
own summand. -/
theorem trace_inv_add_involutions_mul_split (J K V W : Matrix ι ι ℂ)
    (hJ : J * J = 1) (hK : K * K = 1) (hdet : (J + K).det ≠ 0)
    (hV : Commute J V) (hW : Commute K W) :
    ((J + K)⁻¹ * (V + W)).trace = ((J * V).trace + (K * W).trace) / 2 := by
  have hv := trace_inv_add_involutions_mul_of_commute J K V hJ hK hdet hV
  have hw := trace_inv_add_involutions_mul_of_commute K J W hK hJ
    (by rwa [add_comm]) hW
  rw [add_comm K J] at hw
  rw [Matrix.mul_add, Matrix.trace_add, hv, hw]
  ring

end

end MOC
