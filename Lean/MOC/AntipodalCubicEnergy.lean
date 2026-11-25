import MOC.AntipodalDeterminantJet
import Mathlib.Tactic.LinearCombination

/-! At an invertible residual involution center, the cubic Schur
self-energy on a crossed kernel line depends only on the signed
variances within the two spectral lists. Mixed terms vanish exactly.
For block elimination by the Schur complement, see Cottle, DOI:
10.1016/0024-3795(74)90066-4. -/

open BigOperators Matrix

namespace MOC

noncomputable section

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι]

private theorem residual_intertwine_right (J K : Matrix ι ι ℂ)
    (hJ : J * J = 1) (hK : K * K = 1) (hd : (J+K).det ≠ 0) :
    let R := (J+K)⁻¹
    R * K = J * R := by
  intro R
  let S := J+K
  have hunit : IsUnit S.det := isUnit_iff_ne_zero.mpr hd
  have hSR : S * R = 1 := S.mul_nonsing_inv hunit
  have hRS : R * S = 1 := S.nonsing_inv_mul hunit
  have h : K * S = S * J := by
    rw [show S = J+K from rfl, Matrix.mul_add, Matrix.add_mul, hJ, hK, add_comm]
  have he := congrArg (fun B : Matrix ι ι ℂ => R * B * R) h
  change R*(K*S)*R = R*(S*J)*R at he
  rwa [← Matrix.mul_assoc R K S, Matrix.mul_assoc (R*K) S R, hSR, Matrix.mul_one,
    ← Matrix.mul_assoc R S J, hRS, Matrix.one_mul] at he

/-- With opposite signs in the two summands, mixed Schur terms are
zero and the two pure terms carry opposite half-weights. The rows
and columns are not assumed to be conjugates; complex spectral
variations use algebraic squares rather than absolute squares. -/
theorem crossed_antipodal_residual_selfEnergy
    (J K : Matrix ι ι ℂ) (hJ : J*J=1) (hK : K*K=1) (hd : (J+K).det ≠ 0)
    (x y : Matrix κ ι ℂ) (z w : Matrix ι κ ℂ)
    (hx : x*J=x) (hz : J*z=z) (hy : y*K = -y) (hw : K*w = -w) :
    let R := (J+K)⁻¹
    (x+y)*R*(z+w) = (1/2 : ℂ) • (x*z-y*w) := by
  intro R
  have hj := inv_add_involutions_anticommutator J K hJ hK hd
  have hk := inv_add_involutions_anticommutator K J hK hJ (by rwa [add_comm K J])
  rw [add_comm K J] at hk
  have he : R*K=J*R := residual_intertwine_right J K hJ hK hd
  have he' : R*J=K*R := by
    have h := residual_intertwine_right K J hK hJ (by rwa [add_comm K J])
    simpa only [R, add_comm K J] using h
  have hj' : R*J+J*R=1 := hj
  have hk' : R*K+K*R=1 := hk
  have hxL : x*(R*J)*z = x*R*z := by
    rw [← Matrix.mul_assoc x R J, Matrix.mul_assoc (x*R) J z, hz]
  have hxR : x*(J*R)*z = x*R*z := by rw [← Matrix.mul_assoc x J R, hx]
  have hyL : y*(R*K)*w = -(y*R*w) := by
    rw [← Matrix.mul_assoc y R K, Matrix.mul_assoc (y*R) K w, hw, Matrix.mul_neg]
  have hyR : y*(K*R)*w = -(y*R*w) := by
    rw [← Matrix.mul_assoc y K R, hy, Matrix.neg_mul, Matrix.neg_mul]
  have hup : x*R*z+x*R*z = x*z := by
    have h := congrArg (fun B : Matrix ι ι ℂ => x*B*z) hj'
    change x*(R*J+J*R)*z = x*1*z at h
    rwa [Matrix.mul_add, Matrix.add_mul, hxL, hxR, Matrix.mul_one] at h
  have hdown : -(y*R*w) + -(y*R*w) = y*w := by
    have h := congrArg (fun B : Matrix ι ι ℂ => y*B*w) hk'
    change y*(R*K+K*R)*w = y*1*w at h
    rwa [Matrix.mul_add, Matrix.add_mul, hyL, hyR, Matrix.mul_one] at h
  have hcross₁ : x*R*w = 0 := by
    have h := congrArg (fun B : Matrix ι ι ℂ => x*B*w) he
    change x*(R*K)*w = x*(J*R)*w at h
    rw [← Matrix.mul_assoc x R K, Matrix.mul_assoc (x*R) K w, hw, Matrix.mul_neg,
      ← Matrix.mul_assoc x J R, hx] at h
    ext i j
    have h' := congrFun (congrFun h i) j
    simp only [Matrix.neg_apply] at h'
    change (x*R*w) i j = 0
    linear_combination -(1/2 : ℂ) * h'
  have hcross₂ : y*R*z = 0 := by
    have h := congrArg (fun B : Matrix ι ι ℂ => y*B*z) he'
    change y*(R*J)*z = y*(K*R)*z at h
    rw [← Matrix.mul_assoc y R J, Matrix.mul_assoc (y*R) J z, hz,
      ← Matrix.mul_assoc y K R, hy, Matrix.neg_mul, Matrix.neg_mul] at h
    ext i j
    have h' := congrFun (congrFun h i) j
    simp only [Matrix.neg_apply] at h'
    change (y*R*z) i j = 0
    linear_combination (1/2 : ℂ) * h'
  rw [Matrix.add_mul, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add,
    hcross₁, hcross₂, add_zero, zero_add]
  ext i j
  have hu := congrFun (congrFun hup i) j
  have hd := congrFun (congrFun hdown i) j
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, Matrix.neg_apply,
    smul_eq_mul] at hu hd ⊢
  linear_combination (1/2 : ℂ) * hu - (1/2 : ℂ) * hd


end

end MOC
