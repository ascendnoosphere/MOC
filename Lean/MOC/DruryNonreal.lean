import MOC.Householder
import Mathlib.Data.Complex.BigOperators
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Tactic.Linarith

/-! A nonreal generalized eigenvalue of a Hermitian pencil gives an exact
rank-one phase deformation through a nontrivial determinant segment. -/

open BigOperators Matrix

namespace MOC

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem det_two_updates_of_triangular_compression (T : Matrix ι ι ℂ)
    (hT : IsUnit T.det) (L₀ L₁ : Matrix ι Unit ℂ) (R₀ R₁ : Matrix Unit ι ℂ)
    (w : ℂ) (htri : R₁ * T⁻¹ * L₀ = 0) :
    (T + w • (L₀ * R₀ + L₁ * R₁)).det = T.det *
      ((1 + w * (R₀ * T⁻¹ * L₀) () ()) * (1 + w * (R₁ * T⁻¹ * L₁) () ())) := by
  let L : Matrix ι (Fin 2) ℂ := fun i j => if j = 0 then L₀ i () else L₁ i ()
  let R : Matrix (Fin 2) ι ℂ := fun i j => if i = 0 then R₀ () j else R₁ () j
  have hLR : L * R = L₀ * R₀ + L₁ * R₁ := by
    ext i j : 1
    simp [L, R, Matrix.mul_apply, Fin.sum_univ_two]
  have hRL₀₀ : (R * T⁻¹ * L) 0 0 = (R₀ * T⁻¹ * L₀) () () := by
    simp only [Matrix.mul_apply, L, R, if_true]
  have hRL₁₀ : (R * T⁻¹ * L) 1 0 = (R₁ * T⁻¹ * L₀) () () := by
    simp only [Matrix.mul_apply, L, R, if_true, if_neg (by decide : (1 : Fin 2) ≠ 0)]
  have hRL₁₁ : (R * T⁻¹ * L) 1 1 = (R₁ * T⁻¹ * L₁) () () := by
    simp only [Matrix.mul_apply, L, R, if_neg (by decide : (1 : Fin 2) ≠ 0)]
  rw [← hLR, ← Matrix.smul_mul, Matrix.det_add_mul (w • L) R hT, Matrix.mul_smul]
  simp only [Matrix.det_fin_two, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.one_apply_eq, Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1),
    Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0), hRL₀₀, hRL₁₀, hRL₁₁,
    htri, Matrix.zero_apply, mul_zero, add_zero, sub_zero]

/-- Rotating the second Hermitian summand at a unit generalized eigenvector
for a nonreal eigenvalue gives an exact determinant line. -/
theorem determinant_rankOnePhase_of_nonreal_pencil_vector (A C : Matrix ι ι ℂ)
    (hA : A.IsHermitian) (hC : C.IsHermitian) (κ ρ : ℂ) (hρ : ρ ≠ star ρ)
    (u : ι → ℂ) (hu : ∑ i, star (u i) * u i = 1)
    (heig : C *ᵥ u = ρ • (A *ᵥ u)) (z : ℂ) (hz : z * star z = 1) :
    let T := A - κ • C
    let V := rankOnePhase u z
    IsUnit T.det →
    1 - κ * ρ ≠ 0 ∧ 1 - κ * star ρ ≠ 0 ∧
    (A - κ • (V * C * Vᴴ)).det = T.det *
      (1 - κ * (1 - κ * ρ)⁻¹ * (1 - κ * star ρ)⁻¹ *
        ((z - 1) * star ρ + (star z - 1) * ρ)) := by
  dsimp only
  let T := A - κ • C
  let V := rankOnePhase u z
  let L : Matrix ι Unit ℂ := fun i _ => u i
  let r := (1 - κ * ρ)⁻¹
  let s := (1 - κ * star ρ)⁻¹
  intro hT
  change IsUnit T.det at hT
  have hLL : Lᴴ * L = 1 := by
    ext i j : 1
    cases i
    cases j
    simpa only [Matrix.mul_apply, Matrix.conjTranspose_apply, L, Matrix.one_apply_eq] using hu
  have hCL : C * L = ρ • (A * L) := by
    ext i j : 1
    simpa only [Matrix.mul_apply, L, Matrix.smul_apply, smul_eq_mul, Matrix.mulVec,
      dotProduct, Pi.smul_apply] using congrFun heig i
  have hLC : Lᴴ * C = star ρ • (Lᴴ * A) := by
    simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_smul, hA.eq, hC.eq] using
      congrArg Matrix.conjTranspose hCL
  have hiso : Lᴴ * A * L = 0 := by
    have he : ρ • (Lᴴ * A * L) = star ρ • (Lᴴ * A * L) := calc
      _ = Lᴴ * (C * L) := by rw [hCL, Matrix.mul_smul, Matrix.mul_assoc]
      _ = _ := by rw [← Matrix.mul_assoc, hLC, Matrix.smul_mul]
    ext i j : 1
    have hij := congrArg (fun M : Matrix Unit Unit ℂ => M i j) he
    simp only [Matrix.smul_apply, smul_eq_mul] at hij
    have hzero : (ρ - star ρ) * (Lᴴ * A * L) i j = 0 := by
      rw [sub_mul, hij, sub_self]
    exact (mul_eq_zero.mp hzero).resolve_left (sub_ne_zero.mpr hρ)
  have hTL : T * L = (1 - κ * ρ) • (A * L) := by
    simp only [T, Matrix.sub_mul, Matrix.smul_mul, hCL, smul_smul, sub_smul, one_smul]
  have hLT : Lᴴ * T = (1 - κ * star ρ) • (Lᴴ * A) := by
    simp only [T, Matrix.mul_sub, Matrix.mul_smul, hLC, smul_smul, sub_smul, one_smul]
  have hleft : L = T⁻¹ * (T * L) := by
    rw [← Matrix.mul_assoc, T.nonsing_inv_mul hT, Matrix.one_mul]
  have hright : Lᴴ = (Lᴴ * T) * T⁻¹ := by
    rw [Matrix.mul_assoc, T.mul_nonsing_inv hT, Matrix.mul_one]
  have hr : 1 - κ * ρ ≠ 0 := by
    intro h
    have hzero : L = 0 := by rw [hleft, hTL, h, zero_smul, Matrix.mul_zero]
    have he : (0 : Matrix Unit Unit ℂ) = 1 := by
      simpa only [hzero, Matrix.conjTranspose_zero, Matrix.mul_zero] using hLL
    exact zero_ne_one he
  have hs : 1 - κ * star ρ ≠ 0 := by
    intro h
    have hzero : Lᴴ = 0 := by rw [hright, hLT, h, zero_smul, Matrix.zero_mul]
    have he : (0 : Matrix Unit Unit ℂ) = 1 := by
      simpa only [hzero, Matrix.zero_mul] using hLL
    exact zero_ne_one he
  refine ⟨hr, hs, ?_⟩
  have hleft' : T⁻¹ * (A * L) = r • L := by
    have he := congrArg (fun M : Matrix ι Unit ℂ => r • M) hleft
    change r • L = r • (T⁻¹ * (T * L)) at he
    rw [hTL, Matrix.mul_smul] at he
    simpa only [r, smul_smul, inv_mul_cancel₀ hr, one_smul] using he.symm
  have hright' : (Lᴴ * A) * T⁻¹ = s • Lᴴ := by
    have he := congrArg (fun M : Matrix Unit ι ℂ => s • M) hright
    change s • Lᴴ = s • ((Lᴴ * T) * T⁻¹) at he
    rw [hLT, Matrix.smul_mul] at he
    simpa only [s, smul_smul, inv_mul_cancel₀ hs, one_smul] using he.symm
  let R := (-κ * star ρ) • (Lᴴ * A)
  have hR : R = (-κ) • (Lᴴ * C) := by
    simp only [R, hLC, smul_smul]
  have hcomp₀ : Lᴴ * T⁻¹ * (A * L) = r • (1 : Matrix Unit Unit ℂ) := by
    rw [Matrix.mul_assoc, hleft', Matrix.mul_smul, hLL]
  have hs' : (-κ * star ρ) * s = 1 - s := by
    have he : (1 - κ * star ρ) * s = 1 := mul_inv_cancel₀ hs
    linear_combination he
  have hcomp₁ : R * T⁻¹ * L = (1 - s) • (1 : Matrix Unit Unit ℂ) := by
    simp only [R, Matrix.smul_mul, hright', smul_smul, hLL, hs']
  have htri : R * T⁻¹ * (A * L) = 0 := by
    simp only [R, Matrix.smul_mul, hright', smul_smul, ← Matrix.mul_assoc Lᴴ A L,
      hiso, smul_zero]
  have hP : L * Lᴴ = vecMulVec u (star ∘ u) := by
    ext i j : 1
    simp [L, Matrix.mul_apply, Matrix.vecMulVec_apply]
  have hV : IsUnitary V := rankOnePhase_unitary u z hu hz
  have hVP : V = 1 + (z - 1) • (L * Lᴴ) := by
    simp only [V, rankOnePhase, hP]
  have hmat : (A - κ • (V * C * Vᴴ)) * V =
      T + (z - 1) • ((A * L) * Lᴴ + L * R) := by
    rw [Matrix.sub_mul, Matrix.smul_mul, Matrix.mul_assoc (V * C) Vᴴ V, hV.2, Matrix.mul_one]
    rw [hVP]
    simp only [T, hR, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul,
      Matrix.mul_smul, Matrix.smul_mul, smul_add, smul_smul, Matrix.mul_assoc, mul_neg,
      neg_smul, mul_comm (z - 1) κ]
    abel
  have hdet : (A - κ • (V * C * Vᴴ)).det * z =
      T.det * ((1 + (z - 1) * r) * (1 + (z - 1) * (1 - s))) := by
    calc
      _ = (A - κ • (V * C * Vᴴ)).det * V.det := by
        rw [show V.det = z from det_rankOnePhase u z hu]
      _ = _ := by
        rw [← Matrix.det_mul, hmat,
          det_two_updates_of_triangular_compression T hT (A * L) L Lᴴ R (z - 1) htri,
          hcomp₀, hcomp₁]
        simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
  have hzn : z ≠ 0 := fun h => by simpa only [h, zero_mul, zero_ne_one] using hz
  apply mul_right_cancel₀ hzn
  rw [hdet]
  have hr' : r - 1 = κ * ρ * r := by
    have he : (1 - κ * ρ) * r = 1 := mul_inv_cancel₀ hr
    linear_combination he
  have he : (1 + (z - 1) * (1 - s)) = z * (1 + (star z - 1) * s) := by
    linear_combination -s * hz
  rw [he]
  have hratio : (1 + (z - 1) * r) * (1 + (star z - 1) * s) =
      1 - κ * r * s * ((z - 1) * star ρ + (star z - 1) * ρ) := by
    linear_combination r * s * hz - (z - 1) * r * hs' - (star z - 1) * s * hr'
  calc
    _ = T.det * ((1 + (z - 1) * r) * (1 + (star z - 1) * s)) * z := by ring
    _ = _ := by rw [hratio]

/-- The determinant of a nonsingular Hermitian pencil with a nonreal
generalized eigenvalue cannot satisfy a quadratic support penalty on its orbit. -/
theorem no_quadratic_support_of_nonreal_pencil_vector (A C : Matrix ι ι ℂ)
    (hA : A.IsHermitian) (hC : C.IsHermitian) (κ ξ ρ : ℂ) (hκ : κ ≠ 0)
    (hρ : ρ ≠ star ρ) (u : ι → ℂ) (hu : ∑ i, star (u i) * u i = 1)
    (heig : C *ᵥ u = ρ • (A *ᵥ u)) :
    let T := A - κ • C
    IsUnit T.det →
    (∀ V : Matrix ι ι ℂ, IsUnitary V →
      let d := (A - κ • (V * C * Vᴴ)).det - T.det
      (ξ * d).re ≤ -Complex.normSq d / 2) → False := by
  dsimp only
  let T := A - κ • C
  let r := (1 - κ * ρ)⁻¹
  let s := (1 - κ * star ρ)⁻¹
  let D := -T.det * κ * r * s
  intro hT hpenalty
  change IsUnit T.det at hT
  obtain ⟨hr, hs, _⟩ := determinant_rankOnePhase_of_nonreal_pencil_vector
    A C hA hC κ ρ hρ u hu heig 1 (by simp) hT
  have hD : D ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr (isUnit_iff_ne_zero.mp hT)) hκ)
      (inv_ne_zero hr)) (inv_ne_zero hs)
  let H (z : ℂ) := 2 * ((z - 1) * star ρ).re
  have hH (z : ℂ) : ((H z : ℝ) : ℂ) = (z - 1) * star ρ + (star z - 1) * ρ := by
    have he : star ((z - 1) * star ρ) = (star z - 1) * ρ := by
      simp only [star_mul', star_sub, star_one, star_star, mul_comm]
    rw [← he, Complex.star_def, Complex.add_conj]
  have hsupport (z : ℂ) (hz : z * star z = 1) :
      H z * (ξ * D).re ≤ -Complex.normSq ((H z : ℂ) * D) / 2 := by
    let V := rankOnePhase u z
    have hd : (A - κ • (V * C * Vᴴ)).det - T.det = (H z : ℂ) * D := by
      rw [(determinant_rankOnePhase_of_nonreal_pencil_vector A C hA hC κ ρ hρ
        u hu heig z hz hT).2.2, ← hH]
      dsimp only [D, r, s]
      ring
    have h := hpenalty V (rankOnePhase_unitary u z hu hz)
    change (ξ * ((A - κ • (V * C * Vᴴ)).det - T.det)).re ≤
      -Complex.normSq ((A - κ • (V * C * Vᴴ)).det - T.det) / 2 at h
    rw [hd] at h
    simpa only [mul_left_comm ξ (H z : ℂ) D, Complex.re_ofReal_mul] using h
  have him : ρ.im ≠ 0 := fun h => hρ (by
    simpa only [Complex.star_def] using (Complex.conj_eq_iff_im.mpr h).symm)
  have hρ₀ : ρ ≠ 0 := fun he => hρ (by simp [he])
  let t := ‖ρ‖
  have ht : 0 < t := norm_pos_iff.mpr hρ₀
  have htn : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  have htbound : -t ≤ ρ.re ∧ ρ.re ≤ t := abs_le.mp (Complex.abs_re_le_norm ρ)
  have hsquare : ρ.re ^ 2 < t ^ 2 := by
    have he := Complex.sq_norm_sub_sq_re ρ
    change t ^ 2 - ρ.re ^ 2 = ρ.im ^ 2 at he
    linarith only [he, sq_pos_of_ne_zero him]
  have hright : ρ.re < t := by
    by_contra! h
    rw [le_antisymm htbound.2 h] at hsquare
    exact (lt_irrefl _) hsquare
  have hleft : -t < ρ.re := by
    by_contra! h
    rw [le_antisymm h htbound.1, neg_sq] at hsquare
    exact (lt_irrefl _) hsquare
  let p : ℂ := ρ / (t : ℂ)
  have hp : p * star p = 1 := by
    have hnorm : Complex.normSq p = 1 := by
      rw [show p = ρ / (t : ℂ) from rfl, Complex.normSq_div, Complex.normSq_ofReal,
        ← Complex.norm_mul_self_eq_normSq ρ]
      exact div_self (mul_ne_zero ht.ne' ht.ne')
    simp only [Complex.star_def, Complex.mul_conj, hnorm, Complex.ofReal_one]
  have hn : (-p) * star (-p) = 1 := by simp only [star_neg, mul_neg, neg_mul, neg_neg, hp]
  have hpρ : p * star ρ = (t : ℂ) := by
    rw [show p = ρ / (t : ℂ) from rfl, div_mul_eq_mul_div, Complex.star_def,
      Complex.mul_conj, ← Complex.norm_mul_self_eq_normSq ρ, Complex.ofReal_mul]
    exact mul_div_cancel_right₀ _ htn
  have hre (z : ℂ) : ((z - 1) * star ρ).re = (z * star ρ).re - ρ.re := by
    rw [sub_mul, one_mul, Complex.sub_re, Complex.star_def, Complex.conj_re]
  have hpos : 0 < H p := by
    dsimp only [H]
    rw [hre, hpρ, Complex.ofReal_re]
    exact mul_pos two_pos (sub_pos.mpr hright)
  have hneg : H (-p) < 0 := by
    dsimp only [H]
    rw [hre, neg_mul, hpρ, Complex.neg_re, Complex.ofReal_re]
    exact mul_neg_of_pos_of_neg two_pos (sub_neg.mpr hleft)
  have hpn : (H p : ℂ) * D ≠ 0 := mul_ne_zero (Complex.ofReal_ne_zero.mpr hpos.ne') hD
  have hstrict : H p * (ξ * D).re < 0 :=
    (hsupport p hp).trans_lt (by linarith only [Complex.normSq_pos.mpr hpn])
  have hξD : (ξ * D).re < 0 := by
    by_contra! he
    exact (not_lt_of_ge (mul_nonneg hpos.le he)) hstrict
  exact (not_le_of_gt (mul_pos_of_neg_of_neg hneg hξD))
    ((hsupport (-p) hn).trans (by linarith only [Complex.normSq_nonneg ((H (-p) : ℂ) * D)]))

private theorem exists_normalized_column (v : ι → ℂ) (hv : v ≠ 0) :
    ∃ k : ℂ, ∑ i, star ((k • v) i) * (k • v) i = 1 := by
  classical
  let s := ∑ i, Complex.normSq (v i)
  have hs : 0 < s := by
    obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
      by_contra! h
      exact hv (funext h)
    exact Finset.sum_pos' (fun i _ => Complex.normSq_nonneg (v i))
      ⟨i, Finset.mem_univ i, Complex.normSq_pos.mpr hi⟩
  let q := Real.sqrt s
  let k := (q : ℂ)⁻¹
  have hq : (q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hs).ne'
  have hkk : star k = k := by simp [k, Complex.star_def]
  have hterm (i : ι) : star ((k • v) i) * (k • v) i =
      (k * k) * (Complex.normSq (v i) : ℂ) := by
    simp only [Pi.smul_apply, smul_eq_mul, star_mul', hkk, Complex.normSq_eq_conj_mul_self,
      ← Complex.star_def]
    ring
  have hqq : (q : ℂ) * (q : ℂ) = (s : ℂ) := by
    rw [← Complex.ofReal_mul, show q * q = s from Real.mul_self_sqrt hs.le]
  refine ⟨k, ?_⟩
  calc
    _ = (k * k) * (s : ℂ) := by
      simp only [hterm, ← Finset.mul_sum, s, Complex.ofReal_sum]
    _ = ((q : ℂ)⁻¹ * (q : ℂ)) * ((q : ℂ)⁻¹ * (q : ℂ)) := by rw [← hqq]; dsimp only [k]; ring
    _ = 1 := by rw [inv_mul_cancel₀ hq, one_mul]

/-- At a quadratic support maximum for a nonsingular Hermitian pencil, every
root of the generalized eigenvalue determinant is real. -/
theorem det_pencil_ne_zero_of_quadratic_support (A C : Matrix ι ι ℂ)
    (hA : A.IsHermitian) (hC : C.IsHermitian) (κ ξ ρ : ℂ) (hκ : κ ≠ 0)
    (hρ : ρ ≠ star ρ) :
    let T := A - κ • C
    IsUnit T.det →
    (∀ V : Matrix ι ι ℂ, IsUnitary V →
      let d := (A - κ • (V * C * Vᴴ)).det - T.det
      (ξ * d).re ≤ -Complex.normSq d / 2) → (C - ρ • A).det ≠ 0 := by
  dsimp only
  intro hT hpenalty hdet
  obtain ⟨v, hv, hz⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have hvec : C *ᵥ v = ρ • (A *ᵥ v) := by
    apply sub_eq_zero.mp
    simpa only [Matrix.sub_mulVec, Matrix.smul_mulVec_assoc] using hz
  obtain ⟨k, hk⟩ := exists_normalized_column v hv
  have heig : C *ᵥ (k • v) = ρ • (A *ᵥ (k • v)) := by
    simp only [Matrix.mulVec_smul, hvec, smul_smul, mul_comm k ρ]
  exact no_quadratic_support_of_nonreal_pencil_vector A C hA hC κ ξ ρ hκ hρ
    (k • v) hk heig hT hpenalty

end

end MOC
