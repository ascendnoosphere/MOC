import MOC.ConcentricCompressedHessian
import MOC.ConcentricStationarity
import MOC.ConcentricTwoBranches

/-! An irreducible support maximum for scaled unitaries has a scalar
relative product, expressed in an eigenbasis of that product. -/

open BigOperators Matrix

namespace MOC

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- In order greater than two, two scaled unitaries with unequal positive
radii cannot have a nonscalar relative product at an orbit support maximum
whose common commutant is scalar. -/
theorem relative_unitary_scalar_of_support_maximum (U : Matrix ι ι ℂ) (hU : IsUnitary U)
    (w : ι → ℂ) (hw : ∀ i, Complex.normSq (w i) = 1)
    (t : ℝ) (ht : 0 < t) (hlt : t < 1) (η : ℂ) (hη : η ≠ 0) (hcard : 2 < Fintype.card ι)
    (hcomm : ∀ Y : Matrix ι ι ℂ, Commute U Y → Commute (diagonal w) Y →
      ∃ c : ℂ, Y = c • (1 : Matrix ι ι ℂ))
    (hmax : ∀ V : Matrix ι ι ℂ, IsUnitary V →
      (η * (U + V * ((t : ℂ) • (U * diagonal w)) * Vᴴ).det).re ≤
        (η * (U + (t : ℂ) • (U * diagonal w)).det).re) :
    ∀ i j, w i = w j := by
  let d (i : ι) := 1 + (t : ℂ) * w i
  let T := (1 : Matrix ι ι ℂ) + (t : ℂ) • diagonal w
  let p (i : ι) := (t : ℂ) * w i / d i
  let ω := η * (U + (t : ℂ) • (U * diagonal w)).det
  have hd (i : ι) : d i ≠ 0 := normSq_phase_denominator_ne_zero t ht hlt (w i) (hw i)
  have hTdiag : T = diagonal d := by
    dsimp only [T]
    rw [← Matrix.diagonal_one, ← Matrix.diagonal_smul, ← Matrix.diagonal_add] <;> rfl
  have hT : IsUnit T.det := isUnit_iff_ne_zero.mpr (by
    rw [hTdiag, Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => hd i)
  have hω : ω ≠ 0 := by
    have hC : U + (t : ℂ) • (U * diagonal w) = U * T := by
      simp [T, Matrix.mul_add, Matrix.mul_smul]
    dsimp only [ω]
    rw [hC, Matrix.det_mul]
    exact mul_ne_zero hη (mul_ne_zero (det_ne_zero_of_unitary hU) (isUnit_iff_ne_zero.mp hT))
  have hInv : T⁻¹ = diagonal (fun i => (d i)⁻¹) := by
    apply Matrix.inv_eq_left_inv
    rw [hTdiag, Matrix.diagonal_mul_diagonal]
    simp [Pi.mul_apply, inv_mul_cancel₀, hd]
  have hP : ((t : ℂ) • diagonal w) * T⁻¹ = diagonal p := by
    rw [hInv, Matrix.smul_mul, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_smul]
    apply congrArg diagonal
    funext i
    simp only [Pi.smul_apply, Pi.mul_apply, p, smul_eq_mul, div_eq_mul_inv, mul_assoc]
  have hpinj (i j : ι) (h : p i = p j) : w i = w j := by
    have he := (div_eq_div_iff (hd i) (hd j)).mp h
    have htEq : (t : ℂ) * w i = (t : ℂ) * w j := by
      dsimp only [d] at he
      linear_combination he
    exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr ht.ne') htEq
  obtain ⟨hsame, htwo⟩ := relative_phase_values_of_support_maximum U hU w hw t ht hlt η hη hcomm hmax
  change ∀ i j, (ω * p i).im = (ω * p j).im at hsame
  have htwoP (i j k : ι) : p i = p j ∨ p i = p k ∨ p j = p k := by
    let f (z : ℂ) := (t : ℂ) * z / (1 + (t : ℂ) * z)
    rcases htwo i j k with h | h | h
    · exact Or.inl (congrArg f h)
    · exact Or.inr (Or.inl (congrArg f h))
    · exact Or.inr (Or.inr (congrArg f h))
  have hp (i : ι) : Complex.normSq (p i) = t ^ 2 * Complex.normSq (1 - p i) :=
    relative_phase_norm t (w i) (hw i) (hd i)
  have hx : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
  let i₀ := Classical.choice hx
  have hhess (v : ι → ℝ) (hv : ∑ i, v i = 0) :
      0 ≤ (∑ i, (v i) ^ 2 * (ω * (p i * (1 - p i))).re) + (ω * (∑ i, (v i : ℂ) * p i) ^ 2).re :=
    concentric_compressed_hessian_nonneg U hU w p hw (t : ℂ) η hcomm hmax hT hP hpinj v hv
      ⟨(ω * p i₀).im, fun i => hsame i i₀⟩
      (fun i j h => re_phase_cross_zero t ht hlt (p i) (p j) ω h hω (hp i) (hp j) (hsame i j))
  have h := constant_phase_of_two_branches_and_compressed_hessian t ht hlt ω hω p hcard hp hsame htwoP hhess
  exact fun i j => hpinj i j (h i j)

end MOC
