import MOC.CompressedUnitaryTangent
import MOC.ConcentricTraceWeights
import MOC.UnitaryOrbitHessian

/-! All real trace-zero diagonal velocities in a relative eigenbasis are
legitimate second-variation directions for the concentric-circle problem. -/

open BigOperators Matrix

namespace MOC

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The compressed determinant Hessian must be nonnegative after reversing
the sign of the Hermitian generator's quadratic terms. -/
theorem concentric_compressed_hessian_nonneg
    (U : Matrix ι ι ℂ) (hU : IsUnitary U)
    (w p : ι → ℂ) (hw : ∀ i, Complex.normSq (w i) = 1)
    (ρ η : ℂ)
    (hcomm : ∀ Y : Matrix ι ι ℂ, Commute U Y → Commute (diagonal w) Y →
      ∃ c : ℂ, Y = c • (1 : Matrix ι ι ℂ))
    (hmax : ∀ V : Matrix ι ι ℂ, IsUnitary V →
      (η * (U + V * (ρ • (U * diagonal w)) * Vᴴ).det).re ≤
        (η * (U + ρ • (U * diagonal w)).det).re)
    (hT : IsUnit ((1 : Matrix ι ι ℂ) + ρ • diagonal w).det)
    (hP : (ρ • diagonal w) * ((1 : Matrix ι ι ℂ) + ρ • diagonal w)⁻¹ = diagonal p)
    (hpinj : ∀ i j, p i = p j → w i = w j)
    (v : ι → ℝ) (hv : ∑ i, v i = 0) :
    let ω := η * (U + ρ • (U * diagonal w)).det
    (∃ c : ℝ, ∀ i, (ω * p i).im = c) →
    (∀ i j, p i ≠ p j → (ω * (p i + p j - 2 * p i * p j)).re = 0) →
    0 ≤ (∑ i, (v i) ^ 2 * (ω * (p i * (1 - p i))).re) +
      (ω * (∑ i, (v i : ℂ) * p i) ^ 2).re := by
  intro ω hphase hcross
  let W := diagonal w
  let P := diagonal p
  let D := diagonal (fun i => (v i : ℂ))
  have hWstar : Wᴴ = diagonal (fun i => star (w i)) := Matrix.diagonal_conjTranspose w
  have hwstar (i : ι) : w i * star (w i) = 1 := by
    simp only [Complex.star_def, Complex.mul_conj, hw, Complex.ofReal_one]
  have hwstar' (i : ι) : star (w i) * w i = 1 := by rw [mul_comm, hwstar]
  have hW : IsUnitary W := by
    constructor
    · change W * Wᴴ = 1
      rw [hWstar, Matrix.diagonal_mul_diagonal]
      simpa only [hwstar] using (Matrix.diagonal_one : diagonal (fun _ => 1) = (1 : Matrix ι ι ℂ))
    · change Wᴴ * W = 1
      rw [hWstar, Matrix.diagonal_mul_diagonal]
      simpa only [hwstar'] using (Matrix.diagonal_one : diagonal (fun _ => 1) = (1 : Matrix ι ι ℂ))
  have hD : D.IsHermitian := by
    change Dᴴ = D
    simp only [D, Matrix.diagonal_conjTranspose]
    exact congrArg diagonal (funext fun i => by simp [Pi.star_apply, Complex.star_def])
  have hDtrace : D.trace = 0 := by
    simp only [D, Matrix.trace_diagonal, ← Complex.ofReal_sum, hv, Complex.ofReal_zero]
  have hDcomp : compressEigenspaces w D = D := by
    ext i j : 1
    by_cases h : i = j
    · subst j
      simp [compressEigenspaces_apply]
    · simp [compressEigenspaces_apply, D, Matrix.diagonal_apply_ne _ h]
  have hcomm' (Y : Matrix ι ι ℂ) (hy : compressEigenspaces w Y = Y) (hu : Commute U Y) :
      ∃ c : ℂ, Y = c • (1 : Matrix ι ι ℂ) := by
    apply hcomm Y hu
    change W * Y = Y * W
    ext i j : 1
    simp only [W, Matrix.diagonal_mul, Matrix.mul_diagonal]
    by_cases he : w i = w j
    · rw [he, mul_comm]
    · have hz := congrArg (fun M : Matrix ι ι ℂ => M i j) hy
      simp only [compressEigenspaces_apply, if_neg he] at hz
      simp [← hz]
  obtain ⟨L, hL, hcompress⟩ := exists_hermitian_for_compressed_unitary_tangent w U hU
    hcomm' D hD hDcomp hDtrace
  let R := Uᴴ * L * U
  let S := W * L * Wᴴ
  let H := R - S
  let E := R * S - S * R
  have hR : Rᴴ = R := by
    simp only [R, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hL.eq, Matrix.mul_assoc]
  have hS : Sᴴ = S := by
    simp only [S, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hL.eq, Matrix.mul_assoc]
  have hH : H.IsHermitian := by change Hᴴ = H; simp only [H, Matrix.conjTranspose_sub, hR, hS]
  have hE : Eᴴ = -E := by
    simp only [E, Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, hR, hS, neg_sub]
  have hEtr : E.trace = 0 := by
    simp only [E, Matrix.trace_sub, Matrix.trace_mul_comm R S, sub_self]
  have hScomp : compressEigenspaces w S = compressEigenspaces w L := by
    ext i j : 1
    simp only [compressEigenspaces_apply]
    by_cases he : w i = w j
    · simp only [if_pos he, S, W, hWstar, Matrix.diagonal_mul, Matrix.mul_diagonal]
      rw [he, mul_right_comm, hwstar, one_mul]
    · simp only [if_neg he]
  have hHcomp : compressEigenspaces w H = D := by
    simp only [H, map_sub, hScomp]
    simpa only [map_sub, R] using hcompress
  have hentries (i j : ι) (hij : w i = w j) : H i j = D i j := by
    have hh := congrArg (fun M : Matrix ι ι ℂ => M i j) hHcomp
    simpa only [compressEigenspaces_apply, if_pos hij] using hh
  have hd (i : ι) : H i i = (v i : ℂ) := by simpa [D] using hentries i i rfl
  have hb (i j : ι) (hij : i ≠ j) (hij' : p i = p j) : H i j = 0 := by
    simpa [D, Matrix.diagonal_apply_ne _ hij] using hentries i j (hpinj i j hij')
  obtain ⟨c, hc⟩ := hphase
  have hcancel : (ω * (E * P).trace).re = 0 := re_trace_skew_mul_diagonal_eq_zero E hE hEtr p ω c hc
  have hK : (Complex.I • L)ᴴ = -(Complex.I • L) := by
    simp only [Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_I, hL.eq, neg_smul]
  have hs := relative_unitary_trace_hessian_nonpos U W hU hW ρ η hT hmax (Complex.I • L) hK
  dsimp only at hs
  have hRK : Uᴴ * (Complex.I • L) * U = Complex.I • R := by
    simp only [R, Matrix.mul_smul, Matrix.smul_mul]
  have hSK : W * (Complex.I • L) * Wᴴ = Complex.I • S := by
    simp only [S, Matrix.mul_smul, Matrix.smul_mul]
  have hDK : (Complex.I • R - Complex.I • S) * diagonal p = Complex.I • (H * P) := by
    rw [← smul_sub, Matrix.smul_mul]
  rw [hRK, hSK, hP, hDK] at hs
  have hacc : (Complex.I • R) * (Complex.I • R) + (Complex.I • S) * (Complex.I • S) -
      ((Complex.I • R) * (Complex.I • S) + (Complex.I • R) * (Complex.I • S)) = E - H * H := by
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Complex.I_mul_I, neg_one_smul,
      E, H, Matrix.sub_mul, Matrix.mul_sub]
    abel
  have hsquare : ((Complex.I • (H * P)).trace) ^ 2 = -((H * P).trace) ^ 2 := by
    rw [Matrix.trace_smul, smul_eq_mul, mul_pow, Complex.I_sq, neg_one_mul]
  have htrace : (H * P).trace = ∑ i, (v i : ℂ) * p i := by
    simp only [P, Matrix.trace, Matrix.diag_apply, Matrix.mul_diagonal, hd]
  change (ω * ((_ * P).trace + ((Complex.I • (H * P)).trace) ^ 2 -
    ((Complex.I • (H * P)) * (Complex.I • (H * P))).trace)).re ≤ 0 at hs
  rw [hacc, Matrix.sub_mul, Matrix.trace_sub, hsquare, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, Complex.I_mul_I, neg_one_smul, Matrix.trace_neg] at hs
  have hexpr :
      (E * P).trace - ((H * H) * P).trace + -((H * P).trace) ^ 2 -
        -((H * P) * (H * P)).trace =
      (E * P).trace - ((((H * H) * P).trace - ((H * P) * (H * P)).trace) + ((H * P).trace) ^ 2) := by
    ring
  rw [hexpr, mul_sub, Complex.sub_re, hcancel, zero_sub, neg_nonpos, mul_add, Complex.add_re] at hs
  rw [re_trace_quadratic_of_diagonal_compression H hH p v ω hd hb hcross, htrace] at hs
  exact hs

end MOC
