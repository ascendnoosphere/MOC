import MOC.SpectralDeterminantStability
import MOC.TranspositionWinding
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-! Three two-dimensional blocks give a determinant range that avoids zero
and contains a loop of winding number one. -/

open Matrix
open scoped unitInterval

namespace MOC

noncomputable section

private def windingBlockLeft : Fin 2 → ℂ := ![1, 16]
private def windingBlockRight : Fin 2 → ℂ := ![4 * Complex.I, -(4 * Complex.I)]

def orderSixWindingLeft (i : Fin 2 × Fin 3) : ℂ := windingBlockLeft i.1
def orderSixWindingRight (i : Fin 2 × Fin 3) : ℂ := windingBlockRight i.1

/-- The entire order-six range avoids zero. Multiplication by `I` sends
the first spectrum into the open upper half-plane and the second to the
real line. -/
theorem zero_notMem_orderSixDeterminantRange :
    0 ∉ determinantRange orderSixWindingLeft orderSixWindingRight := by
  rintro ⟨U, _, hU⟩
  have ha (i : Fin 2 × Fin 3) : 0 < (Complex.I * orderSixWindingLeft i).im := by
    rcases i with ⟨i, k⟩
    fin_cases i <;> norm_num [orderSixWindingLeft, windingBlockLeft, Complex.mul_im]
  have hb (i : Fin 2 × Fin 3) : 0 ≤ (Complex.I * orderSixWindingRight i).im := by
    rcases i with ⟨i, k⟩
    fin_cases i <;> norm_num [orderSixWindingRight, windingBlockRight,
      Complex.mul_re, Complex.mul_im]
  have hn := determinantValue_ne_zero_of_im_pos
    (fun i => Complex.I * orderSixWindingLeft i) (fun i => Complex.I * orderSixWindingRight i)
    U ha hb
  rw [determinantValue_scale, hU, mul_zero] at hn
  exact hn rfl

private theorem windingBlockIdentity : matchingProduct windingBlockLeft windingBlockRight 1 =
    32 + 60 * Complex.I := by
  apply Complex.ext <;>
    norm_num [matchingProduct, Fin.prod_univ_two, windingBlockLeft, windingBlockRight,
      Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im]

private theorem windingBlockSwap :
    matchingProduct windingBlockLeft windingBlockRight (Equiv.swap 0 1) = 32 - 60 * Complex.I := by
  apply Complex.ext <;>
    norm_num [matchingProduct, Fin.prod_univ_two, windingBlockLeft, windingBlockRight,
      Equiv.swap_apply_left, Equiv.swap_apply_right, Complex.mul_re, Complex.mul_im,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im]

private theorem windingBlockSegment (t : I) :
    determinantValue windingBlockLeft windingBlockRight (swapRotation 0 1 t) =
      32 + ((60 * (1 - 2 * (t : ℝ)) : ℝ) : ℂ) * Complex.I := by
  rw [determinantValue_swapRotation _ _ 0 1 (by decide), windingBlockIdentity, windingBlockSwap]
  push_cast
  ring

private def windingLine (t : I) : ℂ :=
  32 + ((32 * Real.sqrt 3 * (2 * (t : ℝ) - 1) : ℝ) : ℂ) * Complex.I

/-- The three-block path, parametrized from the lower end of the
vertical segment to the upper end before taking its cube. -/
def orderSixDeterminantWindingLoop (t : I) : ℂ := (windingLine t) ^ 3

private theorem windingLine_continuous : Continuous windingLine := by
  unfold windingLine
  fun_prop

private theorem windingLine_re (t : I) : (windingLine t).re = 32 := by
  norm_num [windingLine, Complex.add_re, Complex.mul_re]

private theorem windingLine_ne_zero (t : I) : windingLine t ≠ 0 := by
  intro hz
  have h := windingLine_re t
  rw [hz, Complex.zero_re] at h
  norm_num at h

private def windingRotationParam (t : I) : I := by
  let y : ℝ := 32 * Real.sqrt 3 * (2 * (t : ℝ) - 1)
  have ht : |2 * (t : ℝ) - 1| ≤ 1 := abs_le.mpr
    ⟨by linarith only [t.property.1], by linarith only [t.property.2]⟩
  have hsqrt : Real.sqrt 3 < 15 / 8 := (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)
  have hy : |y| ≤ 60 := by
    rw [show y = (32 * Real.sqrt 3) * (2 * (t : ℝ) - 1) from rfl, abs_mul,
      abs_of_nonneg (by positivity : 0 ≤ (32 : ℝ) * Real.sqrt 3)]
    calc
      _ ≤ (32 * Real.sqrt 3) * 1 := mul_le_mul_of_nonneg_left ht (by positivity)
      _ ≤ 60 := by linarith only [hsqrt]
  obtain ⟨hylo, hyhi⟩ := abs_le.mp hy
  exact ⟨(60 - y) / 120, by linarith only [hyhi], by linarith only [hylo]⟩

private theorem windingRotationParam_value (t : I) :
    60 * (1 - 2 * (windingRotationParam t : ℝ)) =
      32 * Real.sqrt 3 * (2 * (t : ℝ) - 1) := by
  change 60 * (1 - 2 * ((60 - 32 * Real.sqrt 3 * (2 * (t : ℝ) - 1)) / 120)) = _
  ring

/-- Every point on the displayed loop is an actual determinant for a
direct sum of three identical swap rotations. -/
theorem orderSixDeterminantWindingLoop_mem (t : I) :
    orderSixDeterminantWindingLoop t ∈ determinantRange orderSixWindingLeft orderSixWindingRight := by
  let R : Matrix (Fin 2) (Fin 2) ℂ := swapRotation 0 1 (windingRotationParam t)
  have hR : IsUnitary R := swapRotation_unitary 0 1 _
  let Q (_ : Fin 3) := R
  have hQr : (fun k => Q k * (Q k)ᴴ) = 1 := funext fun _ => hR.1
  have hQl : (fun k => (Q k)ᴴ * Q k) = 1 := funext fun _ => hR.2
  refine ⟨Matrix.blockDiagonal Q, ⟨?_, ?_⟩, ?_⟩
  · rw [Matrix.blockDiagonal_conjTranspose, ← Matrix.blockDiagonal_mul, hQr,
      Matrix.blockDiagonal_one]
  · rw [Matrix.blockDiagonal_conjTranspose, ← Matrix.blockDiagonal_mul, hQl,
      Matrix.blockDiagonal_one]
  have hdet : determinantValue orderSixWindingLeft orderSixWindingRight (Matrix.blockDiagonal Q) =
      ∏ k : Fin 3, determinantValue windingBlockLeft windingBlockRight (Q k) := by
    unfold determinantValue orderSixWindingLeft orderSixWindingRight
    rw [← Matrix.blockDiagonal_diagonal (fun _ : Fin 3 => windingBlockLeft),
      ← Matrix.blockDiagonal_diagonal (fun _ : Fin 3 => windingBlockRight),
      Matrix.blockDiagonal_conjTranspose, ← Matrix.blockDiagonal_mul, ← Matrix.blockDiagonal_mul,
      ← Matrix.blockDiagonal_add, Matrix.det_blockDiagonal] <;> rfl
  have hline (k : Fin 3) : determinantValue windingBlockLeft windingBlockRight (Q k) =
      windingLine t := by
    change determinantValue windingBlockLeft windingBlockRight
      (swapRotation 0 1 (windingRotationParam t)) = windingLine t
    rw [windingBlockSegment, windingRotationParam_value] <;> rfl
  rw [hdet]
  simp only [hline, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    orderSixDeterminantWindingLoop]

private theorem windingCubeEnd (x : ℝ) (hx : x ^ 2 = 3) :
    ((32 : ℂ) + ((32 * x : ℝ) : ℂ) * Complex.I) ^ 3 = -262144 := by
  apply Complex.ext
  · norm_num [pow_succ, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.neg_re]
    linear_combination -98304 * hx
  · norm_num [pow_succ, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.neg_im]
    linear_combination -32768 * x * hx

private theorem windingLine_zero : windingLine 0 =
    32 + ((32 * (-Real.sqrt 3) : ℝ) : ℂ) * Complex.I := by
  have h : (32 : ℝ) * Real.sqrt 3 * (2 * ((0 : I) : ℝ) - 1) = 32 * (-Real.sqrt 3) := by
    change (32 : ℝ) * Real.sqrt 3 * (2 * 0 - 1) = 32 * (-Real.sqrt 3)
    ring
  simp only [windingLine, h]

private theorem windingLine_one : windingLine 1 =
    32 + ((32 * Real.sqrt 3 : ℝ) : ℂ) * Complex.I := by
  have h : (32 : ℝ) * Real.sqrt 3 * (2 * ((1 : I) : ℝ) - 1) = 32 * Real.sqrt 3 := by
    change (32 : ℝ) * Real.sqrt 3 * (2 * 1 - 1) = 32 * Real.sqrt 3
    ring
  simp only [windingLine, h]

theorem orderSixDeterminantWindingLoop_endpoints :
    orderSixDeterminantWindingLoop 0 = -262144 ∧ orderSixDeterminantWindingLoop 1 = -262144 := by
  have hs : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  constructor
  · simpa only [orderSixDeterminantWindingLoop, windingLine_zero] using
      windingCubeEnd (-Real.sqrt 3) (by simpa only [neg_sq] using hs)
  · simpa only [orderSixDeterminantWindingLoop, windingLine_one] using windingCubeEnd _ hs

private theorem windingLine_arg_zero : (windingLine 0).arg = -(Real.pi / 3) := by
  have hθ : -(Real.pi / 3) ∈ Set.Ioc (-Real.pi) Real.pi :=
    ⟨by linarith only [Real.pi_pos], by linarith only [Real.pi_pos]⟩
  have he : windingLine 0 = (↑(64 : ℝ) : ℂ) *
      ((Real.cos (-(Real.pi / 3)) : ℂ) + (Real.sin (-(Real.pi / 3)) : ℂ) * Complex.I) := by
    rw [windingLine_zero, Real.cos_neg, Real.sin_neg, Real.cos_pi_div_three, Real.sin_pi_div_three]
    apply Complex.ext <;>
      norm_num [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im] <;> ring
  rw [he]
  exact Complex.arg_mul_cos_add_sin_mul_I (by norm_num) hθ

private theorem windingLine_arg_one : (windingLine 1).arg = Real.pi / 3 := by
  have hθ : Real.pi / 3 ∈ Set.Ioc (-Real.pi) Real.pi :=
    ⟨by linarith only [Real.pi_pos], by linarith only [Real.pi_pos]⟩
  have he : windingLine 1 = (↑(64 : ℝ) : ℂ) *
      ((Real.cos (Real.pi / 3) : ℂ) + (Real.sin (Real.pi / 3) : ℂ) * Complex.I) := by
    rw [windingLine_one, Real.cos_pi_div_three, Real.sin_pi_div_three]
    apply Complex.ext <;>
      norm_num [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im] <;> ring
  rw [he]
  exact Complex.arg_mul_cos_add_sin_mul_I (by norm_num) hθ

/-- A continuous logarithm along the loop gains imaginary part `2π`.
This gives winding number one about zero. -/
theorem orderSixDeterminantWindingLoop_logarithm :
    ∃ L : I → ℂ, Continuous L ∧ (∀ t, Complex.exp (L t) = orderSixDeterminantWindingLoop t) ∧
      (L 1).im - (L 0).im = 2 * Real.pi := by
  let L (t : I) : ℂ := 3 * (windingLine t).log
  have hslit (t : I) : windingLine t ∈ Complex.slitPlane := by
    apply Complex.mem_slitPlane_iff.mpr
    left
    rw [windingLine_re]
    norm_num
  refine ⟨L, continuous_const.mul (windingLine_continuous.clog hslit), ?_, ?_⟩
  · intro t
    change Complex.exp ((↑(3 : ℕ) : ℂ) * (windingLine t).log) = (windingLine t) ^ 3
    rw [Complex.exp_nat_mul, Complex.exp_log (windingLine_ne_zero t)]
  · simp only [L, Complex.mul_im, Complex.re_ofNat, Complex.im_ofNat, zero_mul, add_zero,
      Complex.log_im, windingLine_arg_one, windingLine_arg_zero]
    ring

private theorem interval_logarithm_change_eq (L M : I → ℂ)
    (hL : Continuous L) (hM : Continuous M) (he : ∀ t, Complex.exp (L t) = Complex.exp (M t)) :
    (L 1).im - (L 0).im = (M 1).im - (M 0).im := by
  let l (t : I) := (L t - L 0).im
  let m (t : I) := (M t - M 0).im
  have hl : Continuous l := Complex.continuous_im.comp (hL.sub continuous_const)
  have hm : Continuous m := Complex.continuous_im.comp (hM.sub continuous_const)
  have hcomp : Circle.exp ∘ l = Circle.exp ∘ m := by
    funext t
    have hn : Complex.exp (L t - L 0) = Complex.exp (M t - M 0) := by
      rw [Complex.exp_sub, Complex.exp_sub, he t, he 0]
    obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp hn
    refine Circle.exp_eq_exp.mpr ⟨n, ?_⟩
    have hi := congrArg Complex.im hn
    simpa [l, m, Complex.mul_im, Complex.mul_re] using hi
  have heq := (T2Space.isSeparatedMap Circle.exp).eq_of_comp_eq
    isLocalHomeomorph_circleExp.isLocallyInjective hl hm hcomp (0 : I) (by simp [l, m])
  simpa only [l, m, Complex.sub_im] using congrFun heq (1 : I)

private theorem logarithm_change_zero_of_square (F : I × I → ℂ)
    (hF : Continuous F) (hn : ∀ x, F x ≠ 0)
    (hclosed : ∀ s : I, F (s, 0) = F (s, 1)) (hconstant : ∀ t : I, F (1, t) = F (1, 0))
    (L : I → ℂ) (hL : Continuous L) (hLexp : ∀ t : I, Complex.exp (L t) = F (0, t)) :
    (L 1).im - (L 0).im = 0 := by
  obtain ⟨K, hK, hKexp⟩ := exists_continuousLog_unitSquare F hF hn
  have hc₁ (s : I) : Continuous (fun t : I => K (s, t)) :=
    hK.comp (continuous_const.prodMk continuous_id)
  have hc₂ (t : I) : Continuous (fun s : I => K (s, t)) :=
    hK.comp (continuous_id.prodMk continuous_const)
  have htop := interval_logarithm_change_eq (fun t => K (1, t)) (fun _ => K (1, 0))
    (hc₁ 1) continuous_const (fun t => by rw [hKexp, hKexp, hconstant t])
  have hsides := interval_logarithm_change_eq (fun s => K (s, 0)) (fun s => K (s, 1))
    (hc₂ 0) (hc₂ 1) (fun s => by rw [hKexp, hKexp, hclosed s])
  have hbottom := interval_logarithm_change_eq (fun t => K (0, t)) L
    (hc₁ 0) hL (fun t => by rw [hKexp, hLexp])
  linarith only [htop, hsides, hbottom]

/-- The order-six determinant range has a loop that is not homotopic to
the constant path with its endpoints fixed. -/
theorem orderSix_determinantRange_nontrivial_loop :
    ∃ z : determinantRange orderSixWindingLeft orderSixWindingRight,
      ∃ p : Path z z, ¬ Path.Homotopic p (Path.refl z) := by
  let R := determinantRange orderSixWindingLeft orderSixWindingRight
  let z : R := ⟨orderSixDeterminantWindingLoop 0, orderSixDeterminantWindingLoop_mem 0⟩
  let p : Path z z :=
    { toFun := fun t => ⟨orderSixDeterminantWindingLoop t, orderSixDeterminantWindingLoop_mem t⟩
      continuous_toFun := (windingLine_continuous.pow 3).subtype_mk _
      source' := rfl
      target' := Subtype.ext (orderSixDeterminantWindingLoop_endpoints.2.trans
        orderSixDeterminantWindingLoop_endpoints.1.symm) }
  refine ⟨z, p, ?_⟩
  rintro ⟨H⟩
  let F (x : I × I) : ℂ := (H x : R).val
  have hF : Continuous F := continuous_subtype_val.comp H.continuous_toFun
  have hn (x : I × I) : F x ≠ 0 := by
    intro h
    have hmem : F x ∈ R := (H x : R).property
    rw [h] at hmem
    exact zero_notMem_orderSixDeterminantRange hmem
  have hclosed (s : I) : F (s, 0) = F (s, 1) := by
    change (H (s, 0) : R).val = (H (s, 1) : R).val
    rw [Path.Homotopy.source H s, Path.Homotopy.target H s]
  have hconstant (t : I) : F (1, t) = F (1, 0) := by
    change (H (1, t) : R).val = (H (1, 0) : R).val
    rw [H.map_one_left t, H.map_one_left 0] <;> rfl
  obtain ⟨L, hL, hLexp, hgain⟩ := orderSixDeterminantWindingLoop_logarithm
  have hstart (t : I) : Complex.exp (L t) = F (0, t) := by
    change Complex.exp (L t) = (H (0, t) : R).val
    rw [H.map_zero_left t]
    exact hLexp t
  have hzero := logarithm_change_zero_of_square F hF hn hclosed hconstant L hL hstart
  linarith only [hzero, hgain, Real.pi_pos]

/-- Simple connectedness of determinant ranges fails in order six. -/
theorem orderSix_determinantRange_not_simplyConnected :
    ¬ SimplyConnectedSpace (determinantRange orderSixWindingLeft orderSixWindingRight) := by
  intro h
  letI := h
  obtain ⟨z, p, hp⟩ := orderSix_determinantRange_nontrivial_loop
  exact hp (SimplyConnectedSpace.paths_homotopic p (Path.refl z))

end

end MOC
