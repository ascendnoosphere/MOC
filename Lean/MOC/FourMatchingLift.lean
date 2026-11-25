import MOC.FourMatchingHessian
import Mathlib.Data.Real.Sqrt
import Mathlib.Topology.Order.IntermediateValue

/-! The imaginary coordinates give a rank-one moment lift in a
two-generator kernel of the real matching Hessian. -/

namespace MOC

/-- Real and imaginary parts of a critical matching profile have the same
matching gradient. -/
theorem fourMatchingGradient_real_eq_imaginary (m : Fin 14 → ℂ)
    (hm : ∀ i, fourMatchingGradient m i = 0) (i : Fin 14) :
    fourMatchingGradient (fun j => (m j).re) i =
      fourMatchingGradient (fun j => (m j).im) i := by
  have he := congrArg Complex.re (hm i)
  fin_cases i <;>
    simp [fourMatchingGradient, Complex.mul_re, Complex.sub_re, Complex.add_re,
      Complex.neg_re] at he ⊢ <;>
    linear_combination he

private theorem fourMatchingGradient_two_directions (x y : Fin 14 → ℝ) (s t : ℝ)
    (i : Fin 14) :
    fourMatchingGradient (fun j => s * x j + t * y j) i =
      s ^ 2 * fourMatchingGradient x i +
      (s * t) * (fourMatchingGradient (fun j => x j + y j) i -
        fourMatchingGradient x i - fourMatchingGradient y i) +
      t ^ 2 * fourMatchingGradient y i := by
  fin_cases i <;> simp [fourMatchingGradient] <;> ring

private theorem fourMatchingGradient_complex_re (f g : Fin 14 → ℝ) (i : Fin 14) :
    (fourMatchingGradient (fun j => (⟨f j, g j⟩ : ℂ)) i).re =
      fourMatchingGradient f i - fourMatchingGradient g i := by
  fin_cases i <;>
    simp [fourMatchingGradient, Complex.mul_re, Complex.sub_re, Complex.add_re,
      Complex.neg_re] <;> ring

/-- The two real lift equations exactly recover the complex matching gradient. -/
theorem fourMatchingGradient_lift_iff (f g : Fin 14 → ℝ) :
    (∀ i, fourMatchingGradient (fun j => (⟨f j, g j⟩ : ℂ)) i = 0) ↔
      (fourMatchingHessian f).mulVec g = 0 ∧ fourMatchingGradient f = fourMatchingGradient g := by
  have him (i : Fin 14) :
      (fourMatchingHessian f).mulVec g i =
        (fourMatchingGradient (fun j => (⟨f j, g j⟩ : ℂ)) i).im :=
    fourMatchingHessian_mulVec_im (fun j => ⟨f j, g j⟩) i
  constructor
  · intro h
    refine ⟨funext fun i => ?_, funext fun i => ?_⟩
    · change (fourMatchingHessian f).mulVec g i = 0
      rw [him, h, Complex.zero_im]
    · exact sub_eq_zero.mp ((fourMatchingGradient_complex_re f g i).symm.trans
        (congrArg Complex.re (h i)))
  · rintro ⟨hk, hg⟩ i
    apply Complex.ext
    · rw [fourMatchingGradient_complex_re, hg, sub_self, Complex.zero_re]
    · have hki : (fourMatchingHessian f).mulVec g i = 0 := congrFun hk i
      rw [← him, hki, Complex.zero_im]

/-- When two directions span the Hessian kernel, the gradient of an actual
real profile is a binary moment vector. The two-by-two moment matrix is
positive semidefinite with determinant zero. -/
theorem fourMatchingGradient_has_binary_moment_lift (m : Fin 14 → ℂ)
    (hm : ∀ i, fourMatchingGradient m i = 0) (x y : Fin 14 → ℝ)
    (hspan : ∀ v : Fin 14 → ℝ,
      (fourMatchingHessian (fun j => (m j).re)).mulVec v = 0 →
      ∃ s t : ℝ, v = fun j => s * x j + t * y j) :
    ∃ a b c : ℝ, 0 ≤ a ∧ 0 ≤ c ∧ b ^ 2 = a * c ∧
      ∀ i, fourMatchingGradient (fun j => (m j).re) i =
        a * fourMatchingGradient x i +
        b * (fourMatchingGradient (fun j => x j + y j) i -
          fourMatchingGradient x i - fourMatchingGradient y i) +
        c * fourMatchingGradient y i := by
  let v (j : Fin 14) := (m j).im
  have hker : (fourMatchingHessian (fun j => (m j).re)).mulVec v = 0 := by
    funext i
    change (fourMatchingHessian (fun j => (m j).re)).mulVec (fun j => (m j).im) i = 0
    rw [fourMatchingHessian_mulVec_im, hm, Complex.zero_im]
  obtain ⟨s, t, hst⟩ := hspan v hker
  refine ⟨s ^ 2, s * t, t ^ 2, sq_nonneg s, sq_nonneg t, by ring, fun i => ?_⟩
  calc
    _ = fourMatchingGradient v i := fourMatchingGradient_real_eq_imaginary m hm i
    _ = _ := by
      rw [hst]
      exact fourMatchingGradient_two_directions x y s t i

private theorem binary_line_diagonal_endpoint (a c u w : ℝ)
    (ha : 0 ≤ a) (hc : 0 ≤ c) (hu : u ≠ 0) :
    ∃ T : ℝ, 0 ≤ a + T * u ∧ 0 ≤ c + T * w ∧ (a + T * u) * (c + T * w) = 0 := by
  let T := -a / u
  have hA : a + T * u = 0 := by
    dsimp only [T]
    rw [div_mul_cancel₀ _ hu, add_neg_cancel]
  by_cases hC : 0 ≤ c + T * w
  · exact ⟨T, hA.ge, hC, by rw [hA, zero_mul]⟩
  have hz : c + T * w < 0 := lt_of_not_ge hC
  let d := c - (c + T * w)
  have hd : 0 < d := sub_pos.mpr (hz.trans_le hc)
  let s := c / d
  have hs : s ≤ 1 := (div_le_one hd).mpr (by dsimp only [d]; linarith)
  have hsd : s * d = c := div_mul_cancel₀ c hd.ne'
  have hC' : c + (s * T) * w = 0 := by
    dsimp only [d] at hsd
    linear_combination -hsd
  have hA' : a + (s * T) * u = (1 - s) * a := by
    linear_combination s * hA
  exact ⟨s * T, by rw [hA']; exact mul_nonneg (sub_nonneg.mpr hs) ha,
    hC'.ge, by rw [hC', mul_zero]⟩

/-- A nonconstant line through a positive semidefinite binary moment matrix
contains a positive semidefinite matrix of determinant zero. In particular,
when the moment equations admit a nonzero null direction, their semidefinite
relaxation can be made rank one or zero. -/
theorem binary_psd_line_hits_singular (a b c u v w : ℝ)
    (ha : 0 ≤ a) (hc : 0 ≤ c) (habc : b ^ 2 ≤ a * c)
    (hne : u ≠ 0 ∨ v ≠ 0 ∨ w ≠ 0) :
    ∃ t : ℝ, 0 ≤ a + t * u ∧ 0 ≤ c + t * w ∧
      (b + t * v) ^ 2 = (a + t * u) * (c + t * w) := by
  by_cases hdiag : u ≠ 0 ∨ w ≠ 0
  · have hEnd : ∃ T : ℝ, 0 ≤ a + T * u ∧ 0 ≤ c + T * w ∧ (a + T * u) * (c + T * w) = 0 := by
      rcases hdiag with hu | hw
      · exact binary_line_diagonal_endpoint a c u w ha hc hu
      · obtain ⟨T, hC, hA, hprod⟩ := binary_line_diagonal_endpoint c a w u hc ha hw
        exact ⟨T, hA, hC, by rw [mul_comm]; exact hprod⟩
    obtain ⟨T, hA, hC, hProd⟩ := hEnd
    let f (s : ℝ) := (a + (s * T) * u) * (c + (s * T) * w) - (b + (s * T) * v) ^ 2
    have hcont : Continuous f := by dsimp only [f]; fun_prop
    have hf0 : 0 ≤ f 0 := by simpa [f] using sub_nonneg.mpr habc
    have hf1 : f 1 ≤ 0 := by
      simpa only [f, one_mul, hProd, zero_sub] using neg_nonpos.mpr (sq_nonneg (b + T * v))
    obtain ⟨s, hs, hF⟩ := intermediate_value_Icc' (by norm_num : (0 : ℝ) ≤ 1)
      hcont.continuousOn (show (0 : ℝ) ∈ Set.Icc (f 1) (f 0) from ⟨hf1, hf0⟩)
    refine ⟨s * T, ?_, ?_, (sub_eq_zero.mp hF).symm⟩
    · rw [show a + (s * T) * u = (1 - s) * a + s * (a + T * u) by ring]
      exact add_nonneg (mul_nonneg (sub_nonneg.mpr hs.2) ha) (mul_nonneg hs.1 hA)
    · rw [show c + (s * T) * w = (1 - s) * c + s * (c + T * w) by ring]
      exact add_nonneg (mul_nonneg (sub_nonneg.mpr hs.2) hc) (mul_nonneg hs.1 hC)
  · have hu : u = 0 := not_not.mp (fun h => hdiag (Or.inl h))
    have hw : w = 0 := not_not.mp (fun h => hdiag (Or.inr h))
    have hv : v ≠ 0 := (hne.resolve_left (fun h => h hu)).resolve_right (fun h => h hw)
    let t := (Real.sqrt (a * c) - b) / v
    have hb : b + t * v = Real.sqrt (a * c) := by
      dsimp only [t]
      rw [div_mul_cancel₀ _ hv]
      ring
    exact ⟨t, by simpa only [hu, mul_zero, add_zero] using ha,
      by simpa only [hw, mul_zero, add_zero] using hc,
      by simpa only [hu, hw, hb, mul_zero, add_zero] using Real.sq_sqrt (mul_nonneg ha hc)⟩

/-- A nonzero linear relation between the three binary evaluation vectors
lets a semidefinite lift retain its evaluation with zero determinant. -/
theorem binary_psd_evaluation_has_singular_lift (g₀ g₁ g₂ : Fin 14 → ℝ)
    (a b c u v w : ℝ) (ha : 0 ≤ a) (hc : 0 ≤ c) (habc : b ^ 2 ≤ a * c)
    (hne : u ≠ 0 ∨ v ≠ 0 ∨ w ≠ 0)
    (hnull : ∀ i, u * g₀ i + v * g₁ i + w * g₂ i = 0) :
    ∃ a' b' c' : ℝ, 0 ≤ a' ∧ 0 ≤ c' ∧ b' ^ 2 = a' * c' ∧
      ∀ i, a' * g₀ i + b' * g₁ i + c' * g₂ i = a * g₀ i + b * g₁ i + c * g₂ i := by
  obtain ⟨t, htA, htC, htdet⟩ := binary_psd_line_hits_singular a b c u v w ha hc habc hne
  refine ⟨a + t * u, b + t * v, c + t * w, htA, htC, htdet, fun i => ?_⟩
  linear_combination t * hnull i

private theorem binary_psd_singular_factors (a b c : ℝ)
    (ha : 0 ≤ a) (hc : 0 ≤ c) (hdet : b ^ 2 = a * c) :
    ∃ s t : ℝ, s ^ 2 = a ∧ s * t = b ∧ t ^ 2 = c := by
  rcases ha.eq_or_lt with (rfl | ha')
  · have hb : b = 0 := sq_eq_zero_iff.mp (by simpa only [zero_mul] using hdet)
    exact ⟨0, Real.sqrt c, by simp, by simp [hb], Real.sq_sqrt hc⟩
  · let s := Real.sqrt a
    have hs : s ≠ 0 := (Real.sqrt_pos.2 ha').ne'
    have hsa : s ^ 2 = a := Real.sq_sqrt ha
    refine ⟨s, b / s, hsa, mul_div_cancel₀ _ hs, ?_⟩
    rw [div_pow, hdet, hsa, mul_div_cancel_left₀ _ ha'.ne']

/-- On a two-generator Hessian kernel with linearly dependent binary
evaluation vectors, existence of a complex-critical lift is equivalent to
feasibility of the two-by-two positive semidefinite moment constraints. -/
theorem fourMatchingGradient_binary_psd_iff (f x y : Fin 14 → ℝ)
    (hx : (fourMatchingHessian f).mulVec x = 0)
    (hy : (fourMatchingHessian f).mulVec y = 0)
    (hspan : ∀ g : Fin 14 → ℝ, (fourMatchingHessian f).mulVec g = 0 →
      ∃ s t : ℝ, g = fun j => s * x j + t * y j)
    (u v w : ℝ) (hne : u ≠ 0 ∨ v ≠ 0 ∨ w ≠ 0)
    (hnull : ∀ i, u * fourMatchingGradient x i +
      v * (fourMatchingGradient (fun j => x j + y j) i -
        fourMatchingGradient x i - fourMatchingGradient y i) +
      w * fourMatchingGradient y i = 0) :
    (∃ g : Fin 14 → ℝ, ∀ i, fourMatchingGradient (fun j => (⟨f j, g j⟩ : ℂ)) i = 0) ↔
    ∃ a b c : ℝ, 0 ≤ a ∧ 0 ≤ c ∧ b ^ 2 ≤ a * c ∧
      ∀ i, fourMatchingGradient f i =
        a * fourMatchingGradient x i +
        b * (fourMatchingGradient (fun j => x j + y j) i -
          fourMatchingGradient x i - fourMatchingGradient y i) +
        c * fourMatchingGradient y i := by
  constructor
  · rintro ⟨g, hg⟩
    obtain ⟨hk, hG⟩ := (fourMatchingGradient_lift_iff f g).mp hg
    obtain ⟨s, t, rfl⟩ := hspan g hk
    refine ⟨s ^ 2, s * t, t ^ 2, sq_nonneg s, sq_nonneg t,
      le_of_eq (mul_pow s t 2), fun i => ?_⟩
    rw [hG, fourMatchingGradient_two_directions]
  · rintro ⟨a, b, c, ha, hc, hdet, h⟩
    let g₀ := fourMatchingGradient x
    let g₁ (i : Fin 14) := fourMatchingGradient (fun j => x j + y j) i -
      fourMatchingGradient x i - fourMatchingGradient y i
    let g₂ := fourMatchingGradient y
    obtain ⟨a', b', c', ha', hc', hdet', h'⟩ :=
      binary_psd_evaluation_has_singular_lift g₀ g₁ g₂ a b c u v w ha hc hdet hne hnull
    obtain ⟨s, t, hs, hst, ht⟩ := binary_psd_singular_factors a' b' c' ha' hc' hdet'
    let g (j : Fin 14) := s * x j + t * y j
    refine ⟨g, (fourMatchingGradient_lift_iff f g).mpr ⟨?_, ?_⟩⟩
    · have hmul :
          (fourMatchingHessian f).mulVec g =
            s • ((fourMatchingHessian f).mulVec x) + t • ((fourMatchingHessian f).mulVec y) := by
        change (fourMatchingHessian f).mulVec (s • x + t • y) = _
        simp only [Matrix.mulVec_add, Matrix.mulVec_smul]
      rw [hmul, hx, hy, smul_zero, smul_zero, add_zero]
    · funext i
      change fourMatchingGradient f i = fourMatchingGradient (fun j => s * x j + t * y j) i
      rw [fourMatchingGradient_two_directions, hs, hst, ht]
      exact (h i).trans (h' i).symm

private def realSecantExample : Fin 14 → ℝ :=
  ![3, 1, 0, 0, -4, -3, -1, -3, -1, 0, 0, 0, 0, 4]

set_option maxHeartbeats 1000000 in
private theorem realSecantExample_kernel_squares (v : Fin 14 → ℝ)
    (hv : (fourMatchingHessian realSecantExample).mulVec v = 0) :
    fourMatchingGradient v 9 = -((v 0) ^ 2) - 4 * (v 8) ^ 2 := by
  have hrow (i : Fin 14) :
      fourMatchingGradient (fun j => realSecantExample j + v j) i -
        fourMatchingGradient realSecantExample i - fourMatchingGradient v i = 0 := by
    rw [← fourMatchingHessian_mulVec_apply]
    exact congrFun hv i
  have h₁ := hrow 1
  have h₂ := hrow 2
  have h₃ := hrow 3
  have h₄ := hrow 4
  have h₅ := hrow 5
  have h₆ := hrow 6
  have h₈ := hrow 8
  have h₉ := hrow 9
  have h₁₀ := hrow 10
  have h₁₂ := hrow 12
  norm_num [fourMatchingGradient, realSecantExample] at h₁ h₂ h₃ h₄ h₅ h₆ h₈ h₉ h₁₀ h₁₂
  ring_nf at h₁ h₂ h₃ h₄ h₅ h₆ h₈ h₉ h₁₀ h₁₂
  have h9 : v 9 = 0 := by linarith only [h₈]
  have h11 : v 11 = 0 := by linarith only [h₄, h9]
  have h10 : v 10 = 0 := by linarith only [h₂, h₃, h9, h11]
  have h12 : v 12 = 0 := by linarith only [h₂, h9, h11, h10]
  have h3 : v 3 = 0 := by linarith only [h₁₀, h₁₂]
  have h5 : v 5 = -v 0 := by linarith only [h₁, h₆, h10, h12]
  have h27 : v 2 = v 0 - v 7 := by linarith only [h₅, h₆, h₁₀, h3, h9]
  have h4 : v 4 = -4 * v 8 := by linarith only [h₉, h3, h5, h27, h9, h10, h11, h12]
  norm_num [fourMatchingGradient, h3, h4, h5, h27, h9, h10, h11, h12] <;> ring

/-- A sum of two real matching profiles with zero gradient can fail the
real-lift equations. The gradient at index 9 of any proposed imaginary
vector would have to equal both thirteen and a negative sum of squares. -/
theorem exists_real_matching_secant_without_complex_lift :
    ∃ p q : Fin 14 → ℝ, (∀ i, fourMatchingGradient p i = 0) ∧
      (∀ i, fourMatchingGradient q i = 0) ∧
      ¬ ∃ v : Fin 14 → ℝ,
        ∀ i, fourMatchingGradient (fun j => (⟨p j + q j, v j⟩ : ℂ)) i = 0 := by
  let p : Fin 14 → ℝ := ![0, 0, 0, 0, 0, 0, 0, -3, -1, 0, 0, 0, 0, 4]
  let q : Fin 14 → ℝ := ![3, 1, 0, 0, -4, -3, -1, 0, 0, 0, 0, 0, 0, 0]
  refine ⟨p, q, ?_, ?_, ?_⟩
  · intro i
    fin_cases i <;> norm_num [fourMatchingGradient, p]
  · intro i
    fin_cases i <;> norm_num [fourMatchingGradient, q]
  · have hsum : (fun j => p j + q j) = realSecantExample := by
      funext i
      fin_cases i <;> norm_num [p, q, realSecantExample]
    rintro ⟨v, hv⟩
    have hv' : ∀ i, fourMatchingGradient
        (fun j => (⟨realSecantExample j, v j⟩ : ℂ)) i = 0 := by
      simpa only [← hsum] using hv
    obtain ⟨hk, hG⟩ := (fourMatchingGradient_lift_iff realSecantExample v).mp hv'
    have he : fourMatchingGradient realSecantExample 9 = 13 := by
      norm_num [fourMatchingGradient, realSecantExample]
    rw [hG, realSecantExample_kernel_squares v hk] at he
    nlinarith [sq_nonneg (v 0), sq_nonneg (v 8)]

end MOC
