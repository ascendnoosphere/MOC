import MOC.Claim
import MOC.Singular
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Matrix
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

/-! The exponential of the trace integral along a finite matrix path. -/

open Matrix Polynomial MeasureTheory Set

namespace MOC.Reformulations

noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

private def detLine {n : ℕ} (B : Matrix (Fin n) (Fin n) ℂ) : ℂ[X] :=
  (1 + (X : ℂ[X]) • B.map C).det

private theorem detLine_eval {n : ℕ} (B : Matrix (Fin n) (Fin n) ℂ) (s : ℂ) :
    (detLine B).eval s = (1 + s • B).det := by
  change Polynomial.evalRingHom s (detLine B) = _
  rw [detLine, RingHom.map_det]
  congr 1
  ext i j
  simp [Matrix.one_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul]
  split <;> simp [*, mul_comm]

private theorem hasDerivAt_det_curve {n : ℕ}
    (g : ℝ → Matrix (Fin n) (Fin n) ℂ) (H : Matrix (Fin n) (Fin n) ℂ) (t : ℝ)
    (hg : HasDerivAt g H t) (hunit : IsUnit (g t).det) :
    HasDerivAt (fun s => (g s).det) ((g t).det * (H * (g t)⁻¹).trace) t := by
  let A := g t
  let B := H * A⁻¹
  let d := fderiv ℝ (fun M : Matrix (Fin n) (Fin n) ℂ => M.det) A
  have hD : DifferentiableAt ℝ (fun M : Matrix (Fin n) (Fin n) ℂ => M.det) A := by
    simp only [Matrix.det_apply']
    apply DifferentiableAt.sum
    intro σ _
    apply (differentiableAt_const _).mul
    have hi (i : Fin n) : DifferentiableAt ℝ
        (fun M : Matrix (Fin n) (Fin n) ℂ => M (σ i) i) A := by
      let L : Matrix (Fin n) (Fin n) ℂ →L[ℝ] ℂ :=
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℂ) i).comp
          (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => Fin n → ℂ) (σ i))
      exact L.differentiableAt
    exact (HasFDerivAt.finset_prod (fun i _ => (hi i).hasFDerivAt)
      (u := Finset.univ)).differentiableAt
  have ha : HasFDerivAt (fun M : Matrix (Fin n) (Fin n) ℂ => M.det) d A := by simpa only [d] using hD.hasFDerivAt
  have hlin : HasDerivAt (fun s : ℝ => A + s • H) H 0 := by
    simpa using (hasDerivAt_const (0 : ℝ) A).add ((hasDerivAt_id (0 : ℝ)).smul_const H)
  have hd : HasDerivAt (fun s : ℝ => (A + s • H).det) (d H) 0 := by
    exact (show HasFDerivAt (fun M : Matrix (Fin n) (Fin n) ℂ => M.det) d
      (A + (0 : ℝ) • H) by simpa using ha).comp_hasDerivAt (0 : ℝ) hlin
  let p := detLine B
  have hp : HasDerivAt (fun s : ℝ => p.eval (s : ℂ) * A.det) (B.trace * A.det) 0 := by
    simpa only [Complex.ofReal_zero, p, detLine, derivative_det_one_add_X_smul] using
      ((p.hasDerivAt ((0 : ℝ) : ℂ)).comp_ofReal (z := (0 : ℝ))).mul_const A.det
  have hcurve (s : ℝ) : (A + s • H).det = p.eval (s : ℂ) * A.det := by
    have hmat : (1 + s • B) * A = A + s • H := by
      rw [Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul, show B * A = H by
        simp only [B, Matrix.mul_assoc, nonsing_inv_mul A hunit, Matrix.mul_one]]
    rw [← hmat, Matrix.det_mul, show p.eval (s : ℂ) = (1 + s • B).det by
      simpa only [p, Complex.real_smul] using detLine_eval B (s : ℂ)]
  have heq := hd.unique (by simpa only [hcurve] using hp : HasDerivAt
    (fun s : ℝ => (A + s • H).det) (B.trace * A.det) 0)
  simpa only [Function.comp_apply, heq, mul_comm B.trace, A, B] using ha.comp_hasDerivAt t hg

/-- On a smooth segment, exponentiating the logarithmic determinant integral
gives the ratio of the endpoint determinants. The integrand may be given by
its continuous extension at the segment endpoints. -/
theorem det_eq_exp_mul_of_segment {n : ℕ} {a b : ℝ} (hab : a ≤ b)
    (g H : ℝ → Matrix (Fin n) (Fin n) ℂ)
    (hg : ContinuousOn g (Icc a b))
    (hd : ∀ t ∈ Ioo a b, HasDerivAt g (H t) t)
    (hu : ∀ t ∈ Icc a b, IsUnit (g t).det)
    (f : ℝ → ℂ) (hf : ContinuousOn f (Icc a b))
    (hlog : ∀ t ∈ Ioo a b, f t = (H t * (g t)⁻¹).trace) :
    (g b).det = Complex.exp (∫ t in a..b, f t) * (g a).det := by
  let F (t : ℝ) := ∫ s in a..t, f s
  let P (t : ℝ) := Complex.exp (-F t) * (g t).det
  have hi : IntervalIntegrable f volume a b := (by simpa only [uIcc_of_le hab] using hf :
    ContinuousOn f (uIcc a b)).intervalIntegrable
  have hFc : ContinuousOn F (Icc a b) := by
    simpa only [uIcc_of_le hab] using
      intervalIntegral.continuousOn_primitive_interval (intervalIntegrable_iff'.mp hi)
  have hdet : ContinuousOn (fun t => (g t).det) (Icc a b) := by fun_prop
  have hPc : ContinuousOn P (Icc a b) :=
    (Complex.continuous_exp.comp_continuousOn hFc.neg).mul hdet
  have hPd (t : ℝ) (ht : t ∈ Ioo a b) : HasDerivAt P (0 : ℂ) t := by
    have hnt := isOpen_Ioo.mem_nhds ht
    have hfc := (hf.mono Ioo_subset_Icc_self).continuousAt hnt
    have hmeas := (hf.mono Ioo_subset_Icc_self).stronglyMeasurableAtFilter (μ := volume) isOpen_Ioo t ht
    have hit : IntervalIntegrable f volume a t := hi.mono_set (by
      rw [uIcc_of_le ht.1.le, uIcc_of_le hab]
      exact Icc_subset_Icc_right ht.2.le)
    have hFt : HasDerivAt F (f t) t := intervalIntegral.integral_hasDerivAt_right hit hmeas hfc
    have hdt := hasDerivAt_det_curve g (H t) t (hd t ht) (hu t (Ioo_subset_Icc_self ht))
    rw [← hlog t ht] at hdt
    convert hFt.neg.cexp.mul hdt using 1
    ring
  have hend : P b - P a = 0 := by
    simpa using (intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hPc hPd
      (continuous_const.intervalIntegrable a b)).symm
  have he : (Complex.exp (F b))⁻¹ * (g b).det = (g a).det := by
    simpa [P, F, Complex.exp_neg] using sub_eq_zero.mp hend
  have hmul := congrArg (fun z => Complex.exp (F b) * z) he
  change Complex.exp (F b) * ((Complex.exp (F b))⁻¹ * (g b).det) = _ at hmul
  rwa [← mul_assoc, mul_inv_cancel₀ (Complex.exp_ne_zero _), one_mul] at hmul

/-- The logarithmic integral of an invertible path with a finite smooth
partition. At breakpoints the segment integrands can have different limiting
values, which do not change any of the integrals. -/
inductive DetPathIntegral {n : ℕ} (g : ℝ → Matrix (Fin n) (Fin n) ℂ) :
    ℝ → ℝ → ℂ → Prop
  | segment {a b : ℝ} (hab : a ≤ b)
      (H : ℝ → Matrix (Fin n) (Fin n) ℂ) (f : ℝ → ℂ)
      (hg : ContinuousOn g (Icc a b))
      (hd : ∀ t ∈ Ioo a b, HasDerivAt g (H t) t)
      (hu : ∀ t ∈ Icc a b, IsUnit (g t).det)
      (hf : ContinuousOn f (Icc a b))
      (hlog : ∀ t ∈ Ioo a b, f t = (H t * (g t)⁻¹).trace) :
      DetPathIntegral g a b (∫ t in a..b, f t)
  | join {a b c : ℝ} {x y : ℂ}
      (hx : DetPathIntegral g a b x) (hy : DetPathIntegral g b c y) :
      DetPathIntegral g a c (x + y)

/-- Jacobi's determinant path identity on an arbitrary finite partition. -/
theorem DetPathIntegral.det_eq_exp_mul {n : ℕ}
    {g : ℝ → Matrix (Fin n) (Fin n) ℂ} {a b : ℝ} {z : ℂ}
    (h : DetPathIntegral g a b z) :
    (g b).det = Complex.exp z * (g a).det := by
  induction h with
  | segment hab H f hg hd hu hf hlog =>
    exact det_eq_exp_mul_of_segment hab g H hg hd hu f hf hlog
  | join _ _ hx hy =>
    rw [hy, hx, Complex.exp_add, mul_left_comm, mul_assoc]

/-- The exponent of the path expression uses the ordinary
trace; normalizing the trace by n and multiplying the integral by n
cancels the normalization in positive dimension. -/
def DeterminantPathForm : Prop :=
  ∀ (n : ℕ) (a b : Fin n → ℂ) (U : Matrix (Fin n) (Fin n) ℂ), IsUnitary U →
    ∀ (g : ℝ → Matrix (Fin n) (Fin n) ℂ) (z : ℂ),
      g 0 = 1 → g 1 = diagonal a + U * diagonal b * Uᴴ → DetPathIntegral g 0 1 z →
      Complex.exp z ∈ convexHull ℝ (Set.range (matchingProduct a b))

theorem determinantPathForm_of_moc (h : MOCIsTrue) : DeterminantPathForm := by
  intro n a b U hU g z h₀ h₁ hz
  have he := hz.det_eq_exp_mul
  rw [h₀, h₁, Matrix.det_one, mul_one] at he
  rw [← he]
  exact h n a b U hU

/-- The quadratic scalar path from 0 to 1 can avoid the finitely many roots
of the determinant along the complex line. This constructs a smooth path
to any invertible matrix, without a matrix logarithm. -/
private theorem exists_det_path {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : IsUnit A.det) :
    ∃ (g : ℝ → Matrix (Fin n) (Fin n) ℂ) (z : ℂ),
      g 0 = 1 ∧ g 1 = A ∧ DetPathIntegral g 0 1 z := by
  classical
  let B := A - 1
  let P := detLine B
  have hP₀ : P.eval 0 = 1 := by simp [P, detLine_eval]
  have hP₁ : P.eval 1 = A.det := by
    rw [show P.eval 1 = (1 + (1 : ℂ) • B).det from detLine_eval _ _, one_smul]
    simp [B]
  have hP : P ≠ 0 := by intro h; simp [h] at hP₀
  let slope (w : ℂ) : ℝ := w.im / (w.re * (1 - w.re))
  obtain ⟨r, hr⟩ := (P.roots.toFinset.image slope).exists_not_mem
  let q : ℂ[X] := X + C ((r : ℂ) * Complex.I) * X * (1 - X)
  let z : ℝ → ℂ := fun t => q.eval (t : ℂ)
  have hz (t : ℝ) : z t = (t : ℂ) + (r : ℂ) * Complex.I * t * (1 - t) := by simp [z, q]
  have hz₀ : z 0 = 0 := by simp [hz]
  have hz₁ : z 1 = 1 := by simp [hz]
  let g : ℝ → Matrix (Fin n) (Fin n) ℂ := fun t => 1 + z t • B
  have hg₀ : g 0 = 1 := by simp [g, hz₀]
  have hg₁ : g 1 = A := by simp [g, B, hz₁]
  have hunit (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : IsUnit (g t).det := by
    rw [isUnit_iff_ne_zero, show (g t).det = P.eval (z t) from (detLine_eval B (z t)).symm]
    intro h
    by_cases h₀ : t = 0
    · subst t
      simp [hz₀, hP₀] at h
    by_cases h₁ : t = 1
    · subst t
      exact (isUnit_iff_ne_zero.mp hA) (by simpa [hz₁, hP₁] using h)
    have hre : (z t).re = t := by
      rw [hz]
      simp [Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im]
    have him : (z t).im = r * (t * (1 - t)) := by
      rw [hz]
      simp [Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
        mul_assoc]
    have hden : t * (1 - t) ≠ 0 := mul_ne_zero h₀ (sub_ne_zero.mpr (Ne.symm h₁))
    have hs : slope (z t) = r := by
      dsimp [slope]
      rw [him, hre, mul_div_cancel_right₀ _ hden]
    apply hr
    exact Finset.mem_image.mpr ⟨z t, Multiset.mem_toFinset.mpr ((mem_roots hP).mpr h), hs⟩
  let L : ℂ →L[ℝ] Matrix (Fin n) (Fin n) ℂ :=
    (ContinuousLinearMap.toSpanSingleton ℂ B).restrictScalars ℝ
  let H : ℝ → Matrix (Fin n) (Fin n) ℂ := fun t => L (q.derivative.eval (t : ℂ))
  have hg (t : ℝ) : HasDerivAt g (H t) t := by
    have hq : HasDerivAt z (q.derivative.eval (t : ℂ)) t := (q.hasDerivAt (t : ℂ)).comp_ofReal
    exact (hasDerivAt_const t (1 : Matrix (Fin n) (Fin n) ℂ)).add
      (L.hasFDerivAt.comp_hasDerivAt t hq) |>.congr_deriv (by simp [H])
  have hgc : Continuous g := continuous_iff_continuousAt.mpr fun t => (hg t).continuousAt
  have hHc : Continuous H := L.continuous.comp
    (continuous_iff_continuousAt.mpr fun t =>
      ((q.derivative.hasDerivAt (t : ℂ)).comp_ofReal (z := t)).continuousAt)
  let f (t : ℝ) : ℂ := (H t * (g t)⁻¹).trace
  have hInv : ContinuousOn (fun t => (g t)⁻¹) (Icc (0 : ℝ) 1) := by
    intro t ht
    apply ContinuousAt.continuousWithinAt
    apply (continuousAt_matrix_inv (g t) _).comp hgc.continuousAt
    rw [Ring.inverse_eq_inv']
    exact continuousAt_inv₀ (isUnit_iff_ne_zero.mp (hunit t ht))
  have hfc : ContinuousOn f (Icc (0 : ℝ) 1) := by
    unfold f Matrix.trace
    fun_prop
  exact ⟨g, ∫ t in (0 : ℝ)..1, f t, hg₀, hg₁, .segment zero_le_one H f
    hgc.continuousOn (fun t _ => hg t) hunit hfc (fun _ _ => rfl)⟩

/-- Equivalence for the matrix path determinant comparison. The singular endpoint
case already satisfies MOC by the independent singular-sum theorem. -/
theorem determinantPathForm_iff : DeterminantPathForm ↔ MOCIsTrue := by
  refine ⟨?_, determinantPathForm_of_moc⟩
  intro h n a b U hU
  by_cases ht : determinantValue a b U = 0
  · exact holds_of_singular a b hU ht
  obtain ⟨g, z, h₀, h₁, hz⟩ :=
    exists_det_path (diagonal a + U * diagonal b * Uᴴ) (isUnit_iff_ne_zero.mpr ht)
  have he := hz.det_eq_exp_mul
  rw [h₀, h₁, Matrix.det_one, mul_one] at he
  unfold Holds determinantValue
  rw [he]
  exact h n a b U hU g z h₀ h₁ hz

end
end MOC.Reformulations
