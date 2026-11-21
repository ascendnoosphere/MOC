import MOC.Collinear
import Mathlib.Tactic.Linarith

/-! Common inversion at tangency takes two signed spectral circles to parallel
lines. Circle-preserving perturbations handle eigenvalues at the inversion pole. -/

open scoped ComplexConjugate Topology

namespace MOC

noncomputable section

private theorem re_mul_inv_of_circle (u z : ℂ) (hz : z ≠ 0)
    (h : Complex.normSq (z - u) = Complex.normSq u) :
    (u * z⁻¹).re = 1 / 2 := by
  rw [Complex.normSq_sub] at h
  have hswap : (u * conj z).re = (z * conj u).re := by
    simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
    ring
  have hre : (z * conj u).re = Complex.normSq z / 2 := by linarith
  have hn : Complex.normSq z ≠ 0 := mt Complex.normSq_eq_zero.mp hz
  rw [Complex.inv_def, ← mul_assoc, Complex.re_mul_ofReal, hswap, hre]
  field_simp [hn]
  exact mul_comm _ _

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem holds_of_constant_real_parts (a b : ι → ℂ) (u : ℂ) (hu : u ≠ 0)
    (s t : ℝ) (ha : ∀ i, (u * a i).re = s) (hb : ∀ i, (u * b i).re = t)
    (U : Matrix ι ι ℂ) (hU : IsUnitary U) : Holds a b U := by
  have hline (z : ℂ) (r : ℝ) (hr : (u * z).re = r) :
      u⁻¹ * Complex.I * ((u * z).im : ℂ) + u⁻¹ * (r : ℂ) = z := by
    calc
      _ = u⁻¹ * ((r : ℂ) + (u * z).im * Complex.I) := by ring
      _ = _ := by
        rw [← hr, Complex.re_add_im, ← mul_assoc, inv_mul_cancel₀ hu, one_mul]
  have hleft : (fun i => u⁻¹ * Complex.I * ((u * a i).im : ℂ) + u⁻¹ * (s : ℂ)) = a :=
    funext fun i => hline (a i) s (ha i)
  have hright : (fun i => u⁻¹ * Complex.I * ((u * b i).im : ℂ) + u⁻¹ * (t : ℂ)) = b :=
    funext fun i => hline (b i) t (hb i)
  simpa only [hleft, hright] using
    holds_of_parallel_affine_lines (fun i => (u * a i).im) (fun i => (u * b i).im)
      (u⁻¹ * Complex.I) (u⁻¹ * (s : ℂ)) (u⁻¹ * (t : ℂ)) U hU

private theorem holds_of_tangent_circles_at_zero_of_nonzero (a c : ι → ℂ)
    (u : ℂ) (r : ℝ) (hu : u ≠ 0) (hr : r ≠ 0)
    (ha : ∀ i, Complex.normSq (a i - u) = Complex.normSq u)
    (hc : ∀ i, Complex.normSq (c i - (r : ℂ) * u) = Complex.normSq ((r : ℂ) * u))
    (han : ∀ i, a i ≠ 0) (hcn : ∀ i, c i ≠ 0)
    (U : Matrix ι ι ℂ) (hU : IsUnitary U) : Holds a (fun i => -c i) U := by
  apply (holds_inv_iff a c U hU han hcn).mp
  apply holds_of_constant_real_parts _ _ u hu (1 / 2) (-(1 / 2) / r) _ _ U hU
  · exact fun i => re_mul_inv_of_circle u (a i) (han i) (ha i)
  · intro i
    have h := re_mul_inv_of_circle ((r : ℂ) * u) (c i) (hcn i) (hc i)
    rw [mul_assoc, Complex.re_ofReal_mul] at h
    rw [mul_neg, Complex.neg_re]
    apply (eq_div_iff hr).mpr
    rw [neg_mul, mul_comm _ r, h]

private def circleRotation (t : ℝ) : ℂ :=
  (1 + (t : ℂ) * Complex.I) / (1 - (t : ℂ) * Complex.I)

private theorem circleRotation_denominator_ne (t : ℝ) :
    1 - (t : ℂ) * Complex.I ≠ 0 := by
  intro h
  simpa [Complex.mul_re] using congrArg Complex.re h

private theorem continuous_circleRotation : Continuous circleRotation := by
  unfold circleRotation
  have h : Continuous (fun t : ℝ => (t : ℂ) * Complex.I) :=
    Complex.continuous_ofReal.mul continuous_const
  exact (continuous_const.add h).div (continuous_const.sub h) circleRotation_denominator_ne

private theorem circleRotation_normSq (t : ℝ) : Complex.normSq (circleRotation t) = 1 := by
  have h : Complex.normSq (1 + (t : ℂ) * Complex.I) =
      Complex.normSq (1 - (t : ℂ) * Complex.I) := by
    simp [Complex.normSq, Complex.mul_re, Complex.mul_im]
  rw [circleRotation, Complex.normSq_div, h]
  exact div_self (mt Complex.normSq_eq_zero.mp (circleRotation_denominator_ne t))

private theorem circleRotation_ne_one {t : ℝ} (ht : t ≠ 0) : circleRotation t ≠ 1 := by
  intro h
  have he : 1 + (t : ℂ) * Complex.I = 1 - (t : ℂ) * Complex.I := by
    simpa only [one_mul] using (div_eq_iff (circleRotation_denominator_ne t)).mp h
  apply ht
  have hi := congrArg Complex.im he
  simp [Complex.mul_im] at hi
  linarith

private def moveCirclePole (u z : ℂ) (t : ℝ) : ℂ :=
  if z = 0 then u - circleRotation t * u else z

private theorem continuous_moveCirclePole (u z : ℂ) : Continuous (moveCirclePole u z) := by
  by_cases hz : z = 0
  · have he : moveCirclePole u z = fun t => u - circleRotation t * u :=
      funext fun _ => if_pos hz
    rw [he]
    exact continuous_const.sub (continuous_circleRotation.mul continuous_const)
  · have he : moveCirclePole u z = fun _ => z := funext fun _ => if_neg hz
    rw [he]
    exact continuous_const

private theorem moveCirclePole_zero (u z : ℂ) : moveCirclePole u z 0 = z := by
  by_cases hz : z = 0 <;> simp [moveCirclePole, circleRotation, hz]

private theorem moveCirclePole_normSq (u z : ℂ) (t : ℝ)
    (h : Complex.normSq (z - u) = Complex.normSq u) :
    Complex.normSq (moveCirclePole u z t - u) = Complex.normSq u := by
  by_cases hz : z = 0
  · have he : moveCirclePole u z t - u = -(circleRotation t * u) := by
      simp only [moveCirclePole, hz, if_true]
      ring
    rw [he, Complex.normSq_neg, Complex.normSq_mul, circleRotation_normSq, one_mul]
  · simpa only [moveCirclePole, hz, if_false] using h

private theorem moveCirclePole_ne_zero (u z : ℂ) (hu : u ≠ 0) {t : ℝ} (ht : t ≠ 0) :
    moveCirclePole u z t ≠ 0 := by
  by_cases hz : z = 0
  · simp only [moveCirclePole, hz, if_true]
    intro he
    apply circleRotation_ne_one ht
    apply mul_right_cancel₀ hu
    simpa only [one_mul] using (sub_eq_zero.mp he).symm
  · rw [moveCirclePole, if_neg hz]
    exact hz

private theorem holds_of_tangent_circles_at_zero (a c : ι → ℂ)
    (u : ℂ) (r : ℝ) (hu : u ≠ 0) (hr : r ≠ 0)
    (ha : ∀ i, Complex.normSq (a i - u) = Complex.normSq u)
    (hc : ∀ i, Complex.normSq (c i - (r : ℂ) * u) = Complex.normSq ((r : ℂ) * u))
    (U : Matrix ι ι ℂ) (hU : IsUnitary U) : Holds a (fun i => -c i) U := by
  by_contra hfail
  rw [holds_iff_directional, not_forall] at hfail
  obtain ⟨k, hk⟩ := hfail
  push_neg at hk
  let a' (t : ℝ) (i : ι) := moveCirclePole u (a i) t
  let c' (t : ℝ) (i : ι) := moveCirclePole ((r : ℂ) * u) (c i) t
  have ha₀ : a' 0 = a := funext fun i => moveCirclePole_zero u (a i)
  have hc₀ : c' 0 = c := funext fun i => moveCirclePole_zero ((r : ℂ) * u) (c i)
  have hca : Continuous a' := continuous_pi fun i => continuous_moveCirclePole u (a i)
  have hcc : Continuous c' := continuous_pi fun i => continuous_moveCirclePole ((r : ℂ) * u) (c i)
  have hd : Continuous (fun t => (k * determinantValue (a' t) (fun i => -c' t i) U).re) := by
    unfold determinantValue
    fun_prop
  have hm (σ : Equiv.Perm ι) :
      Continuous (fun t => (k * matchingProduct (a' t) (fun i => -c' t i) σ).re) := by
    have hp : Continuous (fun t => matchingProduct (a' t) (fun i => -c' t i) σ) := by
      unfold matchingProduct
      apply continuous_finset_prod
      intro j _
      fun_prop
    fun_prop
  have hsep : ∀ᶠ t in 𝓝[≠] (0 : ℝ), ∀ σ : Equiv.Perm ι,
      (k * matchingProduct (a' t) (fun i => -c' t i) σ).re <
        (k * determinantValue (a' t) (fun i => -c' t i) U).re := by
    apply Filter.eventually_all.mpr
    intro σ
    exact ((hm σ).continuousAt.eventually_lt hd.continuousAt
      (by simpa only [ha₀, hc₀] using hk σ)).filter_mono nhdsWithin_le_nhds
  obtain ⟨t, hsep', ht⟩ := (hsep.and
    (self_mem_nhdsWithin : ∀ᶠ t in 𝓝[≠] (0 : ℝ), t ≠ 0)).exists
  have h' := holds_of_tangent_circles_at_zero_of_nonzero (a' t) (c' t) u r hu hr
    (fun i => moveCirclePole_normSq u (a i) t (ha i))
    (fun i => moveCirclePole_normSq ((r : ℂ) * u) (c i) t (hc i))
    (fun i => moveCirclePole_ne_zero u (a i) hu ht)
    (fun i => moveCirclePole_ne_zero ((r : ℂ) * u) (c i)
      (mul_ne_zero (Complex.ofReal_ne_zero.mpr hr) hu) ht) U hU
  obtain ⟨σ, hσ⟩ := (holds_iff_directional _ _ _).mp h' k
  exact (not_le_of_gt (hsep' σ)) hσ

/-- Inclusion for spectra on circles tangent at a common point in the difference
convention. The negative of the second spectrum lies on the second circle.
Radii may differ, and either spectrum may contain the point of tangency. -/
theorem holds_of_tangent_circles (a b : ι → ℂ) (p u : ℂ) (r : ℝ)
    (hu : u ≠ 0) (hr : r ≠ 0)
    (ha : ∀ i, Complex.normSq (a i - p - u) = Complex.normSq u)
    (hb : ∀ i, Complex.normSq (-b i - p - (r : ℂ) * u) = Complex.normSq ((r : ℂ) * u))
    (U : Matrix ι ι ℂ) (hU : IsUnitary U) : Holds a b U := by
  apply (holds_shift_iff a b hU (-p)).mp
  have hneg : (fun i => -(-b i - p)) = fun i => b i - -p := by
    funext i
    ring
  have h := holds_of_tangent_circles_at_zero (fun i => a i + -p) (fun i => -b i - p)
    u r hu hr (fun i => by simpa only [sub_eq_add_neg] using ha i) hb U hU
  rw [hneg] at h
  exact h

end

end MOC
