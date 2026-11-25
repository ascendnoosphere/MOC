import Mathlib.Analysis.Complex.Basic

/-! Equality geometry for a unit-modulus anchored rank-two kernel.
The bisector calculation avoids appealing to geometric circle
intersection or to enumeration of the entries. -/

namespace MOC

private theorem reciprocal_bisector (z c : ℂ) (hz : z ≠ 0)
    (h : Complex.normSq (1 + c * z) = 1) :
    Complex.normSq c + 2 * (c.re * z⁻¹.re + c.im * z⁻¹.im) = 0 := by
  have he : (1 + c * z) * z⁻¹ = z⁻¹ + c := by
    rw [add_mul,one_mul,mul_assoc,mul_inv_cancel₀ hz,mul_one]
  have hn := congrArg Complex.normSq he
  rw [Complex.normSq_mul,h,one_mul,add_comm z⁻¹ c,Complex.normSq_add,
    Complex.mul_re,Complex.conj_re,Complex.conj_im] at hn
  linarith

/-- Two distinct nonzero coefficients define at most one common
nonzero point on the anchored unit-modulus circles. -/
theorem unit_affine_circles_unique_nonzero
    {x x' y y' : ℂ} (hx : x ≠ 0) (hx' : x' ≠ 0) (hxx : x ≠ x')
    (hy : y ≠ 0) (hy' : y' ≠ 0)
    (hxy : Complex.normSq (1 + x * y) = 1)
    (hxy' : Complex.normSq (1 + x * y') = 1)
    (hx'y : Complex.normSq (1 + x' * y) = 1)
    (hx'y' : Complex.normSq (1 + x' * y') = 1) :
    y = y' := by
  let u := x * y
  let v := x * y'
  let c := x' / x
  have hu : u ≠ 0 := mul_ne_zero hx hy
  have hv : v ≠ 0 := mul_ne_zero hx hy'
  have hc : c ≠ 0 := div_ne_zero hx' hx
  have hc1 : c ≠ 1 := fun he => hxx (((div_eq_iff hx).mp he).trans (one_mul x)).symm
  have hcu : c * u = x' * y := by
    dsimp only [c,u]
    rw [← mul_assoc,div_mul_cancel₀ _ hx]
  have hcv : c * v = x' * y' := by
    dsimp only [c,v]
    rw [← mul_assoc,div_mul_cancel₀ _ hx]
  have hu₀ := reciprocal_bisector u 1 hu (by simpa only [one_mul] using hxy)
  have hv₀ := reciprocal_bisector v 1 hv (by simpa only [one_mul] using hxy')
  simp only [Complex.normSq_one,Complex.one_re,Complex.one_im,one_mul,zero_mul,add_zero] at hu₀ hv₀
  have hu₁ := reciprocal_bisector u c hu (by simpa only [hcu] using hx'y)
  have hv₁ := reciprocal_bisector v c hv (by simpa only [hcv] using hx'y')
  have hci : c.im ≠ 0 := by
    intro hz
    rw [Complex.normSq_apply,hz,zero_mul,add_zero,zero_mul,add_zero] at hu₁
    have hfac : c.re * (c.re - 1) = 0 := by
      linear_combination hu₁ - c.re * hu₀
    rcases mul_eq_zero.mp hfac with hcr | hcr
    · exact hc (Complex.ext hcr hz)
    · exact hc1 (Complex.ext (sub_eq_zero.mp hcr) hz)
  have hreal : u⁻¹.re = v⁻¹.re := by linarith
  have him : c.im * (u⁻¹.im - v⁻¹.im) = 0 := by
    rw [hreal] at hu₁
    linear_combination (hu₁ - hv₁) / 2
  have hInv : u⁻¹ = v⁻¹ :=
    Complex.ext hreal (sub_eq_zero.mp ((mul_eq_zero.mp him).resolve_left hci))
  exact mul_left_cancel₀ hx (inv_injective hInv)

/-- If every entry of an anchored rank-two kernel has unit modulus,
then one of its two factor lists has at most two values. -/
theorem anchored_rankTwo_unitModulus_two_types
    {I J : Type*} (x : I → ℂ) (y : J → ℂ)
    (h : ∀ i j, Complex.normSq (1 + x i * y j) = 1) :
    (∃ u v : ℂ, ∀ i, x i = u ∨ x i = v) ∨
      (∃ u v : ℂ, ∀ j, y j = u ∨ y j = v) := by
  classical
  by_cases hx : ∃ i, x i ≠ 0
  · obtain ⟨i,hi⟩ := hx
    by_cases hs : ∀ k, x k = 0 ∨ x k = x i
    · exact Or.inl ⟨0,x i,hs⟩
    · push_neg at hs
      obtain ⟨k,hkn,hki⟩ := hs
      right
      by_cases hy : ∃ j, y j ≠ 0
      · obtain ⟨j,hj⟩ := hy
        refine ⟨0,y j,fun l => ?_⟩
        by_cases hl : y l = 0
        · exact Or.inl hl
        · exact Or.inr (unit_affine_circles_unique_nonzero hi hkn (Ne.symm hki) hl hj
            (h i l) (h i j) (h k l) (h k j))
      · exact ⟨0,0,fun l => Or.inl (not_not.mp fun hl => hy ⟨l,hl⟩)⟩
  · exact Or.inl ⟨0,0,fun i => Or.inl (not_not.mp fun hi => hx ⟨i,hi⟩)⟩

end MOC
