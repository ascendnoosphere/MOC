import MOC.PhaseMove

/-! Scalar constraints on two consecutive couplings at a normal support maximum. -/

namespace MOC

private theorem star_eq_neg_of_re_eq_zero (c : ℂ) (h : c.re = 0) : star c = -c := by
  apply Complex.ext <;> simp [Complex.star_def, h]

private theorem normSq_eq_one_of_mul_star (c : ℂ) (h : c * star c = 1) :
    Complex.normSq c = 1 := by
  simpa only [Complex.star_def, Complex.mul_conj, Complex.ofReal_re, Complex.one_re] using
    congrArg Complex.re h

private theorem phase_factorization (x y p s t : ℂ) (hp : p ≠ 0)
    (hs : s * star s = 1) (ht : t * star t = 1)
    (hsy : (p * s * y).re = 0) (htx : (p * t * x).re = 0)
    (hmixed : p * (x + y) = -(star (p * (x + y)) * star (s * t))) :
    s = t ∨ s * y = t * x := by
  have hu := star_eq_neg_of_re_eq_zero _ hsy
  have hv := star_eq_neg_of_re_eq_zero _ htx
  simp only [star_mul'] at hu hv
  have hy : star p * star y + p * s ^ 2 * y = 0 := by
    linear_combination s * hu - (star p * star y) * hs
  have hx : star p * star x + p * t ^ 2 * x = 0 := by
    linear_combination t * hv - (star p * star x) * ht
  have hst : (s * t) * (star s * star t) = 1 := by
    linear_combination (t * star t) * hs + ht
  simp only [star_mul', star_add] at hmixed
  have hm : p * (x + y) * (s * t) + star p * (star x + star y) = 0 := by
    linear_combination (s * t) * hmixed - (star p * (star x + star y)) * hst
  have hfactor : p * ((s - t) * (s * y - t * x)) = 0 := by
    linear_combination hy + hx - hm
  simpa only [sub_eq_zero] using mul_eq_zero.mp ((mul_eq_zero.mp hfactor).resolve_left hp)

/-- The pair and mixed phase identities force a path with two nonzero couplings
to have equal endpoint eigenvalues when the real support is nonzero. Here
`p` is the support multiplier divided by the product of the three eigenvalues. -/
theorem endpoints_eq_of_mixed_phase (x y z p s t : ℂ) (hxz : x ≠ z)
    (hκ : (p * x * y * z).re ≠ 0)
    (hs : s * star s = 1) (ht : t * star t = 1)
    (hsphase : s * (star x - star z) = x - z)
    (htphase : t * (star z - star y) = z - y)
    (hsy : (p * s * y).re = 0) (htx : (p * t * x).re = 0)
    (hmixed : p * (x + y) = -(star (p * (x + y)) * star (s * t))) :
    x = y := by
  by_contra hxy
  have hp : p ≠ 0 := fun h => hκ (by simp [h])
  rcases phase_factorization x y p s t hp hs ht hsy htx hmixed with hst | hst
  · subst t
    have hsnz : s ≠ 0 := fun h => by simp [h] at hs
    have hu := star_eq_neg_of_re_eq_zero _ hsy
    have hv := star_eq_neg_of_re_eq_zero _ htx
    rw [star_mul'] at hu hv
    have hcancel : star (p * s) * (x * star y - star x * y) = 0 := by
      linear_combination x * hu - y * hv
    have hpstar : star (p * s) ≠ 0 :=
      fun h => mul_ne_zero hp hsnz (star_eq_zero.mp h)
    have hxyphase : x * star y = star x * y :=
      sub_eq_zero.mp ((mul_eq_zero.mp hcancel).resolve_left hpstar)
    have hphase : s * (star x - star y) = x - y := by
      linear_combination hsphase + htphase
    have hfactor : (star x - star y) * (s * star x - x) = 0 := by
      linear_combination star x * hphase + hxyphase
    have hsx : s * star x = x :=
      sub_eq_zero.mp ((mul_eq_zero.mp hfactor).resolve_left
        (sub_ne_zero.mpr (star_injective.ne hxy)))
    have hsz : s * star z = z := by
      linear_combination hsx - hsphase
    have hxzphase : x * star z = z * star x := by
      linear_combination star x * hsz - star z * hsx
    have hreal : (x * star z).im = 0 := by
      have he : star (x * star z) = x * star z := by
        rw [star_mul', star_star, mul_comm (star x) z, ← hxzphase]
      have hi := congrArg Complex.im he
      simp only [Complex.star_def, Complex.conj_im] at hi
      linarith only [hi]
    have hrep : p * x * y * z = (p * s * y) * (x * star z) := by
      linear_combination -(p * x * y) * hsz
    apply hκ
    rw [hrep, Complex.mul_re, hsy, hreal, zero_mul, mul_zero, sub_zero]
  · have hnorm := congrArg Complex.normSq hst
    simp only [Complex.normSq_mul, normSq_eq_one_of_mul_star s hs,
      normSq_eq_one_of_mul_star t ht, one_mul] at hnorm
    have hxyabs : x * star x = y * star y := by
      simpa only [Complex.star_def, Complex.mul_conj] using congrArg Complex.ofReal hnorm.symm
    have hphase :
        y * (x - z) * (star z - star y) = x * (star x - star z) * (z - y) := by
      linear_combination -(y * (star z - star y)) * hsphase +
        (x * (star x - star z)) * htphase + ((star x - star z) * (star z - star y)) * hst
    have hfactor : (x - y) * (z * star z - x * star x) = 0 := by
      linear_combination hphase - (x - z) * hxyabs
    have hxzabs : z * star z = x * star x :=
      sub_eq_zero.mp ((mul_eq_zero.mp hfactor).resolve_left (sub_ne_zero.mpr hxy))
    have hfactor' : (star x - star z) * (s * (x * star x) + x * z) = 0 := by
      linear_combination (x * star x) * hsphase - x * hxzabs
    have hneg : s * (x * star x) = -(x * z) :=
      eq_neg_of_add_eq_zero_left ((mul_eq_zero.mp hfactor').resolve_left
        (sub_ne_zero.mpr (star_injective.ne hxz)))
    have hrep : p * x * y * z = -(p * s * y) * (x * star x) := by
      linear_combination (p * y) * hneg
    apply hκ
    rw [hrep, Complex.star_def, Complex.mul_conj, Complex.mul_re, Complex.neg_re, hsy,
      Complex.ofReal_im, neg_zero, zero_mul, mul_zero, sub_zero]

end MOC
