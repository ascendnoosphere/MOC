import MOC.FourContactCertificate
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases

/-! The real projections of actual order-four matching profiles lie on the
matching cubic. The fourteen bracket coordinates and cubic normalization are
from Zheng (preprint DOI: 10.13140/RG.2.2.36790.25923, Appendix A).
For the eight-point invariant-theoretic description, see Howard--Millson--
Snowden--Vakil (DOI: 10.1112/plms/pds016; open DOI: 10.48550/arXiv.1103.5255).
The proof below uses bracket polynomial identities, not the geometric
identification of the singular locus or a table of permutation cases. -/

open BigOperators

namespace MOC

def fourBracketLift {R : Type*} [CommRing R] (z : Fin 8 → R) : Fin 14 → R :=
  let b (i j : Fin 8) := z i - z j
  ![b 0 1 * b 2 3 * b 4 5 * b 6 7,
    b 0 1 * b 2 3 * b 4 7 * b 5 6,
    b 0 1 * b 2 5 * b 3 4 * b 6 7,
    b 0 1 * b 2 7 * b 3 4 * b 5 6,
    b 0 1 * b 2 7 * b 3 6 * b 4 5,
    b 0 3 * b 1 2 * b 4 5 * b 6 7,
    b 0 3 * b 1 2 * b 4 7 * b 5 6,
    b 0 5 * b 1 2 * b 3 4 * b 6 7,
    b 0 5 * b 1 4 * b 2 3 * b 6 7,
    b 0 7 * b 1 2 * b 3 4 * b 5 6,
    b 0 7 * b 1 2 * b 3 6 * b 4 5,
    b 0 7 * b 1 4 * b 2 3 * b 5 6,
    b 0 7 * b 1 6 * b 2 3 * b 4 5,
    b 0 7 * b 1 6 * b 2 5 * b 3 4]

private def cubicGradient {R : Type*} [CommRing R] (m : Fin 14 → R) : Fin 14 → R :=
  ![-2*m 0*m 9 - m 1*m 9 - m 10*m 3 - m 10*m 9 - m 11*m 7 - m 11*m 9 - m 12*m 9 + m 13*m 6 - m 2*m 9 - m 3*m 9 - m 5*m 9 - m 7*m 9 - m 9^2,
    -m 0*m 9 + m 10*m 2 + m 10*m 7 + m 12*m 7 - m 13*m 5 - m 5*m 9,
    -m 0*m 9 + m 1*m 10 + m 10*m 11 + m 11*m 5 - m 12*m 6 - m 12*m 9,
    -m 0*m 10 - m 0*m 9 - m 10*m 8 + m 11*m 5 + m 12*m 5 + m 12*m 7,
    -m 11*m 7 + m 8*m 9,
    -m 0*m 9 - m 1*m 13 - m 1*m 9 + m 11*m 2 + m 11*m 3 + m 12*m 3,
    m 0*m 13 - m 12*m 2,
    -m 0*m 11 - m 0*m 9 + m 1*m 10 + m 1*m 12 - m 11*m 4 + m 12*m 3,
    -m 10*m 3 + m 4*m 9,
    -m 0^2 - m 0*m 1 - m 0*m 10 - m 0*m 11 - m 0*m 12 - m 0*m 2 - m 0*m 3 - m 0*m 5 - m 0*m 7 - 2*m 0*m 9 - m 1*m 5 - m 12*m 2 + m 4*m 8,
    -m 0*m 3 - m 0*m 9 + m 1*m 2 + m 1*m 7 + m 11*m 2 - m 3*m 8,
    -m 0*m 7 - m 0*m 9 + m 10*m 2 + m 2*m 5 + m 3*m 5 - m 4*m 7,
    -m 0*m 9 + m 1*m 7 - m 2*m 6 - m 2*m 9 + m 3*m 5 + m 3*m 7,
    m 0*m 6 - m 1*m 5]

private def cubicSlope {R : Type*} [CommRing R] (x y : Fin 14 → R) : R :=
  ∑ k, cubicGradient x k * y k

set_option maxHeartbeats 1600000 in
private theorem cubic_polarization {R : Type*} [CommRing R]
    (x y : Fin 14 → R) (s t : R) :
    fourMatchingCubic (fun k => s * x k + t * y k) =
      s^3 * fourMatchingCubic x + s^2*t * cubicSlope x y +
      s*t^2 * cubicSlope y x + t^3 * fourMatchingCubic y := by
  simp [fourMatchingCubic,cubicSlope,cubicGradient,Fin.sum_univ_succ]
  ring

private theorem cubic_euler {R : Type*} [CommRing R] (x : Fin 14 → R) :
    cubicSlope x x = 3 * fourMatchingCubic x := by
  simp [fourMatchingCubic,cubicSlope,cubicGradient,Fin.sum_univ_succ]
  ring

set_option maxHeartbeats 2500000 in
private theorem bracket_gradient_zero {R : Type*} [CommRing R] (z : Fin 8 → R) (k : Fin 14) :
    cubicGradient (fourBracketLift z) k = 0 := by
  fin_cases k <;> simp [cubicGradient, fourBracketLift] <;> ring

private theorem bracket_slope_zero {R : Type*} [CommRing R] (z : Fin 8 → R) (y : Fin 14 → R) :
    cubicSlope (fourBracketLift z) y = 0 := by
  simp [cubicSlope,bracket_gradient_zero]

private theorem bracket_cubic_zero (z : Fin 8 → ℂ) :
    fourMatchingCubic (fourBracketLift z) = 0 := by
  have h := cubic_euler (fourBracketLift z)
  rw [bracket_slope_zero,zero_eq_mul] at h
  exact h.resolve_left (by norm_num)

/-- The cubic vanishes on the full complex secant between any two actual
bracket profiles, including repeated points and zero brackets. -/
theorem fourMatchingCubic_secant (x y : Fin 8 → ℂ) (s t : ℂ) :
    fourMatchingCubic (fun k => s * fourBracketLift x k + t * fourBracketLift y k) = 0 := by
  rw [cubic_polarization,bracket_cubic_zero,bracket_cubic_zero,bracket_slope_zero,bracket_slope_zero]
  ring

private theorem bracket_conj (z : Fin 8 → ℂ) (k : Fin 14) :
    fourBracketLift (fun i => star (z i)) k = star (fourBracketLift z k) := by
  fin_cases k <;> simp [fourBracketLift,map_sub,map_mul]

/-- Every supporting projection of an exact order-four profile satisfies
the same cubic, without any genericity, positivity or nonzero assumptions. -/
theorem fourMatchingCubic_re_bracket (z : Fin 8 → ℂ) (η : ℂ) :
    fourMatchingCubic (fun k => (η * fourBracketLift z k).re) = 0 := by
  apply Complex.ofReal_injective
  have he (k : Fin 14) :
      ((η * fourBracketLift z k).re : ℂ) =
        (η/2) * fourBracketLift z k + (star η/2) * fourBracketLift (fun i => star (z i)) k := by
    rw [bracket_conj]
    apply Complex.ext <;> simp [Complex.div_re,Complex.div_im,Complex.mul_re,Complex.mul_im] <;> ring
  simpa only [fourMatchingCubic,Complex.ofReal_add,Complex.ofReal_sub,Complex.ofReal_mul,
    Complex.ofReal_zero,Complex.ofReal_neg,he] using fourMatchingCubic_secant z (fun i => star (z i)) (η/2) (star η/2)

end MOC
