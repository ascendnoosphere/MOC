import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
The exact scalar residue of the signed-coordinate reflection comparison.
The two signs share one even term. Stationarity removes the odd term only;
it does not force that even term to vanish.
-/

namespace MOC

/-- The homogeneous reflection coefficient after inserting the matrix entries
of the inverse sum into the four bilinear forms. For unit eigenvectors
`x,e` of the two summands, use `d = eᵀx`, `f = xᵀFx`, `g = eᵀFe`,
`p = eᵀFx` with `F = (A+B)⁻¹`. The argument `t` is the coefficient
of `e` in `x + t e`. -/
def signedReflectionResidue (ℓ m d f g p t : ℂ) : ℂ :=
  ((1 - m * f) + t * (d + (ℓ - m) * p) + t ^ 2 * (ℓ * g)) *
    (m * f + t * (d + (m - ℓ) * p) + t ^ 2 * (1 - ℓ * g)) -
  (m * (1 - m * f) + 2 * t * ℓ * m * p + t ^ 2 * (ℓ * (1 - ℓ * g))) *
    (f + 2 * t * p + t ^ 2 * g)

theorem signedReflectionResidue_expand (ℓ m d f g p t : ℂ) :
    signedReflectionResidue ℓ m d f g p t =
      (t + t ^ 3) * (d - (ℓ + m) * p) +
        t ^ 2 * (1 + d ^ 2 - (ℓ + m) * (f + g) + (ℓ + m) ^ 2 * (f * g - p ^ 2)) := by
  unfold signedReflectionResidue
  ring

/-- Removing the stationary odd part leaves the same even support residue
for either signed coordinate target. The residue has no imposed sign. -/
theorem signedReflectionResidue_re_eq_of_stationary
    (ℓ m d f g p ω : ℂ) (h : (ω * (d - (ℓ + m) * p)).re = 0) :
    (ω * signedReflectionResidue ℓ m d f g p 1).re =
      (ω * signedReflectionResidue ℓ m d f g p (-1)).re := by
  rw [signedReflectionResidue_expand, signedReflectionResidue_expand]
  simp only [one_pow, neg_one_sq, one_mul, show (-1 : ℂ) ^ 3 = -1 by ring,
    mul_add, Complex.add_re]
  rw [show ω * ((1 + 1) * (d - (ℓ + m) * p)) =
    (ω * (d - (ℓ + m) * p)) + (ω * (d - (ℓ + m) * p)) by ring,
    show ω * ((-1 + -1) * (d - (ℓ + m) * p)) =
    -((ω * (d - (ℓ + m) * p)) + (ω * (d - (ℓ + m) * p))) by ring]
  simp [Complex.add_re, Complex.neg_re, h]


/-- The stationary even residue is the real projection of a two-dimensional
determinant of the compressed form `I - (ℓ+m) F`. The off-diagonal
entry is orthogonal to the support functional by stationarity. -/
theorem signedReflectionResidue_re_eq_compressed (ℓ m d f g p ω : ℂ)
    (h : (ω * (d - (ℓ + m) * p)).re = 0)
    (hd : star d = d) :
    (ω * signedReflectionResidue ℓ m d f g p 1).re =
      (ω * ((1 - (ℓ + m) * f) * (1 - (ℓ + m) * g) -
        (d - (ℓ + m) * p) ^ 2)).re := by
  rw [signedReflectionResidue_expand]
  have he : (1 + (1 : ℂ) ^ 3) * (d - (ℓ + m) * p) +
      (1 : ℂ) ^ 2 * (1 + d ^ 2 - (ℓ + m) * (f + g) + (ℓ + m) ^ 2 * (f * g - p ^ 2)) =
      ((1 - (ℓ + m) * f) * (1 - (ℓ + m) * g) - (d - (ℓ + m) * p) ^ 2) +
      (2 + 2 * d) * (d - (ℓ + m) * p) := by ring
  rw [he, mul_add, Complex.add_re]
  have hr : d = (d.re : ℂ) := by
    apply Complex.ext
    · simp
    · have hi := congrArg Complex.im hd
      simp only [Complex.star_def, Complex.conj_im] at hi
      simp only [Complex.ofReal_im]
      linarith
  have hb : (2 + 2 * d) = ((2 + 2 * d.re : ℝ) : ℂ) := by rw [hr]; push_cast; simp
  rw [← mul_assoc, mul_comm ω (2 + 2 * d), mul_assoc, hb, Complex.re_ofReal_mul, h,
    mul_zero, add_zero]

end MOC
