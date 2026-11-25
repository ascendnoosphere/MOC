import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Scalar minor comparison for the standalone T55 case in Zheng's
preprint, DOI 10.13140/RG.2.2.36790.25923. The proof uses two elementary
partition identities for subset-image indicators. The evaluation of
those indicators in the determinant profile uses Merikoski--Virtanen,
DOI 10.1016/0024-3795(89)90709-X. -/

namespace MOC.ZhengT55SignedStar

/-- The Laurent expression for the single signed coefficient is a
cleared relation in the arbitrary (noncollision) projective chart. Both
the matching products and their differences carry the same common
factor; no equality of the first and sixth products is imposed. -/
theorem chart_signed_coefficient {R : Type*} [CommRing R] (x y t α γ : R) :
    let p₁ := (y-t)*γ
    let p₂ := y*(1-t+t*γ)*α
    let p₇ := (x-t)*γ
    let p₁₀ := (x-t)*(y-1)*(1-γ)
    let p₁₂ := x*(1-t+t*γ)*α
    let p₂₀ := (x-1)*(y-t)*(1-γ)
    α*(p₇-p₁₀+p₂₀-p₁) = p₁₂-p₂ := by
  dsimp
  ring

variable (A B C D E F G Z N : ℝ) (a b c d e f g z : ℝ)

/-- The elementary indicator identity behind the alternative minor basis. -/
theorem marker_exchange {B E F G Z N q x₀ x₁ x₂ : ℝ}
    (hpair : B+G+q=x₁+x₂)
    (havoid : q+E+F=1-x₀-N)
    (hrow : x₀+x₁+x₂+Z=1) : Z+B+G-E=F+N := by
  linarith

/-- The T55 signed objective is one star plus seven ordinary terms. -/
theorem signed_star (hex : Z+B+G-E=F+N) :
    a*A+b*B+c*C+d*D+e*E+f*F+g*G+z*Z =
      (-e-z)*(A+B+C+G-E)+(a+e+z)*A+(b+e)*B+(c+e+z)*C+
        (g+e)*G+d*D+(f+z)*F+z*N := by
  linear_combination z*hex

variable {A B C D E F G Z N a b c d e f g z}

/-- The standalone T55 comparison is nonnegative when the star coefficient
is nonpositive. In particular this excludes the additional contact 4
without using any spectral equation or any test on permutation or matrix
examples. -/
theorem nonneg_of_star_nonpos
    (hA : 0≤A) (hB : 0≤B) (hC : 0≤C) (hD : 0≤D)
    (hE : 0≤E) (hF : 0≤F) (hG : 0≤G) (hZ : 0≤Z) (hN : 0≤N)
    (ha : 0≤a) (hb : 0≤b) (hc : 0≤c) (hd : 0≤d)
    (hg : 0≤g) (hz : 0≤z)
    (hbe : 0≤b+e) (hge : 0≤g+e)
    (hbf : 0≤b+f) (hgf : 0≤g+f) (hzf : 0≤z+f)
    (hβ : -e-z≤0) (hex : Z+B+G-E=F+N) :
    0≤a*A+b*B+c*C+d*D+e*E+f*F+g*G+z*Z := by
  by_cases hf : 0≤f
  · by_cases he : 0≤e
    · positivity
    · have he' : 0≤-e := by linarith
      have hze : 0≤z+e := by linarith
      have hfe : 0≤f-e := by linarith
      suffices heq : a*A+b*B+c*C+d*D+e*E+f*F+g*G+z*Z =
          a*A+(b+e)*B+c*C+d*D+(f-e)*F+(g+e)*G+(z+e)*Z+(-e)*N by
        rw [heq]
        positivity
      linear_combination (-e)*hex
  · have hf' : 0≤-f := by linarith
    by_cases hef : 0≤e-f
    · suffices heq : a*A+b*B+c*C+d*D+e*E+f*F+g*G+z*Z =
          a*A+(b+f)*B+c*C+d*D+(e-f)*E+(g+f)*G+(z+f)*Z+(-f)*N by
        rw [heq]
        positivity
      linear_combination (-f)*hex
    · have he' : 0≤-e := by linarith
      have hze : 0≤z+e := by linarith
      have hfe : 0≤f-e := by linarith
      suffices heq : a*A+b*B+c*C+d*D+e*E+f*F+g*G+z*Z =
          a*A+(b+e)*B+c*C+d*D+(f-e)*F+(g+e)*G+(z+e)*Z+(-e)*N by
        rw [heq]
        positivity
      linear_combination (-e)*hex

/-- Secant compensation for standalone T55 with additional contact 0.
The shift z is the coefficient of the singleton indicator 2→0. The
calculation producing the displayed Hessian factor is on paper. -/
theorem boundary0_compensation {p T A z : ℝ}
    (hp : 0 ≤ p) (hA : 0 ≤ A) (hz : 0 ≤ z)
    (h : (p-T)*A^2-(p+1)*(T-z-1)*A+(p+1)*(z+1)=0) :
    1 ≤ A*T := by
  have hB : 0 ≤ (p+1)*(z+1)-1 := by
    nlinarith only [hp, hz, mul_nonneg hp hz]
  have he :
      (A*T-1)*(A+p+1) = p*A^2+((p+1)*(z+1)-1)*A+(p+1)*z := by
    linear_combination -h
  have hn : 0 ≤ (A*T-1)*(A+p+1) := by
    rw [he]
    positivity
  have hC : 0 < A+p+1 := by positivity
  by_contra! hlt
  exact (not_lt_of_ge hn) (mul_neg_of_neg_of_pos (by linarith) hC)

end MOC.ZhengT55SignedStar
