import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Ring

/-! Cleared bracket identities for several of the early Zheng contact sets.
Facet labels follow Denzel Zheng, *The Marcus–de Oliveira conjecture for n = 4*,
preprint DOI 10.13140/RG.2.2.36790.25923. These identities do not assume the
supplement. A cleared identity is not a support estimate for its contact set. -/

namespace MOC.ZhengStageOneCharts

/-- The five fixed ratios and the nonconstant rectangle ratio on the T2 curve.
Products use homogeneous chart coordinates, so no divisions are involved. -/
theorem t2_cleared (z s t k l : ℂ) :
    let v := s*z-k
    let u := z*(s-k)
    let a := t*(l-s*z)
    let b := l-t
    let p₀ := (z*v-u)*(s*z)*(a-t*b)
    let p₁ := (z*v-u)*(s*z-t)*a
    let p₂ := (z*v-u)*(s*z-1)*(a-t*b)
    let p₃ := (z*v-u)*(s*z-t)*(a-b)
    let p₆ := (z-1)*v*(s*z)*(a-t*b)
    let p₇ := (z-1)*v*(s*z-t)*a
    let p₈ := (z-1)*(s*z*v-u)*(a-t*b)
    let D := p₀-p₂
    D = s*t*z*(z-1)*(t-s*z) ∧
    p₀-p₁ = l*D ∧ t*(p₀-p₃) = (t*l+t-l)*D ∧
    p₀-p₆ = k*D ∧ s*(p₀-p₈) = (s*k+s-k)*D ∧
    s*z*(p₀-p₇) = ((k+l)*s*z-k*l)*D := by
  dsimp
  repeat' constructor <;> ring

/-- The fixed ratios on the T7 curve, multiplied by their common normalizer.
The unprescribed ratio for label 3 retains a free variable. -/
theorem t7_cleared (y t d k m : ℂ) :
    let a := d*(y-1)
    let z := y-a
    let b := z-t
    let V := k*y-m*b
    let X := y*(V-k*a)
    let W := V-y*b
    let N := X-y*b
    let J := k*y*d-V
    let B := X*W-V*N
    let p₀ := B*(y-1)*z
    let p₁ := B*(y-1)*b
    let p₂ := B*y*(z-1)
    let p₃ := B*y*b
    let p₄ := B*(y-t)*(z-1)
    let p₇ := (X-V)*(y*W-N)*b
    let p₈ := (X-V)*y*(z*W-N)
    let D := p₀-p₂
    D = d*y*(y-1)^2*b*J ∧
    d*(p₀-p₁) = t*D ∧ p₁-p₄ = (1-t)*D ∧
    p₁-p₇ = k*D ∧ p₂-p₈ = m*D ∧
    a*(p₂-p₃) = (t-1)*y*D := by
  dsimp
  repeat' constructor <;> ring

/-- Cleared T3 identities, parameterized by the ratio of the two fixed differences. -/
theorem t3_cleared (z t l k r : ℂ) :
    let x := z-r*(z-l)
    let v := z-l-k
    let u := z-l-k*x
    let a := t*(l-z)
    let b := l-t
    let p₀ := (x*v-u)*z*(a-t*b)
    let p₁ := (x*v-u)*(z-t)*a
    let p₂ := (x*v-u)*(z-1)*(a-t*b)
    let p₃ := (x*v-u)*(z-t)*(a-b)
    let p₄ := (x*v-u)*(z-1)*a
    let p₇ := (x-1)*v*(z-t)*a
    let p₈ := (x-1)*(z*v-u)*(a-t*b)
    let D := p₀-p₂
    D = (x-1)*(z-l)*t*(t-z) ∧
    p₀-p₁ = l*D ∧ t*(p₀-p₃) = (t*l+t-l)*D ∧
    p₁-p₇ = k*D ∧ p₂-p₈ = k*r*D ∧
    (a-t*b)*(p₀-p₄) = (a-t*b*z)*D := by
  dsimp
  repeat' constructor <;> ring

/-- The T6 variant uses the same curve as T7 with a different fixed swap. -/
theorem t6_cleared (y t d k m : ℂ) :
    let a := d*(y-1)
    let b := y-a
    let V := k*y-m*b
    let X := y*(V-k*a)
    let W := V-y*b
    let N := X-y*b
    let J := k*y*d-V
    let B := X*W-V*N
    let p₀ := B*(y-1)*b
    let p₁ := B*(y-1)*(b-t)
    let p₂ := B*y*(b-1)
    let p₃ := B*y*(b-t)
    let p₄ := B*(y-t)*(b-1)
    let p₆ := (X-V)*(y*W-N)*b
    let p₈ := (X-V)*y*(b*W-N)
    let D := p₀-p₂
    D = d*y*(y-1)^2*b*J ∧
    d*(p₀-p₁) = t*D ∧ p₁-p₄ = (1-t)*D ∧
    p₀-p₆ = k*D ∧ p₂-p₈ = m*D ∧
    a*(p₂-p₃) = (t-1)*y*D := by
  dsimp
  repeat' constructor <;> ring

/-- T4 branch after exchanging columns 2 and 3. -/
theorem t4_cleared (z t l k q : ℂ) :
    let U := z*((z-q)*(t-z)-(z-k-1)*(l-z))
    let V := k*(l-z)
    let u := z*V-k*U
    let v := (z-k)*V
    let a := t*(l-z)
    let b := l-t
    let A := U*v-V*u
    let p₀ := A*z*(a-t*b)
    let p₁ := A*(z-t)*a
    let p₂ := A*(z-1)*(a-t*b)
    let p₃ := A*(z-t)*(a-b)
    let p₆ := (U-V)*v*z*(a-t*b)
    let p₁₀ := (U-V)*(z*v-u)*a
    let D := p₀-p₂
    D = z*V*(U-V)*t*(t-z) ∧
    p₀-p₁ = l*D ∧ t*(p₀-p₃) = (t*l+t-l)*D ∧
    p₀-p₆ = k*D ∧ p₀-p₁₀ = q*D := by
  dsimp
  repeat' constructor <;> ring

/-- T5 branch after the preliminary relabeling. The row 0 and column 0
homogeneous scalings clear constant chart denominators. -/
theorem t5_cleared (z t l k q : ℂ) :
    let a := t*(l-z)
    let b := l-t
    let U := (k-q)*a+b*(z-t*(z-q))
    let V := k*b
    let u := z*V-k*U
    let v := (z-k)*V
    let A := U*v-V*u
    let p₀ := A*z*(a-t*b)
    let p₁ := A*(z-t)*a
    let p₂ := A*(z-1)*(a-t*b)
    let p₃ := A*(z-t)*(a-b)
    let p₆ := (U-V)*v*z*(a-t*b)
    let p₁₁ := (U-V)*z*(a*v-b*u)
    let D := p₀-p₂
    D = z*V*(U-V)*t*(t-z) ∧
    p₀-p₁ = l*D ∧ t*(p₀-p₃) = (t*l+t-l)*D ∧
    p₀-p₆ = k*D ∧ p₀-p₁₁ = q*D := by
  dsimp
  repeat' constructor <;> ring

/-- Variable and constant ratios for the T15 branch after relabeling. -/
theorem t15_cleared (x z a t m : ℂ) :
    let u := (m+1)*x-z
    let v := m+x-z
    let A := x*v-u
    let p₀ := A*z*(a-t)
    let p₂ := A*(z-1)*(a-t)
    let p₆ := (x-1)*v*z*(a-t)
    let p₈ := (x-1)*(z*v-u)*(a-t)
    let p₁₀ := (x-1)*(z*v-u)*a
    let D := p₀-p₂
    D = (x-1)*(x-z)*(a-t) ∧
    p₂-p₈ = m*D ∧ (a-t)*p₁₀ = (z-m-1)*a*D ∧
    (x-z)*(p₀-p₆) = -m*z*D := by
  dsimp
  repeat' constructor <;> ring

/-- Equality of the support gaps at labels 7 and 9 on the T2 chart:
after dividing by the nonzero normalizer, the right-hand ratio is real
whenever the four fixed chart parameters are real. -/
theorem t2_gap79_cleared (z s t k l : ℂ) :
    let v := s*z-k
    let u := z*(s-k)
    let a := t*(l-s*z)
    let b := l-t
    let D := s*t*z*(z-1)*(t-s*z)
    let p₇ := (z-1)*v*(s*z-t)*a
    let p₉ := (z-1)*(s*z-t)*(a*v-b*u)
    s*t*(p₇-p₉) = -(l-t)*(s-k)*D := by
  dsimp
  ring

end MOC.ZhengStageOneCharts
