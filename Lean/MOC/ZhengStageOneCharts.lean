import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Ring

/-! Cleared bracket identity for the Zheng contact set numbered seven.
Facet labels follow Denzel Zheng, *The Marcus–de Oliveira conjecture for n = 4*,
preprint DOI 10.13140/RG.2.2.36790.25923. These identities do not assume the
supplement. A cleared identity is not a support estimate for its contact set. -/

namespace MOC.ZhengStageOneCharts

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

end MOC.ZhengStageOneCharts
