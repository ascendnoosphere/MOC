import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Ring

/-! Cleared chart identities for the T55 overlap in Zheng's preprint,
DOI 10.13140/RG.2.2.36790.25923. The symbolic products in this file use
row-to-column lexicographic labels and the affine chart with the first
point of the second signed spectrum at infinity. -/

namespace MOC.ZhengT55Chart

/-- The rational profile identities are polynomial after multiplying each
matching product by the common factor `(1-α)*(1-γ)`. The values written here
are precisely these scaled matching products. No denominator hypotheses are
necessary for the cleared identities. -/
theorem cleared_normalization (α γ r t : ℂ) :
    let x := t*(1+r*γ)
    let y := t*(1+r*α)
    let E := 1-t+t*γ
    let F := 1-t+t*α
    let p₁ := (y-t)*γ
    let p₂ := y*E*α
    let p₃ := y*γ*F
    let p₄ := (y-1)*E
    let p₆ := (x-t)*α
    let p₇ := (x-t)*γ
    let p₈ := (x-t)*y*α*(1-γ)
    let p₁₀ := (x-t)*(y-1)*(1-γ)
    let p₁₁ := (x-t)*(y-1)*(1-α)
    let p₁₂ := x*E*α
    let p₂₀ := (x-1)*(y-t)*(1-γ)
    let p₂₁ := (x-1)*(y-t)*(1-α)
    let D := p₃-p₂
    let K := p₁₂-p₂
    let J := p₁₂-p₁
    let A := K+(K-D)*r*α
    let N := A-J*(1+r*α)
    D = y*(1-t)*(γ-α) ∧ p₁ = p₆ ∧
    p₁₁-p₁ = -r*(J-K+D) ∧ p₂₀-p₁ = -r*J ∧
    (1-t)*A = D*r*α*γ*t ∧
    r*N*(γ-α) = -(r*A*(α-1)+K*(1+r*α)) ∧
    p₈-p₁ = -J*r*α-K ∧
    (p₄-p₁)*A = -D*(J*r*α+K) ∧
    α*(p₇-p₁₀-r*J) = K ∧
    (p₂₁-p₁)*(1+r*α) =
      (-r*J+r*K-(r+1)*D)*(1+r*α)+(r+1)*D := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> ring

/-- The two cross-arm disk defects differ by a multiple of `k-1`.
The right factor is strictly positive for `0<s≤1`, `k>0` and a
nonreal chart parameter. -/
theorem disk_defect_difference (j k s x y : ℝ) :
    s*(j-k+1)-((k*x-(k-1)*s)^2+(k*y)^2)-(s*j-k*(x^2+y^2)) =
      -(k-1)*(k*((x-s)^2+y^2)+s*(1-s)) := by
  ring

end MOC.ZhengT55Chart
