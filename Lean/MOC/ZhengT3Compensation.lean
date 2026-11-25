import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Scalar compensation for the T3 contact set of Zheng's order-four
preprint, DOI 10.13140/RG.2.2.36790.25923 (Appendices E and G).
The inputs are the cleared chart identities and nonnegative gaps.
The resulting product bound is used in the T15 paired-cofactor inequality. -/

namespace MOC.ZhengT3Compensation

/-- The residue comparison is a polynomial identity in homogeneous
coordinates, so the comparison remains valid when two poles coincide. -/
theorem cleared_residue {R : Type*} [CommRing R] (z t l k r : R) :
    let x := z-r*(z-l)
    let v := z-l-k
    let w := z-l-k*x
    let a := t*(l-z)
    let b := l-t
    let D := (x*v-w)*(a-t*b)
    let P₀ := (x*v-w)*z*(a-t*b)
    let P₁₀ := (x-1)*(z*v-w)*a
    let P₁₄ := x*(z*v-w)*(a-t*b)
    let P₂₀ := (x-t)*(z*v-w)*a
    (1-t-r*(l-t))*(P₀-P₂₀)+r*(l-t)*(P₀-P₁₀)+(l-1)*(1-t)*(P₀-P₁₄) =
      -l*(t-1)*(k*r+1)*D := by
  dsimp
  ring

/-- In the chamber beyond the strip, the two gaps on the negative side of
the cleared residue equation must each vanish. This includes coincident
poles, since the equation is not divided by the pole separation. -/
theorem gaps_zero_of_residue {l t r U g₁₀ g₁₄ g₂₀ : ℝ}
    (ht : t < 1) (hl : 1 < l) (hr : 0 < r) (hU : 0 ≤ U)
    (h₁₀ : 0 ≤ g₁₀) (h₁₄ : 0 ≤ g₁₄) (h₂₀ : 0 ≤ g₂₀)
    (he : U*g₂₀ = -(r*(l-t)*g₁₀)-((l-1)*(1-t)*g₁₄)) :
    g₁₀ = 0 ∧ g₁₄ = 0 := by
  have hL : 0 < r*(l-t) := mul_pos hr (sub_pos.mpr (ht.trans hl))
  have hR : 0 < (l-1)*(1-t) := mul_pos (sub_pos.mpr hl) (sub_pos.mpr ht)
  have h₁ := mul_nonneg hL.le h₁₀
  have h₂ := mul_nonneg hR.le h₁₄
  have h₃ := mul_nonneg hU h₂₀
  have hzero : r*(l-t)*g₁₀ = 0 ∧ (l-1)*(1-t)*g₁₄ = 0 := by
    constructor <;> linarith only [he,h₁,h₂,h₃]
  exact ⟨(mul_eq_zero.mp hzero.1).resolve_left hL.ne',
         (mul_eq_zero.mp hzero.2).resolve_left hR.ne'⟩

/-- The two independent real chart ratios pay for the entire signed
cofactor term, provided the chart parameter lies in the closed strip. -/
theorem product_compensation {l t W G β : ℝ}
    (ht : 0 < t) (hL : t < l) (hl : l ≤ 1)
    (hW : 0 ≤ W) (hβ : 0 ≤ β)
    (hWβ : t*β ≤ (l-t)*W) (hGβ : (1-t)*β ≤ t*G) :
    β^2 ≤ W*G := by
  have hW' : t*β ≤ (1-t)*W := hWβ.trans
    (mul_le_mul_of_nonneg_right (by linarith) hW)
  have ht' : 0 < 1-t := sub_pos.mpr (hL.trans_le hl)
  have h := mul_le_mul hW' hGβ (mul_nonneg ht'.le hβ)
    (mul_nonneg ht'.le hW)
  apply (mul_le_mul_left (mul_pos ht ht')).mp
  calc
    (t*(1-t))*β^2 = (t*β)*((1-t)*β) := by ring
    _ ≤ ((1-t)*W)*(t*G) := h
    _ = (t*(1-t))*(W*G) := by ring

end MOC.ZhengT3Compensation
