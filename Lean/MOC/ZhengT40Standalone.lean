import MOC.ZhengT40RotationBound
import Mathlib.Tactic.Positivity

/-! Two seven-contact boundaries of Zheng's standalone T40 pattern
(DOI: 10.13140/RG.2.2.36790.25923). The normalized mixed coefficient is
one. The sign theorem is conditional on the exact secant polynomial;
the projection and Hessian calculation are explained separately. -/

namespace MOC.ZhengT40Standalone

/-- The reduced Hessian factor for the boundary with gap 15 zero. -/
def boundaryFactor (b d s C D : ℝ) : ℝ :=
  let lam := C*D
  (D+1)*(d+1)*((1-lam)*(1+C+b)+C^2*b) +
    s*((d+1)*(C*(1-lam)+C*D^2+D^2+D+1) +
      b*((d+1)*(C-D)^2+lam+C+D+1))

/-- The scalar secant condition supplies sufficient defect compensation. -/
theorem defect_product_of_boundary_factor {b d s C D : ℝ}
    (hb : 0 ≤ b) (hd : 0 ≤ d) (hs : 0 ≤ s)
    (hC : 0 ≤ C) (hD : 0 ≤ D) (h : boundaryFactor b d s C D = 0) :
    1 ≤ C*D := by
  by_contra! hl
  have hz : 0 < 1 - C*D := sub_pos.mpr hl
  have hp : 0 < (D+1)*(d+1)*((1-C*D)*(1+C+b)+C^2*b) := by positivity
  have hn : 0 ≤ s*((d+1)*(C*(1-C*D)+C*D^2+D^2+D+1) +
      b*((d+1)*(C-D)^2+C*D+C+D+1)) := by positivity
  exact (ne_of_gt (add_pos_of_pos_of_nonneg hp hn)) h

/-- The exact factor condition proves the rotation comparison for the
boundary without a positive coefficient on the complementary minor. -/
theorem rotation_of_boundary_factor (L R : ZhengT40RotationBound.Entries)
    {b d s C D : ℝ}
    (hb : 0 ≤ b) (hd : 0 ≤ d) (hs : 0 ≤ s)
    (hC : 0 ≤ C) (hD : 0 ≤ D) (h : boundaryFactor b d s C D = 0) :
    (L.b-R.b)^2 ≤ (1+D)*(L.l-R.l)^2 +
      2*(L.p^2+R.p^2) + (1+C)*(L.w-R.w)^2 :=
  ZhengT40RotationBound.rotation_bound_of_defect L R hC hD
    (defect_product_of_boundary_factor hb hd hs hC hD h)

end MOC.ZhengT40Standalone
