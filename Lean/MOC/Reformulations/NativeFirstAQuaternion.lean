import Mathlib.Analysis.Quaternion
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! The quaternion norm under unit quaternion conjugation. The metric
ingredient holds for any real inner-product imaginary subspace, including
the imaginary subspace in the rank-two octonion norm comparison. -/

open scoped Quaternion

namespace MOC.Reformulations
noncomputable section

/-- Cauchy–Schwarz gives both exact rank-two norm endpoints. -/
theorem nativeScalarImaginaryNormBounds {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (s : ℝ) (x y : E) :
    s^2 + (‖x‖ - ‖y‖)^2 ≤ s^2 + ‖x + y‖^2 ∧
      s^2 + ‖x + y‖^2 ≤ s^2 + (‖x‖ + ‖y‖)^2 := by
  obtain ⟨hlo, hhi⟩ := abs_le.mp (abs_real_inner_le_norm x y)
  rw [norm_add_sq_real]
  constructor <;> nlinarith only [hlo, hhi]

private theorem quaternionScalarImaginaryNorm (s : ℝ) (v : ℍ[ℝ]) (hv : v.re = 0) :
    Quaternion.normSq ((s : ℍ[ℝ]) + v) = s ^ 2 + ‖v‖ ^ 2 := by
  rw [pow_two ‖v‖, ← Quaternion.normSq_eq_norm_mul_self]
  simp [Quaternion.normSq_def', hv]; ring

/-- The quaternion algebra statement, using star for inversion at unit norm. -/
theorem nativeUnitQuaternionNormHull (s t : ℝ) (v w u : ℍ[ℝ])
    (hv : v.re = 0) (hw : w.re = 0) (hu : ‖u‖ = 1) :
    let z := Quaternion.normSq ((s : ℍ[ℝ]) + v + u * ((t : ℍ[ℝ]) + w) * star u)
    (s + t)^2 + (‖v‖ - ‖w‖)^2 ≤ z ∧ z ≤ (s + t)^2 + (‖v‖ + ‖w‖)^2 := by
  let r := u * w * star u
  have hru : ‖r‖ = ‖w‖ := by simp [r, norm_mul, Quaternion.norm_star, hu]
  have hstar : star w = -w := by
    ext <;> simp [hw]
  have hrs : star r = -r := by
    simp only [r, star_mul, star_star, hstar, neg_mul, mul_neg]
    rw [mul_assoc u w (star u)]
  have hrr : r.re = 0 := by
    have he := congrArg (fun q : ℍ[ℝ] => q.re) hrs
    simp at he
    linarith
  have huu : u * star u = 1 := by
    rw [Quaternion.self_mul_star, Quaternion.normSq_eq_norm_mul_self, hu, mul_one]
    simp
  have ht : u * (t : ℍ[ℝ]) * star u = (t : ℍ[ℝ]) := by
    rw [← Quaternion.coe_commutes t u, mul_assoc, huu, mul_one]
  have he : ((s : ℍ[ℝ]) + v + u * ((t : ℍ[ℝ]) + w) * star u) =
      ((s + t : ℝ) : ℍ[ℝ]) + (v + r) := by
    rw [mul_add, add_mul, ht, Quaternion.coe_add]
    unfold r
    abel
  dsimp only
  rw [he, quaternionScalarImaginaryNorm _ _ (by simp [hv, hrr])]
  simpa only [hru] using nativeScalarImaginaryNormBounds (s + t) v r

end
end MOC.Reformulations
