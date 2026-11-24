import MOC.FourParityCorrection

/-! The exact feasibility threshold of the displacement-label parity
repair on the left-quaternion shape proportional to `(1,1,1,t)`.
This is a scalar classification of that repair, not a necessity result
for arbitrary matching laws or for MOC. -/

namespace MOC

/-- The translation weights, two-label weights, and correction for a
negative three-cycle weight must be nonnegative. The variables are the
four real displacement-label coefficients; they may have either sign. -/
def QuaternionShapeRepair (t a b c d : ℝ) : Prop :=
  1 ≤ a+b+c+d ∧
  (0 ≤ 1+4*t*a ∧ 0 ≤ 1+4*t*b ∧ 0 ≤ 1+4*t*c ∧ 0 ≤ t^4+4*t*d) ∧
  (2*t*(a+b) ≤ 1 ∧ 2*t*(a+c) ≤ 1 ∧ 2*t*(b+c) ≤ 1) ∧
  (2*t*(a+d) ≤ t^2 ∧ 2*t*(b+d) ≤ t^2 ∧ 2*t*(c+d) ≤ t^2)

/-- Only the fourth translation weight, three mixed weights, and a
negative three-cycle are needed to force the cubic threshold. -/
theorem quaternionShapeRepair_cubic_necessary {t a b c d : ℝ} (ht : 0 < t)
    (hs : 1 ≤ a+b+c+d) (hd : 0 ≤ t^4+4*t*d)
    (ha : 2*t*(a+d) ≤ t^2) (hb : 2*t*(b+d) ≤ t^2)
    (hc : 2*t*(c+d) ≤ t^2) : 0 ≤ t^3+3*t-2 := by
  have h2t : 0 < 2*t := by positivity
  have hda : a+d ≤ t/2 := by
    apply (le_of_mul_le_mul_left · h2t)
    calc
      2*t*(a+d) ≤ t^2 := ha
      _ = 2*t*(t/2) := by ring
  have hdb : b+d ≤ t/2 := by
    apply (le_of_mul_le_mul_left · h2t)
    calc
      2*t*(b+d) ≤ t^2 := hb
      _ = 2*t*(t/2) := by ring
  have hdc : c+d ≤ t/2 := by
    apply (le_of_mul_le_mul_left · h2t)
    calc
      2*t*(c+d) ≤ t^2 := hc
      _ = 2*t*(t/2) := by ring
  have hdd : 0 ≤ t^3+4*d := by
    apply nonneg_of_mul_nonneg_right _ ht
    calc
      0 ≤ t^4+4*t*d := hd
      _ = t*(t^3+4*d) := by ring
  linarith

/-- Exact threshold within the displacement-label correction ansatz.
The sufficiency witness allows a signed fourth coefficient. -/
theorem quaternionShapeRepair_feasible_iff {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1) :
    (∃ a b c d, QuaternionShapeRepair t a b c d) ↔ 0 ≤ t^3+3*t-2 := by
  constructor
  · rintro ⟨a, b, c, d, hs, ⟨_, _, _, hd⟩, _, ha, hb, hc⟩
    exact quaternionShapeRepair_cubic_necessary ht hs hd ha hb hc
  · intro h
    obtain ⟨hs, hw, hv, hp, hq⟩ := nearBalancedParityCorrection_signed ht.le ht' h
    refine ⟨(2-t)/4, (2-t)/4, (2-t)/4, (3*t-2)/4, ?_, ⟨hw, hw, hw, hv⟩,
      ⟨hp, hp, hp⟩, ⟨hq.le, hq.le, hq.le⟩⟩
    linarith

end MOC
