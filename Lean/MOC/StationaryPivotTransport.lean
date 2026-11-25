import MOC.StationaryFullSupport
import Mathlib.Data.Real.Sqrt

/-! A dense symbolic obstruction to requiring an admissible pivot for
every real orthogonal matrix of order four. This is not a spectral
stationary-point obstruction or a counterexample to MOC. -/

open Matrix

namespace MOC.StationaryFullSupport

noncomputable def quaternionMixer (a b c d : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![a, -b, -c, -d; b, a, -d, c; c, d, a, -b; d, -c, b, a]

theorem quaternionMixer_orthogonal {a b c d : ℝ} (h : a*a + b*b + c*c + d*d = 1) :
    quaternionMixer a b c d * (quaternionMixer a b c d)ᵀ = 1 ∧
    (quaternionMixer a b c d)ᵀ * quaternionMixer a b c d = 1 := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [quaternionMixer, Matrix.mul_apply, Fin.sum_univ_four, Matrix.one_apply] <;>
    linarith [h]

theorem quaternionMixer_dense {a b c d : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (hd : 0 < d) (i j : Fin 4) : quaternionMixer a b c d i j ≠ 0 := by
  fin_cases i <;> fin_cases j <;>
    simp [quaternionMixer, ne_of_gt ha, ne_of_gt hb, ne_of_gt hc, ne_of_gt hd]

/-- Signed basis action of right multiplication by a basis quaternion. -/
private def move (k : Fin 4) : Fin 4 → Fin 4 :=
  ![![0,1,2,3], ![1,0,3,2], ![2,3,0,1], ![3,2,1,0]] k

private def sgn (k : Fin 4) : Fin 4 → ℝ :=
  ![![1,1,1,1], ![1,-1,-1,1], ![1,1,-1,-1], ![1,-1,1,-1]] k

private theorem move_self (k i : Fin 4) : move k (move k i) = i := by
  fin_cases k <;> fin_cases i <;> rfl

private theorem move_zero (k : Fin 4) : move k 0 = k := by
  fin_cases k <;> rfl

private theorem sgn_sq (k i : Fin 4) : sgn k i * sgn k i = 1 := by
  fin_cases k <;> fin_cases i <;> norm_num [sgn]

/-- Left and right basis actions commute; in entries this is a
simultaneous signed permutation. The entry calculation verifies that
identity, not a test of candidate pivots. -/
private theorem move_entry (a b c d : ℝ) (k r s : Fin 4) :
    quaternionMixer a b c d (move k r) (move k s) =
      sgn k r * sgn k s * quaternionMixer a b c d r s := by
  fin_cases k <;> fin_cases r <;> fin_cases s <;> norm_num [move, sgn, quaternionMixer] <;> rfl

private def BadRect (U : Matrix (Fin 4) (Fin 4) ℝ) (i j r s : Fin 4) : Prop :=
  (U i j * U r s) * (U i j * U r s - U r j * U i s) < 0

private theorem bad_move {a b c d : ℝ} {i j r s : Fin 4}
    (k : Fin 4) (h : BadRect (quaternionMixer a b c d) i j r s) :
    BadRect (quaternionMixer a b c d) (move k i) (move k j) (move k r) (move k s) := by
  unfold BadRect at *
  simp only [move_entry]
  have hcalc : ∀ x y z w u v p q : ℝ, x*x = 1 → y*y = 1 → z*z = 1 → w*w = 1 →
      ((x*y*u)*(z*w*v))*((x*y*u)*(z*w*v)-(z*y*p)*(x*w*q)) =
      (u*v)*(u*v-p*q) := by
    intro x y z w u v p q hx hy hz hw
    calc
      _ = (x*x)*(y*y)*(z*z)*(w*w)*((u*v)*(u*v-p*q)) := by ring
      _ = _ := by simp [hx, hy, hz, hw]
  rw [hcalc _ _ _ _ _ _ _ _ (sgn_sq k i) (sgn_sq k j) (sgn_sq k r) (sgn_sq k s)]
  exact h

private theorem first_row_bad {a b c d : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (hd : 0 < d) (h₁ : a*d < b*c) (h₂ : b*d < a*c)
    (h₃ : c*d < a*b) (j : Fin 4) :
    ∃ r s, r ≠ 0 ∧ BadRect (quaternionMixer a b c d) 0 j r s := by
  fin_cases j
  · refine ⟨1, 2, by decide, ?_⟩
    change (a * (-d)) * (a * (-d) - b * (-c)) < 0
    apply mul_neg_of_neg_of_pos
    · linarith [mul_pos ha hd]
    · linarith
  · refine ⟨3, 0, by decide, ?_⟩
    change ((-b) * d) * ((-b) * d - (-c) * a) < 0
    apply mul_neg_of_neg_of_pos
    · linarith [mul_pos hb hd]
    · linarith
  · refine ⟨2, 1, by decide, ?_⟩
    change ((-c) * d) * ((-c) * d - a * (-b)) < 0
    apply mul_neg_of_neg_of_pos
    · linarith [mul_pos hc hd]
    · linarith
  · refine ⟨1, 1, by decide, ?_⟩
    change ((-d) * a) * ((-d) * a - c * (-b)) < 0
    apply mul_neg_of_neg_of_pos
    · linarith [mul_pos ha hd]
    · linarith

/-- This entire open region on the unit quaternion sphere gives dense
orthogonal mixers for which every pivot has a strictly negative
corrected singleton. One cannot close the dense case by requiring all
orthogonal mixers to have an admissible pivot. -/
theorem quaternionMixer_no_admissible_pivot {a b c d : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (h₁ : a*d < b*c) (h₂ : b*d < a*c) (h₃ : c*d < a*b) (i j : Fin 4) :
    ∃ (r s : Fin 4), corrected (quaternionMixer a b c d) i j r s < 0 := by
  obtain ⟨r, s, hr, hbad⟩ := first_row_bad ha hb hc hd h₁ h₂ h₃ (move i j)
  have hbad' := bad_move i hbad
  rw [move_zero, move_self] at hbad'
  have hri : move i r ≠ i := by
    intro he
    have he' := congrArg (move i) (he.trans (move_zero i).symm)
    rw [move_self, move_self] at he'
    exact hr he'
  refine ⟨move i r, move i s, lt_of_not_ge ?_⟩
  intro hn
  exact (not_le_of_gt hbad') ((corrected_nonneg_iff (quaternionMixer a b c d) (quaternionMixer_dense ha hb hc hd i j) hri).mp hn)


/-- For every shape parameter strictly between zero and one there is
such a dense orthogonal mixer. The proof is symbolic normalization,
not a search for matrix entries or signs. -/
theorem exists_dense_orthogonal_mixer_no_admissible_pivot {t : ℝ}
    (ht : 0 < t) (ht' : t < 1) :
    ∃ U : Matrix (Fin 4) (Fin 4) ℝ,
      U * Uᵀ = 1 ∧ Uᵀ * U = 1 ∧
      (∀ i j, U i j ≠ 0) ∧
      ∀ i j, ∃ r s, corrected U i j r s < 0 := by
  let q := Real.sqrt (3 + t * t)
  have hq : 0 < q := by
    change 0 < Real.sqrt (3 + t * t)
    exact Real.sqrt_pos.2 (by nlinarith [sq_nonneg t])
  have hq2 : q ^ 2 = 3 + t*t := Real.sq_sqrt (by nlinarith [sq_nonneg t])
  let x := 1 / q
  have hx : 0 < x := one_div_pos.mpr hq
  have htx : 0 < t*x := mul_pos ht hx
  have hn : x*x + x*x + x*x + (t*x)*(t*x) = 1 := by
    dsimp [x]
    field_simp
    nlinarith [hq2]
  have hdom : x * (t*x) < x*x :=
    mul_lt_mul_of_pos_left (by simpa using mul_lt_mul_of_pos_right ht' hx) hx
  obtain ⟨ho, ho'⟩ := quaternionMixer_orthogonal hn
  exact ⟨quaternionMixer x x x (t*x), ho, ho',
    quaternionMixer_dense hx hx hx htx,
    quaternionMixer_no_admissible_pivot hx hx hx htx hdom hdom hdom⟩

end MOC.StationaryFullSupport
