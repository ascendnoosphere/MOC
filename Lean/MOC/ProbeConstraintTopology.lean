import MOC.ContinuousWeightProbes
import Mathlib.Topology.Homotopy.Equiv

/-! An explicit deformation retraction of the union of probe constraints
onto the boundary of the simplex of equations. -/

open BigOperators Finset
open scoped unitInterval

namespace MOC.ProbeWitness

noncomputable section

variable {κ : Type*} [Fintype κ] {k : ℕ}

/-- Probability laws satisfying at least one probe equation. -/
abbrev ConstraintUnion (d : ProbeWitness κ k) :=
  {w : κ → ℝ // (∀ p, 0 ≤ w p) ∧ (∑ p, w p = 1) ∧ ∃ j, d.signedError w j = 0}

/-- Probability vectors on the probes with at least one coordinate zero. -/
abbrev SimplexBoundary (k : ℕ) :=
  {u : Fin (k + 1) → ℝ // (∀ j, 0 ≤ u j) ∧ (∑ j, u j = 1) ∧ ∃ j, u j = 0}

private def positiveError (d : ProbeWitness κ k) (w : d.ConstraintUnion)
    (j : Fin (k + 1)) : ℝ :=
  max (d.signedError w.val j) 0

private theorem sum_positiveError_pos (d : ProbeWitness κ k) (w : d.ConstraintUnion) :
    0 < ∑ j, d.positiveError w j := by
  apply d.gap_pos.trans_le
  exact (d.sum_signedError_ge w.val w.property.1).trans
    (sum_le_sum fun j _ => le_max_left _ _)

private theorem continuous_signedError (d : ProbeWitness κ k) (j : Fin (k + 1)) :
    Continuous (fun w : κ → ℝ => d.signedError w j) := by
  induction j using Fin.cases with
  | zero =>
    simp only [signedError, Fin.cases_zero, expectation]
    fun_prop
  | succ j =>
    simp only [signedError, Fin.cases_succ, expectation]
    fun_prop

private theorem continuous_positiveError (d : ProbeWitness κ k) (j : Fin (k + 1)) :
    Continuous (fun w => d.positiveError w j) :=
  ((d.continuous_signedError j).comp continuous_subtype_val).max continuous_const

/-- Keep only positive signed errors, then normalize their sum. -/
def projectToBoundary (d : ProbeWitness κ k) : C(d.ConstraintUnion, SimplexBoundary k) where
  toFun w := by
    refine ⟨fun j => d.positiveError w j / (∑ l, d.positiveError w l), ?_, ?_, ?_⟩
    · intro j
      exact div_nonneg (le_max_right _ _) (d.sum_positiveError_pos w).le
    · rw [← sum_div, div_self (d.sum_positiveError_pos w).ne']
    · obtain ⟨j, hj⟩ := w.property.2.2
      exact ⟨j, by simp [positiveError, hj]⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro j
    exact (d.continuous_positiveError j).div
      (continuous_finset_sum _ fun l _ => d.continuous_positiveError l)
      (fun w => (d.sum_positiveError_pos w).ne')

/-- A boundary vector gives a law on the selected permutations. -/
def boundaryToLaw (d : ProbeWitness κ k) : C(SimplexBoundary k, d.ConstraintUnion) where
  toFun u := by
    refine ⟨d.law u.val, d.law_nonneg _ u.property.1, d.law_sum _ u.property.2.1, ?_⟩
    obtain ⟨j, hj⟩ := u.property.2.2
    exact ⟨j, by rw [d.signedError_law _ u.property.2.1, hj, mul_zero]⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro p
    unfold law
    apply continuous_finset_sum
    intro a _
    split_ifs
    · unfold mass
      induction a using Fin.cases with
      | zero =>
        simp only [Fin.cases_zero]
        fun_prop
      | succ a =>
        simp only [Fin.cases_succ]
        fun_prop
    · exact continuous_const

theorem project_boundaryToLaw (d : ProbeWitness κ k) (u : SimplexBoundary k) :
    d.projectToBoundary (d.boundaryToLaw u) = u := by
  have he (j : Fin (k + 1)) :
      d.positiveError (d.boundaryToLaw u) j = d.gap * u.val j := by
    unfold positiveError
    change max (d.signedError (d.law u.val) j) 0 = _
    rw [d.signedError_law _ u.property.2.1,
      max_eq_left (mul_nonneg d.gap_pos.le (u.property.1 j))]
  have hs : (∑ l, d.positiveError (d.boundaryToLaw u) l) = d.gap := by
    simp_rw [he, ← mul_sum, u.property.2.1, mul_one]
  apply Subtype.ext
  funext j
  change d.positiveError (d.boundaryToLaw u) j /
    (∑ l, d.positiveError (d.boundaryToLaw u) l) = u.val j
  rw [he, hs]
  apply (div_eq_iff d.gap_pos.ne').mpr
  exact mul_comm _ _

private theorem solved_coordinate_retract (d : ProbeWitness κ k)
    (w : d.ConstraintUnion) (j : Fin (k + 1)) (hj : d.signedError w.val j = 0) :
    d.signedError (d.boundaryToLaw (d.projectToBoundary w)).val j = 0 := by
  have hz : (d.projectToBoundary w).val j = 0 := by
    change d.positiveError w j / _ = 0
    simp [positiveError, hj]
  change d.signedError (d.law (d.projectToBoundary w).val) j = 0
  rw [d.signedError_law _ (d.projectToBoundary w).property.2.1, hz, mul_zero]

private theorem signedError_eq_zero_iff (d : ProbeWitness κ k)
    (w : κ → ℝ) (j : Fin (k + 1)) :
    d.signedError w j = 0 ↔ d.expectation w j = d.target j := by
  induction j using Fin.cases with
  | zero => simp only [signedError, Fin.cases_zero, sub_eq_zero, eq_comm]
  | succ j => simp only [signedError, Fin.cases_succ, sub_eq_zero]

private def interpolation (d : ProbeWitness κ k) (t : I) (w : d.ConstraintUnion) :
    d.ConstraintUnion := by
  let v := d.boundaryToLaw (d.projectToBoundary w)
  let f : κ → ℝ := fun p => (t : ℝ) * w.val p + (1 - (t : ℝ)) * v.val p
  refine ⟨f, ?_, ?_, ?_⟩
  · intro p
    exact add_nonneg (mul_nonneg t.property.1 (w.property.1 p))
      (mul_nonneg (sub_nonneg.mpr t.property.2) (v.property.1 p))
  · simp only [f, sum_add_distrib, ← mul_sum, w.property.2.1, v.property.2.1, mul_one]
    ring
  · obtain ⟨j, hj⟩ := w.property.2.2
    have hv := (d.signedError_eq_zero_iff _ _).mp (d.solved_coordinate_retract w j hj)
    have hw := (d.signedError_eq_zero_iff _ _).mp hj
    refine ⟨j, (d.signedError_eq_zero_iff _ _).mpr ?_⟩
    calc
      d.expectation f j = (t : ℝ) * d.expectation w.val j +
          (1 - (t : ℝ)) * d.expectation v.val j := by
        simp only [expectation, f, add_mul, sum_add_distrib, mul_assoc, mul_sum]
      _ = _ := by rw [hw, hv]; ring

/-- The straight-line homotopy stays within every constraint already
satisfied at its starting law. -/
def constraintUnion_homotopy (d : ProbeWitness κ k) :
    ContinuousMap.Homotopy (d.boundaryToLaw.comp d.projectToBoundary)
      (ContinuousMap.id _) where
  toFun tw := d.interpolation tw.1 tw.2
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro p
    change Continuous (fun tw : I × d.ConstraintUnion =>
      (tw.1 : ℝ) * tw.2.val p + (1 - (tw.1 : ℝ)) *
        (d.boundaryToLaw (d.projectToBoundary tw.2)).val p)
    fun_prop
  map_zero_left w := by
    apply Subtype.ext
    funext p
    simp [interpolation]
  map_one_left w := by
    apply Subtype.ext
    funext p
    simp [interpolation]

/-- For either finite fixture, the union of the exact constraints has the
homotopy type of the indicated simplex boundary. -/
def constraintUnion_homotopyEquiv (d : ProbeWitness κ k) :
    ContinuousMap.HomotopyEquiv d.ConstraintUnion (SimplexBoundary k) where
  toFun := d.projectToBoundary
  invFun := d.boundaryToLaw
  left_inv := ⟨d.constraintUnion_homotopy⟩
  right_inv := by
    have he : d.projectToBoundary.comp d.boundaryToLaw = ContinuousMap.id _ := by
      ext u
      exact d.project_boundaryToLaw u
    rw [he]
    exact ContinuousMap.Homotopic.refl _

end

end MOC.ProbeWitness
