import MOC.FlagSuperlevel

/-! A nonzero off-diagonal coordinate gives a circle factor on an invariant stratum. -/

open Matrix

namespace MOC

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem coordinateCircle_one (i : ι) : coordinateCircle i 1 = 1 := by
  funext j
  by_cases h : j = i <;> simp [coordinateCircle, h]

private theorem coordinateCircle_mul (i : ι) (z w : Circle) :
    coordinateCircle i (z * w) = coordinateCircle i z * coordinateCircle i w := by
  funext j
  by_cases h : j = i <;> simp [coordinateCircle, h]

private theorem continuous_coordinateCircleConj (i : ι) :
    Continuous (fun p : Circle × Matrix ι ι ℂ => coordinateTorusConj (coordinateCircle i p.1) p.2) := by
  have hc : Continuous (coordinateCircle i) := by
    apply continuous_pi
    intro j
    by_cases h : j = i
    · subst j
      simpa only [coordinateCircle, Function.update_self] using
        (continuous_id : Continuous fun z : Circle => z)
    · simpa only [coordinateCircle, Function.update_of_ne h, Pi.one_apply] using
        (continuous_const : Continuous fun _ : Circle => (1 : Circle))
  exact continuous_coordinateTorusConj.comp ((hc.comp continuous_fst).prodMk continuous_snd)

/-- The phase of a nonzero off-diagonal entry trivializes its coordinate-circle action.
The second factor consists of the matrices where that entry is positive real. -/
def coordinateCircleStratumHomeomorph (S : Set (Matrix ι ι ℂ)) {i j : ι} (hij : i ≠ j)
    (hnz : ∀ X ∈ S, X i j ≠ 0)
    (hS : ∀ X ∈ S, ∀ z : Circle, coordinateTorusConj (coordinateCircle i z) X ∈ S) :
    S ≃ₜ Circle × {X : Matrix ι ι ℂ // X ∈ S ∧ X i j = (‖X i j‖ : ℂ)} := by
  let rotate (z : Circle) (X : Matrix ι ι ℂ) := coordinateTorusConj (coordinateCircle i z) X
  let Q := {X : Matrix ι ι ℂ | X ∈ S ∧ X i j = (‖X i j‖ : ℂ)}
  have hentry (z : Circle) (X : Matrix ι ι ℂ) : rotate z X i j = (z : ℂ) * X i j :=
    coordinateTorusConj_coordinateCircle_entry X hij z
  have hrotate (z w : Circle) (X : Matrix ι ι ℂ) :
      rotate z (rotate w X) = rotate (z * w) X := by
    change _ = coordinateTorusConj (coordinateCircle i (z * w)) X
    rw [coordinateCircle_mul, coordinateTorusConj_mul] <;> rfl
  have hone (X : Matrix ι ι ℂ) : rotate 1 X = X := by
    rw [rotate, coordinateCircle_one, coordinateTorusConj_one]
  let phase (X : S) : Circle := ⟨X.val i j / (‖X.val i j‖ : ℂ),
    Metric.mem_sphere_zero_iff_norm.mpr (by
      rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _),
        div_self (norm_ne_zero_iff.mpr (hnz _ X.property))])⟩
  have hphase (X : S) : (phase X : ℂ) = X.val i j / (‖X.val i j‖ : ℂ) := rfl
  let gauge (X : S) : Q := by
    refine ⟨rotate (phase X)⁻¹ X.val, hS _ X.property _, ?_⟩
    change rotate (phase X)⁻¹ X.val i j = (‖rotate (phase X)⁻¹ X.val i j‖ : ℂ)
    have he : rotate (phase X)⁻¹ X.val i j = (‖X.val i j‖ : ℂ) := by
      rw [hentry, Circle.coe_inv, hphase, inv_div, div_mul_cancel₀ _ (hnz _ X.property)]
    rw [he, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _)]
  let assemble (v : Circle × Q) : S := ⟨rotate v.1 v.2.val, hS _ v.2.property.1 _⟩
  have hassemble (z : Circle) (Y : Q) : phase (assemble (z, Y)) = z := by
    apply Circle.ext
    rw [hphase]
    change rotate z Y.val i j / (‖rotate z Y.val i j‖ : ℂ) = (z : ℂ)
    rw [hentry, norm_mul, Circle.norm_coe, one_mul]
    have he : Y.val i j = (‖Y.val i j‖ : ℂ) := Y.property.2
    calc
      _ = (z : ℂ) * (‖Y.val i j‖ : ℂ) / (‖Y.val i j‖ : ℂ) :=
        congrArg (fun w : ℂ => (z : ℂ) * w / (‖Y.val i j‖ : ℂ)) he
      _ = _ := mul_div_cancel_right₀ _ (Complex.ofReal_ne_zero.mpr
        (norm_ne_zero_iff.mpr (hnz _ Y.property.1)))
  have hphaseContinuous : Continuous phase := by
    have he : Continuous (fun X : S => X.val i j) := continuous_subtype_val.matrix_elem i j
    exact (he.div (Complex.continuous_ofReal.comp he.norm) (fun X => Complex.ofReal_ne_zero.mpr
      (norm_ne_zero_iff.mpr (hnz _ X.property)))).subtype_mk _
  have hrotateContinuous : Continuous (fun p : Circle × Matrix ι ι ℂ => rotate p.1 p.2) :=
    continuous_coordinateCircleConj i
  have hgaugeContinuous : Continuous gauge :=
    (hrotateContinuous.comp ((hphaseContinuous.inv).prodMk continuous_subtype_val)).subtype_mk _
  have hassembleContinuous : Continuous assemble :=
    (hrotateContinuous.comp (continuous_fst.prodMk
      (continuous_subtype_val.comp continuous_snd))).subtype_mk _
  refine
    { toFun := fun X => (phase X, gauge X)
      invFun := assemble
      left_inv := ?_
      right_inv := ?_
      continuous_toFun := hphaseContinuous.prodMk hgaugeContinuous
      continuous_invFun := hassembleContinuous }
  · intro X
    apply Subtype.ext
    change rotate (phase X) (rotate (phase X)⁻¹ X.val) = X.val
    rw [hrotate, mul_inv_cancel, hone]
  · rintro ⟨z, Y⟩
    apply Prod.ext
    · exact hassemble z Y
    · apply Subtype.ext
      change rotate (phase (assemble (z, Y)))⁻¹ (rotate z Y.val) = Y.val
      rw [hassemble, hrotate, inv_mul_cancel, hone]

/-- Conditions that selected off-diagonal entries vanish are preserved by
the diagonal torus. Each resulting superlevel stratum with a nonzero pivot
has an explicit circle factor. -/
def flagSuperlevelCircleStratum (a b : ι → ℂ) (η : ℂ) (r : ℝ)
    (Z : Set (ι × ι)) (i j : ι) : Set (Matrix ι ι ℂ) :=
  {X | X ∈ flagDeterminantSuperlevel a b η r ∧ X i j ≠ 0 ∧
    ∀ p ∈ Z, X p.1 p.2 = 0}

def flagSuperlevelCircleStratumHomeomorph (a b : ι → ℂ) (η : ℂ) (r : ℝ)
    (Z : Set (ι × ι)) {i j : ι} (hij : i ≠ j) :
    let S := flagSuperlevelCircleStratum a b η r Z i j
    S ≃ₜ Circle × {X : Matrix ι ι ℂ // X ∈ S ∧ X i j = (‖X i j‖ : ℂ)} := by
  dsimp only
  apply coordinateCircleStratumHomeomorph _ hij (fun _ hX => hX.2.1)
  intro X hX z
  refine ⟨coordinateTorusConj_mem_flagDeterminantSuperlevel hX.1 _, ?_, ?_⟩
  · rw [coordinateTorusConj_coordinateCircle_entry X hij]
    exact mul_ne_zero (Circle.coe_ne_zero z) hX.2.1
  · intro p hp
    rw [coordinateTorusConj_entry, hX.2.2 p hp, mul_zero, zero_mul]

end

end MOC
