import MOC.FourHodgeBlockGenerators
import MOC.FourHodgeCrossRotation
import Mathlib.Tactic.NormNum

/-! Every real special orthogonal matrix on the Hodge basis lifts to a special unitary. -/

open Matrix

namespace MOC

noncomputable section

private def fourHodgeImage : Submonoid (Matrix HodgeIndex HodgeIndex ℝ) where
  carrier := {R | ∃ U : Matrix (Fin 4) (Fin 4) ℂ, IsUnitary U ∧ U.det = 1 ∧
    fourHodgeRealRepresentation U = R}
  one_mem' := ⟨1, isUnitary_one, Matrix.det_one, fourHodgeRealRepresentation_one⟩
  mul_mem' := by
    rintro R S ⟨U, hU, hdU, rfl⟩ ⟨V, hV, hdV, rfl⟩
    have hv : (U * V) * (U * V)ᴴ = 1 := by
      rw [Matrix.conjTranspose_mul]
      calc
        (U * V) * (Vᴴ * Uᴴ) = U * (V * Vᴴ) * Uᴴ := by simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hV.1, Matrix.mul_one, hU.1]
    exact ⟨U * V, ⟨hv, Matrix.mul_eq_one_comm.mp hv⟩,
      by rw [Matrix.det_mul, hdU, hdV, one_mul],
      fourHodgeRealRepresentation_mul U V hU hV hdU hdV⟩

private theorem fourHodgeImage_orthogonal_transpose {Q : Matrix HodgeIndex HodgeIndex ℝ}
    (hQ : Q ∈ fourHodgeImage) : Qᵀ * Q = 1 ∧ Qᵀ ∈ fourHodgeImage := by
  change (∃ U : Matrix (Fin 4) (Fin 4) ℂ, IsUnitary U ∧ U.det = 1 ∧
    fourHodgeRealRepresentation U = Q) at hQ
  obtain ⟨U, hU, hdet, rfl⟩ := hQ
  have horth := fourHodgeRealRepresentation_orthogonal U hU hdet
  have hUadj : IsUnitary Uᴴ := by
    exact ⟨by simpa only [Matrix.conjTranspose_conjTranspose] using hU.2,
      by simpa only [Matrix.conjTranspose_conjTranspose] using hU.1⟩
  have hdadj : Uᴴ.det = 1 := by rw [Matrix.det_conjTranspose, hdet, star_one]
  have hprod : fourHodgeRealRepresentation Uᴴ * fourHodgeRealRepresentation U = 1 := by
    rw [← fourHodgeRealRepresentation_mul Uᴴ U hUadj hU hdadj hdet, hU.2,
      fourHodgeRealRepresentation_one]
  refine ⟨Matrix.mul_eq_one_comm.mp horth, Uᴴ, hUadj, hdadj, ?_⟩
  calc
    fourHodgeRealRepresentation Uᴴ =
        (fourHodgeRealRepresentation Uᴴ * fourHodgeRealRepresentation U) *
          (fourHodgeRealRepresentation U)ᵀ := by rw [Matrix.mul_assoc, horth, Matrix.mul_one]
    _ = (fourHodgeRealRepresentation U)ᵀ := by rw [hprod, Matrix.one_mul]

private theorem fourHodgeImage_transport
    {Q : Matrix HodgeIndex HodgeIndex ℝ} (hQ : Q ∈ fourHodgeImage)
    {i j p q : HodgeIndex} (hij : i ≠ j) (hpq : p ≠ q)
    (hi : ∀ k, Q k i = (1 : Matrix HodgeIndex HodgeIndex ℝ) k p)
    (hj : ∀ k, Q k j = (1 : Matrix HodgeIndex HodgeIndex ℝ) k q) {c s : ℝ}
    (h : realCoordinateRotation i j c s ∈ fourHodgeImage) :
    realCoordinateRotation p q c s ∈ fourHodgeImage := by
  obtain ⟨horth, htrans⟩ := fourHodgeImage_orthogonal_transpose hQ
  rw [← realCoordinateRotation_conjugate Q horth hij hpq hi hj]
  exact fourHodgeImage.mul_mem (fourHodgeImage.mul_mem hQ h) htrans

private def fourHodgeCycleIndex : Equiv.Perm HodgeIndex :=
  fourHodgeBlockCycle.prodCongr (Equiv.refl (Fin 2))

private theorem fourHodgeCycleIndex_apply (p : HodgeIndex) :
    fourHodgeCycleIndex p = (fourHodgeBlockCycle p.1, p.2) := by
  rcases p with ⟨a, b⟩
  rfl

private theorem fourHodgeBlockCycle_zero : fourHodgeBlockCycle 0 = 1 := by decide
private theorem fourHodgeBlockCycle_one : fourHodgeBlockCycle 1 = 2 := by decide
private theorem fourHodgeBlockCycle_two : fourHodgeBlockCycle 2 = 0 := by decide

private theorem fourHodgeImage_cycle {i j : HodgeIndex} (hij : i ≠ j) {c s : ℝ}
    (h : realCoordinateRotation i j c s ∈ fourHodgeImage) :
    realCoordinateRotation (fourHodgeCycleIndex i) (fourHodgeCycleIndex j) c s ∈
      fourHodgeImage := by
  let Q : Matrix HodgeIndex HodgeIndex ℝ :=
    fun p q => if p = (fourHodgeBlockCycle q.1, q.2) then 1 else 0
  have hQ : Q ∈ fourHodgeImage := fourHodge_block_cycle_lifts
  have hcol (p k : HodgeIndex) : Q k p =
      (1 : Matrix HodgeIndex HodgeIndex ℝ) k (fourHodgeCycleIndex p) := by
    simp only [Q, Matrix.one_apply, fourHodgeCycleIndex_apply]
  exact fourHodgeImage_transport hQ hij (fourHodgeCycleIndex.injective.ne hij) (hcol i) (hcol j) h

private theorem fourHodgeImage_within_block (a : Fin 3) (c s : ℝ)
    (h : c ^ 2 + s ^ 2 = 1) :
    realCoordinateRotation ((a, 0) : HodgeIndex) (a, 1) c s ∈ fourHodgeImage := by
  have h0 : realCoordinateRotation ((0, 0) : HodgeIndex) (0, 1) c s ∈ fourHodgeImage :=
    fourHodge_block_zero_rotation_lifts c s h
  have h1 : realCoordinateRotation ((1, 0) : HodgeIndex) (1, 1) c s ∈ fourHodgeImage := by
    simpa only [fourHodgeCycleIndex_apply, fourHodgeBlockCycle_zero] using
      fourHodgeImage_cycle (by decide : ((0, 0) : HodgeIndex) ≠ (0, 1)) h0
  have h2 : realCoordinateRotation ((2, 0) : HodgeIndex) (2, 1) c s ∈ fourHodgeImage := by
    simpa only [fourHodgeCycleIndex_apply, fourHodgeBlockCycle_one] using
      fourHodgeImage_cycle (by decide : ((1, 0) : HodgeIndex) ≠ (1, 1)) h1
  fin_cases a
  · exact h0
  · exact h1
  · exact h2

private theorem fourHodgeImage_cycle_plane (a : Fin 3) (c s : ℝ)
    (h : c ^ 2 + s ^ 2 = 1) :
    realCoordinateRotation ((a, 0) : HodgeIndex) (fourHodgeBlockCycle a, 0) c s ∈
      fourHodgeImage := by
  have h12 : realCoordinateRotation ((1, 0) : HodgeIndex) (2, 0) c s ∈ fourHodgeImage :=
    exists_fourHodgeCrossRotation c s h
  have h20 : realCoordinateRotation ((2, 0) : HodgeIndex) (0, 0) c s ∈ fourHodgeImage := by
    simpa only [fourHodgeCycleIndex_apply, fourHodgeBlockCycle_one, fourHodgeBlockCycle_two] using
      fourHodgeImage_cycle (by decide : ((1, 0) : HodgeIndex) ≠ (2, 0)) h12
  have h01 : realCoordinateRotation ((0, 0) : HodgeIndex) (1, 0) c s ∈ fourHodgeImage := by
    simpa only [fourHodgeCycleIndex_apply, fourHodgeBlockCycle_two, fourHodgeBlockCycle_zero] using
      fourHodgeImage_cycle (by decide : ((2, 0) : HodgeIndex) ≠ (0, 0)) h20
  fin_cases a
  · simpa only [fourHodgeBlockCycle_zero] using h01
  · simpa only [fourHodgeBlockCycle_one] using h12
  · simpa only [fourHodgeBlockCycle_two] using h20

private theorem fourHodgeImage_first_axes {a b : Fin 3} (hab : a ≠ b) (c s : ℝ)
    (h : c ^ 2 + s ^ 2 = 1) :
    realCoordinateRotation ((a, 0) : HodgeIndex) (b, 0) c s ∈ fourHodgeImage := by
  by_cases hcycle : fourHodgeBlockCycle a = b
  · rw [← hcycle]
    exact fourHodgeImage_cycle_plane a c s h
  have hreverse : fourHodgeBlockCycle b = a := by
    fin_cases a <;> fin_cases b <;>
      norm_num [fourHodgeBlockCycle_zero, fourHodgeBlockCycle_one, fourHodgeBlockCycle_two]
        at hab hcycle ⊢
  have hba : ((b, 0) : HodgeIndex) ≠ (a, 0) := fun he => hab.symm (congrArg Prod.fst he)
  rw [realCoordinateRotation_swap hba, ← hreverse]
  exact fourHodgeImage_cycle_plane b c (-s) (by simpa only [neg_sq] using h)

private theorem fourHodgeImage_block_axis (a : Fin 3) (u : Fin 2) :
    ∃ Q ∈ fourHodgeImage,
      (∀ k, Q k (a, 0) = (1 : Matrix HodgeIndex HodgeIndex ℝ) k (a, u)) ∧
      (∀ p : HodgeIndex, p.1 ≠ a → ∀ k, Q k p = (1 : Matrix HodgeIndex HodgeIndex ℝ) k p) := by
  fin_cases u
  · exact ⟨1, fourHodgeImage.one_mem, fun _ => rfl, fun _ _ _ => rfl⟩
  let i : HodgeIndex := (a, 0)
  let j : HodgeIndex := (a, 1)
  have hij : i ≠ j := fun he => (by decide : (0 : Fin 2) ≠ 1) (congrArg Prod.snd he)
  let Q := realCoordinateRotation i j 0 1
  refine ⟨Q, fourHodgeImage_within_block a 0 1 (by norm_num), ?_, ?_⟩
  · change ∀ k, Q k i = (1 : Matrix HodgeIndex HodgeIndex ℝ) k j
    intro k
    by_cases hki : k = i
    · subst k
      simp [Q, realCoordinateRotation, Matrix.one_apply, hij]
    by_cases hkj : k = j
    · subst k
      simp [Q, realCoordinateRotation, Matrix.one_apply, hij.symm]
    simp [Q, realCoordinateRotation, Matrix.one_apply, hki, hkj]
  · intro p hp k
    have hpi : p ≠ i := fun he => hp (congrArg Prod.fst he)
    have hpj : p ≠ j := fun he => hp (congrArg Prod.fst he)
    by_cases hki : k = i
    · subst k
      simp [Q, realCoordinateRotation, Matrix.one_apply, hpi, hpj, hpi.symm]
    by_cases hkj : k = j
    · subst k
      simp [Q, realCoordinateRotation, Matrix.one_apply, hij.symm, hpi, hpj, hpj.symm]
    simp [Q, realCoordinateRotation, Matrix.one_apply, hki, hkj]

private theorem fourHodgeImage_rotation {i j : HodgeIndex} (hij : i ≠ j) {c s : ℝ}
    (hcs : c ^ 2 + s ^ 2 = 1) : realCoordinateRotation i j c s ∈ fourHodgeImage := by
  rcases i with ⟨a, u⟩
  rcases j with ⟨b, v⟩
  by_cases hab : a = b
  · subst b
    fin_cases u <;> fin_cases v
    · exact (hij rfl).elim
    · exact fourHodgeImage_within_block a c s hcs
    · have hne : ((a, 0) : HodgeIndex) ≠ (a, 1) := hij.symm
      rw [realCoordinateRotation_swap hne]
      exact fourHodgeImage_within_block a c (-s) (by simpa only [neg_sq] using hcs)
    · exact (hij rfl).elim
  have hne (u v : Fin 2) : ((a, u) : HodgeIndex) ≠ (b, v) :=
    fun he => hab (congrArg Prod.fst he)
  obtain ⟨P, hP, hPa, hPfixed⟩ := fourHodgeImage_block_axis a u
  obtain ⟨Q, hQ, hQb, hQfixed⟩ := fourHodgeImage_block_axis b v
  have hfirst : realCoordinateRotation ((a, u) : HodgeIndex) (b, 0) c s ∈ fourHodgeImage :=
    fourHodgeImage_transport hP (hne 0 0) (hne u 0) hPa (hPfixed (b, 0) hab.symm)
      (fourHodgeImage_first_axes hab c s hcs)
  exact fourHodgeImage_transport hQ (hne u 0) (hne u v) (hQfixed (a, u) hab) hQb hfirst

/-- Every six-dimensional real orthogonal matrix of determinant one has a lift under
the exterior-square representation of the special unitary group in dimension four. -/
theorem fourHodgeRealRepresentation_surjective (R : Matrix HodgeIndex HodgeIndex ℝ)
    (hR : Rᵀ * R = 1) (hdet : R.det = 1) :
    ∃ U : Matrix (Fin 4) (Fin 4) ℂ, IsUnitary U ∧ U.det = 1 ∧
      fourHodgeRealRepresentation U = R := by
  have himage : realCoordinateRotationMonoid HodgeIndex ≤ fourHodgeImage := by
    unfold realCoordinateRotationMonoid
    apply Submonoid.closure_le.mpr
    rintro _ ⟨i, j, c, s, hij, hcs, rfl⟩
    exact fourHodgeImage_rotation hij hcs
  exact himage (realCoordinateRotationMonoid_of_orthogonal_det R hR hdet)

end

end MOC
