import MOC.ContactCensus
import MOC.OrthogonalOrientationTrace
import MOC.SubsetAssignmentSupport

/-! The 24 permutations of four labels act as the orientation-preserving
assignments of the three complementary pairs of doubletons. -/

open BigOperators Finset Matrix

namespace MOC

local notation "FourPair" => SubsetLayer (Fin 4) 2

/-- Doubletons grouped into the three complementary pairs, with the
sets containing zero listed first in each pair. -/
def fourBlockPair (p : Fin 3 × Fin 2) : FourPair :=
  ⟨(![![{0, 1}, {2, 3}], ![{0, 2}, {3, 1}], ![{0, 3}, {1, 2}]] p.1) p.2, by
    rcases p with ⟨i, j⟩
    fin_cases i <;> fin_cases j <;> decide⟩

set_option maxRecDepth 4096 in
set_option maxHeartbeats 3000000 in
/-- Every doubleton occurs at exactly one complementary pair coordinate. -/
theorem fourBlockPair_bijective : Function.Bijective fourBlockPair := by
  have h₁ : ∀ p q : Fin 3 × Fin 2, fourBlockPair p = fourBlockPair q → p = q := by
    decide +kernel
  have h₂ : ∀ I : FourPair, ∃ p : Fin 3 × Fin 2, fourBlockPair p = I := by
    decide +kernel
  refine ⟨?_, h₂⟩
  intro p q hpq
  exact h₁ p q hpq

/-- The complementary coordinates enumerate the doubletons. -/
noncomputable def fourBlockPairEquiv : Fin 3 × Fin 2 ≃ FourPair :=
  Equiv.ofBijective fourBlockPair fourBlockPair_bijective

/-- Apply a permutation of the blocks and optionally exchange the two
coordinates in each source block. -/
def fourBlockAssignment (π : Equiv.Perm (Fin 3)) (flip : Fin 3 → Bool)
    (q : Fin 3 × Fin 2) : Fin 3 × Fin 2 :=
  (π q.1, if flip q.1 then (if q.2 = 0 then 1 else 0) else q.2)

/-- The determinant sign of the local coordinate assignment. -/
def fourBlockSign (flip : Bool) : ℤ := if flip then -1 else 1

/-- Sending a column doubleton to its row image gives this signed
assignment on the three complementary pairs. -/
def fourBlockRepresents (σ : Equiv.Perm (Fin 4)) (π : Equiv.Perm (Fin 3))
    (flip : Fin 3 → Bool) : Prop :=
  ∀ q : Fin 3 × Fin 2, (fourBlockPair q).val.map σ.toEmbedding =
    (fourBlockPair (fourBlockAssignment π flip q)).val

instance (σ : Equiv.Perm (Fin 4)) (π : Equiv.Perm (Fin 3)) (flip : Fin 3 → Bool) :
    Decidable (fourBlockRepresents σ π flip) := by
  unfold fourBlockRepresents
  infer_instance

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
/-- Every permutation gives an assignment with an even number of exchanges. -/
theorem exists_oriented_assignment_of_fourPerm (σ : Equiv.Perm (Fin 4)) :
    ∃ (π : Equiv.Perm (Fin 3)) (flip : Fin 3 → Bool),
      (∏ j, fourBlockSign (flip j)) = 1 ∧ fourBlockRepresents σ π flip := by
  have h : ∀ p : Fin 24, ∃ (π : Equiv.Perm (Fin 3)) (flip : Fin 3 → Bool),
      (∏ j, fourBlockSign (flip j)) = 1 ∧ fourBlockRepresents (fourPerm p) π flip := by
    intro p
    fin_cases p <;> decide +kernel
  obtain ⟨p, rfl⟩ := fourPerm_surjective σ
  exact h p

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
/-- Every orientation-preserving signed assignment comes from a
permutation of the original four labels. -/
theorem exists_fourPerm_of_oriented_assignment (π : Equiv.Perm (Fin 3)) (flip : Fin 3 → Bool)
    (hflip : (∏ j, fourBlockSign (flip j)) = 1) :
    ∃ σ : Equiv.Perm (Fin 4), fourBlockRepresents σ π flip := by
  have h : ∀ (ρ : Equiv.Perm (Fin 3)) (ε : Fin 3 → Bool),
      (∏ j, fourBlockSign (ε j)) = 1 → ∃ p : Fin 24, fourBlockRepresents (fourPerm p) ρ ε := by
    decide +kernel
  obtain ⟨p, hp⟩ := h π flip hflip
  exact ⟨fourPerm p, hp⟩

noncomputable section

/-- The mean of the two assignment costs in a block. -/
def fourBlockNormCost (C : FourPair → FourPair → ℝ) (i j : Fin 3) : ℝ :=
  (C (fourBlockPair (i, 0)) (fourBlockPair (j, 0)) +
    C (fourBlockPair (i, 1)) (fourBlockPair (j, 1)) +
    C (fourBlockPair (i, 0)) (fourBlockPair (j, 1)) +
    C (fourBlockPair (i, 1)) (fourBlockPair (j, 0))) / 2

/-- Half the cost difference between the two orientations in a block. -/
def fourBlockDetCost (C : FourPair → FourPair → ℝ) (i j : Fin 3) : ℝ :=
  (C (fourBlockPair (i, 0)) (fourBlockPair (j, 0)) +
    C (fourBlockPair (i, 1)) (fourBlockPair (j, 1)) -
    C (fourBlockPair (i, 0)) (fourBlockPair (j, 1)) -
    C (fourBlockPair (i, 1)) (fourBlockPair (j, 0))) / 2

/-- The cost of a signed assignment, with one summand per source block. -/
def fourOrientedAssignmentCost (C : FourPair → FourPair → ℝ) (π : Equiv.Perm (Fin 3))
    (flip : Fin 3 → Bool) : ℝ :=
  ∑ j, fourBlockNormCost C (π j) j + (fourBlockSign (flip j) : ℝ) * fourBlockDetCost C (π j) j

/-- A permutation doubleton cost equals its oriented assignment cost. -/
theorem fourPairPermutationCost_eq_oriented_assignment
    (C : FourPair → FourPair → ℝ) (σ : Equiv.Perm (Fin 4)) (π : Equiv.Perm (Fin 3))
    (flip : Fin 3 → Bool) (h : fourBlockRepresents σ π flip) :
    (∑ J : FourPair, ∑ I : FourPair, C I J * (if J.val.map σ.toEmbedding = I.val then 1 else 0)) =
      fourOrientedAssignmentCost C π flip := by
  classical
  let e := fourBlockPairEquiv
  have hsum (q : Fin 3 × Fin 2) :
      (∑ I : FourPair, C I (fourBlockPair q) *
        (if (fourBlockPair q).val.map σ.toEmbedding = I.val then 1 else 0)) =
        C (fourBlockPair (fourBlockAssignment π flip q)) (fourBlockPair q) := by
    let I₀ := fourBlockPair (fourBlockAssignment π flip q)
    rw [h q, Finset.sum_eq_single_of_mem I₀ (Finset.mem_univ I₀)]
    · simp only [I₀, if_pos rfl, mul_one]
    · intro I _ hI
      have hne : I₀.val ≠ I.val := fun he => hI (Subtype.ext he.symm)
      simp only [I₀, hne, if_false, mul_zero]
  rw [← Equiv.sum_comp e (fun J : FourPair => ∑ I : FourPair,
    C I J * (if J.val.map σ.toEmbedding = I.val then 1 else 0))]
  change (∑ q : Fin 3 × Fin 2, ∑ I : FourPair, C I (fourBlockPair q) *
    (if (fourBlockPair q).val.map σ.toEmbedding = I.val then 1 else 0)) = _
  simp only [hsum]
  rw [Fintype.sum_prod_type, fourOrientedAssignmentCost]
  apply Finset.sum_congr rfl
  intro j _
  rw [Fin.sum_univ_two]
  cases hflip : flip j <;>
    simp [fourBlockAssignment, hflip, fourBlockSign, fourBlockNormCost, fourBlockDetCost] <;> ring

/-- The block of a real matrix on the two coordinates of each pair. -/
def fourHodgeRealBlock (R : Matrix (Fin 3 × Fin 2) (Fin 3 × Fin 2) ℝ) (i j : Fin 3) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of fun a b => R (i, a) (j, b)

/-- The quadratic objective on the real exterior-square coordinates. -/
def fourHodgeQuadraticCost (C : FourPair → FourPair → ℝ)
    (R : Matrix (Fin 3 × Fin 2) (Fin 3 × Fin 2) ℝ) : ℝ :=
  ∑ j, ∑ i, fourBlockNormCost C i j * ((∑ a, ∑ b, (fourHodgeRealBlock R i j a b)^2) / 2) +
    fourBlockDetCost C i j * (fourHodgeRealBlock R i j).det

/-- The cost of the two squared amplitudes in a block has the grouped
square-norm and determinant form. -/
theorem fourHodgeQuadraticCost_eq_amplitudes (C : FourPair → FourPair → ℝ)
    (R : Matrix (Fin 3 × Fin 2) (Fin 3 × Fin 2) ℝ) :
    fourHodgeQuadraticCost C R =
      ∑ j : Fin 3, ∑ i : Fin 3, ∑ b : Fin 2, ∑ a : Fin 2,
        C (fourBlockPair (i, a)) (fourBlockPair (j, b)) *
          orientedPlaneAmplitude (a == b) (fourHodgeRealBlock R i j) ^ 2 := by
  unfold fourHodgeQuadraticCost
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  simp [Fin.sum_univ_two, orientedPlaneAmplitude_sq, fourBlockNormCost, fourBlockDetCost] <;> ring

end

end MOC
