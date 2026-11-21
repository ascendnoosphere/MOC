import MOC.Core
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-! A rational witness from the repository's regular-pencil example.
It formalizes the common-minor obstruction of the type introduced by Drury.
The mixed cost below is nonnegative at every permutation profile. -/

open BigOperators Matrix

namespace MOC

noncomputable section

private def rationalRotation : Matrix (Fin 4) (Fin 4) ℚ :=
  (1 / 51 : ℚ) • !![-37, 16, 20, -24; -8, -31, -26, -30; -12, 30, -39, 6; 32, 22, 2, -33]

def fourRotation : Matrix (Fin 4) (Fin 4) ℂ :=
  rationalRotation.map (Rat.castHom ℂ)

def minorSq (U : Matrix (Fin 4) (Fin 4) ℂ) (i k j l : Fin 4) : ℝ :=
  Complex.normSq (U i j * U k l - U i l * U k j)

def mixedCost (U : Matrix (Fin 4) (Fin 4) ℂ) : ℝ :=
  Complex.normSq (U 1 0) + Complex.normSq (U 3 2) +
    minorSq U 2 3 0 3 - minorSq U 1 2 0 1

private theorem rationalRotation_orthogonal :
    rationalRotation * rationalRotationᵀ = 1 ∧ rationalRotationᵀ * rationalRotation = 1 := by
  constructor <;> apply Matrix.ext <;> intro i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [rationalRotation, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_succ,
      Matrix.smul_apply, smul_eq_mul, Matrix.one_apply, Fin.ext_iff, Matrix.cons_val']

theorem fourRotation_unitary : IsUnitary fourRotation := by
  have hstar : fourRotationᴴ = rationalRotationᵀ.map (Rat.castHom ℂ) := by
    apply Matrix.ext
    intro i j
    simp [fourRotation, Matrix.conjTranspose_apply]
  have hone : (1 : Matrix (Fin 4) (Fin 4) ℚ).map (Rat.castHom ℂ) = 1 :=
    Matrix.map_one _ (map_zero _) (map_one _)
  constructor
  · rw [hstar, fourRotation, ← Matrix.map_mul, rationalRotation_orthogonal.1, hone]
  · rw [hstar, fourRotation, ← Matrix.map_mul, rationalRotation_orthogonal.2, hone]

private theorem rationalCost :
    let U := rationalRotation
    U 1 0 * U 1 0 + U 3 2 * U 3 2 +
      (U 2 0 * U 3 3 - U 2 3 * U 3 0) * (U 2 0 * U 3 3 - U 2 3 * U 3 0) -
      (U 1 0 * U 2 1 - U 1 1 * U 2 0) * (U 1 0 * U 2 1 - U 1 1 * U 2 0) =
        -(20 / 867 : ℚ) := by
  norm_num [rationalRotation, Matrix.smul_apply, smul_eq_mul, Matrix.cons_val']
  decide +kernel

theorem mixedCost_fourRotation : mixedCost fourRotation = -(20 / 867 : ℝ) := by
  simp only [mixedCost, minorSq, fourRotation, Matrix.map_apply, Rat.coe_castHom,
    ← Rat.cast_mul, ← Rat.cast_sub, Complex.normSq_ratCast, ← Rat.cast_add]
  simpa using congrArg (fun q : ℚ => (q : ℝ)) rationalCost

/-- The four indicator coordinates of the mixed cost, written on a row-to-column permutation. -/
def permutationCost (σ : Equiv.Perm (Fin 4)) : ℝ :=
  (if σ 1 = 0 then 1 else 0) + (if σ 3 = 2 then 1 else 0) +
    (if (σ 2 = 0 ∧ σ 3 = 3) ∨ (σ 2 = 3 ∧ σ 3 = 0) then 1 else 0) -
    (if (σ 1 = 0 ∧ σ 2 = 1) ∨ (σ 1 = 1 ∧ σ 2 = 0) then 1 else 0)

theorem permutationCost_nonneg (σ : Equiv.Perm (Fin 4)) : 0 ≤ permutationCost σ := by
  have h12 : σ 1 ≠ σ 2 := fun eq => by have := σ.injective eq; omega
  have h13 : σ 1 ≠ σ 3 := fun eq => by have := σ.injective eq; omega
  have h23 : σ 2 ≠ σ 3 := fun eq => by have := σ.injective eq; omega
  unfold permutationCost
  generalize σ 1 = x at *
  generalize σ 2 = y at *
  generalize σ 3 = z at *
  fin_cases x <;> fin_cases y <;> fin_cases z <;>
    norm_num [Fin.ext_iff, show ((3 : Fin 4) : ℕ) = 3 from rfl] at *

private theorem permMatrix_entry (σ : Equiv.Perm (Fin 4)) (i j : Fin 4) :
    σ.permMatrix ℂ i j = if σ i = j then 1 else 0 := by
  simp [PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, eq_comm]

private theorem minorSq_permMatrix (σ : Equiv.Perm (Fin 4)) (i k j l : Fin 4) (hjl : j ≠ l) :
    minorSq (σ.permMatrix ℂ) i k j l =
      if (σ i = j ∧ σ k = l) ∨ (σ i = l ∧ σ k = j) then 1 else 0 := by
  have product (u v : Prop) [Decidable u] [Decidable v] :
      (if u then (1 : ℂ) else 0) * (if v then 1 else 0) = if u ∧ v then 1 else 0 := by
    by_cases hu : u <;> by_cases hv : v <;> simp [hu, hv]
  simp only [minorSq, permMatrix_entry, product]
  by_cases hd : σ i = j ∧ σ k = l
  · have ho : ¬ (σ i = l ∧ σ k = j) := fun h => hjl (hd.1.symm.trans h.1)
    simp [hd, ho, hjl]
  · by_cases ho : σ i = l ∧ σ k = j <;> simp [hd, ho, hjl, Ne.symm hjl]

theorem mixedCost_permMatrix (σ : Equiv.Perm (Fin 4)) :
    mixedCost (σ.permMatrix ℂ) = permutationCost σ := by
  have bit (p : Prop) [Decidable p] :
      Complex.normSq (if p then (1 : ℂ) else 0) = if p then (1 : ℝ) else 0 := by
    by_cases hp : p <;> simp [hp]
  simp only [mixedCost, permutationCost, permMatrix_entry, minorSq_permMatrix _ _ _ _ _
    (by decide : (0 : Fin 4) ≠ 3), minorSq_permMatrix _ _ _ _ _ (by decide : (0 : Fin 4) ≠ 1),
    bit]

/-- Even just these four minor coordinates cannot share nonnegative permutation weights. -/
theorem no_common_minor_weights_fourRotation :
    ¬ ∃ w : Equiv.Perm (Fin 4) → ℝ, (∀ σ, 0 ≤ w σ) ∧
      ∑ σ, w σ * permutationCost σ = mixedCost fourRotation := by
  rintro ⟨w, hw, hm⟩
  have hn := Finset.sum_nonneg (fun σ (_ : σ ∈ Finset.univ) =>
    mul_nonneg (hw σ) (permutationCost_nonneg σ))
  rw [hm, mixedCost_fourRotation] at hn
  norm_num at hn

theorem mixedCost_fourRotation_outside_permutation_hull :
    mixedCost fourRotation ∉ convexHull ℝ (Set.range (fun σ : Equiv.Perm (Fin 4) =>
      mixedCost (σ.permMatrix ℂ))) := by
  intro h
  have hs : Set.range (fun σ : Equiv.Perm (Fin 4) => mixedCost (σ.permMatrix ℂ)) ⊆ Set.Ici 0 := by
    rintro _ ⟨σ, rfl⟩
    change 0 ≤ mixedCost (σ.permMatrix ℂ)
    rw [mixedCost_permMatrix]
    exact permutationCost_nonneg σ
  have hn := convexHull_min hs (convex_Ici (0 : ℝ)) h
  rw [mixedCost_fourRotation] at hn
  norm_num [Set.mem_Ici] at hn

end

end MOC
