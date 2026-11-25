import MOC.MatchingProfileCompactness
import Mathlib.Logic.Relation
import Mathlib.Tactic.LinearCombination

/-! The nonzero entries of a rank-two kernel permit short directed paths. -/

open Matrix

namespace MOC

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem short_nonzero_triplet (K : Matrix ι ι ℂ) (hK : VanishingThreeMinors K)
    {i a b j : ι} (hia : K i a ≠ 0) (hab : K a b ≠ 0) (hbj : K b j ≠ 0) :
    K i j ≠ 0 ∨ ∃ k, K i k ≠ 0 ∧ K k j ≠ 0 := by
  by_cases hij : K i j ≠ 0
  · exact Or.inl hij
  by_cases haj : K a j ≠ 0
  · exact Or.inr ⟨a, hia, haj⟩
  by_cases hib : K i b ≠ 0
  · exact Or.inr ⟨b, hib, hbj⟩
  exfalso
  have hdet := hK ![i, a, b] ![a, b, j]
  have hprod : K i a * K a b * K b j = 0 := by
    simpa [Matrix.det_fin_three, Matrix.submatrix_apply, not_ne_iff.mp hij,
      not_ne_iff.mp haj, not_ne_iff.mp hib] using hdet
  exact (mul_ne_zero (mul_ne_zero hia hab) hbj) hprod

/-- Every reachable entry of a diagonal-nonzero rank-two kernel can be
reached in at most two edges of its nonzero-entry graph. -/
theorem rankTwo_support_reach_in_two (K : Matrix ι ι ℂ) (hK : VanishingThreeMinors K)
    (hd : ∀ i, K i i ≠ 0) {i j : ι}
    (h : Relation.ReflTransGen (fun a b => K a b ≠ 0) i j) :
    K i j ≠ 0 ∨ ∃ k, K i k ≠ 0 ∧ K k j ≠ 0 := by
  induction h with
  | refl => exact Or.inl (hd i)
  | @tail b c _ hbc ih =>
    obtain hib | ⟨a, hia, hab⟩ := ih
    · exact Or.inr ⟨b, hib, hbc⟩
    · exact short_nonzero_triplet K hK hia hab hbc

/-- With diagonal entries one, a rank-two kernel has at most two
strongly connected components in its nonzero-entry graph. -/
theorem rankTwo_mutually_reachable_of_three (K : Matrix ι ι ℂ) (hK : VanishingThreeMinors K)
    (hd : ∀ i, K i i = 1) (v : Fin 3 → ι) :
    ∃ i j : Fin 3, i ≠ j ∧
      Relation.ReflTransGen (fun a b => K a b ≠ 0) (v i) (v j) ∧
      Relation.ReflTransGen (fun a b => K a b ≠ 0) (v j) (v i) := by
  by_contra h
  have hpair (i j : Fin 3) (hij : i ≠ j) : K (v i) (v j) * K (v j) (v i) = 0 := by
    by_contra hprod
    exact h ⟨i, j, hij, Relation.ReflTransGen.single (fun hz => hprod (by rw [hz, zero_mul])),
      Relation.ReflTransGen.single (fun hz => hprod (by rw [hz, mul_zero]))⟩
  have hcycle (i j k : Fin 3) (hij : i ≠ j) :
      K (v i) (v j) * K (v j) (v k) * K (v k) (v i) = 0 := by
    by_contra hprod
    have h₁ : K (v i) (v j) ≠ 0 := fun hz => hprod (by rw [hz, zero_mul, zero_mul])
    have h₂ : K (v j) (v k) ≠ 0 := fun hz => hprod (by rw [hz, mul_zero, zero_mul])
    have h₃ : K (v k) (v i) ≠ 0 := fun hz => hprod (by rw [hz, mul_zero])
    exact h ⟨i, j, hij, Relation.ReflTransGen.single h₁,
      (Relation.ReflTransGen.single h₂).tail h₃⟩
  have hdet : (K.submatrix v v).det = 1 := by
    simp only [Matrix.det_fin_three, Matrix.submatrix_apply, hd, one_mul, mul_one]
    linear_combination -hpair 0 1 (by decide) - hpair 0 2 (by decide) - hpair 1 2 (by decide) +
      hcycle 0 1 2 (by decide) + hcycle 0 2 1 (by decide)
  exact zero_ne_one ((hK v v).symm.trans hdet)

end MOC
