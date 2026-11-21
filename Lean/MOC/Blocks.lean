import MOC.Weights
import Mathlib.Algebra.Algebra.Bilinear

/-! Direct-sum closure (Rodtes, bibliography entry 23) and the repository's
block cases. Combining two convex witnesses uses multiplication in ℂ. -/

open BigOperators Matrix

namespace MOC

noncomputable section

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem mul_mem_of_mem_convexHulls {s t K : Set ℂ} (hK : Convex ℝ K)
    (hprod : ∀ x ∈ s, ∀ y ∈ t, x * y ∈ K)
    {x y : ℂ} (hx : x ∈ convexHull ℝ s) (hy : y ∈ convexHull ℝ t) :
    x * y ∈ K := by
  have hleft (u : ℂ) (hu : u ∈ s) : u * y ∈ K := by
    exact convexHull_min (fun v hv => hprod u hu v hv)
      (hK.linear_preimage (LinearMap.mulLeft ℝ u)) hy
  exact convexHull_min hleft (hK.linear_preimage (LinearMap.mulRight ℝ y)) hx

omit [DecidableEq ι] [DecidableEq κ] in
theorem matchingProduct_sum (a b : ι → ℂ) (c d : κ → ℂ)
    (σ : Equiv.Perm ι) (τ : Equiv.Perm κ) :
    matchingProduct (Sum.elim a c) (Sum.elim b d) (Equiv.sumCongr σ τ) =
      matchingProduct a b σ * matchingProduct c d τ := by
  simp [matchingProduct, Fintype.prod_sum_type]

/-- Concatenating two covered blocks produces a covered normal pair. -/
theorem holds_directSum (a b : ι → ℂ) (c d : κ → ℂ)
    (U : Matrix ι ι ℂ) (V : Matrix κ κ ℂ) (hU : Holds a b U) (hV : Holds c d V) :
    Holds (Sum.elim a c) (Sum.elim b d) (fromBlocks U 0 0 V) := by
  have hd : determinantValue (Sum.elim a c) (Sum.elim b d) (fromBlocks U 0 0 V) =
      determinantValue a b U * determinantValue c d V := by
    unfold determinantValue
    rw [← Matrix.fromBlocks_diagonal, ← Matrix.fromBlocks_diagonal,
      Matrix.fromBlocks_conjTranspose]
    simp only [Matrix.fromBlocks_multiply, Matrix.fromBlocks_add, Matrix.det_fromBlocks_zero₂₁,
      Matrix.conjTranspose_zero, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add]
  unfold Holds at *
  rw [hd]
  apply mul_mem_of_mem_convexHulls (convex_convexHull ℝ _) _ hU hV
  rintro _ ⟨σ, rfl⟩ _ ⟨τ, rfl⟩
  rw [← matchingProduct_sum]
  exact matchingProduct_mem_hull _ _ _

theorem unitary_directSum {U : Matrix ι ι ℂ} {V : Matrix κ κ ℂ}
    (hU : IsUnitary U) (hV : IsUnitary V) : IsUnitary (fromBlocks U 0 0 V) := by
  constructor <;>
    simp [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply,
      hU.1, hU.2, hV.1, hV.2]

theorem unitary_directSum_iff {U : Matrix ι ι ℂ} {V : Matrix κ κ ℂ} :
    IsUnitary (fromBlocks U 0 0 V) ↔ IsUnitary U ∧ IsUnitary V := by
  constructor
  · intro h
    unfold IsUnitary at h
    simp only [Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_zero,
      Matrix.fromBlocks_multiply, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add,
      ← Matrix.fromBlocks_one, Matrix.fromBlocks_inj, and_true, true_and] at h
    exact ⟨⟨h.1.1, h.2.1⟩, ⟨h.1.2, h.2.2⟩⟩
  · rintro ⟨hU, hV⟩
    exact unitary_directSum hU hV

theorem holds_blocks_of_conjectures (hι : Conjecture ι) (hκ : Conjecture κ)
    (a b : ι → ℂ) (c d : κ → ℂ) (U : Matrix ι ι ℂ) (V : Matrix κ κ ℂ)
    (hU : IsUnitary U) (hV : IsUnitary V) :
    Holds (Sum.elim a c) (Sum.elim b d) (fromBlocks U 0 0 V) :=
  holds_directSum a b c d U V (hι a b U hU) (hκ c d V hV)

end

end MOC
