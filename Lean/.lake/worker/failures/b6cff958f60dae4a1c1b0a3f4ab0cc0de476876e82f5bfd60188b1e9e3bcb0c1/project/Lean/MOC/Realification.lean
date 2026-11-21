import MOC.TwoValues
import Mathlib.LinearAlgebra.UnitaryGroup

/-! The squared-minor expansion transfers convex combinations of real orthogonal minor tables
to determinant values. Zheng's order-four result invokes this implication after constructing
the two real orthogonal tables. -/

open BigOperators Matrix

namespace MOC

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A common affine combination of squared minors gives the same affine combination of
determinant values, for every pair of spectra. -/
theorem determinantValue_of_subsetMinorSq_combination
    (a b : ι → ℂ) {U V W : Matrix ι ι ℂ}
    (hU : IsUnitary U) (hV : IsUnitary V) (hW : IsUnitary W) (t : ℝ)
    (hminor : ∀ I J : Finset ι,
      subsetMinorSq U I J = t * subsetMinorSq V I J + (1 - t) * subsetMinorSq W I J) :
    determinantValue a b U = t • determinantValue a b V + (1 - t) • determinantValue a b W := by
  rw [determinantValue_eq_sum_subsetMinors a b U hU, determinantValue_eq_sum_subsetMinors a b V hV,
    determinantValue_eq_sum_subsetMinors a b W hW]
  simp only [Complex.real_smul, Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro J _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro I _
  push_cast [hminor I J]
  ring

/-- Convexity transfers the Marcus–de Oliveira inclusion across a common minor mixture. -/
theorem holds_of_subsetMinorSq_convex_combination
    (a b : ι → ℂ) {U V W : Matrix ι ι ℂ}
    (hU : IsUnitary U) (hV : IsUnitary V) (hW : IsUnitary W)
    (t : ℝ) (ht : 0 ≤ t) (ht' : t ≤ 1)
    (hminor : ∀ I J : Finset ι,
      subsetMinorSq U I J = t * subsetMinorSq V I J + (1 - t) * subsetMinorSq W I J)
    (hVH : Holds a b V) (hWH : Holds a b W) : Holds a b U := by
  unfold Holds at *
  rw [determinantValue_of_subsetMinorSq_combination a b hU hV hW t hminor]
  exact (convex_convexHull ℝ (Set.range (matchingProduct a b)))
    hVH hWH ht (sub_nonneg.mpr ht') (by ring)

/-- A real orthogonal matrix becomes unitary under the real-to-complex scalar embedding. -/
theorem isUnitary_ofReal_orthogonal (O : Matrix.orthogonalGroup ι ℝ) :
    IsUnitary (Complex.ofRealHom.mapMatrix O.val) := by
  let f : Matrix ι ι ℝ →+* Matrix ι ι ℂ := Complex.ofRealHom.mapMatrix
  have hc : (f O.val)ᴴ = f O.valᵀ := by
    ext i j
    change star ((O.val j i : ℝ) : ℂ) = ((O.val j i : ℝ) : ℂ)
    exact Complex.conj_ofReal (O.val j i)
  change IsUnitary (f O.val)
  constructor
  · rw [hc, ← f.map_mul]
    have h : O.val * O.valᵀ = 1 := (Matrix.mem_orthogonalGroup_iff ι ℝ).mp O.property
    rw [h, f.map_one]
  · rw [hc, ← f.map_mul]
    have h : O.valᵀ * O.val = 1 := (Matrix.mem_orthogonalGroup_iff' ι ℝ).mp O.property
    rw [h, f.map_one]

/-- Marcus–de Oliveira with real orthogonal relative eigenbases and arbitrary complex spectra. -/
def OrthogonalConjecture (ι : Type*) [Fintype ι] [DecidableEq ι] : Prop :=
  ∀ (a b : ι → ℂ) (O : Matrix.orthogonalGroup ι ℝ), Holds a b (Complex.ofRealHom.mapMatrix O.val)

/-- Zheng's two-endpoint minor decomposition, stated as a hypothesis for the transfer. -/
def TwoOrthogonalMinorTables (ι : Type*) [Fintype ι] [DecidableEq ι] : Prop :=
  ∀ (U : Matrix ι ι ℂ), IsUnitary U →
    ∃ (P Q : Matrix.orthogonalGroup ι ℝ) (t : ℝ), 0 ≤ t ∧ t ≤ 1 ∧
      ∀ I J : Finset ι, subsetMinorSq U I J =
        t * subsetMinorSq (Complex.ofRealHom.mapMatrix P.val) I J +
          (1 - t) * subsetMinorSq (Complex.ofRealHom.mapMatrix Q.val) I J

/-- The order-four realification implication works in any size satisfying the minor hypothesis. -/
theorem conjecture_iff_orthogonal_of_minor_convexification (hminor : TwoOrthogonalMinorTables ι) :
    Conjecture ι ↔ OrthogonalConjecture ι := by
  constructor
  · intro h a b O
    exact h a b _ (isUnitary_ofReal_orthogonal O)
  · intro h a b U hU
    obtain ⟨P, Q, t, h0, h1, hm⟩ := hminor U hU
    exact holds_of_subsetMinorSq_convex_combination a b hU (isUnitary_ofReal_orthogonal P)
      (isUnitary_ofReal_orthogonal Q) t h0 h1 hm (h a b P) (h a b Q)

end

end MOC
