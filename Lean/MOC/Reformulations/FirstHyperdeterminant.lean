import MOC.StrongSupport
import Mathlib.Data.Matrix.Notation
import Mathlib.Tactic.NormNum

/-! The intrinsic 2 × 2 × 2 specialization of atlas entry 023 is false.
The invariant here is Cayley's polynomial, in its two-slice discriminant
normalization. The evaluated finite spectral layer is a different statement. -/

open BigOperators Matrix

namespace MOC.Reformulations
noncomputable section

abbrev TensorTwo := Fin 2 → Fin 2 → Fin 2 → ℂ

/-- Discriminant of `det(slice₀ + t • slice₁)`, the Cayley
hyperdeterminant in format 2 × 2 × 2. -/
def cayleyHyperdeterminant (T : TensorTwo) : ℂ :=
  let A := T 0 0 0 * T 1 1 0 - T 0 1 0 * T 1 0 0
  let B := T 0 0 0 * T 1 1 1 + T 0 0 1 * T 1 1 0
    - T 0 1 0 * T 1 0 1 - T 0 1 1 * T 1 0 0
  let C := T 0 0 1 * T 1 1 1 - T 0 1 1 * T 1 0 1
  B ^ 2 - 4 * A * C

/-- Tensor with its two prescribed all-mode diagonal entries. -/
def diagonalTensorTwo (a : Fin 2 → ℂ) : TensorTwo :=
  fun i j k => if i = k ∧ j = k then a k else 0

/-- The first two modes receive a unitary and its complex conjugate. The
third mode retains the original label. -/
def firstTwoModeOrbit (b : Fin 2 → ℂ) (U : Matrix (Fin 2) (Fin 2) ℂ) : TensorTwo :=
  fun i j k => U i k * star (U j k) * b k

def cayleyDiagonalOrbitHull : Prop :=
  ∀ (a b : Fin 2 → ℂ) (U : Matrix (Fin 2) (Fin 2) ℂ), IsUnitary U →
    cayleyHyperdeterminant (diagonalTensorTwo a + firstTwoModeOrbit b U) ∈
      convexHull ℝ (Set.range fun σ : Equiv.Perm (Fin 2) =>
        cayleyHyperdeterminant (diagonalTensorTwo a + diagonalTensorTwo (b ∘ σ)))

private def flipTwo : Matrix (Fin 2) (Fin 2) ℂ :=
  (Equiv.swap (0 : Fin 2) 1).permMatrix ℂ

private theorem flipTwo_unitary : IsUnitary flipTwo :=
  isUnitary_permMatrix (Equiv.swap (0 : Fin 2) 1)

private theorem diagonalTensorSum_hdet (a b : Fin 2 → ℂ) :
    cayleyHyperdeterminant (diagonalTensorTwo a + diagonalTensorTwo b) =
      ((a 0 + b 0) * (a 1 + b 1)) ^ 2 := by
  norm_num [cayleyHyperdeterminant, diagonalTensorTwo, Pi.add_apply]

/-- All comparison vertices are 4; the actual two-mode unitary orbit gives
9. In particular the intrinsic higher-order comparison cannot be used as
an equivalent of MOC. -/
theorem cayleyDiagonalOrbitHull_false : ¬ cayleyDiagonalOrbitHull := by
  let a : Fin 2 → ℂ := ![1, 1]
  let b : Fin 2 → ℂ := ![1, -2]
  intro h
  have h9 : cayleyHyperdeterminant (diagonalTensorTwo a + firstTwoModeOrbit b flipTwo) = 9 := by
    norm_num [a, b, cayleyHyperdeterminant, diagonalTensorTwo, firstTwoModeOrbit,
      flipTwo, PEquiv.toMatrix_toPEquiv_apply, Pi.single_apply, Pi.add_apply]
  have h4 (σ : Equiv.Perm (Fin 2)) :
      cayleyHyperdeterminant (diagonalTensorTwo a + diagonalTensorTwo (b ∘ σ)) = 4 := by
    rw [diagonalTensorSum_hdet]
    change ((1 + b (σ 0)) * (1 + b (σ 1))) ^ 2 = 4
    have hp := Equiv.prod_comp σ (fun i => 1 + b i)
    rw [Fin.prod_univ_two, Fin.prod_univ_two] at hp
    rw [hp]
    norm_num [b]
  have hset : (Set.range fun σ : Equiv.Perm (Fin 2) =>
        cayleyHyperdeterminant (diagonalTensorTwo a + diagonalTensorTwo (b ∘ σ))) =
      {4} := by
    ext z
    constructor
    · rintro ⟨σ, rfl⟩
      exact Set.mem_singleton_iff.mpr (h4 σ)
    · intro hz
      exact ⟨1, (h4 1).trans (Set.mem_singleton_iff.mp hz).symm⟩
  have hv := h a b flipTwo flipTwo_unitary
  rw [h9, hset, convexHull_singleton, Set.mem_singleton_iff] at hv
  norm_num at hv

end
end MOC.Reformulations
