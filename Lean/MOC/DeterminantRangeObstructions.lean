import MOC.ContinuousWeightCounterexample
import MOC.OrderSixDeterminantWinding

/-! Nonconvex determinant ranges and a nonmonomial support maximizer. -/

open Matrix
open scoped unitInterval

namespace MOC

/-- A bound on distance from zero alone does not imply hull membership
even for a singleton comparison set. -/
theorem exists_modulus_bound_without_hull_membership :
    ∃ z p : ℂ, ‖z‖ ≤ ‖p‖ ∧ z ∉ convexHull ℝ ({p} : Set ℂ) := by
  refine ⟨-1, 1, by simp, ?_⟩
  rw [convexHull_singleton, Set.mem_singleton_iff]
  norm_num

/-- The order-six range contains opposite nonzero real points and omits zero. -/
theorem orderSix_determinantRange_not_convex :
    ¬ Convex ℝ (determinantRange orderSixWindingLeft orderSixWindingRight) := by
  intro hc
  let half : I := ⟨1 / 2, by norm_num, by norm_num⟩
  have hhalf : orderSixDeterminantWindingLoop half = 32768 := by
    change ((32 : ℂ) + ((32 * Real.sqrt 3 * (2 * (1 / 2 : ℝ) - 1) : ℝ) : ℂ) *
      Complex.I) ^ 3 = 32768
    norm_num
  have hp : (32768 : ℂ) ∈ determinantRange orderSixWindingLeft orderSixWindingRight :=
    hhalf ▸ orderSixDeterminantWindingLoop_mem half
  have hn : (-262144 : ℂ) ∈ determinantRange orderSixWindingLeft orderSixWindingRight :=
    orderSixDeterminantWindingLoop_endpoints.1 ▸ orderSixDeterminantWindingLoop_mem 0
  have hz := hc hp hn (by norm_num : 0 ≤ (8 / 9 : ℝ)) (by norm_num : 0 ≤ (1 / 9 : ℝ))
    (by norm_num : (8 / 9 : ℝ) + 1 / 9 = 1)
  have he : (8 / 9 : ℝ) • (32768 : ℂ) + (1 / 9 : ℝ) • (-262144 : ℂ) = 0 := by
    apply Complex.ext <;>
      norm_num [Complex.real_smul, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im]
  exact zero_notMem_orderSixDeterminantRange (he ▸ hz)

/-- A unitary with two nonzero entries in one row can maximize a
determinant support functional. The scalar spectra make the determinant
constant on the unitary orbit. -/
theorem exists_nonmonomial_support_maximizer :
    ∃ (a b : Fin 4 → ℂ) (U : Matrix (Fin 4) (Fin 4) ℂ), IsUnitary U ∧
      (∀ V : Matrix (Fin 4) (Fin 4) ℂ, IsUnitary V →
        (determinantValue a b V).re ≤ (determinantValue a b U).re) ∧
      U 0 0 ≠ 0 ∧ U 0 1 ≠ 0 := by
  refine ⟨fun _ => 1, fun _ => 0, ContinuousWeightCounterexample.mixer,
    ContinuousWeightCounterexample.isUnitary_mixer, ?_, ?_, ?_⟩
  · intro V _
    simp only [determinantValue, Matrix.diagonal_one, Matrix.diagonal_zero, Matrix.mul_zero,
      Matrix.zero_mul, add_zero] <;> exact le_rfl
  · change (1 / 7 : ℂ) * GaussianInt.toComplex 1 ≠ 0
    norm_num
  · change (1 / 7 : ℂ) * GaussianInt.toComplex 4 ≠ 0
    norm_num

end MOC
