import MOC.HermitianByNormalFourFacets

/-! Integer coefficient evaluation for the weighted-diamond facet charts. -/

open Matrix

namespace MOC

private def weightedDiamondBaseForm {R : Type*} [CommRing R]
    (k : Fin 12 ⊕ Fin 4) (x : R) (σ : FourPerm) : R :=
  k.elim (fun j => weightedDiamondOrdinaryForm j x (diamondPermProfile σ))
    (fun j => weightedDiamondHardForm j x (diamondPermProfile σ))

/-- The constant, linear, and quadratic coefficients of twice a base facet
evaluated on a permutation. -/
def weightedDiamondBaseCoefficients (k : Fin 12 ⊕ Fin 4) (σ : FourPerm) : Fin 3 → ℤ :=
  let f (x : ℤ) := weightedDiamondBaseForm k x σ
  ![2 * f 0, f 1 - f (-1), f 1 + f (-1) - 2 * f 0]

set_option maxHeartbeats 1800000 in
private theorem weightedDiamondBaseForm_cast (k : Fin 12 ⊕ Fin 4) (σ : FourPerm) (x : ℤ) :
    ((weightedDiamondBaseForm k x σ : ℤ) : ℝ) = weightedDiamondBaseForm k (x : ℝ) σ := by
  rcases k with k | k <;> fin_cases k <;>
    simp only [weightedDiamondBaseForm, Sum.elim_inl, Sum.elim_inr, weightedDiamondOrdinaryForm,
      weightedDiamondHardForm, diamondPermProfile, Matrix.cons_val_zero', Matrix.cons_val_succ',
      zsmul_eq_mul, smul_eq_mul, Int.cast_add, Int.cast_sub, Int.cast_mul, Int.cast_neg,
      Int.cast_pow, Int.cast_ite, Int.cast_one, Int.cast_zero, Int.cast_ofNat]

set_option maxHeartbeats 600000 in
private theorem weightedDiamondBaseForm_interpolate (k : Fin 12 ⊕ Fin 4) (σ : FourPerm) (x : ℝ) :
    let f (y : ℝ) := weightedDiamondBaseForm k y σ
    2 * f x = 2 * f 0 + x * (f 1 - f (-1)) + x^2 * (f 1 + f (-1) - 2 * f 0) := by
  dsimp only
  rcases k with k | k <;> fin_cases k <;>
    simp only [weightedDiamondBaseForm, Sum.elim_inl, Sum.elim_inr, weightedDiamondOrdinaryForm,
      weightedDiamondHardForm, Matrix.cons_val_zero', Matrix.cons_val_succ', smul_eq_mul] <;> ring

private theorem weightedDiamondBaseForm_twice (k : Fin 12 ⊕ Fin 4) (σ : FourPerm) (x : ℝ) :
    let a := weightedDiamondBaseCoefficients k σ
    2 * weightedDiamondBaseForm k x σ = (a 0 : ℝ) + x * (a 1 : ℝ) + x^2 * (a 2 : ℝ) := by
  let f (z : ℤ) := weightedDiamondBaseForm k z σ
  change 2 * weightedDiamondBaseForm k x σ =
    ((2 * f 0 : ℤ) : ℝ) + x * ((f 1 - f (-1) : ℤ) : ℝ) +
      x^2 * ((f 1 + f (-1) - 2 * f 0 : ℤ) : ℝ)
  simpa only [f, Int.cast_add, Int.cast_sub, Int.cast_mul, Int.cast_ofNat, weightedDiamondBaseForm_cast,
    Int.cast_zero, Int.cast_one, Int.cast_neg] using weightedDiamondBaseForm_interpolate k σ x

/-- Evaluate a row-relabeled facet at the ratio of chart coordinates, clearing
the denominator and the factor of two used by the integer coefficients. -/
theorem weightedDiamondFacet_homogeneous (i : WeightedDiamondFacetIndex) (σ : FourPerm)
    (n d : ℝ) (hd : d ≠ 0) :
    let a := weightedDiamondBaseCoefficients i.2 (i.1⁻¹ * σ)
    2 * d^2 * weightedDiamondFacet i (n / d) (diamondPermProfile σ) =
      (a 0 : ℝ) * d^2 + (a 1 : ℝ) * n * d + (a 2 : ℝ) * n^2 := by
  dsimp only
  rw [weightedDiamondFacet_permProfile]
  change 2 * d^2 * weightedDiamondBaseForm i.2 (n / d) (i.1⁻¹ * σ) = _
  rw [mul_comm 2 (d^2), mul_assoc (d^2) 2, weightedDiamondBaseForm_twice]
  field_simp [hd]
  <;> ring

end MOC
