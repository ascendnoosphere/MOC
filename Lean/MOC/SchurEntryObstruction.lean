import MOC.Householder

/-! The exact change of a zero entry under a rank-one phase. -/

open BigOperators Matrix

namespace MOC

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A rank-one phase creates a formerly zero matrix entry with an exact
product of three squared moduli. -/
theorem rankOnePhase_entry_normSq_of_zero (U : Matrix ι ι ℂ) (v : ι → ℂ)
    (z : ℂ) (i j : ι) (hzero : U i j = 0) :
    Complex.normSq ((rankOnePhase v z * U) i j) =
      Complex.normSq (z - 1) * Complex.normSq (v i) *
        Complex.normSq (∑ k, star (v k) * U k j) := by
  have hp : (vecMulVec v (star ∘ v) * U) i j = v i * ∑ k, star (v k) * U k j := by
    simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Function.comp_apply, Finset.mul_sum,
      mul_assoc]
  rw [rankOnePhase, Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul, Matrix.add_apply,
    Matrix.smul_apply, smul_eq_mul, hzero, zero_add, hp]
  simp only [Complex.normSq_mul]
  ring

end

end MOC
