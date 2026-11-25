import MOC.WeightedDiamondHardFacets

/-! The other twelve weighted-diamond facets are nonnegative sums of
ordinary squared minors with coefficients polynomial in `x`. -/

open BigOperators Matrix

namespace MOC

private abbrev DiamondProfile (M : Type*) := Finset (Fin 4) → Finset (Fin 4) → M

/-- The ordinary forms for census indices `0,1,2,3,4,5,6,7,8,10,13,14`.
For indices 4, 7 and 10 the formula is multiplied by `x` to clear the
positive denominator. -/
def weightedDiamondOrdinaryForm {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (k : Fin 12) (x : R) (m : Finset (Fin 4) → Finset (Fin 4) → M) : M :=
  let c := m ∅ ∅
  let p (i : Fin 4) := m {i} {0}
  let q (i : Fin 4) := m {i} {3}
  let r (i j : Fin 4) := m {i,j} {0,1} + (1+x) • m {i,j} {0,2}
  ![c-p 0-p 1-p 2,
    (x+2) • c-r 0 1-r 0 2-r 0 3-r 1 2-r 1 3,
    -c-(x+1) • p 0-(x+1) • p 1+r 0 1+r 0 2+r 0 3+r 1 2+r 1 3,
    q 0,
    -c-(x+1) • p 0+q 0+r 0 1+r 0 2+r 0 3,
    (x+1) • c+p 0+p 1+p 2-q 0-r 0 1-r 0 2-r 0 3-r 1 2,
    p 2-q 0+r 1 3,
    (x+1) • c+p 0-(x+1) • q 0-r 0 1-r 0 2-r 0 3,
    (x+1) • q 1+(x+1) • q 2-r 0 3,
    -(x+1) • p 1-(x+1) • p 2+(x+1) • q 1+(x+1) • q 2-r 0 3+(x+1) • r 1 2,
    -c+p 0+p 1+p 2+q 1+r 1 3,
    -c+p 0+q 1+r 1 2+r 1 3] k

private def ordinaryBudget {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (k : Fin 12) (x : R) (m : DiamondProfile M) : M :=
  ![m {3} {0},
    (1+x) • m {0,1} {1,3} + m {0,1} {2,3},
    (1+x) • m {0,1} {1,2} + x • m {0,1} {2,3},
    m {0} {3},
    x • m {0} {2},
    m {0,3} {1,2} + x • (m {0,1} {1,3} + m {0,2} {1,3}),
    m {0,1} {1,2} + m {0,3} {1,2} + x • m {0,2} {1,3},
    x • m {0} {1},
    (1+x) • m {0,3} {1,2} + x • m {0,3} {0,1},
    x • m {0,3} {0,1} + (x+x^2) • m {0,3} {1,3},
    m {0,1} {0,3} + m {0,3} {1,2} + x • m {0,2} {1,3},
    m {0,1} {0,3} + x • (m {0,2} {1,3} + m {0,3} {1,3})] k

set_option maxHeartbeats 5000000 in
set_option maxRecDepth 5000 in
private theorem ordinary_integer_check (k : Fin 12) : ∀ (l : Fin 24),
    let m : DiamondProfile ℤ := diamondPermProfile (fourPerm l)
    let P (x : ℤ) := weightedDiamondOrdinaryForm k x m = ordinaryBudget k x m
    P 0 ∧ P 1 ∧ P (-1) := by
  fin_cases k <;> decide +kernel

set_option maxHeartbeats 1800000 in
private theorem ordinary_check_cast (k : Fin 12) (x : ℤ) (σ : FourPerm) (h :
    weightedDiamondOrdinaryForm k x (diamondPermProfile (R := ℤ) σ) =
      ordinaryBudget k x (diamondPermProfile (R := ℤ) σ)) :
    weightedDiamondOrdinaryForm k (x : ℝ) (diamondPermProfile (R := ℝ) σ) =
      ordinaryBudget k (x : ℝ) (diamondPermProfile (R := ℝ) σ) := by
  have he := congrArg (fun p : ℤ => (p : ℝ)) h
  fin_cases k <;> simpa only [weightedDiamondOrdinaryForm, ordinaryBudget, diamondPermProfile,
    Matrix.cons_val_zero', Matrix.cons_val_succ', zsmul_eq_mul, smul_eq_mul, Int.cast_add,
    Int.cast_sub, Int.cast_mul, Int.cast_neg, Int.cast_pow, Int.cast_ite, Int.cast_one,
    Int.cast_zero, Int.cast_ofNat] using he

private theorem ordinaryForm_interpolate (k : Fin 12) (x : ℝ) (m : DiamondProfile ℝ) :
    let f (y : ℝ) := weightedDiamondOrdinaryForm k y m
    f x = f 0 + x * (f 1 - f (-1)) / 2 + x^2 * ((f 1 + f (-1)) / 2 - f 0) := by
  dsimp only
  fin_cases k <;> simp only [weightedDiamondOrdinaryForm, Matrix.cons_val_zero',
    Matrix.cons_val_succ', smul_eq_mul] <;> ring

private theorem ordinaryBudget_interpolate (k : Fin 12) (x : ℝ) (m : DiamondProfile ℝ) :
    let g (y : ℝ) := ordinaryBudget k y m
    g x = g 0 + x * (g 1 - g (-1)) / 2 + x^2 * ((g 1 + g (-1)) / 2 - g 0) := by
  dsimp only
  fin_cases k <;> simp only [ordinaryBudget, Matrix.cons_val_zero',
    Matrix.cons_val_succ', smul_eq_mul] <;> ring

set_option maxHeartbeats 1600000 in
private theorem ordinary_perm_check (k : Fin 12) (x : ℝ) (σ : FourPerm) :
    weightedDiamondOrdinaryForm k x (diamondPermProfile (R := ℝ) σ) =
      ordinaryBudget k x (diamondPermProfile (R := ℝ) σ) := by
  obtain ⟨l, hl⟩ := fourPerm_surjective σ
  have hpoints := ordinary_integer_check k l
  let m : DiamondProfile ℝ := diamondPermProfile σ
  let f (x : ℝ) := weightedDiamondOrdinaryForm k x m
  let g (x : ℝ) := ordinaryBudget k x m
  have h₀ : f 0 = g 0 := by
    simpa only [hl, Int.cast_zero] using ordinary_check_cast k 0 (fourPerm l) hpoints.1
  have h₁ : f 1 = g 1 := by
    simpa only [hl, Int.cast_one] using ordinary_check_cast k 1 (fourPerm l) hpoints.2.1
  have hneg : f (-1) = g (-1) := by
    simpa only [hl, Int.cast_neg, Int.cast_one] using
      ordinary_check_cast k (-1) (fourPerm l) hpoints.2.2
  have hf : f x = f 0 + x * (f 1 - f (-1)) / 2 + x^2 * ((f 1 + f (-1)) / 2 - f 0) :=
    ordinaryForm_interpolate k x m
  have hg : g x = g 0 + x * (g 1 - g (-1)) / 2 + x^2 * ((g 1 + g (-1)) / 2 - g 0) :=
    ordinaryBudget_interpolate k x m
  change f x = g x
  rw [hf, hg, h₀, h₁, hneg]

set_option maxHeartbeats 600000 in
private theorem ordinary_form_eq_budget (k : Fin 12) (x : ℝ)
    (U : Matrix (Fin 4) (Fin 4) ℂ) (hU : IsUnitary U) :
    weightedDiamondOrdinaryForm k x (subsetMinorSq U) = ordinaryBudget k x (subsetMinorSq U) := by
  let f := weightedDiamondOrdinaryForm k x diamondEvaluate
  let g := ordinaryBudget k x diamondEvaluate
  have hf (m : DiamondProfile ℝ) : f m = weightedDiamondOrdinaryForm k x m := by
    fin_cases k <;> simp only [f, weightedDiamondOrdinaryForm, Matrix.cons_val_zero',
      Matrix.cons_val_succ', LinearMap.add_apply, LinearMap.sub_apply, LinearMap.neg_apply,
      LinearMap.smul_apply, diamondEvaluate, LinearMap.coe_mk, AddHom.coe_mk]
  have hg (m : DiamondProfile ℝ) : g m = ordinaryBudget k x m := by
    fin_cases k <;> simp only [g, ordinaryBudget, Matrix.cons_val_zero', Matrix.cons_val_succ',
      LinearMap.add_apply, LinearMap.smul_apply, diamondEvaluate, LinearMap.coe_mk, AddHom.coe_mk]
  have hperm (σ : FourPerm) : f (diamondPermProfile σ) = g (diamondPermProfile σ) :=
    (hf _).trans ((ordinary_perm_check k x σ).trans (hg _).symm)
  calc
    _ = f (subsetMinorSq U) := (hf _).symm
    _ = g (subsetMinorSq U) := diamondLinearForm_eq_of_perm_eq f g hperm U hU
    _ = _ := hg _

/-- The twelve ordinary weighted-diamond facet inequalities. -/
theorem weightedDiamondOrdinaryForm_nonneg (k : Fin 12) (x : ℝ) (hx : 0 ≤ x)
    (U : Matrix (Fin 4) (Fin 4) ℂ) (hU : IsUnitary U) :
    0 ≤ weightedDiamondOrdinaryForm k x (subsetMinorSq U) := by
  rw [ordinary_form_eq_budget k x U hU]
  have hm (I J : Finset (Fin 4)) : 0 ≤ subsetMinorSq U I J := subsetMinorSq_nonneg U I J
  fin_cases k <;> simp only [ordinaryBudget, Matrix.cons_val_zero', Matrix.cons_val_succ', smul_eq_mul]
  all_goals apply_rules [hm, hx, add_nonneg, mul_nonneg, sq_nonneg, zero_le_one]

end MOC
