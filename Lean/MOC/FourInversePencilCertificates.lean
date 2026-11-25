import MOC.FourInversePencil
import MOC.FourMixedRayCancellation
import MOC.FourSevenContactAffineElimination
import MOC.SparsePolynomialCertificate
import Mathlib.Tactic

/-! Determinant and matching-square certificates for the mixed-ray family
with ordinary ray indices 7, 13, 18, 28 and 31. A nonnegative coefficient
of ray 30 gives the extension. -/

open BigOperators Matrix

namespace MOC

noncomputable section

/-- The inverse pencil in row-major coordinates with the common scale of 32. -/
def fourTwoFactorPencil {R : Type*} [CommRing R] (a b c d f e : R) :
    Matrix (Fin 9) (Fin 9) R :=
  !![2*e + 2*f + 2, 0, 0, 0, -a - b - 2*e + 2*f, -a + b, 0, a - b, a + b + 2;
    0, 2*d - 2*e - 2*f - 2, 0, a + b + 2*e - 2*f, 0, a + b + 2*d + 2, -a + b, 0, -a + b;
    0, 0, -2*d, a - b, -a - b - 2*d - 2, 0, -a - b - 2, a - b, 0;
    0, a + b + 2*e - 2*f, a - b, 2*c - 2*e - 2*f - 2, 0, 0, 0, a + b + 2*c + 2, a - b;
    -a - b - 2*e + 2*f, 0, -a - b - 2*d - 2, 0, -2*c - 2*d + 2*e + 2*f, 0, -a - b - 2*c - 2, 0, -a - b;
    -a + b, a + b + 2*d + 2, 0, 0, 0, 2*d + 2, -a + b, a + b, 0;
    0, -a + b, -a - b - 2, 0, -a - b - 2*c - 2, -a + b, -2*c, 0, 0;
    a - b, 0, a - b, a + b + 2*c + 2, 0, a + b, 0, 2*c + 2, 0;
    a + b + 2, -a + b, 0, a - b, -a - b, 0, 0, 0, -2]

private def twoFactorBasis : Matrix (Fin 9) (Fin 9) ℝ :=
  !![0, 1, 0, 0, -1, 0, 0, 0, 0;
    -1, 0, 0, -1, 0, 0, 0, 0, 0;
    0, -1, 1, 0, 0, 0, 0, 0, 0;
    -1, 0, 0, 1, 0, 0, 0, 0, 0;
    0, 1, 0, 0, 1, 0, 0, 0, 0;
    1, 0, 0, 0, 0, 1, 0, 0, 0;
    0, -1, 0, 0, 0, 0, 1, 0, 0;
    1, 0, 0, 0, 0, 0, 0, 1, 0;
    0, 1, 0, 0, 0, 0, 0, 0, 1]

private def basisBlockIndices : Fin 4 ⊕ Fin 5 ≃ Fin 9 :=
  finSumFinEquiv.trans ((Equiv.swap (3 : Fin 9) 4).trans (Equiv.swap 2 3))

private theorem twoFactorBasis_det : twoFactorBasis.det = 4 := by
  let block : Matrix (Fin 4) (Fin 4) ℝ :=
    !![0,1,0,-1; -1,0,-1,0; -1,0,1,0; 0,1,0,1]
  let lower : Matrix (Fin 5) (Fin 4) ℝ :=
    twoFactorBasis.submatrix (basisBlockIndices ∘ Sum.inr) (basisBlockIndices ∘ Sum.inl)
  have hb : twoFactorBasis.submatrix basisBlockIndices basisBlockIndices =
      Matrix.fromBlocks block 0 lower 1 := by
    ext (i | i) (j | j) : 1
    · fin_cases i <;> fin_cases j <;> rfl
    · fin_cases i <;> fin_cases j <;> rfl
    · rfl
    · fin_cases i <;> fin_cases j <;> norm_num [basisBlockIndices, twoFactorBasis,
        Matrix.submatrix_apply, Matrix.fromBlocks, Matrix.one_apply, finSumFinEquiv,
        Equiv.swap_apply_def, Matrix.of_apply, Matrix.cons_val]
  rw [← Matrix.det_submatrix_equiv_self basisBlockIndices twoFactorBasis, hb,
    Matrix.det_fromBlocks_zero₁₂, Matrix.det_one, mul_one]
  norm_num [block, Matrix.det_succ_row_zero, Matrix.det_fin_zero, Fin.sum_univ_succ,
    Matrix.submatrix_apply, Matrix.of_apply, Matrix.cons_val, Fin.succAbove]

open SparsePolynomialCertificate

private abbrev TwoFactorTerms := SparsePolynomialCertificate.Polynomial 5

private def coreDeterminant : (n : ℕ) → (Fin n → Fin n → TwoFactorTerms) → TwoFactorTerms
  | 0, _ => constant 5 1
  | n + 1, A => normalize (sum fun j =>
      if (A 0 j).isEmpty then [] else
        mul (constant 5 ((-1) ^ j.val))
          (mul (A 0 j) (coreDeterminant n fun i k => A i.succ (j.succAbove k))))

private theorem eval_coreDeterminant (x : Fin 5 → ℝ) (n : ℕ)
    (A : Fin n → Fin n → TwoFactorTerms) :
    eval x (coreDeterminant n A) =
      (fun i j => eval x (A i j) : Matrix (Fin n) (Fin n) ℝ).det := by
  induction n with
  | zero => rw [coreDeterminant, eval_constant, Matrix.det_fin_zero, Int.cast_one]
  | succ n ih =>
    rw [coreDeterminant, eval_normalize, eval_sum, Matrix.det_succ_row_zero]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : A 0 j = []
    · simp [hj]
    · have hnot : (A 0 j).isEmpty = false := by
        cases h : A 0 j with
        | nil => exact False.elim (hj h)
        | cons a as => rfl
      simp only [hnot, Bool.false_eq_true, if_false, eval_mul, eval_constant, ih, Int.cast_pow,
        Int.cast_neg, Int.cast_one]
      change (-1 : ℝ) ^ j.val * (eval x (A 0 j) *
        (fun i k => eval x (A i.succ (j.succAbove k)) : Matrix (Fin n) (Fin n) ℝ).det) = _
      exact (mul_assoc _ _ _).symm

private def scaleTerms (k : ℤ) (p : TwoFactorTerms) : TwoFactorTerms :=
  mul (constant 5 k) p

private def coreEntry (i j : Fin 7) : TwoFactorTerms :=
  let a := indeterminate (0 : Fin 5)
  let b := indeterminate (1 : Fin 5)
  let c := indeterminate (2 : Fin 5)
  let d := indeterminate (3 : Fin 5)
  let e := indeterminate (4 : Fin 5)
  let signedDifference := a ++ scaleTerms (-1) b
  let coefficientSum := a ++ b
  let left := coefficientSum ++ scaleTerms 2 c ++ constant 5 2
  let right := coefficientSum ++ scaleTerms 2 d ++ constant 5 2
  let middle := scaleTerms (-2) coefficientSum ++ scaleTerms 2 c ++
    scaleTerms 2 d ++ scaleTerms (-8) e
  normalize
    (!![scaleTerms (-2) d, signedDifference, scaleTerms (-1) right, [],
          scaleTerms (-1) (coefficientSum ++ constant 5 2), signedDifference, [];
        signedDifference, middle ++ constant 5 (-4), [], scaleTerms (-1) right,
          signedDifference, left, scaleTerms 2 signedDifference;
        scaleTerms (-1) right, [], scaleTerms (-1) middle ++ constant 5 2,
          signedDifference, scaleTerms (-1) left, scaleTerms (-1) signedDifference,
          scaleTerms (-2) (coefficientSum ++ constant 5 1);
        [], scaleTerms (-1) right, signedDifference, scaleTerms 2 d ++ constant 5 2,
          scaleTerms (-1) signedDifference, coefficientSum, [];
        scaleTerms (-1) (coefficientSum ++ constant 5 2), signedDifference, scaleTerms (-1) left,
          scaleTerms (-1) signedDifference, scaleTerms (-2) c, [], [];
        signedDifference, left, scaleTerms (-1) signedDifference, coefficientSum, [],
          scaleTerms 2 c ++ constant 5 2, [];
        [], scaleTerms 2 signedDifference, scaleTerms (-2) (coefficientSum ++ constant 5 1),
          [], [], [], constant 5 (-2)] i j)

private def corePencil (x : Fin 5 → ℝ) : Matrix (Fin 7) (Fin 7) ℝ :=
  fun i j => eval x (coreEntry i j)

private def extensionBlock (f : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  diagonal ![-8 * (1 + f), 8 * (1 + f)]

set_option maxHeartbeats 4000000 in
private theorem twoFactor_congruence (a b c d f e : ℝ) :
    (twoFactorBasisᵀ * fourTwoFactorPencil a b c d f e * twoFactorBasis).submatrix
        (finSumFinEquiv : Fin 2 ⊕ Fin 7 ≃ Fin 9) finSumFinEquiv =
      Matrix.fromBlocks (extensionBlock f) 0 0 (corePencil ![a,b,c,d,e]) := by
  ext (i | i) (j | j) : 1 <;> fin_cases i <;> fin_cases j <;>
    norm_num [twoFactorBasis, fourTwoFactorPencil, corePencil, coreEntry, extensionBlock,
      Matrix.mul_apply, Matrix.transpose_apply, Matrix.submatrix_apply, Matrix.fromBlocks,
      Matrix.diagonal_apply, finSumFinEquiv, Fin.sum_univ_succ, Matrix.of_apply,
      Matrix.cons_val, eval_normalize, eval_append, scaleTerms] <;> ring

private def factorP (a b c d : ℝ) : ℝ := (a + 1) * (b + 1) - c * d

private def factorQ (a b e : ℝ) : ℝ := (a + 1) * (b + 1) + e

private def factorZ (a b c d e : ℝ) : ℝ :=
  (a + 1) * (b + 1) * (1 + c + d) + (a + b + 1) * c * d +
    e * ((c + 1) * (d + 1) - a * b)

private def coreFactors : TwoFactorTerms :=
  let a := indeterminate (0 : Fin 5)
  let b := indeterminate (1 : Fin 5)
  let c := indeterminate (2 : Fin 5)
  let d := indeterminate (3 : Fin 5)
  let e := indeterminate (4 : Fin 5)
  let one := constant 5 1
  let ab := mul (a ++ one) (b ++ one)
  let cd := mul c d
  let p := ab ++ scaleTerms (-1) cd
  let q := ab ++ e
  let z := mul ab (one ++ c ++ d) ++ mul (a ++ b ++ one) cd ++
    mul e (mul (c ++ one) (d ++ one) ++ scaleTerms (-1) (mul a b))
  scaleTerms (-2048) (mul (mul p q) z)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem coreFactorCertificate :
    (normalizedKeys (coreDeterminant 7 coreEntry) == normalizedKeys coreFactors) = true := by
  decide +kernel

private theorem corePencil_det (a b c d e : ℝ) :
    (corePencil ![a,b,c,d,e]).det = -2048 * factorP a b c d * factorQ a b e * factorZ a b c d e := by
  let x : Fin 5 → ℝ := ![a,b,c,d,e]
  change (corePencil x).det = _
  rw [show (corePencil x).det = eval x (coreDeterminant 7 coreEntry) from
    (eval_coreDeterminant x 7 coreEntry).symm]
  rw [eval_eq_of_normalizedKeys_eq x coreFactorCertificate]
  simp [x, coreFactors, scaleTerms, factorP, factorQ, factorZ]
  <;> ring

/-- The positive extension factor leaves the two relevant zero factors
of the base pencil unchanged. -/
theorem fourTwoFactorPencil_det (a b c d f e : ℝ) :
    (fourTwoFactorPencil a b c d f e).det =
      8192 * (1 + f)^2 * factorP a b c d * factorQ a b e * factorZ a b c d e := by
  have h := congrArg Matrix.det (twoFactor_congruence a b c d f e)
  have hext : (extensionBlock f).det = -64 * (1+f)^2 := by
    rw [extensionBlock, Matrix.det_diagonal, Fin.prod_univ_two]
    ring
  rw [Matrix.det_submatrix_equiv_self, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
    twoFactorBasis_det, Matrix.det_fromBlocks_zero₁₂, hext, corePencil_det] at h
  linear_combination h / 16

private def twoFactorRays : Fin 6 → Fin 34 := ![7,13,18,28,30,31]

private def twoFactorBase : Matrix (Fin 9) (Fin 9) ℤ :=
  fourTwoFactorPencil 0 0 0 0 0 0

private def twoFactorUnit (k : Fin 6) : Matrix (Fin 9) (Fin 9) ℤ :=
  let x (j : Fin 6) : ℤ := if j = k then 1 else 0
  fourTwoFactorPencil (x 0) (x 1) (x 2) (x 3) (x 4) (x 5)

private theorem twoFactorBase_entries (i j : Fin 9) :
    twoFactorBase i j = fourInverseRayMatrix 10 i j + fourInverseRayMatrix 7 i j +
      fourInverseRayMatrix 17 i j - fourInverseRayMatrix 25 i j := by
  revert i j
  decide +kernel

private theorem twoFactorUnit_entries (k : Fin 6) (i j : Fin 9) :
    twoFactorUnit k i j - twoFactorBase i j = fourInverseRayMatrix (twoFactorRays k) i j := by
  revert k i j
  decide +kernel

private theorem twoFactorAffine_entries (x : Fin 6 → ℝ) (i j : Fin 9) :
    fourTwoFactorPencil (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) i j =
      (twoFactorBase i j : ℝ) +
        ∑ k, x k * ((twoFactorUnit k i j - twoFactorBase i j : ℤ) : ℝ) := by
  fin_cases i <;> fin_cases j <;>
    norm_num [twoFactorBase, twoFactorUnit, fourTwoFactorPencil, Fin.sum_univ_succ,
      Matrix.of_apply, Matrix.cons_val] <;> ring

/-- Ordinary-ray expansion with the mixed coefficient fixed at one. -/
def fourTwoFactorCoefficients (a b c d f e : ℝ) (r : Fin 34) : ℝ :=
  (if r = 10 then 1 else 0) + (if r = 7 then a + 1 else 0) +
  (if r = 17 then 1 else 0) - (if r = 25 then 1 else 0) +
  (if r = 13 then b else 0) + (if r = 18 then c else 0) +
  (if r = 28 then d else 0) + (if r = 30 then f else 0) + (if r = 31 then e else 0)

private theorem sum_twoFactorCoefficients (a b c d f e : ℝ) (g : Fin 34 → ℝ) :
    (∑ r, fourTwoFactorCoefficients a b c d f e r * g r) =
      g 10 + g 7 + g 17 - g 25 + a * g 7 + b * g 13 + c * g 18 + d * g 28 +
        f * g 30 + e * g 31 := by
  simp only [fourTwoFactorCoefficients, add_mul, sub_mul, ite_mul, zero_mul, one_mul,
    Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  ring

theorem fourTwoFactorPencil_eq_inversePencil (a b c d f e : ℝ) :
    fourTwoFactorPencil a b c d f e =
      fourInversePencil (fourTwoFactorCoefficients a b c d f e) := by
  ext i j : 1
  change fourTwoFactorPencil a b c d f e i j =
    ∑ r, fourTwoFactorCoefficients a b c d f e r * (fourInverseRayMatrix r i j : ℝ)
  rw [sum_twoFactorCoefficients]
  have haffine := twoFactorAffine_entries (![a,b,c,d,f,e] : Fin 6 → ℝ) i j
  simp_rw [twoFactorUnit_entries] at haffine
  rw [twoFactorBase_entries] at haffine
  simp only [twoFactorRays, Int.cast_add, Int.cast_sub, Fin.sum_univ_succ,
    Fin.sum_univ_zero, add_zero, Matrix.cons_val_zero, Matrix.cons_val_succ] at haffine
  linear_combination haffine

private abbrev ray (i : Fin 34) : Fin 24 → ℝ := ordinaryCostRay i

private def seed (p : Fin 24) : ℝ := mixedCostSeedInt p

private def exceptionalInt (p : Fin 24) : ℤ := if p = 5 then 1 else 0

private def exceptional (p : Fin 24) : ℝ := exceptionalInt p

private theorem seed_square (p : Fin 24) : seed p ^ 2 = seed p + 2 * exceptional p := by
  have h : ∀ p : Fin 24,
      mixedCostSeedInt p ^ 2 = mixedCostSeedInt p + 2 * exceptionalInt p := by
    decide +kernel
  unfold seed exceptional
  exact_mod_cast h p

private theorem pair_product (p : Fin 24) : ray 18 p * ray 28 p = exceptional p := by
  have h : ∀ p : Fin 24,
      ordinaryCostRayInt 18 p * ordinaryCostRayInt 28 p = exceptionalInt p := by
    decide +kernel
  change (ordinaryCostRayInt 18 p : ℝ) * (ordinaryCostRayInt 28 p : ℝ) =
    (exceptionalInt p : ℝ)
  exact_mod_cast h p

private theorem gram_product (p : Fin 24) :
    seed p * ray 31 p + ray 7 p * ray 13 p - ray 7 p * ray 31 p - ray 13 p * ray 31 p =
      exceptional p := by
  have h : ∀ p : Fin 24, mixedCostSeedInt p * ordinaryCostRayInt 31 p +
      ordinaryCostRayInt 7 p * ordinaryCostRayInt 13 p -
      ordinaryCostRayInt 7 p * ordinaryCostRayInt 31 p -
      ordinaryCostRayInt 13 p * ordinaryCostRayInt 31 p = exceptionalInt p := by
    decide +kernel
  change (mixedCostSeedInt p : ℝ) * (ordinaryCostRayInt 31 p : ℝ) +
    (ordinaryCostRayInt 7 p : ℝ) * (ordinaryCostRayInt 13 p : ℝ) -
    (ordinaryCostRayInt 7 p : ℝ) * (ordinaryCostRayInt 31 p : ℝ) -
    (ordinaryCostRayInt 13 p : ℝ) * (ordinaryCostRayInt 31 p : ℝ) = (exceptionalInt p : ℝ)
  exact_mod_cast h p

private theorem seed_mem : seed ∈ realMatchingFunctionSpace := by
  have h : seed = ray 10 + ray 7 + ray 17 - ray 25 := by
    funext p
    simp [seed, mixedCostSeedInt, ray, ordinaryCostRay, Pi.add_apply, Pi.sub_apply]
  rw [h]
  exact realMatchingFunctionSpace.sub_mem
    (realMatchingFunctionSpace.add_mem
      (realMatchingFunctionSpace.add_mem (ordinaryCostRay_mem_realMatchingFunctionSpace 10)
        (ordinaryCostRay_mem_realMatchingFunctionSpace 7))
      (ordinaryCostRay_mem_realMatchingFunctionSpace 17))
    (ordinaryCostRay_mem_realMatchingFunctionSpace 25)

/-- The mixed ray plus ordinary rays 7, 13, 18, 28, 30 and 31 in that order. -/
def fourTwoFactorCost (a b c d f e : ℝ) (p : Fin 24) : ℝ :=
  seed p + a * ray 7 p + b * ray 13 p + c * ray 18 p + d * ray 28 p +
    f * ray 30 p + e * ray 31 p

private theorem fourTwoFactorCost_eq_sum (a b c d f e : ℝ) (p : Fin 24) :
    fourTwoFactorCost a b c d f e p =
      ∑ r, fourTwoFactorCoefficients a b c d f e r * ordinaryCostRay r p := by
  rw [sum_twoFactorCoefficients]
  simp [fourTwoFactorCost, seed, mixedCostSeedInt, ray, ordinaryCostRay] <;> ring

theorem fourTwoFactorCost_mem (a b c d f e : ℝ) :
    fourTwoFactorCost a b c d f e ∈ realMatchingFunctionSpace := by
  change (seed + a • ray 7 + b • ray 13 + c • ray 18 + d • ray 28 +
    f • ray 30 + e • ray 31) ∈ realMatchingFunctionSpace
  apply realMatchingFunctionSpace.add_mem (realMatchingFunctionSpace.add_mem
    (realMatchingFunctionSpace.add_mem (realMatchingFunctionSpace.add_mem
      (realMatchingFunctionSpace.add_mem (realMatchingFunctionSpace.add_mem seed_mem
        (realMatchingFunctionSpace.smul_mem a (ordinaryCostRay_mem_realMatchingFunctionSpace 7)))
          (realMatchingFunctionSpace.smul_mem b (ordinaryCostRay_mem_realMatchingFunctionSpace 13)))
          (realMatchingFunctionSpace.smul_mem c (ordinaryCostRay_mem_realMatchingFunctionSpace 18)))
          (realMatchingFunctionSpace.smul_mem d (ordinaryCostRay_mem_realMatchingFunctionSpace 28)))
          (realMatchingFunctionSpace.smul_mem f (ordinaryCostRay_mem_realMatchingFunctionSpace 30)))
          (realMatchingFunctionSpace.smul_mem e (ordinaryCostRay_mem_realMatchingFunctionSpace 31))

private theorem gram_square_completion (a b e m x y w : ℝ)
    (ha : a ≠ 0) (hab : a * b - 1 ≠ 0) :
    m^2 + a*x^2 + b*y^2 + e*w^2 - 2*(m*w+x*y-x*w-y*w) =
      (m-w)^2 + a*(x+(w-y)/a)^2 +
      (b-1/a)*(y+(a+1)/(a*b-1)*w)^2 +
      (e-(a+1)*(b+1)/(a*b-1))*w^2 := by
  field_simp [ha, hab] <;> ring

private theorem mixed_seed (p : Fin 24) : mixedCostRay 0 p = seed p := by
  have h : ∀ p : Fin 24, mixedCostRayInt 0 p = mixedCostSeedInt p := by decide +kernel
  unfold mixedCostRay seed
  exact_mod_cast h p

/-- Under the Gram budget, four matching functions give a sum of squares. -/
theorem fourMatchingSOS_of_gram_budget {a b e : ℝ}
    (ha : 0 < a) (hab : 1 < a*b) (he : (a+1)*(b+1) ≤ e*(a*b-1)) :
    IsRealMatchingSOS (fun p =>
      mixedCostRay 0 p + a*ordinaryCostRay 7 p + b*ordinaryCostRay 13 p +
        e*ordinaryCostRay 31 p) := by
  have hbcomp : 0 ≤ b-1/a :=
    sub_nonneg.mpr ((div_le_iff₀ ha).2 (by simpa only [mul_comm b a] using hab.le))
  have hecomp : 0 ≤ e-(a+1)*(b+1)/(a*b-1) :=
    sub_nonneg.mpr ((div_le_iff₀ (sub_pos.mpr hab)).2 he)
  let w : Fin 4 → ℝ := ![1, a, b-1/a, e-(a+1)*(b+1)/(a*b-1)]
  let features : Fin 4 → Fin 24 → ℝ := ![seed-ray 31, ray 7 + a⁻¹ • (ray 31-ray 13),
    ray 13 + ((a+1)/(a*b-1)) • ray 31, ray 31]
  have hw : ∀ i, 0 ≤ w i := by
    intro i
    fin_cases i
    · norm_num [w]
    · exact ha.le
    · exact hbcomp
    · exact hecomp
  have hfeat : ∀ i, features i ∈ realMatchingFunctionSpace := by
    intro i
    fin_cases i
    · exact realMatchingFunctionSpace.sub_mem seed_mem (ordinaryCostRay_mem_realMatchingFunctionSpace 31)
    · exact realMatchingFunctionSpace.add_mem (ordinaryCostRay_mem_realMatchingFunctionSpace 7) (realMatchingFunctionSpace.smul_mem _
        (realMatchingFunctionSpace.sub_mem (ordinaryCostRay_mem_realMatchingFunctionSpace 31) (ordinaryCostRay_mem_realMatchingFunctionSpace 13)))
    · exact realMatchingFunctionSpace.add_mem (ordinaryCostRay_mem_realMatchingFunctionSpace 13)
        (realMatchingFunctionSpace.smul_mem _ (ordinaryCostRay_mem_realMatchingFunctionSpace 31))
    · exact ordinaryCostRay_mem_realMatchingFunctionSpace 31
  have hcost : (fun p => mixedCostRay 0 p + a * ray 7 p + b * ray 13 p + e * ray 31 p) =
      (fun p => ∑ i, w i * features i p ^ 2) := by
    funext p
    calc
      mixedCostRay 0 p + a * ray 7 p + b * ray 13 p + e * ray 31 p =
          seed p^2 + a*(ray 7 p)^2 + b*(ray 13 p)^2 + e*(ray 31 p)^2 -
            2*(seed p*ray 31 p+ray 7 p*ray 13 p-ray 7 p*ray 31 p-ray 13 p*ray 31 p) := by
        rw [mixed_seed, seed_square, ordinaryCostRay_sq, ordinaryCostRay_sq, ordinaryCostRay_sq, gram_product]
        ring
      _ = _ := by
        rw [gram_square_completion a b e (seed p) (ray 7 p) (ray 13 p) (ray 31 p)
          ha.ne' (sub_pos.mpr hab).ne']
        simp [w,features,Fin.sum_univ_succ,Pi.add_apply,Pi.sub_apply,Pi.smul_apply,
          smul_eq_mul,one_div,div_eq_mul_inv]
        <;> ring
  rw [hcost]
  exact isRealMatchingSOS_weighted w features hw hfeat

/-- A nonnegative ordinary coefficient adds one square to a certificate. -/
theorem fourMatchingSOS_add_ordinaryRay {g : Fin 24 → ℝ} (hs : IsRealMatchingSOS g)
    (r : Fin 34) {c : ℝ} (hc : 0 ≤ c) :
    IsRealMatchingSOS (fun p => g p + c * ordinaryCostRay r p) :=
  realMatchingSOS_add_ordinaryCostRay hs r c hc

/-- A singular pencil yields a matching square certificate on either
factor branch. The ordinary coefficient on the extension may vanish. -/
theorem fourTwoFactorCost_sos_of_det_eq_zero {a b c d f e : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (hf : 0 ≤ f) (he : 0 < e)
    (hdet : (fourTwoFactorPencil a b c d f e).det = 0) :
    IsRealMatchingSOS (fourTwoFactorCost a b c d f e) := by
  rw [fourTwoFactorPencil_det] at hdet
  have hscale : (8192 * (1+f)^2 : ℝ) ≠ 0 := by positivity
  have hQ : factorQ a b e ≠ 0 := ne_of_gt (by unfold factorQ; positivity)
  have hz : (8192 * (1+f)^2) * ((factorP a b c d * factorQ a b e) * factorZ a b c d e) = 0 := by
    linear_combination hdet
  have hzero := (mul_eq_zero.mp hz).resolve_left hscale
  rcases mul_eq_zero.mp hzero with hp | hz
  · have hp := (mul_eq_zero.mp hp).resolve_right hQ
    have hcd : 1 < c * d := by
      unfold factorP at hp
      nlinarith only [ha, hb, mul_pos ha hb, hp]
    have hdc : 0 ≤ d - 1 / c := sub_nonneg.mpr ((div_le_iff₀ hc).2 (by
      simpa only [mul_comm d c] using hcd.le))
    let w : Fin 7 → ℝ := ![1, c, d-1/c, a, b, e, f]
    let features : Fin 7 → Fin 24 → ℝ := ![seed, ray 18-c⁻¹ • ray 28,
      ray 28, ray 7, ray 13, ray 31, ray 30]
    have hw : ∀ i, 0 ≤ w i := by
      intro i
      fin_cases i
      · norm_num [w]
      · exact hc.le
      · exact hdc
      · exact ha.le
      · exact hb.le
      · exact he.le
      · exact hf
    have hfeat : ∀ i, features i ∈ realMatchingFunctionSpace := by
      intro i
      fin_cases i
      · exact seed_mem
      · exact realMatchingFunctionSpace.sub_mem (ordinaryCostRay_mem_realMatchingFunctionSpace 18)
          (realMatchingFunctionSpace.smul_mem _ (ordinaryCostRay_mem_realMatchingFunctionSpace 28))
      · exact ordinaryCostRay_mem_realMatchingFunctionSpace 28
      · exact ordinaryCostRay_mem_realMatchingFunctionSpace 7
      · exact ordinaryCostRay_mem_realMatchingFunctionSpace 13
      · exact ordinaryCostRay_mem_realMatchingFunctionSpace 31
      · exact ordinaryCostRay_mem_realMatchingFunctionSpace 30
    have heq : fourTwoFactorCost a b c d f e =
        (fun p => ∑ i, w i * features i p ^ 2) := by
      funext p
      calc
        fourTwoFactorCost a b c d f e p =
            seed p^2 + a*(ray 7 p)^2 + b*(ray 13 p)^2 + c*(ray 18 p)^2 +
              d*(ray 28 p)^2 + e*(ray 31 p)^2 + f*(ray 30 p)^2 -
              2*(ray 18 p * ray 28 p) := by
          rw [seed_square, ordinaryCostRay_sq, ordinaryCostRay_sq, ordinaryCostRay_sq, ordinaryCostRay_sq, ordinaryCostRay_sq,
            ordinaryCostRay_sq, pair_product]
          unfold fourTwoFactorCost
          ring
        _ = _ := by
          simp [w, features, Fin.sum_univ_succ, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, one_div]
          field_simp [hc.ne'] <;> ring
    rw [heq]
    exact isRealMatchingSOS_weighted w features hw hfeat
  · unfold factorZ at hz
    have hpos : 0 < (a+1)*(b+1)*(1+c+d)+(a+b+1)*c*d := by positivity
    have hprod : e*(a*b-(c+1)*(d+1)) =
        (a+1)*(b+1)*(1+c+d)+(a+b+1)*c*d := by
      linear_combination -hz
    have hgap : (c+1)*(d+1) < a*b := by
      by_contra! h
      have hn := mul_nonpos_of_nonneg_of_nonpos he.le (sub_nonpos.mpr h)
      linarith only [hprod, hpos, hn]
    have hab : 1 < a*b := by nlinarith only [hc, hd, mul_pos hc hd, hgap]
    have hrest : 0 < (a+1)*(b+1)*(c+d)+(a+b+1)*c*d+e*(c+d+c*d) := by positivity
    have heq : e*(a*b-1)-(a+1)*(b+1) =
        (a+1)*(b+1)*(c+d)+(a+b+1)*c*d+e*(c+d+c*d) := by
      linear_combination -hz
    have hbudget : (a+1)*(b+1) ≤ e*(a*b-1) := by linarith only [heq, hrest]
    have hs := fourMatchingSOS_of_gram_budget ha hab hbudget
    have h₁ := fourMatchingSOS_add_ordinaryRay hs 18 hc.le
    have h₂ := fourMatchingSOS_add_ordinaryRay h₁ 28 hd.le
    have h₃ := fourMatchingSOS_add_ordinaryRay h₂ 30 hf
    convert h₃ using 1
    funext p
    simp only [fourTwoFactorCost, mixed_seed]
    ring

/-- The determinant zero and a positive corrected moment suffice for
nonnegative evaluation on the mixer. -/
theorem fourTwoFactorCost_nonneg_of_det_eq_zero
    (U : Matrix (Fin 4) (Fin 4) ℂ) (t : ℝ) {a b c d f e : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (hf : 0 ≤ f) (he : 0 < e)
    (hdet : (fourTwoFactorPencil a b c d f e).det = 0)
    (hm : (realMatchingMoment (fun p => realSignedWeight U (fourPerm p).symm +
      t * matchingSign p)).PosSemidef) :
    0 ≤ fourSupportCostValue U (fourTwoFactorCost a b c d f e) := by
  change 0 ≤ ∑ p : Fin 24, realSignedWeight U (fourPerm p).symm * fourTwoFactorCost a b c d f e p
  exact realMatchingSOS_pairing_nonneg_of_positiveMoment _ t (fourTwoFactorCost_mem a b c d f e)
    (fourTwoFactorCost_sos_of_det_eq_zero ha hb hc hd hf he hdet) hm

/-- An actual spectral cost in the two-factor family admits matching squares. -/
theorem fourTwoFactorCost_sos_of_spectralGap
    (α β : Fin 4 → ℂ) (η : ℂ) (h : ℝ) {a b c d f e : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (hf : 0 ≤ f) (he : 0 < e)
    (hgap : ∀ p, fourTwoFactorCost a b c d f e p =
      h - (η * matchingProduct α β (fourPerm p).symm).re) :
    IsRealMatchingSOS (fourTwoFactorCost a b c d f e) := by
  apply fourTwoFactorCost_sos_of_det_eq_zero ha hb hc hd hf he
  rw [fourTwoFactorPencil_eq_inversePencil]
  apply fourInversePencil_det_eq_zero_of_spectralGap _ α β η h
  intro p
  rw [← fourTwoFactorCost_eq_sum, hgap p]

end

end MOC
