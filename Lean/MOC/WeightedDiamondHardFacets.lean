import MOC.ContactCensus
import MOC.FourMinorTransport
import MOC.FourQuaternionMinor
import MOC.WeightedMinor

/-! The four weighted-diamond facets with a mixed linear coefficient are
compensated by their constant and quadratic squared-minor coefficients. -/

open BigOperators Matrix

namespace MOC

private abbrev DiamondMinorProfile (M : Type*) := Finset (Fin 4) → Finset (Fin 4) → M

/-- The four hard facet forms, in the order 9, 11, 12, 15 of the weighted
diamond census. The right labels zero and infinity have column indices three
and zero. The middle weight is `1 + x`. -/
def weightedDiamondHardForm {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (k : Fin 4) (x : R) (m : Finset (Fin 4) → Finset (Fin 4) → M) : M :=
  let c := m ∅ ∅
  let p (i : Fin 4) := m {i} {0}
  let q (i : Fin 4) := m {i} {3}
  let r (i j : Fin 4) := m {i,j} {0,1} + (1 + x) • m {i,j} {0,2}
  ![(x^2 + x - 1) • c - p 0 + x • p 1 + x • p 2 + q 0 + (x + 1) • q 1 + (x + 1) • q 2 +
    (1 - x) • r 0 1 + (1 - x) • r 0 2 - x • r 0 3 - x • r 1 2 - x • r 1 3,
    (-(x+1)) • c - p 0 - (x+2) • p 1 - p 2 + x • q 0 + (x+1) • q 1 + (x+1) • q 2 +
    r 0 1 + r 0 2 + (x+2) • r 1 2 + r 1 3,
    c + (x+1) • p 0 + (x+1) • p 1 + (2*x+1) • p 2 - (x+1) • q 0 + x • q 1 -
    r 0 1 - r 0 2 - r 0 3 - r 1 2 + x • r 1 3,
    (-(x+2)) • c - (x+1) • p 1 - p 2 + (x+1) • q 0 + (x+2) • q 1 + (x+1) • q 2 +
    r 0 1 + r 0 2 + (x+2) • r 1 2 + r 1 3] k

private def diamondRowOrder : Fin 4 → FourPerm :=
  ![fourPerm 7, fourPerm 7, fourPerm 2, fourPerm 0]

private def diamondColOrder : Fin 4 → FourPerm :=
  ![fourPerm 21, fourPerm 15, fourPerm 10, fourPerm 19]

private def diamondSwap (k : Fin 4) : Bool := decide (k = 0 ∨ k = 2)

private def diamondDonorForm {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (swap : Bool) (x : R) (m : DiamondMinorProfile M) : M :=
  let A := m {2,3} {2,3}
  let C := m {1,2} {1,2}
  let F := m {1} {2} + m {2} {1} + A - m {1,3} {0,2}
  if swap then C + x • (F + C) + x^2 • A else A + x • (F + C) + x^2 • C

private def diamondRelabel {M : Type*} (k : Fin 4) (m : DiamondMinorProfile M) : DiamondMinorProfile M :=
  fun I J => m (I.map (diamondRowOrder k).toEmbedding) (J.map (diamondColOrder k).toEmbedding)

/-- Subset-image indicators of a permutation in the same indices as squared minors. -/
def diamondPermProfile {R : Type*} [Zero R] [One R] (σ : FourPerm) : DiamondMinorProfile R :=
  fun I J => if J.map σ.toEmbedding = I then 1 else 0

set_option maxHeartbeats 1800000 in
set_option maxRecDepth 4000 in
private theorem diamond_integer_check : ∀ (k : Fin 4) (l : Fin 24),
    let m : DiamondMinorProfile ℤ := diamondPermProfile (fourPerm l)
    let P (x : ℤ) := weightedDiamondHardForm k x m =
      diamondDonorForm (diamondSwap k) x (diamondRelabel k m)
    P 0 ∧ P 1 ∧ P (-1) := by
  decide +kernel

private theorem diamond_check_cast (k : Fin 4) (x : ℤ) (σ : FourPerm) (h :
    weightedDiamondHardForm k x (diamondPermProfile (R := ℤ) σ) =
      diamondDonorForm (diamondSwap k) x (diamondRelabel k (diamondPermProfile (R := ℤ) σ))) :
    weightedDiamondHardForm k (x : ℝ) (diamondPermProfile (R := ℝ) σ) =
      diamondDonorForm (diamondSwap k) (x : ℝ) (diamondRelabel k (diamondPermProfile (R := ℝ) σ)) := by
  have he := congrArg (fun p : ℤ => (p : ℝ)) h
  fin_cases k <;> simpa only [weightedDiamondHardForm, diamondDonorForm, diamondRelabel,
    diamondPermProfile, Matrix.cons_val_zero', Matrix.cons_val_succ',
    zsmul_eq_mul, smul_eq_mul, Int.cast_add, Int.cast_sub, Int.cast_mul, Int.cast_neg,
    Int.cast_pow, Int.cast_ite, Int.cast_one, Int.cast_zero, Int.cast_ofNat] using he

private theorem hardForm_interpolate (k : Fin 4) (x : ℝ) (m : DiamondMinorProfile ℝ) :
    let f (y : ℝ) := weightedDiamondHardForm k y m
    f x = f 0 + x * (f 1 - f (-1)) / 2 + x^2 * ((f 1 + f (-1)) / 2 - f 0) := by
  dsimp only
  fin_cases k <;> simp only [weightedDiamondHardForm, Matrix.cons_val_zero',
    Matrix.cons_val_succ', smul_eq_mul] <;> ring

private theorem donorForm_interpolate (swap : Bool) (x : ℝ) (m : DiamondMinorProfile ℝ) :
    let g (y : ℝ) := diamondDonorForm swap y m
    g x = g 0 + x * (g 1 - g (-1)) / 2 + x^2 * ((g 1 + g (-1)) / 2 - g 0) := by
  cases swap <;> simp [diamondDonorForm, smul_eq_mul] <;> ring

set_option maxHeartbeats 1800000 in
private theorem diamond_perm_check (k : Fin 4) (x : ℝ) (σ : FourPerm) :
    weightedDiamondHardForm k x (diamondPermProfile (R := ℝ) σ) =
      diamondDonorForm (diamondSwap k) x (diamondRelabel k (diamondPermProfile (R := ℝ) σ)) := by
  obtain ⟨l, hl⟩ := fourPerm_surjective σ
  have hpoints := diamond_integer_check k l
  let m : DiamondMinorProfile ℝ := diamondPermProfile σ
  let f (x : ℝ) := weightedDiamondHardForm k x m
  let g (x : ℝ) := diamondDonorForm (diamondSwap k) x (diamondRelabel k m)
  have h₀ : f 0 = g 0 := by
    simpa only [hl, Int.cast_zero] using diamond_check_cast k 0 (fourPerm l) hpoints.1
  have h₁ : f 1 = g 1 := by
    simpa only [hl, Int.cast_one] using diamond_check_cast k 1 (fourPerm l) hpoints.2.1
  have hneg : f (-1) = g (-1) := by
    simpa only [hl, Int.cast_neg, Int.cast_one] using
      diamond_check_cast k (-1) (fourPerm l) hpoints.2.2
  have hf : f x = f 0 + x * (f 1 - f (-1)) / 2 + x^2 * ((f 1 + f (-1)) / 2 - f 0) :=
    hardForm_interpolate k x m
  have hg : g x = g 0 + x * (g 1 - g (-1)) / 2 + x^2 * ((g 1 + g (-1)) / 2 - g 0) :=
    donorForm_interpolate (diamondSwap k) x (diamondRelabel k m)
  change f x = g x
  rw [hf, hg, h₀, h₁, hneg]

/-- Evaluation of one row-set and column-set coordinate of a minor profile. -/
def diamondEvaluate (I J : Finset (Fin 4)) : DiamondMinorProfile ℝ →ₗ[ℝ] ℝ where
  toFun m := m I J
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The real signed determinant law reproduces all squared minor coordinates. -/
theorem diamond_weighted_profile (U : Matrix (Fin 4) (Fin 4) ℂ) (hU : IsUnitary U) :
    subsetMinorSq U = ∑ σ : FourPerm, realSignedWeight U σ • diamondPermProfile σ := by
  classical
  funext I J
  have h := congrArg Complex.re (sum_signedWeight_image_eq_subsetMinorSq U hU I J)
  simp only [Complex.re_sum, Complex.ofReal_re] at h
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, diamondPermProfile, mul_ite,
    mul_one, mul_zero, ← Finset.sum_filter, realSignedWeight]
  exact h.symm

/-- Equality of linear forms on permutation indicator profiles implies
equality on the squared-minor profile of a unitary. -/
theorem diamondLinearForm_eq_of_perm_eq
    (f g : DiamondMinorProfile ℝ →ₗ[ℝ] ℝ) (h : ∀ σ : FourPerm,
      f (diamondPermProfile σ) = g (diamondPermProfile σ))
    (U : Matrix (Fin 4) (Fin 4) ℂ) (hU : IsUnitary U) :
    f (subsetMinorSq U) = g (subsetMinorSq U) := by
  rw [diamond_weighted_profile U hU, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro σ _
  simp only [map_smul, h σ]

private theorem diamond_form_eq_donors (k : Fin 4) (x : ℝ)
    (U : Matrix (Fin 4) (Fin 4) ℂ) (hU : IsUnitary U) :
    weightedDiamondHardForm k x (subsetMinorSq U) =
      diamondDonorForm (diamondSwap k) x (diamondRelabel k (subsetMinorSq U)) := by
  let f := weightedDiamondHardForm k x diamondEvaluate
  let g := diamondDonorForm (diamondSwap k) x (diamondRelabel k diamondEvaluate)
  have hf (m : DiamondMinorProfile ℝ) : f m = weightedDiamondHardForm k x m := by
    fin_cases k <;> simp [f, weightedDiamondHardForm, diamondEvaluate, smul_eq_mul] <;> ring
  have hg (m : DiamondMinorProfile ℝ) : g m = diamondDonorForm (diamondSwap k) x (diamondRelabel k m) := by
    by_cases h : diamondSwap k <;>
      simp [g, diamondDonorForm, diamondRelabel, diamondEvaluate, h, smul_eq_mul] <;> ring
  rw [← hf, ← hg]
  exact diamondLinearForm_eq_of_perm_eq f g (fun σ => by rw [hf, hg, diamond_perm_check]) U hU

private theorem diamond_compensated_square {A B C x : ℝ} (hx : 0 ≤ x) (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hB : 0 ≤ B + 2 * √(A * C)) : 0 ≤ A + x * B + x^2 * C := by
  have hs := sq_nonneg (√A - x * √C)
  rw [sub_sq, mul_pow, Real.sq_sqrt hA, Real.sq_sqrt hC] at hs
  have he : 2 * √A * (x * √C) = 2 * x * √(A * C) := by
    rw [Real.sqrt_mul hA]
    ring
  rw [he] at hs
  nlinarith only [hs, mul_nonneg hx hB]

private theorem diamondDonor_real_nonneg (swap : Bool) (x : ℝ) (hx : 0 ≤ x)
    (O : Matrix.orthogonalGroup (Fin 4) ℝ) :
    0 ≤ diamondDonorForm swap x (subsetMinorSq (Complex.ofRealHom.mapMatrix O.val)) := by
  let U := Complex.ofRealHom.mapMatrix O.val
  let m := subsetMinorSq U
  let A := m {2,3} {2,3}
  let C := m {1,2} {1,2}
  let F := m {1} {2} + m {2} {1} + A - m {1,3} {0,2}
  have hA : 0 ≤ A := subsetMinorSq_nonneg U _ _
  have hC : 0 ≤ C := subsetMinorSq_nonneg U _ _
  obtain ⟨p,q,hp,hq,hs,hpair⟩ := exists_quaternionRotation_same_squaredMinors O
  have hb : 0 ≤ F + C + 2 * √(A * C) := by
    dsimp only [F,A,C,m,U]
    rw [hs 1 2, hs 2 1, hpair 2 3 2 3 (by decide) (by decide),
      hpair 1 3 0 2 (by decide) (by decide), hpair 1 2 1 2 (by decide) (by decide)]
    exact mixed_quaternion_rotation_weighted p q (by simpa only [Fin.sum_univ_four] using hp)
      (by simpa only [Fin.sum_univ_four] using hq)
  cases swap
  · exact diamond_compensated_square hx hA hC hb
  · have hb' : 0 ≤ F + C + 2 * √(C * A) := by rwa [mul_comm C A]
    exact diamond_compensated_square hx hC hA hb'

private theorem diamondDonor_nonneg (swap : Bool) (x : ℝ) (hx : 0 ≤ x)
    (U : Matrix (Fin 4) (Fin 4) ℂ) (hU : IsUnitary U) :
    0 ≤ diamondDonorForm swap x (subsetMinorSq U) := by
  obtain ⟨κ,inst,w,O,hw,_,hm⟩ := four_minor_mixture U hU
  letI := inst
  let m (k : κ) := subsetMinorSq (Complex.ofRealHom.mapMatrix (O k).val)
  have hprofile : subsetMinorSq U = ∑ k : κ, w k • m k := by
    funext I J
    simpa only [m, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using hm I J
  let f := diamondDonorForm swap x diamondEvaluate
  have hf (p : DiamondMinorProfile ℝ) : f p = diamondDonorForm swap x p := by
    cases swap <;> simp [f, diamondDonorForm, diamondEvaluate, smul_eq_mul] <;> ring
  rw [← hf, hprofile, map_sum]
  apply Finset.sum_nonneg
  intro k _
  rw [map_smul, hf, smul_eq_mul]
  exact mul_nonneg (hw k) (diamondDonor_real_nonneg swap x hx (O k))

/-- Each of the four mixed weighted-diamond facets is nonnegative on every
unitary mixer, for every middle weight at least one. -/
theorem weightedDiamondHardForm_nonneg (k : Fin 4) (x : ℝ) (hx : 0 ≤ x)
    (U : Matrix (Fin 4) (Fin 4) ℂ) (hU : IsUnitary U) :
    0 ≤ weightedDiamondHardForm k x (subsetMinorSq U) := by
  rw [diamond_form_eq_donors k x U hU]
  have hprofile : diamondRelabel k (subsetMinorSq U) =
      subsetMinorSq (U.submatrix (diamondRowOrder k) (diamondColOrder k)) := by
    funext I J
    exact (squared_minor_reindex (diamondRowOrder k) (diamondColOrder k) U hU I J).symm
  rw [hprofile]
  exact diamondDonor_nonneg (diamondSwap k) x hx _ (unitary_reindex _ _ hU)

end MOC
