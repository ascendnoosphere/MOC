import MOC.ContinuousDeterminantWeights
import MOC.ContactCensus
import MOC.Support
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.NumberTheory.Zsqrtd.GaussianInt

/-! Exact determinant values at two spectral inputs and a smooth collision
of the two corresponding fields. -/

open BigOperators Matrix Set Filter Topology
open scoped ContDiff

namespace MOC.ContinuousWeightCounterexample

noncomputable section

def mixerNumerator : Matrix (Fin 4) (Fin 4) GaussianInt :=
  !![1,4,4,4; -4,1,4,-4; -4,-4,1,4; -4,4,-4,1]

def mixer : Matrix (Fin 4) (Fin 4) ℂ :=
  (1 / 7 : ℂ) • mixerNumerator.map GaussianInt.toComplex

theorem isUnitary_divide_gaussian_matrix {n : ℕ}
    (N : Matrix (Fin n) (Fin n) GaussianInt)
    (hN : N * Nᴴ = (49 : GaussianInt) • (1 : Matrix (Fin n) (Fin n) GaussianInt)) :
    IsUnitary ((1 / 7 : ℂ) • N.map GaussianInt.toComplex) := by
  let g := GaussianInt.toComplex
  have hG := congrArg (fun M : Matrix (Fin n) (Fin n) GaussianInt => M.map g) hN
  have hstar := Matrix.conjTranspose_map (A := N) g GaussianInt.toComplex_star
  simp only [Matrix.map_mul, hstar, Matrix.map_smul' g _ _ (map_mul g), map_ofNat,
    Matrix.map_one g (map_zero g) (map_one g)] at hG
  have hU : ((1 / 7 : ℂ) • N.map g) * ((1 / 7 : ℂ) • N.map g)ᴴ = 1 := by
    simp only [Matrix.conjTranspose_smul, star_div₀, star_one, star_ofNat,
      Matrix.smul_mul, Matrix.mul_smul, smul_smul, hG]
    norm_num [smul_smul]
  exact ⟨hU, Matrix.mul_eq_one_comm.mp hU⟩

theorem isUnitary_mixer : IsUnitary mixer := by
  apply isUnitary_divide_gaussian_matrix
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> decide +kernel

theorem mixerNumerator_det : mixerNumerator.det = 2401 := by
  rw [Matrix.det_succ_column_zero]
  simp only [Matrix.det_fin_three, Fin.sum_univ_four]
  decide +kernel

private def leftInt (positive : Bool) : Fin 4 → GaussianInt :=
  if positive then ![⟨-83,-31⟩, ⟨-22,26⟩, ⟨-23,-33⟩, 0]
  else ![⟨-15,-19⟩, ⟨-11,-42⟩, ⟨23,116⟩, 0]

private def rightInt : Fin 4 → GaussianInt :=
  ![41, -41, ⟨41,41⟩, ⟨0,41⟩]

/-- The first spectrum for each of the two strict scalar hull points. -/
def leftSpectrum (positive : Bool) : Fin 4 → ℂ := GaussianInt.toComplex ∘ leftInt positive

/-- The same second spectrum for both inputs. -/
def rightSpectrum : Fin 4 → ℂ := GaussianInt.toComplex ∘ rightInt

private def valueInt (positive : Bool) : GaussianInt :=
  if positive then ⟨3199311590,8332470672⟩ else ⟨-5018932754,-11746623656⟩

private def scaledSum (positive : Bool) : Matrix (Fin 4) (Fin 4) GaussianInt :=
  (49 : GaussianInt) • diagonal (leftInt positive) +
    mixerNumerator * diagonal rightInt * mixerNumeratorᴴ

private theorem scaledSum_det (positive : Bool) :
    (scaledSum positive).det = (49 : GaussianInt)^2 * valueInt positive := by
  rw [Matrix.det_succ_column_zero]
  simp only [Matrix.det_fin_three, Fin.sum_univ_four]
  cases positive <;> decide +kernel

private theorem determinantValue_eq_exact (positive : Bool) :
    determinantValue (leftSpectrum positive) rightSpectrum mixer =
      GaussianInt.toComplex (valueInt positive) / 2401 := by
  let g := GaussianInt.toComplex
  let D := diagonal (leftSpectrum positive) + mixer * diagonal rightSpectrum * mixerᴴ
  have hmap : mixerNumerator.map g = (7 : ℂ) • mixer := by
    simp [g, mixer, smul_smul] <;> norm_num
  have hstar := Matrix.conjTranspose_map (A := mixerNumerator) g GaussianInt.toComplex_star
  have hsum : (scaledSum positive).map g = (49 : ℂ) • D := by
    change (scaledSum positive).map g = (49 : ℂ) •
      (diagonal (fun i => g (leftInt positive i)) +
        mixer * diagonal (fun i => g (rightInt i)) * mixerᴴ)
    simp only [scaledSum, Matrix.map_add g (map_add g),
      Matrix.map_smul' g _ _ (map_mul g), map_ofNat, Matrix.map_mul,
      Matrix.diagonal_map (map_zero g), hstar, hmap, Matrix.conjTranspose_smul,
      star_ofNat, Matrix.smul_mul, Matrix.mul_smul, smul_smul, smul_add]
    norm_num
  have he := congrArg g (scaledSum_det positive)
  simp only [RingHom.map_det, RingHom.mapMatrix_apply, hsum, Matrix.det_smul,
    Fintype.card_fin, map_mul, map_pow, map_ofNat] at he
  change D.det = _
  apply (eq_div_iff (show (2401 : ℂ) ≠ 0 by norm_num)).mpr
  linear_combination he / 2401

theorem determinantValue_positive_input :
    determinantValue (leftSpectrum true) rightSpectrum mixer =
      (3199311590 + 8332470672 * Complex.I) / 2401 := by
  rw [determinantValue_eq_exact]
  norm_num [valueInt, GaussianInt.toComplex_def']

theorem determinantValue_negative_input :
    determinantValue (leftSpectrum false) rightSpectrum mixer =
      (-5018932754 - 11746623656 * Complex.I) / 2401 := by
  rw [determinantValue_eq_exact]
  norm_num [valueInt, GaussianInt.toComplex_def', sub_eq_add_neg, neg_mul]

private def vertexInt (positive : Bool) (p : FourPerm) : GaussianInt :=
  ∏ j, (leftInt positive j + rightInt (p j))

private theorem matchingProduct_eq_exact (positive : Bool) (p : FourPerm) :
    matchingProduct (leftSpectrum positive) rightSpectrum p.symm =
      GaussianInt.toComplex (vertexInt positive p) := by
  rw [matchingProduct_inverse]
  simp only [vertexInt, map_prod, map_add, leftSpectrum, rightSpectrum, Function.comp_apply]

private def directionInt : GaussianInt := ⟨6,-1⟩

/-- Integer score on the two simultaneous matching products. -/
def jointScore (p : FourPerm) : ℤ :=
  (directionInt * (vertexInt true p - vertexInt false p)).re

private theorem jointScore_le (p : FourPerm) : jointScore p ≤ 28850019 := by
  have h : ∀ i : Fin 24, jointScore (fourPerm i) ≤ 28850019 := by
    decide +kernel
  obtain ⟨i, rfl⟩ := fourPerm_surjective p
  exact h i

theorem jointScore_attains_bound : ∃ p : FourPerm, jointScore p = 28850019 := by
  refine ⟨fourPerm 7, ?_⟩
  decide +kernel

private theorem directionInt_toComplex :
    GaussianInt.toComplex directionInt = 6 - Complex.I := by
  norm_num [directionInt, GaussianInt.toComplex_def', sub_eq_add_neg, neg_mul]

theorem joint_determinant_score :
    ((6 - Complex.I) *
      (determinantValue (leftSpectrum true) rightSpectrum mixer -
        determinantValue (leftSpectrum false) rightSpectrum mixer)).re =
      69388560392 / 2401 := by
  rw [determinantValue_eq_exact, determinantValue_eq_exact, ← directionInt_toComplex,
    ← sub_div, ← map_sub, ← mul_div_assoc, ← map_mul,
    show (2401 : ℂ) = ((2401 : ℝ) : ℂ) by norm_num,
    Complex.div_ofReal_re, ← GaussianInt.to_real_re]
  rw [show (directionInt * (valueInt true - valueInt false)).re = 69388560392 by
    decide +kernel]
  norm_num

/-- No single probability law represents the two actual determinants. -/
theorem no_common_weights_two_spectra :
    ¬ ∃ w : FourPerm → ℝ, (∀ p, 0 ≤ w p) ∧ (∑ p, w p = 1) ∧
      ∀ s : Bool, weightedMatchingValue (leftSpectrum s) rightSpectrum w =
        determinantValue (leftSpectrum s) rightSpectrum mixer := by
  rintro ⟨w, hw, hs, h⟩
  have hsum : (∑ p, w p * (jointScore p.symm : ℝ)) =
      ((6 - Complex.I) *
        (weightedMatchingValue (leftSpectrum true) rightSpectrum w -
          weightedMatchingValue (leftSpectrum false) rightSpectrum w)).re := by
    unfold weightedMatchingValue
    rw [← Finset.sum_sub_distrib, Finset.mul_sum, Complex.re_sum]
    apply Finset.sum_congr rfl
    intro p _
    have hp (s : Bool) : matchingProduct (leftSpectrum s) rightSpectrum p =
        GaussianInt.toComplex (vertexInt s p.symm) := by
      simpa only [Equiv.symm_symm] using matchingProduct_eq_exact s p.symm
    rw [hp, hp, ← mul_sub, mul_left_comm, Complex.re_ofReal_mul,
      ← directionInt_toComplex, ← map_sub, ← map_mul, ← GaussianInt.to_real_re]
    rfl
  have hbound : (∑ p, w p * (jointScore p.symm : ℝ)) ≤ 28850019 := calc
    _ ≤ ∑ p, w p * 28850019 := Finset.sum_le_sum fun p _ =>
      mul_le_mul_of_nonneg_left (by exact_mod_cast jointScore_le p.symm) (hw p)
    _ = _ := by rw [← Finset.sum_mul, hs, one_mul]
  rw [hsum, h true, h false, joint_determinant_score] at hbound
  norm_num at hbound

def triangleIndex (s : Bool) : Fin 3 → Fin 24 :=
  if s then ![0,3,9] else ![0,1,3]

private def triangleWeightInt (s : Bool) : Fin 3 → ℕ :=
  if s then ![2544406916225,4548876904424,7323809339576]
  else ![734165856995,370100097296,7031996299024]

private def triangleDenominator (s : Bool) : ℕ :=
  if s then 14417093160225 else 8136262253315

private theorem triangle_identity (s : Bool) :
    (2401 : GaussianInt) * (∑ j, (triangleWeightInt s j : GaussianInt) *
      vertexInt s (fourPerm (triangleIndex s j))) =
        (triangleDenominator s : GaussianInt) * valueInt s := by
  cases s <;> decide +kernel

/-- Each point has a certificate using the stated three vertices with
all three coefficients strictly positive. -/
theorem triangle_certificate (s : Bool) :
    ∃ w : Fin 3 → ℝ, (∀ j, 0 < w j) ∧ (∑ j, w j = 1) ∧
      (∑ j, (w j : ℂ) * matchingProduct (leftSpectrum s) rightSpectrum
        (fourPerm (triangleIndex s j)).symm) =
        determinantValue (leftSpectrum s) rightSpectrum mixer := by
  have hn : 0 < triangleDenominator s := by cases s <;> decide
  have hw (j : Fin 3) : 0 < triangleWeightInt s j := by
    cases s <;> fin_cases j <;> decide
  refine ⟨fun j => (triangleWeightInt s j : ℝ) / triangleDenominator s, ?_, ?_, ?_⟩
  · intro j
    exact div_pos (by exact_mod_cast hw j) (by exact_mod_cast hn)
  · have hmass : (∑ j, triangleWeightInt s j) = triangleDenominator s := by
      cases s <;> decide +kernel
    have hd : (triangleDenominator s : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    rw [← Finset.sum_div, ← Nat.cast_sum, hmass, div_self hd]
  · have he := congrArg GaussianInt.toComplex (triangle_identity s)
    simp only [map_mul, map_sum, map_natCast, map_ofNat] at he
    have hd : (triangleDenominator s : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
    rw [determinantValue_eq_exact]
    simp only [Complex.ofReal_div, Complex.ofReal_natCast, matchingProduct_eq_exact,
      div_mul_eq_mul_div, ← Finset.sum_div]
    field_simp [hd]
    linear_combination he

theorem holds_two_spectra (s : Bool) : Holds (leftSpectrum s) rightSpectrum mixer := by
  obtain ⟨w, hw, hs, he⟩ := triangle_certificate s
  refine mem_convexHull_of_exists_fintype w _ (fun j => (hw j).le) hs
    (fun j => ⟨(fourPerm (triangleIndex s j)).symm, rfl⟩) ?_
  simpa only [Complex.real_smul] using he

theorem triangle_signed_area (s : Bool) :
    let z j := matchingProduct (leftSpectrum s) rightSpectrum (fourPerm (triangleIndex s j)).symm
    (star (z 1 - z 0) * (z 2 - z 0)).im =
      if s then 40375066392900 else -193677606341510 := by
  dsimp only
  simp only [matchingProduct_eq_exact, Complex.star_def, ← GaussianInt.toComplex_sub,
    ← GaussianInt.toComplex_star, ← GaussianInt.toComplex_mul]
  have h : (star (vertexInt s (fourPerm (triangleIndex s 1)) -
      vertexInt s (fourPerm (triangleIndex s 0))) *
      (vertexInt s (fourPerm (triangleIndex s 2)) -
        vertexInt s (fourPerm (triangleIndex s 0)))).im =
      if s then 40375066392900 else -193677606341510 := by cases s <;> decide +kernel
  rw [← GaussianInt.to_real_im, h]
  cases s <;> norm_num

theorem injective_leftSpectrum (s : Bool) : Function.Injective (leftSpectrum s) := by
  have h : Function.Injective (leftInt s) := by cases s <;> decide +kernel
  exact GaussianInt.toComplex_injective.comp h

theorem injective_rightSpectrum : Function.Injective rightSpectrum := by
  have h : Function.Injective rightInt := by decide +kernel
  exact GaussianInt.toComplex_injective.comp h

/-- The flat scale is exp(-1/t²) for nonzero t. -/
def flatScale (t : ℝ) : ℝ := expNegInvGlue (t ^ 2)

theorem flatScale_value {t : ℝ} (ht : t ≠ 0) :
    flatScale t = Real.exp (-(t ^ 2)⁻¹) := by
  unfold flatScale expNegInvGlue
  rw [if_neg (not_le.mpr (sq_pos_of_ne_zero ht))]

private def positiveFlatScale (t : ℝ) : ℝ :=
  expNegInvGlue (2 * t) * expNegInvGlue (2 * t ^ 2 / (2 - t))

private theorem positiveFlatScale_of_nonpos {t : ℝ} (ht : t ≤ 0) :
    positiveFlatScale t = 0 := by
  rw [positiveFlatScale, expNegInvGlue.zero_of_nonpos (by linarith), zero_mul]

private theorem positiveFlatScale_of_pos {t : ℝ} (ht : 0 < t) (ht' : t < 2) :
    positiveFlatScale t = flatScale t := by
  have ht₀ : 0 < 2 * t := by linarith
  have ht₁ : 0 < 2 - t := by linarith
  have ht₂ : 0 < t ^ 2 := sq_pos_of_ne_zero ht.ne'
  rw [positiveFlatScale, flatScale, expNegInvGlue, expNegInvGlue, expNegInvGlue]
  rw [if_neg ht₀.not_le, if_neg (div_pos (mul_pos (by norm_num) ht₂) ht₁).not_le,
    if_neg ht₂.not_le, ← Real.exp_add]
  congr 1
  field_simp [ht.ne', ht₁.ne']
  <;> ring

/-- The first spectrum joins the scaled inputs with a flat junction. -/
def leftIntervalSpectrum (t : ℝ) (j : Fin 4) : ℂ :=
  (positiveFlatScale t : ℂ) * leftSpectrum true j +
    (positiveFlatScale (-t) : ℂ) * leftSpectrum false j

def rightIntervalSpectrum (t : ℝ) (j : Fin 4) : ℂ :=
  (flatScale t : ℂ) * rightSpectrum j

theorem intervalSpectrum_half (s : Bool) (t : ℝ)
    (ht : t ∈ (if s then Ioo 0 1 else Ioo (-1) 0)) :
    leftIntervalSpectrum t = fun j => (flatScale t : ℂ) * leftSpectrum s j := by
  funext j
  have hsym : flatScale (-t) = flatScale t := by simp [flatScale, neg_sq]
  cases s
  · change -1 < t ∧ t < 0 at ht
    rw [leftIntervalSpectrum, positiveFlatScale_of_nonpos ht.2.le,
      positiveFlatScale_of_pos (by linarith [ht.2]) (by linarith [ht.1]), hsym]
    simp
  · change 0 < t ∧ t < 1 at ht
    rw [leftIntervalSpectrum, positiveFlatScale_of_pos ht.1 (by linarith [ht.2]),
      positiveFlatScale_of_nonpos (by linarith [ht.1])]
    simp

private theorem contDiffOn_positiveFlatScale :
    ContDiffOn ℝ ∞ positiveFlatScale (Ioo (-2) 2) := by
  have h₁ : ContDiff ℝ ∞ (fun t : ℝ => 2 * t) := contDiff_const.mul contDiff_id
  have h₂ : ContDiffOn ℝ ∞ (fun t : ℝ => 2 * t ^ 2 / (2 - t)) (Ioo (-2) 2) := by
    have hnum : ContDiff ℝ ∞ (fun t : ℝ => 2 * t ^ 2) := contDiff_const.mul (contDiff_id.pow 2)
    have hden : ContDiff ℝ ∞ (fun t : ℝ => 2 - t) := contDiff_const.sub contDiff_id
    exact hnum.contDiffOn.div hden.contDiffOn (fun t ht => sub_ne_zero.mpr (ne_of_gt ht.2))
  exact (expNegInvGlue.contDiff.comp h₁).contDiffOn.mul
    (expNegInvGlue.contDiff.comp_contDiffOn h₂)

theorem interval_spectra_smooth (j : Fin 4) :
    ContDiffOn ℝ ∞ (fun t => leftIntervalSpectrum t j) (Icc (-1) 1) ∧
      ContDiffOn ℝ ∞ (fun t => rightIntervalSpectrum t j) (Icc (-1) 1) := by
  have hs : Icc (-1 : ℝ) 1 ⊆ Ioo (-2) 2 := fun t ht => by
    constructor <;> linarith [ht.1, ht.2]
  have h₁ : ContDiffOn ℝ ∞ positiveFlatScale (Icc (-1) 1) :=
    contDiffOn_positiveFlatScale.mono hs
  have hneg : ContDiff ℝ ∞ (fun t : ℝ => -t) := contDiff_id.neg
  have h₂ : ContDiffOn ℝ ∞ (fun t : ℝ => positiveFlatScale (-t)) (Icc (-1) 1) :=
    contDiffOn_positiveFlatScale.comp hneg.contDiffOn (fun t ht => by
      constructor <;> linarith [ht.1, ht.2])
  have hr : ContDiff ℝ ∞ flatScale := by
    unfold flatScale
    exact expNegInvGlue.contDiff.comp (contDiff_id.pow 2)
  constructor
  · exact ((Complex.ofRealCLM.contDiff.comp_contDiffOn h₁).mul contDiffOn_const).add
      ((Complex.ofRealCLM.contDiff.comp_contDiffOn h₂).mul contDiffOn_const)
  · exact ((Complex.ofRealCLM.contDiff.comp hr).mul contDiff_const).contDiffOn

theorem interval_spectra_at_zero :
    leftIntervalSpectrum 0 = 0 ∧ rightIntervalSpectrum 0 = 0 := by
  constructor <;> funext j <;> simp [leftIntervalSpectrum, rightIntervalSpectrum,
    positiveFlatScale, flatScale]

theorem interval_pointwise_holds (s : Bool) (t : ℝ)
    (ht : t ∈ (if s then Ioo 0 1 else Ioo (-1) 0)) :
    Holds (leftIntervalSpectrum t) (rightIntervalSpectrum t) mixer := by
  rw [intervalSpectrum_half s t ht]
  unfold Holds
  rw [show rightIntervalSpectrum t = fun j => (flatScale t : ℂ) * rightSpectrum j by rfl,
    determinantValue_scale]
  obtain ⟨w, hw, hs, he⟩ := triangle_certificate s
  refine mem_convexHull_of_exists_fintype w
    (fun j => matchingProduct (fun i => (flatScale t : ℂ) * leftSpectrum s i)
      (fun i => (flatScale t : ℂ) * rightSpectrum i) (fourPerm (triangleIndex s j)).symm)
    (fun j => (hw j).le) hs (fun j => Set.mem_range_self (fourPerm (triangleIndex s j)).symm) ?_
  simp only [matchingProduct_scale, Complex.real_smul,
    ← mul_left_comm ((flatScale t : ℂ) ^ Fintype.card (Fin 4)), ← Finset.mul_sum, he]

/-- On the smooth interval collision, pointwise representations cannot be
chosen continuously at zero. -/
theorem no_continuous_weights_interval :
    ¬ ∃ w : ℝ → FourPerm → ℝ,
      (∀ p, ContinuousWithinAt (fun t => w t p) (Icc (-1) 1) 0) ∧
      (∀ p, 0 ≤ w 0 p) ∧ (∑ p, w 0 p = 1) ∧
      ∀ t ∈ Icc (-1) 1, weightedMatchingValue (leftIntervalSpectrum t)
        (rightIntervalSpectrum t) (w t) =
          determinantValue (leftIntervalSpectrum t) (rightIntervalSpectrum t) mixer := by
  rintro ⟨w, hwc, hw, hs, hd⟩
  apply no_common_weights_two_spectra
  refine ⟨w 0, hw, hs, fun s => ?_⟩
  have hc : ContinuousWithinAt (fun t => weightedMatchingValue (leftSpectrum s)
      rightSpectrum (w t)) (Icc (-1) 1) 0 := by
    unfold ContinuousWithinAt weightedMatchingValue
    refine tendsto_finset_sum _ fun σ _ => ?_
    exact (Complex.continuous_ofReal.continuousAt.comp_continuousWithinAt (hwc σ)).mul
      continuousWithinAt_const
  apply continuous_zero_eq_of_open_half hc s
  intro t ht
  have ht₀ : t ≠ 0 := by
    cases s
    · exact ne_of_lt ht.2
    · exact ne_of_gt ht.1
  have ht' : t ∈ Icc (-1 : ℝ) 1 := by
    cases s <;> constructor <;> linarith [ht.1, ht.2]
  have hscale : (flatScale t : ℂ) ≠ 0 := by
    exact_mod_cast (expNegInvGlue.pos_of_pos (sq_pos_of_ne_zero ht₀)).ne'
  specialize hd t ht'
  rw [intervalSpectrum_half s t ht,
    show rightIntervalSpectrum t = fun j => (flatScale t : ℂ) * rightSpectrum j by rfl,
    determinantValue_scale] at hd
  unfold weightedMatchingValue at *
  simp_rw [matchingProduct_scale, mul_left_comm (_ : ℂ) ((flatScale t : ℂ) ^ _),
    ← Finset.mul_sum] at hd
  exact mul_left_cancel₀ (pow_ne_zero _ hscale) hd

end

end MOC.ContinuousWeightCounterexample
