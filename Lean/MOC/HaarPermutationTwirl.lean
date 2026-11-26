import MOC.HaarPermutationGram
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Data.Matrix.Bilinear
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.RingTheory.RootsOfUnity.Complex

/-! Haar averaging on the tensor basis indexed by finite words. -/

open BigOperators Matrix MeasureTheory

namespace MOC

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private abbrev Word (ι : Type*) := ι → ι
private abbrev UGroup (ι : Type*) [Fintype ι] [DecidableEq ι] := Matrix.unitaryGroup ι ℂ

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

private def tensorPower (A : Matrix ι ι ℂ) : Matrix (Word ι) (Word ι) ℂ :=
  Matrix.of fun f g => ∏ i, A (f i) (g i)

private theorem tensorPower_mul (A B : Matrix ι ι ℂ) :
    tensorPower (A * B) = tensorPower A * tensorPower B := by
  ext f g
  simp only [tensorPower, Matrix.of_apply, Matrix.mul_apply, Fintype.prod_sum,
    Finset.prod_mul_distrib]

private theorem tensorPower_one : tensorPower (1 : Matrix ι ι ℂ) = 1 := by
  classical
  ext f g
  by_cases h : f = g
  · subst g
    simp only [tensorPower, Matrix.of_apply, Matrix.one_apply_eq, Finset.prod_const_one]
  · obtain ⟨i, hi⟩ : ∃ i, f i ≠ g i := Function.ne_iff.mp h
    rw [Matrix.one_apply_ne h]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (Matrix.one_apply_ne hi)

private theorem tensorPower_conjTranspose (A : Matrix ι ι ℂ) :
    tensorPower Aᴴ = (tensorPower A)ᴴ := by
  ext f g
  simp only [tensorPower, Matrix.of_apply, Matrix.conjTranspose_apply, star_prod]

private theorem tensorPower_unitary (U : UGroup ι) :
    tensorPower (U : Matrix ι ι ℂ) * (tensorPower (U : Matrix ι ι ℂ))ᴴ = 1 := by
  rw [← tensorPower_conjTranspose, ← tensorPower_mul,
    Matrix.mem_unitaryGroup_iff.mp U.property, tensorPower_one]

private theorem compactSpace_unitary : CompactSpace (UGroup ι) := by
  let K : Set (Matrix ι ι ℂ) :=
    Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => Metric.closedBall (0 : ℂ) 1
  have hK : IsCompact K := isCompact_univ_pi fun _ =>
    isCompact_univ_pi fun _ => isCompact_closedBall (0 : ℂ) 1
  have hclosed : IsClosed (Matrix.unitaryGroup ι ℂ : Set (Matrix ι ι ℂ)) := by
    have he : (Matrix.unitaryGroup ι ℂ : Set (Matrix ι ι ℂ)) =
        {A | A * Aᴴ = 1} := by
      ext A
      exact Matrix.mem_unitaryGroup_iff
    rw [he]
    exact isClosed_eq (continuous_id.matrix_mul continuous_id.matrix_conjTranspose) continuous_const
  apply isCompact_iff_compactSpace.mp (hK.of_isClosed_subset hclosed ?_)
  intro U hU i _ j _
  rw [Metric.mem_closedBall, dist_zero_right]
  exact entry_norm_bound_of_unitary hU i j

private def wordPerm (p : Equiv.Perm ι) : Equiv.Perm (Word ι) where
  toFun f := f ∘ p
  invFun f := f ∘ p.symm
  left_inv f := funext fun i => congrArg f (p.apply_symm_apply i)
  right_inv f := funext fun i => congrArg f (p.symm_apply_apply i)

/-- The position permutation sends the basis vector at word `f` to the
basis vector at `f ∘ p`. -/
private def positionPermutation (p : Equiv.Perm ι) : Matrix (Word ι) (Word ι) ℂ := by
  classical
  exact ((wordPerm p).symm : Equiv.Perm (Word ι)).permMatrix ℂ

private theorem positionPermutation_commute (A : Matrix ι ι ℂ) (p : Equiv.Perm ι) :
    Commute (positionPermutation p) (tensorPower A) := by
  classical
  change (positionPermutation p) * tensorPower A = tensorPower A * positionPermutation p
  unfold positionPermutation
  rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
  ext f g
  change (∏ i, A (f (p.symm i)) (g i)) = ∏ i, A (f i) (g (p i))
  simpa only [Equiv.apply_symm_apply] using
    Equiv.prod_comp p.symm (fun i => A (f i) (g (p i)))

private def identityWordProjection : Matrix (Word ι) (Word ι) ℂ := by
  classical
  exact diagonal (fun f => if f = id then 1 else 0)

private def twirlTerm (U : UGroup ι) : Matrix (Word ι) (Word ι) ℂ :=
  (tensorPower (U : Matrix ι ι ℂ))ᴴ * identityWordProjection *
    tensorPower (U : Matrix ι ι ℂ)

private theorem continuous_tensorPower : Continuous (tensorPower : Matrix ι ι ℂ → _) := by
  apply continuous_matrix
  intro f g
  exact continuous_finset_prod _ fun i _ => continuous_id.matrix_elem (f i) (g i)

private theorem integrable_twirlTerm (μ : Measure (UGroup ι)) [IsFiniteMeasure μ] :
    Integrable twirlTerm μ := by
  letI : CompactSpace (UGroup ι) := compactSpace_unitary
  have hc : Continuous (fun U : UGroup ι => tensorPower (U : Matrix ι ι ℂ)) :=
    continuous_tensorPower.comp continuous_subtype_val
  have h : Continuous (twirlTerm : UGroup ι → Matrix (Word ι) (Word ι) ℂ) :=
    (hc.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul hc
  exact h.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- The average of the identity-word projection under the tensor action. -/
private def unitaryTwirl (μ : Measure (UGroup ι)) : Matrix (Word ι) (Word ι) ℂ :=
  ∫ U, twirlTerm U ∂μ

private theorem unitaryTwirl_trace_pair (μ : Measure (UGroup ι)) [IsProbabilityMeasure μ]
    (p : Equiv.Perm ι) :
    ((positionPermutation p)ᴴ * unitaryTwirl μ).trace =
      ((positionPermutation p)ᴴ * identityWordProjection).trace := by
  let R := (positionPermutation p)ᴴ
  let L : Matrix (Word ι) (Word ι) ℂ →L[ℂ] ℂ :=
    ((Matrix.traceLinearMap (n := Word ι) ℂ ℂ).comp
      (Matrix.mulLeftLinearMap (Word ι) ℂ R)).toContinuousLinearMap
  have hc (U : UGroup ι) : (R * twirlTerm U).trace = (R * identityWordProjection).trace := by
    let T := tensorPower (U : Matrix ι ι ℂ)
    have hcomm : Commute R T := by
      have he := congrArg Matrix.conjTranspose
        (positionPermutation_commute ((U : Matrix ι ι ℂ)ᴴ) p).eq
      exact (show T * R = R * T by
        simpa only [T, R, tensorPower_conjTranspose, Matrix.conjTranspose_mul,
          Matrix.conjTranspose_conjTranspose] using he).symm
    change (R * (Tᴴ * identityWordProjection * T)).trace = _
    calc
      _ = ((T * R) * Tᴴ * identityWordProjection).trace := by
        calc
          _ = ((R * Tᴴ * identityWordProjection) * T).trace := by
            simp only [Matrix.mul_assoc]
          _ = (T * (R * Tᴴ * identityWordProjection)).trace := Matrix.trace_mul_comm _ _
          _ = _ := by simp only [Matrix.mul_assoc]
      _ = _ := by
        rw [hcomm.eq.symm, Matrix.mul_assoc R, tensorPower_unitary U, Matrix.mul_one]
  change L (∫ U, twirlTerm U ∂μ) = _
  rw [← L.integral_comp_comm (integrable_twirlTerm μ)]
  change (∫ U, (R * twirlTerm U).trace ∂μ) = _
  simp only [hc, integral_const, measureReal_univ_eq_one, one_smul]

private theorem unitaryTwirl_commute_unitary (μ : Measure (UGroup ι)) [IsFiniteMeasure μ]
    [μ.IsMulRightInvariant] (V : UGroup ι) :
    Commute (unitaryTwirl μ) (tensorPower (V : Matrix ι ι ℂ)) := by
  let T := tensorPower (V : Matrix ι ι ℂ)
  let L : Matrix (Word ι) (Word ι) ℂ →L[ℂ] Matrix (Word ι) (Word ι) ℂ :=
    ((Matrix.mulRightLinearMap (Word ι) ℂ T).comp
      (Matrix.mulLeftLinearMap (Word ι) ℂ Tᴴ)).toContinuousLinearMap
  have hconj : Tᴴ * unitaryTwirl μ * T = unitaryTwirl μ := by
    change L (∫ U, twirlTerm U ∂μ) = _
    rw [← L.integral_comp_comm (integrable_twirlTerm μ)]
    calc
      _ = ∫ U, twirlTerm (U * V) ∂μ := by
        apply integral_congr_ae
        filter_upwards with U
        change Tᴴ * twirlTerm U * T = twirlTerm (U * V)
        simp only [twirlTerm, Matrix.UnitaryGroup.mul_apply, tensorPower_mul,
          Matrix.conjTranspose_mul, T, Matrix.mul_assoc]
      _ = _ := integral_mul_right_eq_self twirlTerm V
  change unitaryTwirl μ * T = T * unitaryTwirl μ
  have h := congrArg (fun M : Matrix (Word ι) (Word ι) ℂ => T * M) hconj
  change T * (Tᴴ * unitaryTwirl μ * T) = T * unitaryTwirl μ at h
  rw [← Matrix.mul_assoc T (Tᴴ * unitaryTwirl μ) T,
    ← Matrix.mul_assoc T Tᴴ (unitaryTwirl μ), tensorPower_unitary V, Matrix.one_mul] at h
  exact h

private theorem tensorPower_diagonal (a : ι → ℂ) :
    tensorPower (diagonal a) = diagonal (fun f : Word ι => ∏ i, a (f i)) := by
  classical
  ext f g
  by_cases h : f = g
  · subst g
    simp only [tensorPower, Matrix.of_apply, Matrix.diagonal_apply_eq]
  · rw [Matrix.diagonal_apply_ne _ h]
    obtain ⟨i, hi⟩ := Function.ne_iff.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (Matrix.diagonal_apply_ne _ hi)

private def wordMultiplicity (f : Word ι) (j : ι) : ℕ :=
  (Finset.univ.filter (fun i => f i = j)).card

private theorem wordMultiplicity_lt (f : Word ι) (j : ι) :
    wordMultiplicity f j < Fintype.card ι + 1 := by
  apply Nat.lt_succ_of_le
  simpa only [wordMultiplicity, Finset.card_univ] using
    Finset.card_filter_le Finset.univ (fun i => f i = j)

private theorem tensorPower_unit_phase_diagonal (a : ι → ℂ) (ha : ∀ i, ‖a i‖ = 1) :
    diagonal a ∈ Matrix.unitaryGroup ι ℂ := by
  apply Matrix.mem_unitaryGroup_iff.mpr
  change diagonal a * (diagonal a)ᴴ = 1
  rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
  have he (i : ι) : a i * star (a i) = 1 := by
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, ha i, one_pow,
      Complex.ofReal_one]
  simp only [Pi.mul_apply, Pi.star_apply, he, Matrix.diagonal_one]

private theorem word_phase_product (f : Word ι) (j : ι) (z : ℂ) :
    (∏ i, if f i = j then z else 1) = z ^ wordMultiplicity f j := by
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]
  rfl

private theorem commute_diagonal_of_commute_unitary
    (F : Matrix (Word ι) (Word ι) ℂ)
    (hF : ∀ U : UGroup ι, Commute F (tensorPower (U : Matrix ι ι ℂ)))
    (a : ι → ℂ) : Commute F (tensorPower (diagonal a)) := by
  classical
  let n := Fintype.card ι + 1
  let z := Complex.exp (2 * Real.pi * Complex.I / n)
  have hprimitive : IsPrimitiveRoot z n := Complex.isPrimitiveRoot_exp n (Nat.succ_ne_zero _)
  have hznorm : ‖z‖ = 1 := by
    have he := congrArg norm hprimitive.pow_eq_one
    rw [norm_pow, norm_one] at he
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg z) (Nat.succ_ne_zero _)).mp he
  have hmultiplicity (f g : Word ι) (hfg : F f g ≠ 0) (j : ι) :
      wordMultiplicity f j = wordMultiplicity g j := by
    let d (i : ι) := if i = j then z else 1
    have hdn (i : ι) : ‖d i‖ = 1 := by
      by_cases hi : i = j <;> simp only [d, hi, if_true, if_false, hznorm, norm_one]
    let U : UGroup ι := ⟨diagonal d, tensorPower_unit_phase_diagonal d hdn⟩
    have hd : Commute F (tensorPower (diagonal d)) := hF U
    rw [tensorPower_diagonal] at hd
    have he := congrArg (fun M : Matrix (Word ι) (Word ι) ℂ => M f g) hd.eq
    simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, d, word_phase_product] at he
    rw [mul_comm (z ^ wordMultiplicity f j) (F f g)] at he
    exact hprimitive.pow_inj (wordMultiplicity_lt f j) (wordMultiplicity_lt g j)
      (mul_left_cancel₀ hfg he).symm
  rw [tensorPower_diagonal]
  change F * diagonal (fun f : Word ι => ∏ i, a (f i)) =
    diagonal (fun f : Word ι => ∏ i, a (f i)) * F
  ext f g
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases hfg : F f g = 0
  · rw [hfg, zero_mul, mul_zero]
  · have hp (h : Word ι) : (∏ i, a (h i)) = ∏ j, a j ^ wordMultiplicity h j := by
      simpa only [Finset.prod_const, wordMultiplicity] using
        (Finset.prod_fiberwise' Finset.univ h a).symm
    rw [hp f, hp g]
    simp only [hmultiplicity f g hfg, mul_comm (F f g)]

end

end MOC
