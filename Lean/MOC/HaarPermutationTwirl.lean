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
open scoped InnerProductSpace

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

private def colorMapMatrix (f : Word ι) : Matrix ι ι ℂ :=
  Matrix.of fun i j => if f j = i then 1 else 0

private theorem colorMapMatrix_eq_diagonal_mul_unitary (f : Word ι) :
    ∃ (d : ι → ℂ) (U : UGroup ι), colorMapMatrix f = diagonal d * (U : Matrix ι ι ℂ) := by
  classical
  let A := colorMapMatrix f
  let x (i : ι) : EuclideanSpace ℂ ι :=
    (WithLp.equiv 2 _).symm (fun j => star (A i j))
  let v (i : ι) : EuclideanSpace ℂ ι := (↑(‖x i‖⁻¹) : ℂ) • x i
  let s : Set ι := {i | x i ≠ 0}
  have hx (i j : ι) (hij : i ≠ j) : ⟪x i, x j⟫_ℂ = 0 := by
    dsimp only [x]
    rw [EuclideanSpace.inner_piLp_equiv_symm, dotProduct]
    apply Finset.sum_eq_zero
    intro k _
    by_cases hk : f k = i
    · have hn : f k ≠ j := fun h => hij (hk.symm.trans h)
      simp only [A, colorMapMatrix, Matrix.of_apply, hn, if_false, star_zero, zero_mul]
    · simp only [A, colorMapMatrix, Matrix.of_apply, hk, if_false, Pi.star_apply,
        star_zero, mul_zero]
  have hv : Orthonormal ℂ (s.restrict v) := by
    rw [orthonormal_iff_ite]
    intro i j
    by_cases hij : i = j
    · subst j
      rw [if_pos rfl, inner_self_eq_norm_sq_to_K]
      have hnorm : ‖v i.val‖ = 1 := by
        change ‖(↑(‖x i.val‖⁻¹) : ℂ) • x i.val‖ = 1
        rw [norm_smul, Complex.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
          inv_mul_cancel₀ (norm_ne_zero_iff.mpr i.property)]
      simpa only [Set.restrict_apply, hnorm, RCLike.ofReal_one, one_pow]
    · rw [if_neg hij]
      have hn : i.val ≠ j.val := fun h => hij (Subtype.ext h)
      change ⟪v i.val, v j.val⟫_ℂ = 0
      simp only [v, inner_smul_left, inner_smul_right, hx _ _ hn, mul_zero]
  obtain ⟨B, hB⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq
    (finrank_euclideanSpace (𝕜 := ℂ) (ι := ι)) hv
  let U : Matrix ι ι ℂ := Matrix.of fun i j => star (B i j)
  have hU : U ∈ Matrix.unitaryGroup ι ℂ := by
    apply Matrix.mem_unitaryGroup_iff.mpr
    change U * Uᴴ = 1
    ext i j : 1
    have h := orthonormal_iff_ite.mp B.orthonormal i j
    rw [EuclideanSpace.inner_eq_star_dotProduct] at h
    change (∑ k, B j k * star (B i k)) = if i = j then (1 : ℂ) else 0 at h
    simpa only [U, Matrix.of_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, star_star,
      Matrix.one_apply, mul_comm] using h
  refine ⟨fun i => (‖x i‖ : ℂ), ⟨U, hU⟩, ?_⟩
  change A = diagonal (fun i => (‖x i‖ : ℂ)) * U
  ext i j : 1
  rw [Matrix.diagonal_mul]
  by_cases hi : x i = 0
  · have h := congrArg (fun y : EuclideanSpace ℂ ι => y j) hi
    change star (A i j) = 0 at h
    have hz : A i j = 0 := star_injective (h.trans star_zero.symm)
    simp only [hi, norm_zero, Complex.ofReal_zero, zero_mul, hz]
  · have he : (‖x i‖ : ℂ) • B i = x i := by
      rw [hB i hi, v, smul_smul, Complex.ofReal_inv,
        mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hi)), one_smul]
    have hc := congrArg (fun y : EuclideanSpace ℂ ι => y j) he
    change (‖x i‖ : ℂ) * B i j = star (A i j) at hc
    have hs := congrArg star hc
    simpa only [U, Matrix.of_apply, star_mul, Complex.star_def, Complex.conj_ofReal,
      Complex.conj_conj, mul_comm] using hs.symm

private theorem tensorPower_colorMapMatrix_apply (f x y : Word ι) :
    tensorPower (colorMapMatrix f) x y = if x = f ∘ y then 1 else 0 := by
  classical
  by_cases h : x = f ∘ y
  · subst x
    simp only [tensorPower, colorMapMatrix, Matrix.of_apply, Function.comp_apply, if_pos rfl,
      Finset.prod_const_one]
  · rw [if_neg h]
    obtain ⟨i, hi⟩ := Function.ne_iff.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by
      change (if f (y i) = x i then (1 : ℂ) else 0) = 0
      exact if_neg hi.symm)

private theorem positionPermutation_apply (p : Equiv.Perm ι) (f g : Word ι) :
    positionPermutation p f g = if f = g ∘ p then 1 else 0 := by
  classical
  simp only [positionPermutation, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply,
    Option.mem_some_iff, Equiv.symm_apply_eq, wordPerm]

private theorem tensorPower_commutant_sum_positionPermutations
    (F : Matrix (Word ι) (Word ι) ℂ)
    (hF : ∀ U : UGroup ι, Commute F (tensorPower (U : Matrix ι ι ℂ))) :
    F = ∑ p : Equiv.Perm ι, F (p : Word ι) id • positionPermutation p := by
  classical
  have hdiag := commute_diagonal_of_commute_unitary F hF
  have hzero (f : Word ι) (hf : ¬Function.Injective f) : F f id = 0 := by
    have hn : ¬Function.Surjective f := fun h => hf (Finite.injective_iff_surjective.mpr h)
    change ¬ ∀ j, ∃ i, f i = j at hn
    push_neg at hn
    obtain ⟨j, hj⟩ := hn
    let d (i : ι) : ℂ := if i = j then 0 else 1
    have h₁ : (∏ i, d (f i)) = 1 := Finset.prod_eq_one fun i _ => if_neg (hj i)
    have h₀ : (∏ i, d (id i)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ j) (if_pos rfl)
    have hd := hdiag d
    rw [tensorPower_diagonal] at hd
    have he := congrArg (fun M : Matrix (Word ι) (Word ι) ℂ => M f id) hd.eq
    simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, h₁, h₀, mul_zero, one_mul] at he
    exact he.symm
  let e : Equiv.Perm ι ↪ Word ι := ⟨fun p => p, fun _ _ h => Equiv.ext (congrFun h)⟩
  ext f g : 1
  have hmap : Commute F (tensorPower (colorMapMatrix g)) := by
    obtain ⟨d, U, hU⟩ := colorMapMatrix_eq_diagonal_mul_unitary g
    rw [hU, tensorPower_mul]
    exact (hdiag d).mul_right (hF U)
  have he := congrArg (fun M : Matrix (Word ι) (Word ι) ℂ => M f id) hmap.eq
  simp only [Matrix.mul_apply, tensorPower_colorMapMatrix_apply, Function.comp_id] at he
  rw [Finset.sum_eq_single g] at he
  · simp only [if_pos rfl, mul_one] at he
    rw [he]
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, positionPermutation_apply,
      mul_comm (F _ id)]
    change (∑ y, (if f = g ∘ y then (1 : ℂ) else 0) * F y id) =
      ∑ p, (if f = g ∘ e p then (1 : ℂ) else 0) * F (e p) id
    rw [← Finset.sum_map]
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro y _ hy
    have hn : ¬ Function.Injective y := by
      intro hi
      let p : Equiv.Perm ι := Equiv.ofBijective y (Finite.injective_iff_bijective.mp hi)
      exact hy (Finset.mem_map.mpr ⟨p, Finset.mem_univ p, rfl⟩)
    rw [hzero y hn, mul_zero]
  · intro y _ hy
    rw [if_neg hy, mul_zero]
  · simp

private theorem positionPermutation_adjoint (p : Equiv.Perm ι) :
    (positionPermutation p)ᴴ = (wordPerm p).permMatrix ℂ := by
  classical
  simp only [positionPermutation, Matrix.conjTranspose_permMatrix, Equiv.Perm.inv_def,
    Equiv.symm_symm]

private theorem positionPermutation_trace_pair (p q : Equiv.Perm ι) :
    ((positionPermutation p)ᴴ * positionPermutation q).trace =
      (permutationColorGram p q : ℂ) := by
  classical
  rw [positionPermutation_adjoint, PEquiv.toMatrix_toPEquiv_mul,
    permutationColorGram_apply_colorings, Complex.ofReal_sum]
  change (∑ f : Word ι, positionPermutation q (f ∘ p) f) = _
  apply Finset.sum_congr rfl
  intro f _
  rw [positionPermutation_apply]
  by_cases h : f ∘ p = f ∘ q
  · simp only [h, if_true, Complex.ofReal_one]
  · simp only [h, if_false, Complex.ofReal_zero]

private theorem positionPermutation_trace_identity_projection (p : Equiv.Perm ι) :
    ((positionPermutation p)ᴴ * identityWordProjection).trace =
      (Pi.single 1 (1 : ℂ) : Equiv.Perm ι → ℂ) p := by
  classical
  rw [positionPermutation_adjoint, PEquiv.toMatrix_toPEquiv_mul]
  change (∑ f : Word ι, identityWordProjection (f ∘ p) f) = _
  rw [Finset.sum_eq_single id]
  · have h : id ∘ (p : Word ι) = id ↔ p = 1 := by
      constructor
      · intro he
        exact Equiv.ext (congrFun he)
      · rintro rfl
        rfl
    simp only [identityWordProjection, Matrix.diagonal_apply, h, if_pos rfl, Pi.single_apply]
  · intro f _ hf
    simp only [identityWordProjection, Matrix.diagonal_apply, hf, if_false, ite_self]
  · simp

private theorem twirlTerm_apply (U : UGroup ι) (f g : Word ι) :
    twirlTerm U f g = star (∏ i, U i (f i)) * ∏ i, U i (g i) := by
  classical
  unfold twirlTerm
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, identityWordProjection, Matrix.diagonal_apply_eq]
  rw [Finset.sum_eq_single id]
  · simp only [if_pos rfl, mul_one, Matrix.conjTranspose_apply, tensorPower,
      Matrix.of_apply, id_eq]
  · intro j _ hj
    rw [if_neg hj, mul_zero, zero_mul]
  · simp

private theorem unitaryTwirl_apply (μ : Measure (UGroup ι)) [IsFiniteMeasure μ]
    (f g : Word ι) :
    unitaryTwirl μ f g = ∫ U, star (∏ i, U i (f i)) * ∏ i, U i (g i) ∂μ := by
  let L : Matrix (Word ι) (Word ι) ℂ →L[ℂ] ℂ :=
    (Matrix.entryLinearMap ℂ ℂ f g).toContinuousLinearMap
  change L (∫ U, twirlTerm U ∂μ) = _
  rw [← L.integral_comp_comm (integrable_twirlTerm μ)]
  exact integral_congr_ae (Filter.Eventually.of_forall fun U => twirlTerm_apply U f g)

/-- Integration against a right-invariant probability measure on the unitary
group gives the inverse permutation Gram matrix on permutation monomials. -/
theorem haar_permutationMonomial_covariance
    (μ : Measure (Matrix.unitaryGroup ι ℂ)) [IsProbabilityMeasure μ] [μ.IsMulRightInvariant]
    (p q : Equiv.Perm ι) :
    (∫ U, star (∏ i, U i (p i)) * ∏ i, U i (q i) ∂μ) =
      ((permutationColorGram (ι := ι)).map Complex.ofReal)⁻¹ p q := by
  classical
  let F := unitaryTwirl μ
  let b (r : Equiv.Perm ι) := F (r : Word ι) id
  let G : Matrix (Equiv.Perm ι) (Equiv.Perm ι) ℂ :=
    (permutationColorGram (ι := ι)).map Complex.ofReal
  let C : Matrix (Equiv.Perm ι) (Equiv.Perm ι) ℂ :=
    Matrix.of fun r s => F (r : Word ι) (s : Word ι)
  have hF : F = ∑ r, b r • positionPermutation r :=
    tensorPower_commutant_sum_positionPermutations F (unitaryTwirl_commute_unitary μ)
  have hG (s r t : Equiv.Perm ι) : G (s * r) (s * t) = G r t := by
    change (permutationColorGram (s * r) (s * t) : ℂ) = (permutationColorGram r t : ℂ)
    rw [permutationColorGram_apply_colorings, permutationColorGram_apply_colorings]
    apply congrArg Complex.ofReal
    simpa only [wordPerm, Function.comp_assoc, Equiv.Perm.coe_mul] using
      Equiv.sum_comp (wordPerm s)
        (fun f => if f ∘ r = f ∘ t then (1 : ℝ) else 0)
  have hb (r : Equiv.Perm ι) : (G *ᵥ b) r = (Pi.single 1 1 : Equiv.Perm ι → ℂ) r := by
    have hp := unitaryTwirl_trace_pair μ r
    change ((positionPermutation r)ᴴ * F).trace = _ at hp
    rw [hF, Finset.mul_sum, Matrix.trace_sum] at hp
    simp only [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul,
      positionPermutation_trace_pair, positionPermutation_trace_identity_projection] at hp
    calc
      (G *ᵥ b) r = ∑ t, b t * (permutationColorGram r t : ℂ) := by
        change (∑ t, (permutationColorGram r t : ℂ) * b t) = _
        exact Finset.sum_congr rfl (fun t _ => mul_comm _ _)
      _ = _ := hp
  have hC (r s : Equiv.Perm ι) : C r s = b (s⁻¹ * r) := by
    change F (r : Word ι) (s : Word ι) = _
    have he (t : Equiv.Perm ι) :
        (r : Word ι) = (s : Word ι) ∘ t ↔ t = s⁻¹ * r := by
      constructor
      · intro h
        exact Equiv.ext fun i => by
          simp only [Equiv.Perm.mul_apply, congrFun h i, Function.comp_apply,
            Equiv.Perm.inv_apply_self]
      · rintro rfl
        funext i
        simp only [Function.comp_apply, Equiv.Perm.mul_apply, Equiv.Perm.apply_inv_self]
    rw [hF, Matrix.sum_apply]
    simp only [Matrix.smul_apply, smul_eq_mul, positionPermutation_apply, he,
      mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have hGC : G * C = 1 := by
    ext r s : 1
    rw [Matrix.mul_apply,
      ← Equiv.sum_comp (Equiv.mulLeft s) (fun t => G r t * C t s)]
    change (∑ t, G r (s * t) * C (s * t) s) = (1 : Matrix _ _ ℂ) r s
    have hh (t : Equiv.Perm ι) : G r (s * t) = G (s⁻¹ * r) t := by
      simpa only [← mul_assoc, mul_inv_cancel, one_mul] using hG s (s⁻¹ * r) t
    have hc (t : Equiv.Perm ι) : C (s * t) s = b t := by
      rw [hC, ← mul_assoc, inv_mul_cancel, one_mul]
    simp only [hh, hc]
    change (G *ᵥ b) (s⁻¹ * r) = (1 : Matrix _ _ ℂ) r s
    rw [hb, Pi.single_apply, Matrix.one_apply]
    simp only [eq_comm (a := (1 : Equiv.Perm ι)) (b := s⁻¹ * r), inv_mul_eq_one,
      eq_comm (a := s) (b := r)]
  have hInv : G⁻¹ = C := Matrix.inv_eq_right_inv hGC
  change _ = G⁻¹ p q
  rw [hInv]
  exact (unitaryTwirl_apply μ (p : Word ι) (q : Word ι)).symm

end

end MOC
