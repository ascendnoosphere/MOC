import MOC.FourMatchingRelations
import Mathlib.Data.Matrix.Rank
import Mathlib.Data.Real.StarOrdered
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! The real auxiliary jet for `(0, 1, -1, w)` and the order-four
matching-function sums of squares. All finite checks use integer arithmetic. -/

open BigOperators Matrix

namespace MOC

abbrev MatchingJetIndex := Fin 2 × Fin 16
abbrev MatchingCornerIndex := Fin 2 × Fin 2

/-- The row index is the lexicographic permutation label. The column is
the degree in the last auxiliary value and the subset mask. -/
private def matchingMask (m : Fin 16) : Finset (Fin 4) :=
  Finset.univ.filter fun i => m.val.testBit i.val

private def specializedMonomial (d : Fin 2) (s : Finset (Fin 4)) : ℤ :=
  if ((3 : Fin 4) ∈ s) ↔ d = 1 then
    ∏ j ∈ s, (![0, 1, -1, 1] : Fin 4 → ℤ) j
  else 0

private def matchingJetInt (p : Fin 24) (c : MatchingJetIndex) : ℤ :=
  specializedMonomial c.1 ((matchingMask c.2).map (fourPerm p).toEmbedding)

noncomputable def realMatchingJet : Matrix (Fin 24) MatchingJetIndex ℝ :=
  fun p c => matchingJetInt p c

private def matchingIndicatorInt (a b : Fin 16) (p : Fin 24) : ℤ :=
  if (matchingMask a).map (fourPerm p).toEmbedding = matchingMask b then 1 else 0

/-- The indicator that a permutation maps one subset onto another. -/
noncomputable def realMatchingIndicator (a b : Fin 16) (p : Fin 24) : ℝ :=
  matchingIndicatorInt a b p

private noncomputable def realMatchingEvaluation : (Fin 14 → ℝ) →ₗ[ℝ] (Fin 24 → ℝ) where
  toFun := fourMatchingEvaluation
  map_add' x y := by
    funext p
    fin_cases p <;> simp [fourMatchingEvaluation] <;> ring
  map_smul' c x := by
    funext p
    fin_cases p <;> simp [fourMatchingEvaluation] <;> ring

/-- The real function space in the existing noncrossing matching coordinates. -/
noncomputable def realMatchingFunctionSpace : Submodule ℝ (Fin 24 → ℝ) :=
  LinearMap.range realMatchingEvaluation

theorem realMatchingFunctionSpace_finrank :
    Module.finrank ℝ realMatchingFunctionSpace = 14 := by
  let e := LinearEquiv.ofInjective realMatchingEvaluation
    (show Function.Injective realMatchingEvaluation from fourMatchingEvaluation_injective)
  simpa only [realMatchingFunctionSpace, Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
    using e.finrank_eq.symm

private theorem evaluation_intCast (m : Fin 14 → ℤ) (p : Fin 24) :
    fourMatchingEvaluation (fun j => (m j : ℝ)) p =
      (fourMatchingEvaluation (R := ℤ) m p : ℝ) := by
  fin_cases p <;> simp [fourMatchingEvaluation]

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem jetColumn_int (c : MatchingJetIndex) (p : Fin 24) :
    fourMatchingEvaluation (fourMatchingCoordinatesOfValues (fun q => matchingJetInt q c)) p =
      matchingJetInt p c := by
  exact (by decide +kernel : ∀ c : MatchingJetIndex, ∀ p : Fin 24,
    fourMatchingEvaluation (fourMatchingCoordinatesOfValues (fun q => matchingJetInt q c)) p =
      matchingJetInt p c) c p

set_option maxRecDepth 12000 in
set_option maxHeartbeats 14000000 in
private theorem indicatorColumn_int (a b : Fin 16) (p : Fin 24) :
    fourMatchingEvaluation (fourMatchingCoordinatesOfValues (matchingIndicatorInt a b)) p =
      matchingIndicatorInt a b p := by
  exact (by decide +kernel : ∀ a b : Fin 16, ∀ p : Fin 24,
    fourMatchingEvaluation (fourMatchingCoordinatesOfValues (matchingIndicatorInt a b)) p =
      matchingIndicatorInt a b p) a b p

theorem realMatchingIndicator_mem (a b : Fin 16) :
    realMatchingIndicator a b ∈ realMatchingFunctionSpace := by
  refine ⟨fun k => (fourMatchingCoordinatesOfValues (R := ℤ) (matchingIndicatorInt a b) k : ℝ), ?_⟩
  funext p
  change fourMatchingEvaluation _ p = _
  rw [evaluation_intCast, indicatorColumn_int]

private theorem jetColumn_mem (c : MatchingJetIndex) :
    (fun p => realMatchingJet p c) ∈ realMatchingFunctionSpace := by
  refine ⟨fun k => (fourMatchingCoordinatesOfValues (R := ℤ) (fun q => matchingJetInt q c) k : ℝ), ?_⟩
  funext p
  change fourMatchingEvaluation _ p = (matchingJetInt p c : ℝ)
  rw [evaluation_intCast, jetColumn_int]

private def pivotColumn : Fin 14 → MatchingJetIndex :=
  ![(0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6),
    (0, 9), (0, 10), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5)]

-- Twice the coefficients of the noncrossing coordinate vectors in the selected jet columns.
private def pivotWeight : Fin 14 → Fin 14 → ℤ :=
  ![![4, 0, 0, 2, 0, 2, 0, 0, 0, -4, -2, 0, -2, 0],
    ![2, 2, 1, 1, 1, 1, 0, 0, 0, -2, -1, -1, -1, -1],
    ![2, 0, 0, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0],
    ![2, 1, 0, 1, 0, 1, 0, 1, 0, -2, 0, 0, 0, 0],
    ![2, 0, 0, 2, 0, 2, 0, 2, 0, -2, 0, 0, 0, 0],
    ![2, 0, 0, 2, 0, 0, 0, 0, 0, -2, -2, 0, 0, 0],
    ![1, 1, 1, 1, 0, 0, 0, 0, 0, -1, -1, -1, 0, 0],
    ![2, 0, 0, 0, 0, 0, 0, 0, 0, -2, -2, 0, 0, 0],
    ![2, 0, 0, 0, 0, 0, 0, 0, 0, -2, -2, 0, -2, 0],
    ![4, 1, 1, 2, 0, 1, 1, 1, 1, -2, -2, 0, 0, 0],
    ![4, 0, 0, 4, 0, 2, 2, 2, 2, -2, -2, 0, 0, 0],
    ![3, 1, 1, 1, 1, 1, 1, 0, 0, -2, -2, 0, -2, 0],
    ![4, 0, 0, 2, 0, 2, 2, 0, 0, -2, -2, 0, -2, 0],
    ![2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem pivotWeight_int :
    ∀ k : Fin 14, ∀ p : Fin 24,
      ∑ j : Fin 14, matchingJetInt p (pivotColumn j) * pivotWeight k j =
        2 * fourMatchingEvaluation (Pi.single k (1 : ℤ)) p := by
  decide +kernel

private theorem realJet_range_generator (k : Fin 14) :
    realMatchingEvaluation (Pi.single k 1) ∈ LinearMap.range realMatchingJet.mulVecLin := by
  refine ⟨∑ j : Fin 14, ((pivotWeight k j : ℝ) / 2) •
    (Pi.single (pivotColumn j) 1 : MatchingJetIndex → ℝ), ?_⟩
  have h p : (∑ j : Fin 14, realMatchingJet p (pivotColumn j) * (pivotWeight k j : ℝ)) =
      2 * fourMatchingEvaluation (Pi.single k (1 : ℝ)) p := by
    have hcast := congrArg (Int.cast : ℤ → ℝ) (pivotWeight_int k p)
    have hs : (fun j => (((Pi.single k 1 : Fin 14 → ℤ) j : ℤ) : ℝ)) = Pi.single k (1 : ℝ) := by
      funext j
      by_cases h : j = k <;> simp [Pi.single_apply, h]
    simpa only [Int.cast_sum, Int.cast_mul, Int.cast_ofNat, realMatchingJet, ← evaluation_intCast, hs]
      using hcast
  funext p
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    Matrix.mulVecLin_apply, Matrix.mulVec_single_one]
  change (∑ j : Fin 14, (pivotWeight k j : ℝ) / 2 * realMatchingJet p (pivotColumn j)) =
    fourMatchingEvaluation (Pi.single k (1 : ℝ)) p
  calc
    _ = (∑ j : Fin 14, realMatchingJet p (pivotColumn j) * (pivotWeight k j : ℝ)) / 2 := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = _ := by rw [h p]; ring

theorem realMatchingJet_range :
    LinearMap.range realMatchingJet.mulVecLin = realMatchingFunctionSpace := by
  apply le_antisymm
  · rintro _ ⟨v, rfl⟩
    have h : realMatchingJet.mulVecLin v = ∑ c, v c • (fun p => realMatchingJet p c) := by
      funext p
      simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply,
        smul_eq_mul]
      exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
    rw [h]
    exact realMatchingFunctionSpace.sum_mem fun c _ =>
      realMatchingFunctionSpace.smul_mem (v c) (jetColumn_mem c)
  · rintro _ ⟨m, rfl⟩
    have he : m = ∑ k : Fin 14, m k • (Pi.single k 1 : Fin 14 → ℝ) := by
      funext j
      simp [Finset.sum_apply, Pi.single_apply, eq_comm]
    rw [he, map_sum]
    exact (LinearMap.range realMatchingJet.mulVecLin).sum_mem fun k _ => by
      rw [map_smul]
      exact (LinearMap.range realMatchingJet.mulVecLin).smul_mem _ (realJet_range_generator k)

private noncomputable def subsetIndicatorSpan : Submodule ℝ (Fin 24 → ℝ) :=
  Submodule.span ℝ (Set.range fun a : Fin 16 × Fin 16 => realMatchingIndicator a.1 a.2)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8500000 in
private theorem jet_indicator_expansion_int :
    ∀ c : MatchingJetIndex, ∀ p : Fin 24, matchingJetInt p c =
      ∑ b : Fin 16, specializedMonomial c.1 (matchingMask b) * matchingIndicatorInt c.2 b p := by
  decide +kernel

/-- The noncrossing coordinate space is the span of the intrinsic
subset-image indicators. -/
theorem realMatchingFunctionSpace_eq_indicator_span :
    realMatchingFunctionSpace =
      Submodule.span ℝ (Set.range fun a : Fin 16 × Fin 16 => realMatchingIndicator a.1 a.2) := by
  change realMatchingFunctionSpace = subsetIndicatorSpan
  apply le_antisymm
  · rw [← realMatchingJet_range, Matrix.range_mulVecLin]
    apply Submodule.span_le.mpr
    rintro _ ⟨c, rfl⟩
    have he : realMatchingJet.col c =
        ∑ b : Fin 16, (specializedMonomial c.1 (matchingMask b) : ℝ) •
          realMatchingIndicator c.2 b := by
      funext p
      simpa only [realMatchingJet, Matrix.col, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
        realMatchingIndicator, Int.cast_sum, Int.cast_mul] using
        congrArg (Int.cast : ℤ → ℝ) (jet_indicator_expansion_int c p)
    rw [he]
    exact subsetIndicatorSpan.sum_mem fun b _ =>
      subsetIndicatorSpan.smul_mem _ (Submodule.subset_span ⟨(c.2, b), rfl⟩)
  · apply Submodule.span_le.mpr
    rintro _ ⟨a, rfl⟩
    exact realMatchingIndicator_mem a.1 a.2

/-- Finite sums of squares of intrinsic real matching functions. -/
def IsRealMatchingSOS (g : Fin 24 → ℝ) : Prop :=
  ∃ n : ℕ, ∃ f : Fin n → Fin 14 → ℝ,
    ∀ p, g p = ∑ k, (fourMatchingEvaluation (f k) p)^2

private def matchingSignInt (p : Fin 24) : ℤ :=
  ↑(Equiv.Perm.sign (fourPerm p))

/-- The alternating sign of a matching permutation as a real coefficient. -/
noncomputable def matchingSign (p : Fin 24) : ℝ :=
  matchingSignInt p

private def skewEntry {R : Type*} [CommRing R] (i j : Fin 2) : R :=
  if i = j then 0 else if i = 0 then 1 else -1

/-- The tensor product of the two real two-dimensional skew forms. -/
def matchingCornerKernel {R : Type*} [CommRing R] :
    Matrix MatchingCornerIndex MatchingCornerIndex R :=
  fun a b => skewEntry a.1 b.1 * skewEntry a.2 b.2

private def exceptionalColumn (j : Fin 2) (m : Fin 16) : ℤ :=
  if j = 0 then
    if m = 3 ∨ m = 12 then 1 else if m = 5 ∨ m = 10 then -1 else 0
  else
    if m = 3 ∨ m = 12 ∨ m = 5 ∨ m = 10 then 1 else if m = 6 ∨ m = 9 then -2 else 0

private def exceptionalEmbeddingInt (i : MatchingJetIndex) (a : MatchingCornerIndex) : ℤ :=
  if i.1 = a.1 then exceptionalColumn a.2 i.2 else 0

noncomputable def realMatchingExceptionalEmbedding : Matrix MatchingJetIndex MatchingCornerIndex ℝ :=
  fun i a => exceptionalEmbeddingInt i a

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
private theorem signedJetKernel_int :
    ∀ i j : MatchingJetIndex,
      ∑ p : Fin 24, matchingSignInt p * matchingJetInt p i * matchingJetInt p j =
        ∑ a : MatchingCornerIndex, ∑ b : MatchingCornerIndex,
          exceptionalEmbeddingInt i a * exceptionalEmbeddingInt j b *
            matchingCornerKernel (R := ℤ) a b := by
  decide +kernel

private theorem signedJetKernel (i j : MatchingJetIndex) :
    ∑ p : Fin 24, matchingSign p * realMatchingJet p i * realMatchingJet p j =
      ∑ a : MatchingCornerIndex, ∑ b : MatchingCornerIndex,
        realMatchingExceptionalEmbedding i a * realMatchingExceptionalEmbedding j b *
          matchingCornerKernel (R := ℝ) a b := by
  have h := congrArg (Int.cast : ℤ → ℝ) (signedJetKernel_int i j)
  have hskew (s t : Fin 2) : (skewEntry (R := ℤ) s t : ℝ) = skewEntry s t := by
    unfold skewEntry
    split_ifs <;> norm_num
  simpa only [Int.cast_sum, Int.cast_mul, matchingSign, realMatchingJet,
    realMatchingExceptionalEmbedding, matchingCornerKernel, hskew] using h

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem signedJetColumn_zero (c : MatchingJetIndex) :
    ∑ p : Fin 24, matchingSign p * realMatchingJet p c = 0 := by
  have h : ∀ a : MatchingJetIndex,
      ∑ p : Fin 24, matchingSignInt p * matchingJetInt p a = 0 := by decide +kernel
  simpa only [Int.cast_sum, Int.cast_mul, Int.cast_zero, matchingSign, realMatchingJet]
    using congrArg (Int.cast : ℤ → ℝ) (h c)

theorem realMatching_alternating_sum_zero {g : Fin 24 → ℝ}
    (hg : g ∈ realMatchingFunctionSpace) : ∑ p : Fin 24, matchingSign p * g p = 0 := by
  rw [← realMatchingJet_range] at hg
  obtain ⟨v, rfl⟩ := hg
  calc
    _ = ∑ p : Fin 24, ∑ c : MatchingJetIndex,
          (matchingSign p * realMatchingJet p c) * v c := by
      simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]
    _ = 0 := by rw [Finset.sum_comm]; simp only [← Finset.sum_mul, signedJetColumn_zero,
      zero_mul, Finset.sum_const_zero]

/-- Transpose just the first two-dimensional index of the corner. -/
def matchingCornerPartialTranspose {R : Type*}
    (A : Matrix MatchingCornerIndex MatchingCornerIndex R) :
    Matrix MatchingCornerIndex MatchingCornerIndex R :=
  fun a b => A (b.1, a.2) (a.1, b.2)

private theorem matchingCornerPT_sub (A : Matrix MatchingCornerIndex MatchingCornerIndex ℝ)
    (hA : A.IsHermitian) (a b : MatchingCornerIndex) :
    A a b - matchingCornerPartialTranspose A a b =
      (A (0, 0) (1, 1) - A (0, 1) (1, 0)) * matchingCornerKernel a b := by
  have hs (i j : MatchingCornerIndex) : A i j = A j i := by
    have h := congrArg (fun (B : Matrix MatchingCornerIndex MatchingCornerIndex ℝ) => B j i) hA.eq
    simpa only [Matrix.conjTranspose_apply, star_trivial] using h
  rcases a with ⟨a₁, a₂⟩
  rcases b with ⟨b₁, b₂⟩
  fin_cases a₁ <;> fin_cases a₂ <;> fin_cases b₁ <;> fin_cases b₂ <;>
    norm_num [matchingCornerPartialTranspose, matchingCornerKernel, skewEntry, Fin.ext_iff] <;>
    linarith only [hs (0, 0) (0, 1), hs (0, 0) (1, 0), hs (0, 0) (1, 1),
      hs (0, 1) (1, 0), hs (0, 1) (1, 1), hs (1, 0) (1, 1)]

private theorem matchingCorner_kernel_pairing (A : Matrix MatchingCornerIndex MatchingCornerIndex ℝ)
    (hA : A.IsHermitian) :
    ∑ a : MatchingCornerIndex, ∑ b : MatchingCornerIndex, matchingCornerKernel a b * A a b =
      2 * (A (0, 0) (1, 1) - A (0, 1) (1, 0)) := by
  have hs (i j : MatchingCornerIndex) : A i j = A j i := by
    have h := congrArg (fun (B : Matrix MatchingCornerIndex MatchingCornerIndex ℝ) => B j i) hA.eq
    simpa only [Matrix.conjTranspose_apply, star_trivial] using h
  norm_num [Fintype.sum_prod_type, Fin.sum_univ_two, matchingCornerKernel, skewEntry, Fin.ext_iff]
  linarith only [hs (0, 0) (1, 1), hs (0, 1) (1, 0)]

theorem matchingCornerPartialTranspose_eq_of_zero_pairing
    (A : Matrix MatchingCornerIndex MatchingCornerIndex ℝ) (hA : A.IsHermitian)
    (hzero : ∑ a : MatchingCornerIndex, ∑ b : MatchingCornerIndex,
      matchingCornerKernel a b * A a b = 0) :
    matchingCornerPartialTranspose A = A := by
  have hz : A (0, 0) (1, 1) - A (0, 1) (1, 0) = 0 := by
    rw [matchingCorner_kernel_pairing A hA] at hzero
    linarith only [hzero]
  ext a b
  have he := matchingCornerPT_sub A hA a b
  rw [hz, zero_mul, sub_eq_zero] at he
  exact he.symm

noncomputable def realMatchingCorner (T : Matrix MatchingJetIndex MatchingJetIndex ℝ) :
    Matrix MatchingCornerIndex MatchingCornerIndex ℝ :=
  realMatchingExceptionalEmbeddingᵀ * T * realMatchingExceptionalEmbedding

noncomputable def realMatchingGramValue (T : Matrix MatchingJetIndex MatchingJetIndex ℝ) (p : Fin 24) : ℝ :=
  dotProduct (realMatchingJet p) (T *ᵥ realMatchingJet p)

private theorem realMatchingCorner_apply (T : Matrix MatchingJetIndex MatchingJetIndex ℝ)
    (a b : MatchingCornerIndex) :
    realMatchingCorner T a b =
      ∑ i : MatchingJetIndex, ∑ j : MatchingJetIndex,
        realMatchingExceptionalEmbedding i a * T i j * realMatchingExceptionalEmbedding j b := by
  unfold realMatchingCorner
  rw [Matrix.mul_assoc]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.mul_sum, mul_assoc]

private theorem sum_swap_pairs {A B C D : Type*}
    [Fintype A] [Fintype B] [Fintype C] [Fintype D] (f : A → B → C → D → ℝ) :
    (∑ a, ∑ b, ∑ c, ∑ d, f a b c d) = ∑ c, ∑ d, ∑ a, ∑ b, f a b c d := by
  calc
    _ = ∑ a, ∑ c, ∑ b, ∑ d, f a b c d := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]
    _ = ∑ c, ∑ a, ∑ b, ∑ d, f a b c d := by rw [Finset.sum_comm]
    _ = ∑ c, ∑ a, ∑ d, ∑ b, f a b c d := by
      apply Finset.sum_congr rfl
      intro c _
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro c _
      rw [Finset.sum_comm]

theorem realMatchingGram_alternating_pairing (T : Matrix MatchingJetIndex MatchingJetIndex ℝ) :
    ∑ p : Fin 24, matchingSign p * realMatchingGramValue T p =
      ∑ a : MatchingCornerIndex, ∑ b : MatchingCornerIndex,
        matchingCornerKernel a b * realMatchingCorner T a b := by
  calc
    _ = ∑ p : Fin 24, ∑ i : MatchingJetIndex, ∑ j : MatchingJetIndex,
        matchingSign p * (realMatchingJet p i * (T i j * realMatchingJet p j)) := by
      simp only [realMatchingGramValue, Matrix.mulVec, dotProduct, Finset.mul_sum]
    _ = ∑ i : MatchingJetIndex, ∑ j : MatchingJetIndex,
        T i j * (∑ p : Fin 24, matchingSign p * realMatchingJet p i * realMatchingJet p j) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      ring
    _ = ∑ a : MatchingCornerIndex, ∑ b : MatchingCornerIndex, ∑ i : MatchingJetIndex,
        ∑ j : MatchingJetIndex,
          T i j * (realMatchingExceptionalEmbedding i a * realMatchingExceptionalEmbedding j b *
            matchingCornerKernel a b) := by
      simp_rw [signedJetKernel, Finset.mul_sum]
      exact sum_swap_pairs _
    _ = _ := by
      simp only [realMatchingCorner_apply, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring

/-- The real matching condition eliminates the extra partial-transpose
constraint on every positive semidefinite Gram matrix for the cost. -/
theorem realMatchingCornerPT_eq {g : Fin 24 → ℝ} (hg : g ∈ realMatchingFunctionSpace)
    (T : Matrix MatchingJetIndex MatchingJetIndex ℝ) (hT : T.PosSemidef)
    (hvalue : ∀ p, g p = realMatchingGramValue T p) :
    matchingCornerPartialTranspose (realMatchingCorner T) = realMatchingCorner T := by
  have hR : (realMatchingCorner T).PosSemidef := by
    simpa only [realMatchingCorner, Matrix.conjTranspose_eq_transpose_of_trivial] using
      hT.conjTranspose_mul_mul_same realMatchingExceptionalEmbedding
  apply matchingCornerPartialTranspose_eq_of_zero_pairing _ hR.isHermitian
  rw [← realMatchingGram_alternating_pairing]
  simpa only [← hvalue] using realMatching_alternating_sum_zero hg

private theorem realMatchingGramValue_gram {ι : Type*} [Fintype ι]
    (B : Matrix ι MatchingJetIndex ℝ) (p : Fin 24) :
    realMatchingGramValue (Bᴴ * B) p =
      ∑ k : ι, (realMatchingJet.mulVecLin (B k) p)^2 := by
  unfold realMatchingGramValue
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_conjTranspose]
  simp only [star_trivial, dotProduct, pow_two, Matrix.mulVecLin_apply]
  apply Finset.sum_congr rfl
  intro k _
  have h : (B *ᵥ realMatchingJet p) k = (realMatchingJet *ᵥ B k) p := by
    simp only [Matrix.mulVec, dotProduct]
    exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
  rw [h]

private theorem realMatchingJet_supported_range :
    LinearMap.range (realMatchingJet * realMatchingJetᵀ).mulVecLin = realMatchingFunctionSpace := by
  rw [← realMatchingJet_range]
  apply Submodule.eq_of_le_of_finrank_eq
  · rintro _ ⟨x, rfl⟩
    refine ⟨realMatchingJetᵀ *ᵥ x, ?_⟩
    exact Matrix.mulVec_mulVec x realMatchingJet realMatchingJetᵀ
  · change (realMatchingJet * realMatchingJetᵀ).rank = realMatchingJet.rank
    exact Matrix.rank_self_mul_transpose realMatchingJet

/-- The real auxiliary positive-semidefinite Gram condition with a
positive partial transpose on its four-dimensional corner. The Gram
matrix has range in the row space of the jet. -/
def IsRealMatchingAuxiliaryPPT (g : Fin 24 → ℝ) : Prop :=
  ∃ T : Matrix MatchingJetIndex MatchingJetIndex ℝ, T.PosSemidef ∧
    LinearMap.range T.mulVecLin ≤ LinearMap.range realMatchingJetᵀ.mulVecLin ∧
    (matchingCornerPartialTranspose (realMatchingCorner T)).PosSemidef ∧
    ∀ p, g p = realMatchingGramValue T p

theorem realMatchingAuxiliaryPPT_iff_sos {g : Fin 24 → ℝ}
    (hg : g ∈ realMatchingFunctionSpace) :
    IsRealMatchingAuxiliaryPPT g ↔ IsRealMatchingSOS g := by
  classical
  constructor
  · rintro ⟨T, hT, _, _, hvalue⟩
    obtain ⟨B, rfl⟩ := Matrix.posSemidef_iff_eq_transpose_mul_self.mp hT
    let e := (Fintype.equivFin MatchingJetIndex).symm
    have hmem (k : MatchingJetIndex) :
        realMatchingJet.mulVecLin (B k) ∈ realMatchingFunctionSpace := by
      rw [← realMatchingJet_range]
      exact ⟨B k, rfl⟩
    have hrep (k : MatchingJetIndex) :
        ∃ f : Fin 14 → ℝ, fourMatchingEvaluation f = realMatchingJet.mulVecLin (B k) :=
      hmem k
    choose f hf using hrep
    refine ⟨Fintype.card MatchingJetIndex, f ∘ e, fun p => ?_⟩
    rw [hvalue, realMatchingGramValue_gram]
    simp only [Function.comp_apply, hf]
    exact (e.sum_comp (fun k => (realMatchingJet.mulVecLin (B k) p)^2)).symm
  · rintro ⟨n, f, hvalue⟩
    have hmem (i : Fin n) : fourMatchingEvaluation (f i) ∈ realMatchingFunctionSpace :=
      ⟨f i, rfl⟩
    have hrep (i : Fin n) : ∃ v : Fin 24 → ℝ,
        (realMatchingJet * realMatchingJetᵀ).mulVecLin v = fourMatchingEvaluation (f i) := by
      have h := hmem i
      rw [← realMatchingJet_supported_range] at h
      exact h
    choose Y hY using hrep
    let Z : Matrix (Fin n) (Fin 24) ℝ := Matrix.of Y
    let B : Matrix (Fin n) MatchingJetIndex ℝ := Z * realMatchingJet
    let T : Matrix MatchingJetIndex MatchingJetIndex ℝ := Bᴴ * B
    have hT : T.PosSemidef := Matrix.posSemidef_conjTranspose_mul_self B
    have hB (i : Fin n) : realMatchingJet.mulVecLin (B i) = fourMatchingEvaluation (f i) := by
      have hrow : B i = realMatchingJetᵀ *ᵥ Y i := by
        funext j
        simp only [B, Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.transpose_apply]
        exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
      rw [hrow, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec]
      exact hY i
    have hsupport : LinearMap.range T.mulVecLin ≤ LinearMap.range realMatchingJetᵀ.mulVecLin := by
      rintro _ ⟨x, rfl⟩
      refine ⟨Zᵀ *ᵥ (B *ᵥ x), ?_⟩
      have hBstar : Bᴴ = realMatchingJetᵀ * Zᵀ := by
        simp only [B, Matrix.conjTranspose_mul, Matrix.conjTranspose_eq_transpose_of_trivial]
      change realMatchingJetᵀ *ᵥ (Zᵀ *ᵥ (B *ᵥ x)) =
        (Bᴴ * B) *ᵥ x
      calc
        _ = (realMatchingJetᵀ * Zᵀ) *ᵥ (B *ᵥ x) :=
          Matrix.mulVec_mulVec (B *ᵥ x) realMatchingJetᵀ Zᵀ
        _ = _ := by rw [← hBstar, Matrix.mulVec_mulVec]
    have hTval (p : Fin 24) : g p = realMatchingGramValue T p := by
      change g p = realMatchingGramValue (Bᴴ * B) p
      rw [hvalue, realMatchingGramValue_gram]
      simp only [hB]
    refine ⟨T, hT, hsupport, ?_, hTval⟩
    rw [realMatchingCornerPT_eq hg T hT hTval]
    simpa only [realMatchingCorner, Matrix.conjTranspose_eq_transpose_of_trivial] using
      hT.conjTranspose_mul_mul_same realMatchingExceptionalEmbedding

/-- Transposing the first tensor index of a rank-one corner changes it
by the tensor skew form with the indicated two by two determinant. -/
theorem matchingCorner_rank_one_PT_defect {R : Type*} [CommRing R]
    (u : MatchingCornerIndex → R) :
    matchingCornerPartialTranspose (Matrix.of fun a b => u a * u b) -
      (Matrix.of fun a b => u a * u b) =
      -(Matrix.of (fun i j : Fin 2 => u (i,j))).det • matchingCornerKernel := by
  ext a b
  rcases a with ⟨a₁, a₂⟩
  rcases b with ⟨b₁, b₂⟩
  fin_cases a₁ <;> fin_cases a₂ <;> fin_cases b₁ <;> fin_cases b₂ <;>
    simp [matchingCornerPartialTranspose, matchingCornerKernel, skewEntry,
      Matrix.det_fin_two, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] <;> ring

/-- The moment matrix of signed coefficients in the real matching jet. -/
noncomputable def realMatchingMoment (c : Fin 24 → ℝ) :
    Matrix MatchingJetIndex MatchingJetIndex ℝ :=
  realMatchingJetᵀ * diagonal c * realMatchingJet

theorem realMatchingMoment_quadratic (c : Fin 24 → ℝ) (v : MatchingJetIndex → ℝ) :
    dotProduct v (realMatchingMoment c *ᵥ v) =
      ∑ p : Fin 24, c p * (realMatchingJet.mulVecLin v p)^2 := by
  unfold realMatchingMoment
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    Matrix.vecMul_transpose]
  simp only [dotProduct, Matrix.mulVec_diagonal, Matrix.mulVecLin_apply]
  apply Finset.sum_congr rfl
  intro p _
  ring

/-- If adding a multiple of the alternating sign makes the moment
positive semidefinite, every matching sum-of-squares cost in the
matching space has nonnegative pairing with the original coefficients. -/
theorem realMatchingSOS_pairing_nonneg_of_positiveMoment
    (c : Fin 24 → ℝ) (t : ℝ) {g : Fin 24 → ℝ} (hg : g ∈ realMatchingFunctionSpace)
    (hsos : IsRealMatchingSOS g)
    (hM : (realMatchingMoment (fun p => c p + t * matchingSign p)).PosSemidef) :
    0 ≤ ∑ p : Fin 24, c p * g p := by
  classical
  obtain ⟨n, f, hf⟩ := hsos
  let w (p : Fin 24) := c p + t * matchingSign p
  have hrep (k : Fin n) :
      ∃ v : MatchingJetIndex → ℝ, realMatchingJet.mulVecLin v = fourMatchingEvaluation (f k) := by
    have h : fourMatchingEvaluation (f k) ∈ realMatchingFunctionSpace := ⟨f k, rfl⟩
    rw [← realMatchingJet_range] at h
    exact h
  choose v hv using hrep
  have hnonneg (k : Fin n) :
      0 ≤ ∑ p : Fin 24, w p * (fourMatchingEvaluation (f k) p)^2 := by
    have h := hM.2 (v k)
    change 0 ≤ dotProduct (star (v k)) (realMatchingMoment w *ᵥ v k) at h
    simpa only [star_trivial, realMatchingMoment_quadratic, hv] using h
  calc
    0 ≤ ∑ k : Fin n, ∑ p : Fin 24, w p * (fourMatchingEvaluation (f k) p)^2 :=
      Finset.sum_nonneg fun k _ => hnonneg k
    _ = ∑ p : Fin 24, w p * g p := by
      rw [Finset.sum_comm]
      simp_rw [← Finset.mul_sum, ← hf]
    _ = _ := by
      simp only [w, add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum,
        realMatching_alternating_sum_zero hg, mul_zero, add_zero]

end MOC
