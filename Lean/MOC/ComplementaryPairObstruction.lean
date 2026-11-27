import MOC.FiniteMinorLaw
import MOC.SegreConvexity
import Mathlib.Data.Matrix.Notation

open BigOperators Finset Matrix

namespace MOC

noncomputable section

private abbrev PairTable (R : Type*) := Matrix (Finset (Fin 4)) (Finset (Fin 4)) R

private def pairFirst (i : Fin 3) : Fin 4 := ![0, 0, 0] i
private def pairSecond (i : Fin 3) : Fin 4 := ![1, 2, 3] i
private def complementFirst (i : Fin 3) : Fin 4 := ![2, 1, 1] i
private def complementSecond (i : Fin 3) : Fin 4 := ![3, 3, 2] i

private def pair (i : Fin 3) : Finset (Fin 4) := {pairFirst i, pairSecond i}
private def otherPair (i : Fin 3) : Finset (Fin 4) := {complementFirst i, complementSecond i}

private def pairUnionEntry {R : Type*} [Add R] (M : PairTable R) (i j : Fin 3) : R :=
  M (pair i) (pair j) + M (pair i) (otherPair j)

private def pairDifferenceEntry {R : Type*} [Sub R] (M : PairTable R) (i j : Fin 3) : R :=
  M (pair i) (pair j) - M (pair i) (otherPair j)

private def pairScore {R : Type*} [Add R] [Sub R] (M : PairTable R) : R :=
  pairUnionEntry M 1 0 - pairUnionEntry M 0 1 -
    (pairDifferenceEntry M 0 0 + pairDifferenceEntry M 1 1 + pairDifferenceEntry M 2 2)

/-- A linear comparison of complementary pair transition probabilities. -/
def complementaryPairScore : PairTable ℝ →ₗ[ℝ] ℝ where
  toFun := pairScore
  map_add' A B := by
    simp only [pairScore, pairUnionEntry, pairDifferenceEntry, Matrix.add_apply]
    ring
  map_smul' t A := by
    simp only [pairScore, pairUnionEntry, pairDifferenceEntry, Matrix.smul_apply,
      smul_eq_mul, RingHom.id_apply]
    ring

private theorem pairScore_perm_integer : ∀ σ : Equiv.Perm (Fin 4),
    pairScore (subsetPermutationOperator (R := ℤ) σ) ≤ 1 := by
  decide +kernel

/-- Every positive permutation mixture satisfies the complementary pair bound. -/
theorem complementaryPairScore_le_one_of_mem_hull (M : PairTable ℝ)
    (hM : M ∈ convexHull ℝ (Set.range (subsetPermutationOperator (ι := Fin 4) (R := ℝ)))) :
    complementaryPairScore M ≤ 1 := by
  apply convexHull_min _ (convex_halfSpace_le complementaryPairScore.isLinear _) hM
  rintro _ ⟨σ, rfl⟩
  have he (I J : Finset (Fin 4)) :
      ((subsetPermutationOperator (R := ℤ) σ I J : ℤ) : ℝ) =
        subsetPermutationOperator (R := ℝ) σ I J := by
    simp only [subsetPermutationOperator, Matrix.of_apply, apply_ite, Int.cast_one, Int.cast_zero]
    split_ifs <;> rfl
  have hcast : ((pairScore (subsetPermutationOperator (R := ℤ) σ) : ℤ) : ℝ) ≤ 1 := by
    exact_mod_cast pairScore_perm_integer σ
  simpa only [complementaryPairScore, LinearMap.coe_mk, AddHom.coe_mk, pairScore, pairUnionEntry,
    pairDifferenceEntry, Int.cast_add, Int.cast_sub, he] using hcast

private def pairMixerScale : ℝ := (Real.sqrt 13)⁻¹

private theorem pairMixerScale_sq : pairMixerScale ^ 2 = 1 / 13 := by
  rw [pairMixerScale, inv_pow, Real.sq_sqrt (by norm_num : 0 ≤ (13 : ℝ))]
  norm_num

private def pairMixerNumerator : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1, -2, -2, -2; 2, 1, -2, 2; 2, 2, 1, -2; 2, -2, 2, 1]

/-- The real unitary that exceeds the complementary pair bound. -/
def complementaryPairMixer : Matrix (Fin 4) (Fin 4) ℂ :=
  Complex.ofRealHom.mapMatrix (pairMixerScale • pairMixerNumerator)

theorem complementaryPairMixer_unitary : IsUnitary complementaryPairMixer := by
  have hs : (pairMixerScale : ℂ) ^ 2 = 1 / 13 := by
    rw [← Complex.ofReal_pow, pairMixerScale_sq]
    norm_num [Complex.ofReal_div]
  have h : complementaryPairMixer * complementaryPairMixerᴴ = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [complementaryPairMixer, pairMixerNumerator, Matrix.mul_apply, Fin.sum_univ_four,
        Matrix.conjTranspose_apply, Matrix.one_apply, Complex.star_def,
        Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail] <;>
      ring_nf <;> rw [hs] <;> norm_num
  exact ⟨h, mul_eq_one_comm.mp h⟩

private def numeratorMinor (i j k l : Fin 4) : ℝ :=
  pairMixerNumerator i k * pairMixerNumerator j l - pairMixerNumerator i l * pairMixerNumerator j k

private theorem pairMixerMinor (i j k l : Fin 4) (hij : i ≠ j) (hkl : k ≠ l) :
    exteriorTransportOperator complementaryPairMixer {i, j} {k, l} = numeratorMinor i j k l ^ 2 / 169 := by
  change subsetMinorSq complementaryPairMixer {i, j} {k, l} = _
  rw [subsetMinorSq_pair _ complementaryPairMixer_unitary hij hkl]
  have he (x y : Fin 4) : complementaryPairMixer x y =
      (↑(pairMixerScale * pairMixerNumerator x y) : ℂ) := rfl
  simp only [he, ← Complex.ofReal_mul, ← Complex.ofReal_sub, Complex.normSq_ofReal]
  rw [show pairMixerScale * pairMixerNumerator i k * (pairMixerScale * pairMixerNumerator j l) -
      pairMixerScale * pairMixerNumerator i l * (pairMixerScale * pairMixerNumerator j k) =
      pairMixerScale ^ 2 * numeratorMinor i j k l by unfold numeratorMinor; ring, pairMixerScale_sq]
  ring

private theorem pair_first_ne_second (i : Fin 3) : pairFirst i ≠ pairSecond i := by
  fin_cases i <;> decide

private theorem complement_first_ne_second (i : Fin 3) : complementFirst i ≠ complementSecond i := by
  fin_cases i <;> decide

/-- The two complementary pair tables, with denominators cleared. -/
theorem complementaryPairMixer_tables (i j : Fin 3) :
    let M := exteriorTransportOperator complementaryPairMixer
    169 * pairUnionEntry M i j = (!![89, 8, 72; 72, 89, 8; 8, 72, 89] : Matrix (Fin 3) (Fin 3) ℝ) i j ∧
    13 * pairDifferenceEntry M i j = (!![-3, 0, 0; 0, -3, 0; 0, 0, -3] : Matrix (Fin 3) (Fin 3) ℝ) i j := by
  dsimp only
  unfold pairUnionEntry pairDifferenceEntry pair otherPair
  rw [pairMixerMinor _ _ _ _ (pair_first_ne_second i) (pair_first_ne_second j),
    pairMixerMinor _ _ _ _ (pair_first_ne_second i) (complement_first_ne_second j)]
  fin_cases i <;> fin_cases j <;>
    norm_num [numeratorMinor, pairMixerNumerator, pairFirst, pairSecond, complementFirst, complementSecond,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail]

theorem complementaryPairMixer_score :
    complementaryPairScore (exteriorTransportOperator complementaryPairMixer) = 181 / 169 := by
  change pairScore (exteriorTransportOperator complementaryPairMixer) = _
  unfold pairScore
  have h₁ := (complementaryPairMixer_tables 1 0).1
  have h₂ := (complementaryPairMixer_tables 0 1).1
  have h₃ := (complementaryPairMixer_tables 0 0).2
  have h₄ := (complementaryPairMixer_tables 1 1).2
  have h₅ := (complementaryPairMixer_tables 2 2).2
  norm_num [Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail] at h₁ h₂ h₃ h₄ h₅
  linarith only [h₁, h₂, h₃, h₄, h₅]

/-- The exterior transport of the explicit unitary is outside the full
permutation transport hull. -/
theorem complementaryPairMixer_exterior_not_mem_hull :
    exteriorTransportOperator complementaryPairMixer ∉
      convexHull ℝ (Set.range (subsetPermutationOperator (ι := Fin 4) (R := ℝ))) := by
  intro h
  have hs := complementaryPairScore_le_one_of_mem_hull _ h
  rw [complementaryPairMixer_score] at hs
  norm_num at hs

end

end MOC
