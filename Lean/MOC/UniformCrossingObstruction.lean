import MOC.OrderFiveCommonLawObstruction
import MOC.FiniteMinorLaw

/-! The flat-reflection compound-law obstruction persists in every order
above four. This is a dimension-uniform extension of the Householder
obstruction studied by Drury, DOI: 10.1016/S0024-3795(99)00173-1. -/

open Matrix Finset BigOperators

namespace MOC

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private def constantUnitVector (ι : Type*) [Fintype ι] (_ : ι) : ℂ :=
  (Real.sqrt (Fintype.card ι : ℝ)⁻¹ : ℝ)

/-- Flat reflection with dimension-dependent constant direction. -/
def flatReflectionUniform (ι : Type*) [Fintype ι] [DecidableEq ι] : Matrix ι ι ℂ :=
  rankOnePhase (constantUnitVector ι) (-1)

omit [DecidableEq ι] in
private theorem constantUnitVector_product (i j : ι) :
    constantUnitVector ι i * star (constantUnitVector ι j) = (Fintype.card ι : ℂ)⁻¹ := by
  have hs : Real.sqrt (Fintype.card ι : ℝ)⁻¹ * Real.sqrt (Fintype.card ι : ℝ)⁻¹ =
      (Fintype.card ι : ℝ)⁻¹ := Real.mul_self_sqrt (inv_nonneg.mpr (Nat.cast_nonneg _))
  simp only [constantUnitVector, Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul,
    hs, Complex.ofReal_inv, Complex.ofReal_natCast]

omit [DecidableEq ι] in
private theorem constantUnitVector_unit (hN : 0 < Fintype.card ι) :
    ∑ i, star (constantUnitVector ι i) * constantUnitVector ι i = 1 := by
  simp_rw [mul_comm (star (constantUnitVector ι _)), constantUnitVector_product]
  rw [sum_const, card_univ, nsmul_eq_mul, mul_inv_cancel₀]
  exact_mod_cast hN.ne'

theorem unitary_flatReflectionUniform (hN : 0 < Fintype.card ι) :
    IsUnitary (flatReflectionUniform ι) :=
  rankOnePhase_unitary (constantUnitVector ι) (-1) (constantUnitVector_unit hN)
    (by simp)

private theorem flatReflectionUniform_entry (i j : ι) :
    flatReflectionUniform ι i j = (if i = j then 1 else 0) - 2/(Fintype.card ι : ℂ) := by
  unfold flatReflectionUniform rankOnePhase
  rw [Matrix.add_apply, Matrix.one_apply, Matrix.smul_apply, vecMulVec_apply]
  change (if i = j then 1 else 0) + (-1 - 1) *
    (constantUnitVector ι i * star (constantUnitVector ι j)) = _
  rw [constantUnitVector_product, div_eq_mul_inv]
  ring

private theorem flatReflectionUniform_disjoint_minor (hN : 0 < Fintype.card ι)
    (I J : Finset ι) (hI : I.card = 2) (hJ : J.card = 2) (hd : Disjoint I J) :
    subsetMinorSq (flatReflectionUniform ι) I J = 0 := by
  classical
  let e : Fin 2 ≃ I := Fintype.equivOfCardEq (by simp [hI])
  let f : Fin 2 ≃ J := Fintype.equivOfCardEq (by simp [hJ])
  rw [subsetMinorSq_eq_normSq_det_submatrix _ (unitary_flatReflectionUniform hN) I J e f]
  let A := (flatReflectionUniform ι).submatrix (Subtype.val ∘ e) (Subtype.val ∘ f)
  have hA (r s : Fin 2) : A r s = -(2 / (Fintype.card ι : ℂ)) := by
    change flatReflectionUniform ι (e r).val (f s).val = _
    have hn : (e r).val ≠ (f s).val := by
      intro he
      exact disjoint_left.mp hd (e r).property (he ▸ (f s).property)
    rw [flatReflectionUniform_entry, if_neg hn, zero_sub]
  have hz : A.det = 0 := det_zero_of_row_eq (Fin.zero_ne_one : (0 : Fin 2) ≠ 1)
    (funext fun j => (hA 0 j).trans (hA 1 j).symm)
  change Complex.normSq A.det = 0
  simp [hz]

private theorem flatReflectionUniform_singleton_diag (hN : 0 < Fintype.card ι) (i : ι) :
    subsetMinorSq (flatReflectionUniform ι) {i} {i} = (1-2/(Fintype.card ι : ℝ))^2 := by
  rw [subsetMinorSq_singleton _ (unitary_flatReflectionUniform hN), flatReflectionUniform_entry, if_pos rfl]
  rw [show (1 - 2/(Fintype.card ι : ℂ)) = ((1-2/(Fintype.card ι : ℝ) : ℝ) : ℂ) by push_cast; rfl]
  rw [Complex.normSq_ofReal, pow_two]

/-- A single positive doubleton law fails for every flat reflection in order
greater than four. A combinatorial support bound gives at most three
moves, but the one-entry mass implied by the pair law gives more. -/
theorem flatReflectionUniform_no_positive_pair_law (hN : 4 < Fintype.card ι) :
    ¬ ∃ w : Equiv.Perm ι → ℝ, (∀ σ, 0 ≤ w σ) ∧ (∑ σ, w σ) = 1 ∧
      ∀ I J : Finset ι, I.card = 2 → J.card = 2 →
        (∑ σ ∈ univ.filter (fun σ : Equiv.Perm ι => J.map σ.toEmbedding = I), w σ) =
          subsetMinorSq (flatReflectionUniform ι) I J := by
  classical
  rintro ⟨w, hw, hmass, hpair⟩
  let U := flatReflectionUniform ι
  have hpos : 0 < Fintype.card ι := Nat.zero_lt_of_lt hN
  let v := realSignedWeight U
  have hU : IsUnitary U := unitary_flatReflectionUniform hpos
  have hV (I J : Finset ι) :
      (∑ σ ∈ univ.filter (fun σ : Equiv.Perm ι => J.map σ.toEmbedding = I), v σ) =
        subsetMinorSq U I J := by
    simpa only [v, realSignedWeight, Complex.re_sum, Complex.ofReal_re] using
      congrArg Complex.re (sum_signedWeight_image_eq_subsetMinorSq U hU I J)
  let moved (σ : Equiv.Perm ι) := (univ.filter fun i => σ i ≠ i).card
  have hFew (σ : Equiv.Perm ι) (hp : w σ ≠ 0) : moved σ ≤ 3 := by
    by_contra h
    obtain ⟨J, hJ, hd⟩ := exists_disjoint_pair_image_of_four_moved σ
      (show 4 ≤ moved σ by omega)
    let I := J.map σ.toEmbedding
    have hi : I.card = 2 := by simp [I, hJ]
    have hm := hpair I J hi hJ
    rw [flatReflectionUniform_disjoint_minor hpos I J hi hJ hd.symm] at hm
    exact hp ((sum_eq_zero_iff_of_nonneg (fun p _ => hw p)).mp hm σ (by simp [I]))
  let N : ℝ := Fintype.card ι
  have hdiag (i : ι) :
      (∑ σ ∈ univ.filter (fun σ : Equiv.Perm ι => σ i = i), w σ) = (1-2/N)^2 := by
    have hSingle := singleton_image_mass_eq_of_pair_image_mass_eq (ι := ι)
      (by omega : 2 < Fintype.card ι) w v
      (hmass.trans (sum_realSignedWeight U hU).symm)
      (fun I J hI hJ => (hpair I J hI hJ).trans (hV I J).symm) i i
    have hh : (∑ σ ∈ univ.filter (fun σ : Equiv.Perm ι => σ i = i), w σ) =
        ∑ σ ∈ univ.filter (fun σ : Equiv.Perm ι => ({i} : Finset ι).map σ.toEmbedding = {i}), v σ := by
      simp only [Finset.map_singleton, Finset.singleton_inj, Equiv.toEmbedding_apply] at hSingle ⊢
      exact hSingle
    exact hh.trans ((hV {i} {i}).trans (flatReflectionUniform_singleton_diag hpos i))
  have hoff (i : ι) : (∑ σ, if σ i ≠ i then w σ else 0) = 1-(1-2/N)^2 := by
    have he := sum_filter_add_sum_filter_not (s := (univ : Finset (Equiv.Perm ι)))
      (p := fun σ => σ i = i) w
    rw [hdiag i, hmass, sum_filter] at he
    linarith
  have hExp : (∑ σ, w σ * (moved σ : ℝ)) = N * (1-(1-2/N)^2) := by
    have hsplit (σ : Equiv.Perm ι) :
        w σ * (moved σ : ℝ) = ∑ i, if σ i ≠ i then w σ else 0 := by
      rw [← sum_filter]
      simp [moved, mul_comm]
    simp_rw [hsplit]
    rw [sum_comm]
    simp only [hoff, sum_const, card_univ, nsmul_eq_mul, N]
  have hle : (∑ σ, w σ * (moved σ : ℝ)) ≤ 3 := by
    calc
      _ ≤ ∑ σ, w σ * 3 := by
        apply sum_le_sum
        intro σ _
        by_cases hz : w σ = 0
        · simp [hz]
        · exact mul_le_mul_of_nonneg_left (by exact_mod_cast hFew σ hz) (hw σ)
      _ = 3 := by rw [← sum_mul, hmass, one_mul]
  have hNr : 4 < N := by
    change (4 : ℝ) < (Fintype.card ι : ℝ)
    exact_mod_cast hN
  have hNpos : 0 < N := by linarith
  have hFormula : N * (1-(1-2/N)^2) = 4 - 4/N := by
    field_simp
    ring
  have hgt : 3 < N * (1-(1-2/N)^2) := by
    rw [hFormula]
    have : 4/N < 1 := (div_lt_iff₀ hNpos).mpr (by simpa using hNr)
    linarith
  exact hgt.not_le (hExp ▸ hle)


/-- Closed-form dual gap for the common pair-law relaxation. It is not
assumed to come from complex spectra. -/
def flatReflectionSyntheticGap (σ : Equiv.Perm ι) : ℝ :=
  3 - ((univ.filter fun i => σ i ≠ i).card : ℝ) +
    ((Fintype.card ι : ℝ) - 3) *
    ((univ.filter fun J : Finset ι => J.card = 2 ∧ Disjoint J (J.map σ.toEmbedding)).card : ℝ)

theorem flatReflectionSyntheticGap_nonneg (hN : 4 < Fintype.card ι)
    (σ : Equiv.Perm ι) : 0 ≤ flatReflectionSyntheticGap σ := by
  let moved := (univ.filter fun i => σ i ≠ i).card
  let d := (univ.filter fun J : Finset ι => J.card = 2 ∧ Disjoint J (J.map σ.toEmbedding)).card
  have hcard : (4 : ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast hN
  have hs : 0 ≤ (Fintype.card ι : ℝ) - 3 := by linarith
  change 0 ≤ 3 - (moved : ℝ) + ((Fintype.card ι : ℝ) - 3) * (d : ℝ)
  by_cases hm : moved ≤ 3
  · have hm' : (moved : ℝ) ≤ 3 := by exact_mod_cast hm
    exact add_nonneg (sub_nonneg.mpr hm') (mul_nonneg hs (Nat.cast_nonneg _))
  · obtain ⟨J, hJ, hd⟩ := exists_disjoint_pair_image_of_four_moved σ
      (show 4 ≤ moved by omega)
    have hd' : 0 < d := card_pos.mpr ⟨J, mem_filter.mpr ⟨mem_univ _, hJ, hd⟩⟩
    have hdR : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast (show 1 ≤ d by omega)
    have hmR : (moved : ℝ) ≤ (Fintype.card ι : ℝ) := by exact_mod_cast
      (card_filter_le (s := (univ : Finset ι)) (p := fun i => σ i ≠ i)).trans_eq card_univ
    have hprod := mul_le_mul_of_nonneg_left hdR hs
    rw [mul_one] at hprod
    linarith

/-- The gap is strictly negative at the exact squared-minor table of the
flat unitary, even though it is nonnegative at every permutation. -/
theorem flatReflectionSyntheticGap_signed_expectation (hN : 4 < Fintype.card ι) :
    (∑ σ : Equiv.Perm ι, realSignedWeight (flatReflectionUniform ι) σ *
      flatReflectionSyntheticGap σ) = 4 / (Fintype.card ι : ℝ) - 1 := by
  classical
  let U := flatReflectionUniform ι
  let w := realSignedWeight U
  let N : ℝ := Fintype.card ι
  let moved (σ : Equiv.Perm ι) := (univ.filter fun i => σ i ≠ i).card
  let d (σ : Equiv.Perm ι) := (univ.filter fun J : Finset ι =>
    J.card = 2 ∧ Disjoint J (J.map σ.toEmbedding)).card
  have hpos : 0 < Fintype.card ι := Nat.zero_lt_of_lt hN
  have hU : IsUnitary U := unitary_flatReflectionUniform hpos
  have hV (I J : Finset ι) :
      (∑ σ ∈ univ.filter (fun σ : Equiv.Perm ι => J.map σ.toEmbedding = I), w σ) =
        subsetMinorSq U I J := by
    simpa only [w, realSignedWeight, Complex.re_sum, Complex.ofReal_re] using
      congrArg Complex.re (sum_signedWeight_image_eq_subsetMinorSq U hU I J)
  have hMass : ∑ σ, w σ = 1 := sum_realSignedWeight U hU
  have hdiag (i : ι) : (∑ σ ∈ univ.filter (fun σ : Equiv.Perm ι => σ i = i), w σ) =
      (1-2/N)^2 := by
    have h := (hV {i} {i}).trans (flatReflectionUniform_singleton_diag hpos i)
    simpa only [Finset.map_singleton, Finset.singleton_inj, Equiv.toEmbedding_apply] using h
  have hoff (i : ι) : (∑ σ, if σ i ≠ i then w σ else 0) = 1-(1-2/N)^2 := by
    have he := sum_filter_add_sum_filter_not (s := (univ : Finset (Equiv.Perm ι)))
      (p := fun σ => σ i = i) w
    rw [hdiag i, hMass, sum_filter] at he
    linarith
  have hExp : (∑ σ, w σ * (moved σ : ℝ)) = N * (1-(1-2/N)^2) := by
    have hsplit (σ : Equiv.Perm ι) :
        w σ * (moved σ : ℝ) = ∑ i, if σ i ≠ i then w σ else 0 := by
      rw [← sum_filter]
      simp [moved, mul_comm]
    simp_rw [hsplit]
    rw [sum_comm]
    simp only [hoff, sum_const, card_univ, nsmul_eq_mul, N]
  have hDisjoint (J : Finset ι) : (∑ σ, if J.card = 2 ∧ Disjoint J (J.map σ.toEmbedding)
      then w σ else 0) = 0 := by
    by_cases hJ : J.card = 2
    · simp only [hJ, true_and]
      rw [← sum_fiberwise univ (fun σ : Equiv.Perm ι => J.map σ.toEmbedding)]
      apply sum_eq_zero
      intro I _
      by_cases hd : Disjoint J I
      · by_cases hI : I.card = 2
        · have hE := hV I J
          rw [flatReflectionUniform_disjoint_minor hpos I J hI hJ hd.symm] at hE
          convert hE using 1
          apply sum_congr rfl
          intro σ hσ
          have he := (mem_filter.mp hσ).2
          simp [he, hd]
        · apply sum_eq_zero
          intro σ hσ
          exact (hI (by rw [← (mem_filter.mp hσ).2, card_map, hJ])).elim
      · apply sum_eq_zero
        intro σ hσ
        have he := (mem_filter.mp hσ).2
        simp [he, hd]
    · simp [hJ]
  have hdExp : (∑ σ, w σ * (d σ : ℝ)) = 0 := by
    have hsplit (σ : Equiv.Perm ι) :
        w σ * (d σ : ℝ) = ∑ J : Finset ι, if J.card = 2 ∧ Disjoint J (J.map σ.toEmbedding)
          then w σ else 0 := by
      rw [← sum_filter]
      simp [d, mul_comm]
    simp_rw [hsplit]
    rw [sum_comm]
    simp [hDisjoint]
  have hNpos : 0 < N := by
    change (0 : ℝ) < (Fintype.card ι : ℝ)
    exact_mod_cast hpos
  have hFormula : N * (1-(1-2/N)^2) = 4 - 4/N := by
    field_simp
    ring
  change (∑ σ, w σ * (3 - (moved σ : ℝ) + (N-3)*(d σ : ℝ))) = _
  simp_rw [mul_add, mul_sub, sum_add_distrib, sum_sub_distrib,
    mul_left_comm (w _) (N-3), ← mul_sum, ← sum_mul, hMass, hExp, hdExp, hFormula]
  change (1 : ℝ) * 3 - (4 - 4/N) + (N-3)*0 = 4/N-1
  ring

/-- The exact separating cost is not a genuine spectral support gap:
the flat Householder reflection satisfies the original conjecture. -/
theorem flatReflectionSyntheticGap_not_spectral (hN : 4 < Fintype.card ι) :
    ¬ ∃ (a b : ι → ℂ) (η : ℂ) (H : ℝ), ∀ σ,
      flatReflectionSyntheticGap σ = H - (η * matchingProduct a b σ).re := by
  rintro ⟨a, b, η, H, hg⟩
  let U := flatReflectionUniform ι
  have hn : 0 < Fintype.card ι := Nat.zero_lt_of_lt hN
  have hU : IsUnitary U := unitary_flatReflectionUniform hn
  have holds : Holds a b U :=
    holds_householder a b (constantUnitVector ι) (constantUnitVector_unit hn)
  obtain ⟨σ, hs⟩ := (holds_iff_directional a b U).mp holds η
  have hh := flatReflectionSyntheticGap_nonneg hN σ
  rw [hg σ] at hh
  have hdet := hs.trans (sub_nonneg.mp hh)
  have he :
      (∑ σ : Equiv.Perm ι, realSignedWeight U σ * (η * matchingProduct a b σ).re) =
        (η * determinantValue a b U).re := by
    rw [← real_signed_determinant a b U hU, Finset.mul_sum, Complex.re_sum]
    apply sum_congr rfl
    intro σ _
    rw [mul_left_comm η, Complex.re_ofReal_mul]
  have hE := flatReflectionSyntheticGap_signed_expectation hN
  change (∑ σ : Equiv.Perm ι, realSignedWeight U σ * flatReflectionSyntheticGap σ) = _ at hE
  simp_rw [hg, mul_sub, sum_sub_distrib] at hE
  rw [← sum_mul, sum_realSignedWeight U hU, one_mul, he] at hE
  have hNr : (4 : ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast hN
  have hpos : 0 < (Fintype.card ι : ℝ) := by linarith
  have hlt : (4 : ℝ) / Fintype.card ι < 1 := (div_lt_iff₀ hpos).mpr (by simpa using hNr)
  linarith only [hE, hlt, hdet]


end

end MOC
