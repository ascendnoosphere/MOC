import MOC.FiniteMinorLaw
import Mathlib.Data.Fintype.Perm
import Mathlib.Tactic.Linarith

/-! An exact order-five spin profile which no single nonnegative permutation
law can realize. The rows and columns index the normalized symmetric
fourth-power basis. -/

open BigOperators Finset Matrix

namespace MOC

noncomputable section

private def spinFiveMultiplicity (i : Fin 5) : ℤ := ![1,4,6,4,1] i

private def spinFiveInteger : Matrix (Fin 5) (Fin 5) ℤ :=
  !![81, -108, 144, -192, 256;
    432, -351, 168, 176, -768;
    864, -252, -239, 252, 864;
    768, 176, -168, -351, -432;
    256, 192, 144, 108, 81]

private def spinFiveScale (i : Fin 5) : ℝ := Real.sqrt (spinFiveMultiplicity i : ℝ)

private theorem spinFiveMultiplicity_pos : ∀ i, 0 < spinFiveMultiplicity i := by
  decide +kernel

private theorem spinFiveScale_ne (i : Fin 5) : spinFiveScale i ≠ 0 := by
  exact (Real.sqrt_pos.2 (by exact_mod_cast spinFiveMultiplicity_pos i)).ne'

private theorem spinFiveScale_sq (i : Fin 5) : spinFiveScale i ^ 2 = (spinFiveMultiplicity i : ℝ) :=
  Real.sq_sqrt (by exact_mod_cast (spinFiveMultiplicity_pos i).le)

/-- The real spin matrix `Sym⁴ [[3/5,-4/5],[4/5,3/5]]` in its orthonormal basis. -/
def spinFive : Matrix (Fin 5) (Fin 5) ℂ := fun i j =>
  ((spinFiveScale j * (spinFiveInteger i j : ℝ) / (625 * spinFiveScale i) : ℝ) : ℂ)

private theorem spinFiveInteger_gram :
    ∀ i k : Fin 5,
      (∑ j : Fin 5, spinFiveMultiplicity j * spinFiveInteger i j * spinFiveInteger k j) =
        if i = k then 625 ^ 2 * spinFiveMultiplicity i else 0 := by
  decide +kernel

/-- The exact normalized spin matrix is unitary. -/
theorem spinFive_unitary : IsUnitary spinFive := by
  have hu : spinFive * spinFiveᴴ = 1 := by
    ext i k : 1
    have ht (j : Fin 5) : spinFive i j * star (spinFive k j) =
        (((spinFiveMultiplicity j * spinFiveInteger i j * spinFiveInteger k j : ℤ) : ℝ) /
          (625 ^ 2 * spinFiveScale i * spinFiveScale k) : ℝ) := by
      simp only [spinFive, Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul]
      congr 1
      push_cast
      rw [div_mul_div_comm]
      have h : spinFiveScale j * (spinFiveInteger i j : ℝ) *
          (spinFiveScale j * (spinFiveInteger k j : ℝ)) =
          (spinFiveMultiplicity j : ℝ) * (spinFiveInteger i j : ℝ) *
            (spinFiveInteger k j : ℝ) := by
        rw [← spinFiveScale_sq j]
        ring
      rw [h]
      congr 1
      ring
    rw [Matrix.mul_apply]
    simp_rw [Matrix.conjTranspose_apply, ht]
    rw [← Complex.ofReal_sum, ← Finset.sum_div, ← Int.cast_sum, spinFiveInteger_gram]
    by_cases hik : i = k
    · subst k
      rw [if_pos rfl, Matrix.one_apply_eq]
      norm_cast
      push_cast
      field_simp [spinFiveScale_ne i]
      nlinarith only [spinFiveScale_sq i]
    · rw [if_neg hik, Matrix.one_apply_ne hik]
      simp
  exact ⟨hu, Matrix.mul_eq_one_comm.mp hu⟩

private theorem spinFive_normSq_entry (i j : Fin 5) :
    Complex.normSq (spinFive i j) =
      ((spinFiveMultiplicity j : ℝ) * (spinFiveInteger i j : ℝ)^2) /
        (625^2 * (spinFiveMultiplicity i : ℝ)) := by
  rw [spinFive, Complex.normSq_ofReal, ← pow_two, div_pow, mul_pow, mul_pow,
    spinFiveScale_sq, spinFiveScale_sq]

private theorem spinFive_normSq_pair (i k j l : Fin 5) :
    Complex.normSq (spinFive i j * spinFive k l - spinFive i l * spinFive k j) =
      ((spinFiveMultiplicity j : ℝ) * (spinFiveMultiplicity l : ℝ) *
        ((spinFiveInteger i j : ℝ) * (spinFiveInteger k l : ℝ) -
          (spinFiveInteger i l : ℝ) * (spinFiveInteger k j : ℝ)) ^ 2) /
        (625^4 * (spinFiveMultiplicity i : ℝ) * (spinFiveMultiplicity k : ℝ)) := by
  have hf : spinFive i j * spinFive k l - spinFive i l * spinFive k j =
      ((spinFiveScale j * spinFiveScale l *
        ((spinFiveInteger i j : ℝ) * (spinFiveInteger k l : ℝ) -
          (spinFiveInteger i l : ℝ) * (spinFiveInteger k j : ℝ)) /
        (625^2 * spinFiveScale i * spinFiveScale k) : ℝ) : ℂ) := by
    simp only [spinFive, ← Complex.ofReal_mul, ← Complex.ofReal_sub]
    congr 1
    rw [div_mul_div_comm, div_mul_div_comm, ← sub_div]
    congr 1 <;> ring
  rw [hf, Complex.normSq_ofReal, ← pow_two, div_pow]
  simp only [mul_pow, spinFiveScale_sq]
  ring

private def spinCoverRows (k : Fin 7) : Finset (Fin 5) :=
  ![{0,1},{0,4},{1,2},{1,3},{1,4},{2,4},{3,4}] k

private def spinCoverCols (k : Fin 7) : Finset (Fin 5) :=
  ![{0,2},{1,3},{0,3},{2,3},{1,4},{1,2},{0,1}] k

private def spinPermCost (σ : Equiv.Perm (Fin 5)) : ℤ :=
  (∑ k, if (spinCoverCols k).map σ.toEmbedding = spinCoverRows k then 1 else 0) -
    (if ({1} : Finset (Fin 5)).map σ.toEmbedding = {4} then 1 else 0)

set_option maxHeartbeats 1500000 in
set_option maxRecDepth 4000 in
private theorem spinCover_combinatorial : ∀ a b c d : Fin 5,
    a ≠ 4 → b ≠ 4 → c ≠ 4 → d ≠ 4 →
    a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
    ({a,b} : Finset (Fin 5)) = {0,1} ∨ c = 0 ∨
      ({a,c} : Finset (Fin 5)) = {1,2} ∨ ({b,c} : Finset (Fin 5)) = {1,3} ∨
      d = 1 ∨ b = 2 ∨ a = 3 := by
  decide +kernel

private theorem spinPermCost_nonneg :
    ∀ σ : Equiv.Perm (Fin 5), 0 ≤ spinPermCost σ := by
  intro σ
  unfold spinPermCost
  apply sub_nonneg.mpr
  have hn (k : Fin 7) : 0 ≤
      (if (spinCoverCols k).map σ.toEmbedding = spinCoverRows k then (1 : ℤ) else 0) := by
    split_ifs <;> norm_num
  by_cases hσ : σ 1 = 4
  · have hne (i : Fin 5) (hi : i ≠ 1) : σ i ≠ 4 := fun h => hi (σ.injective (h.trans hσ.symm))
    have hi (i j : Fin 5) (hij : i ≠ j) : σ i ≠ σ j := fun h => hij (σ.injective h)
    obtain ⟨k,hk⟩ : ∃ k : Fin 7, (spinCoverCols k).map σ.toEmbedding = spinCoverRows k := by
      rcases spinCover_combinatorial (σ 0) (σ 2) (σ 3) (σ 4)
        (hne 0 (by decide)) (hne 2 (by decide)) (hne 3 (by decide)) (hne 4 (by decide))
        (hi 0 2 (by decide)) (hi 0 3 (by decide)) (hi 0 4 (by decide))
        (hi 2 3 (by decide)) (hi 2 4 (by decide)) (hi 3 4 (by decide)) with h|h|h|h|h|h|h
      · exact ⟨0, by simpa [spinCoverCols, spinCoverRows, Finset.map_insert] using h⟩
      · exact ⟨1, by simp [spinCoverCols, spinCoverRows, Finset.map_insert, hσ, h, Finset.pair_comm]⟩
      · exact ⟨2, by simpa [spinCoverCols, spinCoverRows, Finset.map_insert] using h⟩
      · exact ⟨3, by simpa [spinCoverCols, spinCoverRows, Finset.map_insert] using h⟩
      · exact ⟨4, by simp [spinCoverCols, spinCoverRows, Finset.map_insert, hσ, h, Finset.pair_comm]⟩
      · exact ⟨5, by simp [spinCoverCols, spinCoverRows, Finset.map_insert, hσ, h, Finset.pair_comm]⟩
      · exact ⟨6, by simp [spinCoverCols, spinCoverRows, Finset.map_insert, hσ, h]⟩
    have hsum := Finset.single_le_sum (f := fun j : Fin 7 =>
      if (spinCoverCols j).map σ.toEmbedding = spinCoverRows j then (1 : ℤ) else 0)
      (fun j _ => hn j) (Finset.mem_univ k)
    simpa [hk, hσ] using hsum
  · simpa [hσ] using Finset.sum_nonneg (fun j (_ : j ∈ (univ : Finset (Fin 7))) => hn j)

private def spinMinorCost (U : Matrix (Fin 5) (Fin 5) ℂ) : ℝ :=
  (∑ k, subsetMinorSq U (spinCoverRows k) (spinCoverCols k)) - subsetMinorSq U {4} {1}

private theorem spinMinorCost_value :
    spinMinorCost spinFive = -(27627983 / 244140625 : ℝ) := by
  unfold spinMinorCost
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Finset.sum_empty, add_zero,
    spinCoverRows, spinCoverCols, Matrix.cons_val_zero, Matrix.cons_val_succ]
  rw [subsetMinorSq_pair spinFive spinFive_unitary
      (i := 0) (k := 1) (j := 0) (l := 2) (by decide) (by decide),
    subsetMinorSq_pair spinFive spinFive_unitary
      (i := 0) (k := 4) (j := 1) (l := 3) (by decide) (by decide),
    subsetMinorSq_pair spinFive spinFive_unitary
      (i := 1) (k := 2) (j := 0) (l := 3) (by decide) (by decide),
    subsetMinorSq_pair spinFive spinFive_unitary
      (i := 1) (k := 3) (j := 2) (l := 3) (by decide) (by decide),
    subsetMinorSq_pair spinFive spinFive_unitary
      (i := 1) (k := 4) (j := 1) (l := 4) (by decide) (by decide),
    subsetMinorSq_pair spinFive spinFive_unitary
      (i := 2) (k := 4) (j := 1) (l := 2) (by decide) (by decide),
    subsetMinorSq_pair spinFive spinFive_unitary
      (i := 3) (k := 4) (j := 0) (l := 1) (by decide) (by decide)]
  simp_rw [spinFive_normSq_pair]
  rw [subsetMinorSq_singleton spinFive spinFive_unitary, spinFive_normSq_entry]
  change (((1 : ℤ) : ℝ) * ((6 : ℤ) : ℝ) * (((81 : ℤ) : ℝ) * ((168 : ℤ) : ℝ) -
      ((144 : ℤ) : ℝ) * ((432 : ℤ) : ℝ))^2 / (625^4 * ((1 : ℤ) : ℝ) * ((4 : ℤ) : ℝ)) +
    (((4 : ℤ) : ℝ) * ((4 : ℤ) : ℝ) * (((-108 : ℤ) : ℝ) * ((108 : ℤ) : ℝ) -
      ((-192 : ℤ) : ℝ) * ((192 : ℤ) : ℝ))^2 / (625^4 * ((1 : ℤ) : ℝ) * ((1 : ℤ) : ℝ)) +
    (((1 : ℤ) : ℝ) * ((4 : ℤ) : ℝ) * (((432 : ℤ) : ℝ) * ((252 : ℤ) : ℝ) -
      ((176 : ℤ) : ℝ) * ((864 : ℤ) : ℝ))^2 / (625^4 * ((4 : ℤ) : ℝ) * ((6 : ℤ) : ℝ)) +
    (((6 : ℤ) : ℝ) * ((4 : ℤ) : ℝ) * (((168 : ℤ) : ℝ) * ((-351 : ℤ) : ℝ) -
      ((176 : ℤ) : ℝ) * ((-168 : ℤ) : ℝ))^2 / (625^4 * ((4 : ℤ) : ℝ) * ((4 : ℤ) : ℝ)) +
    (((4 : ℤ) : ℝ) * ((1 : ℤ) : ℝ) * (((-351 : ℤ) : ℝ) * ((81 : ℤ) : ℝ) -
      ((-768 : ℤ) : ℝ) * ((192 : ℤ) : ℝ))^2 / (625^4 * ((4 : ℤ) : ℝ) * ((1 : ℤ) : ℝ)) +
    (((4 : ℤ) : ℝ) * ((6 : ℤ) : ℝ) * (((-252 : ℤ) : ℝ) * ((144 : ℤ) : ℝ) -
      ((-239 : ℤ) : ℝ) * ((192 : ℤ) : ℝ))^2 / (625^4 * ((6 : ℤ) : ℝ) * ((1 : ℤ) : ℝ)) +
    (((1 : ℤ) : ℝ) * ((4 : ℤ) : ℝ) * (((768 : ℤ) : ℝ) * ((192 : ℤ) : ℝ) -
      ((176 : ℤ) : ℝ) * ((256 : ℤ) : ℝ))^2 / (625^4 * ((4 : ℤ) : ℝ) * ((1 : ℤ) : ℝ))))))))) - ((4 : ℤ) : ℝ) * ((192 : ℤ) : ℝ)^2 / (625^2 * ((1 : ℤ) : ℝ)) = _
  norm_num

/-- Order-five spin squared minors cannot all be the subset-image marginals
of the same nonnegative law on permutations. -/
theorem spinFive_no_common_minor_law :
    ¬ ∃ w : Equiv.Perm (Fin 5) → ℝ, (∀ σ, 0 ≤ w σ) ∧
      ∀ I J : Finset (Fin 5), subsetMinorSq spinFive I J =
        ∑ σ ∈ univ.filter (fun σ => J.map σ.toEmbedding = I), w σ := by
  rintro ⟨w, hw, hm⟩
  have hnonneg : 0 ≤ ∑ σ : Equiv.Perm (Fin 5), w σ * (spinPermCost σ : ℝ) :=
    Finset.sum_nonneg fun σ _ => mul_nonneg (hw σ) (by exact_mod_cast spinPermCost_nonneg σ)
  have hEq : spinMinorCost spinFive =
      ∑ σ : Equiv.Perm (Fin 5), w σ * (spinPermCost σ : ℝ) := by
    simp_rw [spinMinorCost, hm, Finset.sum_filter, spinPermCost, Int.cast_sub, Int.cast_sum,
      mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
    rw [Finset.sum_comm (s := (univ : Finset (Fin 7)))]
    simp only [apply_ite, Int.cast_one, Int.cast_zero, mul_ite, mul_zero, mul_one]
  rw [← hEq, spinMinorCost_value] at hnonneg
  norm_num at hnonneg

end

end MOC
