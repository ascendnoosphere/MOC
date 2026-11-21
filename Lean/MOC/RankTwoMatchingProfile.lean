import MOC.Core
import Mathlib.Analysis.Complex.Polynomial.Basic

/-! Rank-two kernels with nonzero rows and columns give additive matching profiles. -/

open BigOperators Matrix

namespace MOC

variable {ι κ : Type*}

/-- Vanishing of the three-row minors gives a sum of two products of
row and column functions. The argument uses a Schur complement of one entry. -/
theorem exists_two_product_factors_of_three_minors_eq_zero {K : Type*} [Field K]
    (M : Matrix ι κ K)
    (hminor : ∀ r : Fin 3 → ι, ∀ c : Fin 3 → κ, (M.submatrix r c).det = 0) :
    ∃ a b : ι → K, ∃ u v : κ → K, ∀ i j, M i j = a i * u j + b i * v j := by
  classical
  by_cases hnz : ∃ i j, M i j ≠ 0
  · obtain ⟨p, q, hpq⟩ := hnz
    let a (i : ι) := M i q
    let u (j : κ) := M p j / M p q
    let E (i : ι) (j : κ) := M i j - a i * u j
    have hE (i i' : ι) (j j' : κ) : E i j * E i' j' = E i j' * E i' j := by
      have hdet : M p q * (E i j * E i' j' - E i j' * E i' j) =
          (M.submatrix ![p, i, i'] ![q, j, j']).det := by
        simp [Matrix.det_fin_three, Matrix.submatrix_apply, E, a, u]
        field_simp [hpq] <;> ring
      exact sub_eq_zero.mp ((mul_eq_zero.mp (hdet.trans (hminor _ _))).resolve_left hpq)
    by_cases he : ∃ i j, E i j ≠ 0
    · obtain ⟨i₀, j₀, hE₀⟩ := he
      refine ⟨a, fun i => E i j₀, u, fun j => E i₀ j / E i₀ j₀, fun i j => ?_⟩
      have hf : E i j = E i j₀ * (E i₀ j / E i₀ j₀) := by
        rw [← mul_div_assoc]
        exact (eq_div_iff hE₀).mpr (hE i i₀ j j₀)
      rw [← hf]
      unfold E
      ring
    · refine ⟨a, 0, u, 0, fun i j => ?_⟩
      have hz : E i j = 0 := by by_contra! h; exact he ⟨i, j, h⟩
      have hf : M i j = a i * u j := sub_eq_zero.mp hz
      simpa only [Pi.zero_apply, zero_mul, add_zero] using hf
  · refine ⟨0, 0, 0, 0, fun i j => ?_⟩
    have hz : M i j = 0 := by by_contra! h; exact hnz ⟨i, j, h⟩
    simp [hz]

variable [Fintype ι] [Fintype κ]

private theorem exists_additive_gauge_of_two_products {K : Type*} [Field K] [Infinite K]
    (a b : ι → K) (u v : κ → K)
    (hrow : ∀ i, ¬ (a i = 0 ∧ b i = 0)) (hcol : ∀ j, ¬ (u j = 0 ∧ v j = 0)) :
    ∃ L : ι → K, ∃ R : κ → K, ∃ α : ι → K, ∃ β : κ → K,
      (∀ i, L i ≠ 0) ∧ (∀ j, R j ≠ 0) ∧
      ∀ i j, a i * u j + b i * v j = L i * R j * (α i + β j) := by
  classical
  let A (i : ι) := Polynomial.C (a i) + Polynomial.C (b i) * Polynomial.X
  let B (j : κ) := Polynomial.C (v j) - Polynomial.C (u j) * Polynomial.X
  have hA (i : ι) : A i ≠ 0 := by
    intro h
    have ha : a i = 0 := by simpa [A] using congrArg (Polynomial.eval 0) h
    have hb : b i = 0 := by simpa [A, ha] using congrArg (Polynomial.eval 1) h
    exact hrow i ⟨ha, hb⟩
  have hB (j : κ) : B j ≠ 0 := by
    intro h
    have hv : v j = 0 := by simpa [B] using congrArg (Polynomial.eval 0) h
    have hu : u j = 0 := by simpa [B, hv] using congrArg (Polynomial.eval 1) h
    exact hcol j ⟨hu, hv⟩
  let P := (∏ i, A i) * ∏ j, B j
  have hP : P ≠ 0 := mul_ne_zero
    (Finset.prod_ne_zero_iff.mpr fun i _ => hA i)
    (Finset.prod_ne_zero_iff.mpr fun j _ => hB j)
  obtain ⟨t, ht⟩ := (Polynomial.finite_setOf_isRoot hP).exists_not_mem
  let L (i : ι) := a i + b i * t
  let R (j : κ) := v j - u j * t
  have h : (Polynomial.evalRingHom t) P ≠ 0 := ht
  have hLR : (∏ i, L i) * (∏ j, R j) ≠ 0 := by
    simpa only [P, map_mul, map_prod, Polynomial.coe_evalRingHom, A, B, Polynomial.eval_add,
      Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, L, R] using h
  have hL i := Finset.prod_ne_zero_iff.mp (mul_ne_zero_iff.mp hLR).1 i (Finset.mem_univ i)
  have hR j := Finset.prod_ne_zero_iff.mp (mul_ne_zero_iff.mp hLR).2 j (Finset.mem_univ j)
  refine ⟨L, R, fun i => b i / L i, fun j => u j / R j, hL, hR, fun i j => ?_⟩
  calc
    a i * u j + b i * v j = b i * R j + L i * u j := by dsimp [L, R]; ring
    _ = L i * R j * (b i / L i + u j / R j) := by field_simp [hL i, hR j] <;> ring

/-- If the kernel has no zero row or column and all three-row minors vanish,
nonzero row and column factors turn it into an additive kernel. -/
theorem exists_additive_gauge_of_three_minors_eq_zero {K : Type*} [Field K] [Infinite K]
    (M : Matrix ι κ K)
    (hminor : ∀ r : Fin 3 → ι, ∀ c : Fin 3 → κ, (M.submatrix r c).det = 0)
    (hrow : ∀ i, ∃ j, M i j ≠ 0) (hcol : ∀ j, ∃ i, M i j ≠ 0) :
    ∃ L : ι → K, ∃ R : κ → K, ∃ α : ι → K, ∃ β : κ → K,
      (∀ i, L i ≠ 0) ∧ (∀ j, R j ≠ 0) ∧ ∀ i j, M i j = L i * R j * (α i + β j) := by
  obtain ⟨a, b, u, v, hf⟩ := exists_two_product_factors_of_three_minors_eq_zero M hminor
  have ha (i : ι) : ¬ (a i = 0 ∧ b i = 0) := by
    rintro ⟨ha, hb⟩
    obtain ⟨j, hj⟩ := hrow i
    exact hj (by simp [hf, ha, hb])
  have hu (j : κ) : ¬ (u j = 0 ∧ v j = 0) := by
    rintro ⟨hu, hv⟩
    obtain ⟨i, hi⟩ := hcol j
    exact hi (by simp [hf, hu, hv])
  obtain ⟨L, R, α, β, hL, hR, hg⟩ := exists_additive_gauge_of_two_products a b u v ha hu
  exact ⟨L, R, α, β, hL, hR, fun i j => (hf i j).trans (hg i j)⟩

/-- A diagonal-one kernel with vanishing three-row minors is an actual
additive-spectra matching profile up to a common nonzero factor. -/
theorem exists_projective_matching_profile_of_three_minors_eq_zero (M : Matrix ι ι ℂ)
    (hminor : ∀ r c : Fin 3 → ι, (M.submatrix r c).det = 0)
    (hdiag : ∀ i, M i i = 1) :
    ∃ d : ℂ, d ≠ 0 ∧ ∃ α β : ι → ℂ,
      ∀ σ : Equiv.Perm ι, (∏ j, M (σ j) j) = d * matchingProduct α β σ := by
  classical
  have h i : M i i ≠ 0 := (hdiag i).trans_ne one_ne_zero
  obtain ⟨L, R, α, β, hL, hR, hg⟩ := exists_additive_gauge_of_three_minors_eq_zero M hminor
    (fun i => ⟨i, h i⟩) (fun j => ⟨j, h j⟩)
  let d := (∏ i, L i) * ∏ j, R j
  refine ⟨d, mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun i _ => hL i)
    (Finset.prod_ne_zero_iff.mpr fun j _ => hR j), α, β, fun σ => ?_⟩
  simp only [hg, Finset.prod_mul_distrib, Equiv.prod_comp σ L, d, matchingProduct]

end MOC
