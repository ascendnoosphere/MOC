import MOC.ThreeValues
import MOC.Geometry
import Mathlib.Tactic.FunProp

/-! A repeated three-slot diagonal can be padded by one common spectral value.
Scaling the padded rows gives the three-dimensional compression at zero. -/

open BigOperators Filter Matrix
open scoped Topology

namespace MOC

/-- The determinant of a three-dimensional compression plus a diagonal with
two equal entries is a convex combination of the distinct-label triple products. -/
theorem det_three_compression_mem_hull_of_repeated_diagonal {k : ℕ}
    (U : Matrix (Fin 3 ⊕ Fin k) (Fin 3 ⊕ Fin k) ℂ) (hU : IsUnitary U)
    (a : Fin 3 → ℂ) (b : Fin 3 ⊕ Fin k → ℂ) (j : Fin 3) (c : ℂ)
    (ha : ∀ i, i ≠ j → a i = c) :
    (diagonal a + (U * diagonal b * Uᴴ).toBlocks₁₁).det ∈
      convexHull ℝ (Set.range fun f : Fin 3 ↪ (Fin 3 ⊕ Fin k) => ∏ i, (a i + b (f i))) := by
  classical
  let ι := Fin 3 ⊕ Fin k
  let B := U * diagonal b * Uᴴ
  let d (t : ℂ) : ι → ℂ := Sum.elim a (fun _ => t⁻¹)
  let S (t : ℂ) : Matrix ι ι ℂ := diagonal (Sum.elim (fun _ => 1) (fun _ => t))
  let M (t : ℂ) := fromBlocks (diagonal a + B.toBlocks₁₁) B.toBlocks₁₂
    (t • B.toBlocks₂₁) (1 + t • B.toBlocks₂₂)
  let z (t : ℂ) (σ : Equiv.Perm ι) :=
    (∏ i : Fin 3, (a i + b (σ.symm (.inl i)))) *
      ∏ i : Fin k, (1 + t * b (σ.symm (.inr i)))
  have hM₀ : (M 0).det = (diagonal a + B.toBlocks₁₁).det := by
    simp [M, Matrix.det_fromBlocks_zero₂₁]
  have hz₀ (σ : Equiv.Perm ι) :
      z 0 σ ∈ Set.range (fun f : Fin 3 ↪ ι => ∏ i, (a i + b (f i))) := by
    let f : Fin 3 ↪ ι :=
      ⟨fun i => σ.symm (.inl i), fun _ _ h => Sum.inl.inj (σ.symm.injective h)⟩
    exact ⟨f, by simp [f, z]⟩
  have hpad (t : ℂ) (ht : t ≠ 0) : (M t).det ∈ convexHull ℝ (Set.range (z t)) := by
    have hU' : IsUnitary Uᴴ := by simpa [IsUnitary] using And.intro hU.2 hU.1
    have hH : Holds (d t) b U := (holds_swap_iff (d t) b hU).mp
      (holds_three_values_one_singleton_fintype b (d t) Uᴴ hU' (.inl j) c t⁻¹ (by
        rintro (i | i) hi
        · exact Or.inl (ha i (fun h => hi (congrArg Sum.inl h)))
        · exact Or.inr rfl))
    have hS : (S t).det = t ^ k := by
      simp [S, Matrix.det_diagonal, Fintype.prod_sum_type]
    have hmat : S t * (diagonal (d t) + B) = M t := by
      ext x y : 1
      rcases x with i | i <;> rcases y with l | l
      · simp [S, d, M, Matrix.diagonal_mul, Matrix.add_apply, Sum.elim_inl,
          Matrix.fromBlocks_apply₁₁, Matrix.diagonal_apply]
      · simp [S, d, M, Matrix.diagonal_mul, Matrix.add_apply, Sum.elim_inl, Sum.elim_inr,
          Matrix.fromBlocks_apply₁₂, Matrix.diagonal_apply]
      · simp [S, d, M, Matrix.diagonal_mul, Matrix.add_apply, Sum.elim_inl, Sum.elim_inr,
          Matrix.fromBlocks_apply₂₁, Matrix.diagonal_apply, Matrix.smul_apply, smul_eq_mul]
      · by_cases h : i = l
        · subst l
          simp [S, d, M, Matrix.diagonal_mul, Matrix.add_apply, Sum.elim_inr,
            Matrix.fromBlocks_apply₂₂, Matrix.diagonal_apply, Matrix.one_apply,
            Matrix.smul_apply, smul_eq_mul, mul_add, mul_inv_cancel₀ ht]
        · simp [S, d, M, Matrix.diagonal_mul, Matrix.add_apply, Sum.elim_inr,
            Matrix.fromBlocks_apply₂₂, Matrix.diagonal_apply, Matrix.one_apply,
            Matrix.smul_apply, smul_eq_mul, h]
    have hdet : (M t).det = t ^ k * determinantValue (d t) b U := by
      rw [← hmat, Matrix.det_mul, hS]
      rfl
    have hvalue (σ : Equiv.Perm ι) : z t σ = t ^ k * matchingProduct (d t) b σ := by
      have hprod : matchingProduct (d t) b σ = ∏ i, (d t i + b (σ.symm i)) := by
        simpa [matchingProduct] using
          (Equiv.prod_comp σ (fun i => d t i + b (σ.symm i)))
      have htail : (∏ i : Fin k, (1 + t * b (σ.symm (.inr i)))) =
          t ^ k * ∏ i : Fin k, (t⁻¹ + b (σ.symm (.inr i))) := by
        simp_rw [← mul_inv_cancel₀ ht, ← mul_add]
        rw [Finset.prod_mul_distrib]
        simp
      rw [hprod, Fintype.prod_sum_type]
      simp only [d, z, Sum.elim_inl, Sum.elim_inr, htail]
      ring
    exact hull_of_common_factor hdet hvalue hH
  let hull := convexHull ℝ (Set.range fun f : Fin 3 ↪ ι => ∏ i, (a i + b (f i)))
  change (diagonal a + B.toBlocks₁₁).det ∈ hull
  by_contra hn
  have hclosed : IsClosed hull := (Set.finite_range _).isClosed_convexHull
  obtain ⟨L, q, hlt, hgt⟩ := geometric_hahn_banach_closed_point
    (convex_convexHull ℝ _) hclosed hn
  have hqd : q < L (M 0).det := by rwa [hM₀]
  have hnear (σ : Equiv.Perm ι) : ∀ᶠ t in 𝓝[≠] (0 : ℂ), L (z t σ) < L (M t).det := by
    have hi : L (z 0 σ) < q := hlt _ (subset_convexHull ℝ _ (hz₀ σ))
    have hz : Continuous fun t => z t σ := by dsimp [z]; fun_prop
    have hM : Continuous fun t => (M t).det := by dsimp [M]; fun_prop
    exact (((L.continuous.comp hz).continuousAt.eventually_lt
      (L.continuous.comp hM).continuousAt (hi.trans hqd))).filter_mono nhdsWithin_le_nhds
  have hne : ∀ᶠ t in 𝓝[≠] (0 : ℂ), t ≠ 0 := self_mem_nhdsWithin
  obtain ⟨t, ht, hz⟩ := (hne.and (Filter.eventually_all.mpr hnear)).exists
  have hbound : (M t).det ∈ {z | L z < L (M t).det} := by
    refine convexHull_min ?_ (convex_halfSpace_lt L.toLinearMap.isLinear _) (hpad t ht)
    rintro _ ⟨σ, rfl⟩
    exact hz σ
  exact (lt_irrefl _) hbound

end MOC
