import MOC.NormalCompressionLine
import MOC.PrincipalCoisometry
import Mathlib.Analysis.NormedSpace.HahnBanach.Separation

/-! Distinct points on the supporting affine line are dense while the
deleted-row support and normality of the compression are preserved. -/

open BigOperators Matrix Filter
open scoped Topology

namespace MOC

/-- To prove the rectangular hull inclusion for normal compressions, it
suffices to prove it with a simple spectrum on the deleted row's support. -/
theorem holds_normal_compression_of_distinct_support_test {n : ℕ}
    (a : Fin n → ℂ) (U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (hU : IsUnitary U) (p : Fin (n + 1))
    (hstrict : ∀ b : Fin (n + 1) → ℂ,
      Set.InjOn b {j | U p j ≠ 0} →
      IsStarNormal ((U * diagonal b * Uᴴ).submatrix p.succAbove p.succAbove) →
      (diagonal a + (U * diagonal b * Uᴴ).submatrix p.succAbove p.succAbove).det ∈
        convexHull ℝ (Set.range (rectangularMatchingProduct a b)))
    (β : Fin (n + 1) → ℂ)
    (hC : IsStarNormal ((U * diagonal β * Uᴴ).submatrix p.succAbove p.succAbove)) :
    (diagonal a + (U * diagonal β * Uᴴ).submatrix p.succAbove p.succAbove).det ∈
      convexHull ℝ (Set.range (rectangularMatchingProduct a β)) := by
  classical
  let c := (U * diagonal β * Uᴴ) p p
  obtain ⟨d, hd, hline⟩ := exists_spectral_line_of_normalCompression β U hU p hC
  have ht (j : Fin (n + 1)) : ∃ x : ℝ, U p j ≠ 0 → β j = c + d * (x : ℂ) := by
    by_cases h : U p j = 0
    · exact ⟨0, fun hn => (hn h).elim⟩
    · obtain ⟨x, hx⟩ := hline j h
      exact ⟨x, fun _ => hx⟩
  choose knots hknots using ht
  let ell (t : ℝ) (j : Fin (n + 1)) := knots j + t * (j.val : ℝ)
  let b' (t : ℝ) (j : Fin (n + 1)) :=
    if U p j = 0 then β j else c + d * (ell t j : ℂ)
  have hzero : b' 0 = β := by
    funext j
    by_cases h : U p j = 0
    · simp [b', h]
    · simp [b', ell, h, hknots j h]
  have hline' (t : ℝ) (j : Fin (n + 1)) (hj : U p j ≠ 0) :
      b' t j = c + d * (ell t j : ℂ) := by simp [b', hj]
  have hb : Continuous b' := by
    apply continuous_pi
    intro j
    by_cases hj : U p j = 0
    · simpa [b', hj] using (continuous_const : Continuous (fun _ : ℝ => β j))
    · simp only [b', if_neg hj, ell]
      fun_prop
  have hell (j : Fin (n + 1)) : Continuous (fun t : ℝ => ell t j) := by
    dsimp only [ell]
    fun_prop
  have hnear : ∀ᶠ t in 𝓝[≠] (0 : ℝ), ∀ i j, i ≠ j → ell t i ≠ ell t j := by
    apply Filter.eventually_all.mpr
    intro i
    apply Filter.eventually_all.mpr
    intro j
    by_cases hi : i = j
    · exact Eventually.of_forall fun _ hn => (hn hi).elim
    by_cases he : knots i = knots j
    · have hn : (i.val : ℝ) ≠ (j.val : ℝ) := by
        intro hv
        exact hi (Fin.val_injective (by exact_mod_cast hv))
      filter_upwards [self_mem_nhdsWithin] with t htn
      intro _ he'
      have hm : t * ((i.val : ℝ) - (j.val : ℝ)) = 0 := by
        dsimp only [ell] at he'
        linear_combination he' - he
      exact (mul_ne_zero htn (sub_ne_zero.mpr hn)) hm
    · have hz : ell 0 i - ell 0 j ≠ 0 := by simpa [ell] using sub_ne_zero.mpr he
      filter_upwards [(((hell i).sub (hell j)).continuousAt.eventually_ne hz).filter_mono
        nhdsWithin_le_nhds] with t hn
      intro _
      exact sub_ne_zero.mp hn
  let D (b : Fin (n + 1) → ℂ) :=
    (diagonal a + (U * diagonal b * Uᴴ).submatrix p.succAbove p.succAbove).det
  change D β ∈ convexHull ℝ (Set.range (rectangularMatchingProduct a β))
  by_contra hbad
  have hclosed : IsClosed (convexHull ℝ (Set.range (rectangularMatchingProduct a β))) :=
    (Set.finite_range (rectangularMatchingProduct a β)).isClosed_convexHull
  obtain ⟨L, q, hq, hDq⟩ := geometric_hahn_banach_closed_point
    (convex_convexHull ℝ _) hclosed hbad
  have hsep (e : Fin n ↪ Fin (n + 1)) : L (rectangularMatchingProduct a β e) < L (D β) :=
    (hq _ (subset_convexHull ℝ _ ⟨e, rfl⟩)).trans hDq
  have hdcont : Continuous (fun t => L (D (b' t))) := by
    have hM : Continuous (fun t => U * diagonal (b' t) * Uᴴ) :=
      (continuous_const.matrix_mul hb.matrix_diagonal).matrix_mul continuous_const
    exact L.continuous.comp
      (continuous_const.add (hM.matrix_submatrix p.succAbove p.succAbove)).matrix_det
  have hmatch (e : Fin n ↪ Fin (n + 1)) :
      Continuous (fun t => L (rectangularMatchingProduct a (b' t) e)) := by
    apply L.continuous.comp
    unfold rectangularMatchingProduct
    exact continuous_finset_prod _ fun j _ =>
      continuous_const.add ((continuous_apply (e j)).comp hb)
  have hsep' : ∀ᶠ t in 𝓝[≠] (0 : ℝ), ∀ e : Fin n ↪ Fin (n + 1),
      L (rectangularMatchingProduct a (b' t) e) < L (D (b' t)) := by
    apply Filter.eventually_all.mpr
    intro e
    exact ((hmatch e).continuousAt.eventually_lt hdcont.continuousAt
      (by simpa only [hzero] using hsep e)).filter_mono nhdsWithin_le_nhds
  obtain ⟨t, htsep, hti⟩ := (hsep'.and hnear).exists
  have hti' : Set.InjOn (b' t) {j | U p j ≠ 0} := by
    intro i hi j hj he
    by_contra hn
    rw [hline' t i hi, hline' t j hj] at he
    exact hti i j hn (Complex.ofReal_injective (mul_left_cancel₀ hd (add_left_cancel he)))
  have hh := hstrict (b' t) hti'
    (normalCompression_of_spectral_line_on_support (b' t) U hU p c d (ell t) (hline' t))
  have hl : D (b' t) ∈ {z | L z < L (D (b' t))} := by
    apply convexHull_min _ (convex_halfSpace_lt L.toLinearMap.isLinear _) hh
    rintro _ ⟨e, rfl⟩
    exact htsep e
  exact (lt_irrefl (L (D (b' t)))) hl

end MOC
