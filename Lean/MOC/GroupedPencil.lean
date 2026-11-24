import MOC.SpectralMinorDecomposition

open BigOperators Finset

namespace MOC
noncomputable section

/-- Group the slope coordinates of the coefficient hull by their matched labels.
A zero mass contributes zero. Surjectivity ensures every conditional hull is nonempty. -/
theorem grouped_coefficient_hull_iff
    {I P : Type*} [Fintype I] [Fintype P] (label : P → I)
    (hl : Function.Surjective label) (s : P → ℂ) (a : I → ℂ) (A B : ℂ) :
    (A, B) ∈ convexHull ℝ (Set.range fun p => (s p, a (label p) * s p)) ↔
      ∃ (m : I → ℝ) (z : I → ℂ), (∀ i, 0 ≤ m i) ∧ (∑ i, m i) = 1 ∧
        (∀ i, ∃ u ∈ convexHull ℝ (s '' {p | label p = i}), z i = m i • u) ∧
        (∑ i, z i) = A ∧ (∑ i, a i * z i) = B := by
  classical
  constructor
  · intro hh
    obtain ⟨κ, hκ, w, v, hn, hsum, hv, hvsum⟩ :=
      mem_convexHull_iff_exists_fintype.mp hh
    letI : Fintype κ := hκ
    choose p hp using hv
    let T (i : I) := univ.filter fun k : κ => label (p k) = i
    let m (i : I) := ∑ k ∈ T i, w k
    let z (i : I) := ∑ k ∈ T i, w k • s (p k)
    refine ⟨m, z, fun i => sum_nonneg (fun k _ => hn k), ?_, ?_, ?_, ?_⟩
    · rw [show (∑ i, m i) = ∑ k, w k from sum_fiberwise univ (fun k => label (p k)) w]
      exact hsum
    · intro i
      by_cases hm : m i = 0
      · obtain ⟨q, hq⟩ := hl i
        refine ⟨s q, subset_convexHull ℝ _ ⟨q, hq, rfl⟩, ?_⟩
        rw [hm, zero_smul]
        apply sum_eq_zero
        intro k hk
        rw [(sum_eq_zero_iff_of_nonneg fun k _ => hn k).mp hm k hk, zero_smul]
      · have hm' : 0 < m i := lt_of_le_of_ne (sum_nonneg fun k _ => hn k) (Ne.symm hm)
        let u : ℂ := (m i)⁻¹ • z i
        have hsu : ∑ k ∈ T i, (m i)⁻¹ * w k = 1 := by
          rw [← mul_sum, show (∑ k ∈ T i, w k) = m i from rfl, inv_mul_cancel₀ hm]
        have hu : u ∈ convexHull ℝ (s '' {p | label p = i}) := by
          have hz : u = ∑ k ∈ T i, ((m i)⁻¹ * w k) • s (p k) := by
            simp only [u, z, mul_smul, Finset.smul_sum]
          rw [hz]
          exact (convex_convexHull ℝ _).sum_mem
            (fun k _ => mul_nonneg (inv_nonneg.mpr hm'.le) (hn k)) hsu
            (fun k hk => subset_convexHull ℝ _ ⟨p k, (mem_filter.mp hk).2, rfl⟩)
        exact ⟨u, hu, by rw [show u = (m i)⁻¹ • z i from rfl, smul_smul, mul_inv_cancel₀ hm, one_smul]⟩
    · rw [show (∑ i, z i) = ∑ k, w k • s (p k) from
        sum_fiberwise univ (fun k => label (p k)) (fun k => w k • s (p k))]
      simpa only [Prod.fst_sum, Prod.smul_fst, ← hp] using congrArg Prod.fst hvsum
    · have hgroup (i : I) : a i * z i = ∑ k ∈ T i, w k • (a (label (p k)) * s (p k)) := by
        unfold z
        rw [mul_sum]
        apply sum_congr rfl
        intro k hk
        rw [(mem_filter.mp hk).2, Complex.real_smul, Complex.real_smul]
        ring
      simp_rw [hgroup]
      rw [show (∑ i, ∑ k ∈ T i, w k • (a (label (p k)) * s (p k))) =
          ∑ k, w k • (a (label (p k)) * s (p k)) from
        sum_fiberwise univ (fun k => label (p k)) (fun k => w k • (a (label (p k)) * s (p k)))]
      simpa only [Prod.snd_sum, Prod.smul_snd, ← hp] using congrArg Prod.snd hvsum
  · rintro ⟨m, z, hn, hs, hK, hA, hB⟩
    choose y hy hz using hK
    let L (i : I) : ℂ →ₗ[ℝ] ℂ × ℂ :=
      (LinearMap.id : ℂ →ₗ[ℝ] ℂ).prod (LinearMap.mulLeft ℝ (a i))
    let S := convexHull ℝ (Set.range fun p => (s p, a (label p) * s p))
    have hL (i : I) : L i (y i) ∈ S := by
      have hm : L i (y i) ∈ convexHull ℝ (L i '' (s '' {p | label p = i})) := by
        rw [← (L i).image_convexHull]
        exact ⟨y i, hy i, rfl⟩
      refine convexHull_mono ?_ hm
      rintro _ ⟨_, ⟨p, hp, rfl⟩, rfl⟩
      exact ⟨p, by simp [L, show label p = i from hp]⟩
    have hv : (∑ i, m i • L i (y i)) ∈ S :=
      (convex_convexHull ℝ _).sum_mem (fun i _ => hn i) hs (fun i _ => hL i)
    have he : (∑ i, m i • L i (y i)) = (A,B) := by
      ext
      · simpa only [Prod.fst_sum, Prod.smul_fst, show ∀ i, (L i (y i)).1 = y i from fun i => rfl, ← hz]
          using hA
      · simp only [Prod.snd_sum, Prod.smul_snd, show ∀ i, (L i (y i)).2 = a i * y i from fun i => rfl]
        rw [← hB]
        apply sum_congr rfl
        intro i _
        rw [hz, Complex.real_smul, Complex.real_smul]
        ring
    exact he ▸ hv


/-- The grouped moments are equivalent to every scalar evaluation of a
one-entry determinant pencil. The masses need not be the squared entries. -/
theorem one_entry_pencil_iff_grouped_moments
    {I : Type*} [Fintype I] [DecidableEq I]
    (a b : I → ℂ) (j : I) (U : Matrix I I ℂ) (hU : IsUnitary U) :
    let s (q : Equiv.Perm I) := ∏ k ∈ univ.erase j, (a (q k) + b k)
    let D (v : ℂ) := determinantValue a (Function.update b j v) U
    (∀ v, Holds a (Function.update b j v) U) ↔
      ∃ (m : I → ℝ) (z : I → ℂ), (∀ i, 0 ≤ m i) ∧ (∑ i, m i) = 1 ∧
        (∀ i, ∃ u ∈ convexHull ℝ (s '' {q | q j = i}), z i = m i • u) ∧
        (∑ i, z i) = D 1 - D 0 ∧ (∑ i, a i * z i) = D 0 := by
  classical
  intro s D
  have hmatch (q : Equiv.Perm I) (v : ℂ) :
      matchingProduct a (Function.update b j v) q = (a (q j) + v) * s q := by
    unfold matchingProduct
    rw [← Finset.mul_prod_erase univ _ (mem_univ j), Function.update_self]
    congr 1
    apply prod_congr rfl
    intro k hk
    rw [Function.update_of_ne (mem_erase.mp hk).1]
  have hD (v : ℂ) : D v = D 0 + v * (D 1 - D 0) := by
    simpa only [D, mul_comm v] using determinant_update_interp a b j U hU v
  have hs (v : ℂ) : matchingProduct a (Function.update b j v) =
      fun q => a (q j) * s q + v * s q := by
    funext q
    rw [hmatch]
    ring
  have hEval : (∀ v, Holds a (Function.update b j v) U) ↔
      ∀ v : ℂ, D 0 + v * (D 1 - D 0) ∈ convexHull ℝ
        (Set.range (fun q : Equiv.Perm I => a (q j) * s q + v * s q)) := by
    apply forall_congr'
    intro v
    change D v ∈ convexHull ℝ (Set.range (matchingProduct a (Function.update b j v))) ↔ _
    rw [hD v, hs v]
  rw [hEval]
  rw [affinePencil_hull_iff_joint]
  have swapHull :
      (D 0, D 1 - D 0) ∈ convexHull ℝ (Set.range fun q : Equiv.Perm I => (a (q j) * s q, s q)) ↔
      (D 1 - D 0, D 0) ∈ convexHull ℝ (Set.range fun q : Equiv.Perm I => (s q, a (q j) * s q)) := by
    let f : (ℂ × ℂ) →ₗ[ℝ] ℂ × ℂ := (LinearMap.snd ℝ ℂ ℂ).prod (LinearMap.fst ℝ ℂ ℂ)
    have hF (x y : ℂ) : f (x,y) = (y,x) := rfl
    constructor <;> intro h
    · have hh : f (D 0, D 1 - D 0) ∈ f '' convexHull ℝ
          (Set.range fun q : Equiv.Perm I => (a (q j) * s q, s q)) := ⟨_, h, rfl⟩
      rw [f.image_convexHull, ← Set.range_comp, hF] at hh
      exact hh
    · have hh : f (D 1 - D 0, D 0) ∈ f '' convexHull ℝ
          (Set.range fun q : Equiv.Perm I => (s q, a (q j) * s q)) := ⟨_, h, rfl⟩
      rw [f.image_convexHull, ← Set.range_comp, hF] at hh
      exact hh
  exact swapHull.trans (grouped_coefficient_hull_iff (fun q : Equiv.Perm I => q j)
    (fun i => ⟨Equiv.swap j i, Equiv.swap_apply_left _ _⟩) s a (D 1 - D 0) (D 0))

end
end MOC
