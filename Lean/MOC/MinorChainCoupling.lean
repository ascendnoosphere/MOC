import MOC.AdjacentMinorSupport

/-! Adjacent exterior-minor couplings extend to a common law on a chain of
row subsets. -/

open BigOperators Finset Matrix
open scoped Classical

namespace MOC

universe u

/-- A finite sequence of compatible transports can be realized jointly. The
new coordinate is sampled conditionally on the current one. -/
theorem exists_finite_chain_coupling {α : Type u} [Fintype α]
    (mass : ℕ → α → ℝ) (step : ℕ → α → α → Prop) (k : ℕ)
    (hmass : ∀ a, 0 ≤ mass 0 a)
    (hstep : ∀ j < k, ∃ μ : α → α → ℝ, (∀ a b, 0 ≤ μ a b) ∧
      (∀ a b, μ a b ≠ 0 → step j a b) ∧
      (∀ a, ∑ b, μ a b = mass j a) ∧ (∀ b, ∑ a, μ a b = mass (j + 1) b)) :
    ∃ (Ω : Type u) (hΩ : Fintype Ω) (w : Ω → ℝ) (path : Ω → ℕ → α),
      (∀ ω, 0 ≤ w ω) ∧
      (∀ ω i, i < k → w ω ≠ 0 → step i (path ω i) (path ω (i + 1))) ∧
      (∀ i ≤ k, ∀ a, ∑ ω ∈ (@Finset.univ Ω hΩ).filter (fun ω => path ω i = a), w ω = mass i a) := by
  classical
  induction k with
  | zero =>
    refine ⟨α, inferInstance, mass 0, fun a _ => a, hmass, ?_, ?_⟩
    · intro ω i hi
      exact (Nat.not_lt_zero i hi).elim
    · intro i hi a
      have he : i = 0 := Nat.eq_zero_of_le_zero hi
      subst i
      simp [Finset.sum_filter]
  | succ k ih =>
    obtain ⟨Ω, hΩ, w, path, hw, hp, hm⟩ := ih
      (fun j hj => hstep j (hj.trans (Nat.lt_succ_self k)))
    letI := hΩ
    obtain ⟨μ, hμ, hrel, hrow, hcol⟩ := hstep k (Nat.lt_succ_self k)
    let v (ω : Ω) (a : α) := w ω / mass k (path ω k) * μ (path ω k) a
    let path' (p : Ω × α) (i : ℕ) := if i = k + 1 then p.2 else path p.1 i
    have hn (a : α) : 0 ≤ mass k a := by
      rw [← hm k le_rfl a]
      exact Finset.sum_nonneg fun ω _ => hw ω
    have hω (ω : Ω) : ∑ a, v ω a = w ω := by
      simp only [v, ← Finset.mul_sum, hrow]
      by_cases h : mass k (path ω k) = 0
      · have hl := Finset.single_le_sum (f := w) (fun a _ => hw a)
          (Finset.mem_filter.mpr ⟨Finset.mem_univ ω, rfl⟩ :
            ω ∈ univ.filter (fun ω' => path ω' k = path ω k))
        rw [hm k le_rfl (path ω k), h] at hl
        simp [h, le_antisymm hl (hw ω)]
      · exact div_mul_cancel₀ _ h
    have hnext (b : α) : ∑ ω, v ω b = mass (k + 1) b := by
      rw [← Finset.sum_fiberwise univ (fun ω => path ω k), ← hcol b]
      apply Finset.sum_congr rfl
      intro a _
      have he : (∑ ω ∈ univ.filter (fun ω => path ω k = a), v ω b) =
          ∑ ω ∈ univ.filter (fun ω => path ω k = a), w ω / mass k a * μ a b := by
        apply Finset.sum_congr rfl
        intro ω hω
        simp only [v, (Finset.mem_filter.mp hω).2]
      rw [he, ← Finset.sum_mul, ← Finset.sum_div, hm k le_rfl a]
      by_cases ha : mass k a = 0
      · have hl := Finset.single_le_sum (f := μ a) (fun x _ => hμ a x) (Finset.mem_univ b)
        rw [hrow a, ha] at hl
        simp [ha, le_antisymm hl (hμ a b)]
      · rw [div_self ha, one_mul]
    refine ⟨Ω × α, inferInstance, fun p => v p.1 p.2, path', ?_, ?_, ?_⟩
    · rintro ⟨ω,a⟩
      exact mul_nonneg (div_nonneg (hw ω) (hn _)) (hμ _ _)
    · rintro ⟨ω,a⟩ i hi hv
      have hne (j : ℕ) (hj : j ≤ k) : j ≠ k + 1 := by omega
      have hw' : w ω ≠ 0 := by intro hz; apply hv; simp [v, hz]
      by_cases he : i = k
      · subst i
        have hμ' : μ (path ω k) a ≠ 0 := by intro hz; apply hv; simp [v, hz]
        simpa only [path', if_neg (hne k le_rfl), if_pos rfl] using hrel _ _ hμ'
      · have hlt : i < k := by omega
        simpa only [path', if_neg (hne i (Nat.le_of_lt hlt)),
          if_neg (hne (i + 1) hlt)] using hp ω i hlt hw'
    · intro i hi a
      rw [Finset.sum_filter, Fintype.sum_prod_type]
      by_cases he : i = k + 1
      · subst i
        simpa [path'] using hnext a
      · have hle : i ≤ k := by omega
        simp only [path', if_neg he]
        calc
          _ = ∑ ω, if path ω i = a then w ω else 0 := by
            apply Finset.sum_congr rfl
            intro ω _
            by_cases h : path ω i = a <;> simp [h, hω]
          _ = _ := by rw [← Finset.sum_filter, hm i hle a]

/-- Along any single chain formed by inserting columns, all squared-minor
row-set laws are marginals of one nested row-set process. -/
theorem exists_prefix_minor_coupling {n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ) (hU : IsUnitary U)
    (J : ℕ → Finset (Fin n)) (k : ℕ)
    (hJ : ∀ i < k, ∃ j ∉ J i, J (i + 1) = insert j (J i)) :
    ∃ (Ω : Type) (hΩ : Fintype Ω) (w : Ω → ℝ) (path : Ω → ℕ → Finset (Fin n)),
      (∀ ω, 0 ≤ w ω) ∧ (∀ ω i, i < k → w ω ≠ 0 → path ω i ⊆ path ω (i + 1)) ∧
      (∀ i ≤ k, ∀ I, ∑ ω ∈ (@Finset.univ Ω hΩ).filter (fun ω => path ω i = I), w ω =
        subsetMinorSq U I (J i)) := by
  classical
  refine @exists_finite_chain_coupling (Finset (Fin n)) _ (fun i I => subsetMinorSq U I (J i))
      (fun _ I K => I ⊆ K) k (fun I => subsetMinorSq_nonneg U I (J 0)) ?_
  intro i hi
  obtain ⟨j, hj, he⟩ := hJ i hi
  rw [he]
  exact exists_adjacent_minor_transport U hU (J i) j hj

/-- A single chain law realizes every selected subset law and every singleton
law of its additions. Starting at the empty set gives a law on injections. -/
theorem exists_minor_chain_with_singletons {n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ) (hU : IsUnitary U)
    (J : ℕ → Finset (Fin n)) (k : ℕ)
    (hJ : ∀ i < k, ∃ j ∉ J i, J (i + 1) = insert j (J i)) :
    ∃ (Ω : Type) (hΩ : Fintype Ω) (w : Ω → ℝ) (path : Ω → ℕ → Finset (Fin n)),
      (∀ ω, 0 ≤ w ω) ∧ (@Finset.univ Ω hΩ).sum w = 1 ∧
      (∀ ω i, i < k → w ω ≠ 0 → path ω i ⊆ path ω (i + 1)) ∧
      (∀ ω i, i ≤ k → w ω ≠ 0 → (path ω i).card = (J i).card) ∧
      (∀ i ≤ k, ∀ I, ∑ ω ∈ (@Finset.univ Ω hΩ).filter (fun ω => path ω i = I), w ω =
        subsetMinorSq U I (J i)) ∧
      ∀ i < k, ∀ (j : Fin n), j ∉ J i → J (i + 1) = insert j (J i) → ∀ r : Fin n,
        ∑ ω ∈ (@Finset.univ Ω hΩ).filter (fun ω => r ∈ path ω (i + 1) \ path ω i), w ω =
          Complex.normSq (U r j) := by
  classical
  obtain ⟨Ω,hΩ,w,path,hw,hsub,hm⟩ := exists_prefix_minor_coupling U hU J k hJ
  letI := hΩ
  refine ⟨Ω,hΩ,w,path,hw,?_,hsub,?_,hm,?_⟩
  · rw [← Finset.sum_fiberwise univ (fun ω => path ω 0)]
    simp_rw [hm 0 (Nat.zero_le k)]
    exact sum_subsetMinorSq U hU (J 0)
  · intro ω i hi hω
    have hwpos : 0 < w ω := lt_of_le_of_ne (hw ω) hω.symm
    have hl := Finset.single_le_sum (f := w) (fun ω _ => hw ω)
      (Finset.mem_filter.mpr ⟨Finset.mem_univ ω, rfl⟩ :
        ω ∈ univ.filter (fun ω' => path ω' i = path ω i))
    rw [hm i hi (path ω i)] at hl
    by_contra hn
    have hz : subsetMinorSq U (path ω i) (J i) = 0 := by simp [subsetMinorSq, hn]
    exact (lt_irrefl 0) (hz ▸ hwpos.trans_le hl)
  · intro i hi j hj he r
    have hproj (l : ℕ) (hl : l ≤ k) :
        (∑ ω, if r ∈ path ω l then w ω else 0) =
          ∑ I : Finset (Fin n), subsetMinorSq U I (J l) * (if r ∈ I then 1 else 0) := by
      rw [← Finset.sum_fiberwise univ (fun ω => path ω l)]
      apply Finset.sum_congr rfl
      intro I _
      have hlocal (ω : Ω) (hω : ω ∈ univ.filter fun ω' => path ω' l = I) :
          (if r ∈ path ω l then w ω else 0) = if r ∈ I then w ω else 0 := by
        rw [(Finset.mem_filter.mp hω).2]
      rw [Finset.sum_congr rfl hlocal]
      by_cases hr : r ∈ I <;> simp [hr, hm l hl I]
    have hterm (ω : Ω) :
        (if r ∈ path ω (i + 1) \ path ω i then w ω else 0) =
          (if r ∈ path ω (i + 1) then w ω else 0) - (if r ∈ path ω i then w ω else 0) := by
      by_cases hw0 : w ω = 0
      · simp [hw0]
      · by_cases hp : r ∈ path ω i
        · have hq := hsub ω i hi hw0 hp
          simp [hp,hq]
        · by_cases hq : r ∈ path ω (i + 1) <;> simp [hp,hq]
    rw [Finset.sum_filter]
    simp_rw [hterm, Finset.sum_sub_distrib]
    rw [hproj (i + 1) (by omega), hproj i hi.le, he]
    simpa only [Finset.sum_ite_eq', mul_ite, mul_one, mul_zero, Finset.mem_univ, if_true] using
      adjacent_minor_additive_score U hU (J i) j hj (fun q => if q = r then 1 else 0)

end MOC
