import MOC.Interlacing

/-! Interlacing averages the products with one law for all partner
lists. The probability law is chosen in the convex hull of functions
before a partner list is evaluated. -/

open BigOperators Matrix

namespace MOC

noncomputable section

/-- The matching product associated to an injection of the partner labels. -/
def partialMatchingFunction {m n : ℕ}
    (a : Fin m → ℝ) (f : Fin n ↪ Fin m) (b : Fin n → ℂ) : ℂ :=
  ∏ i, ((a (f i) : ℂ) + b i)

/-- The convex coefficients in interlacing can be chosen independently of all
the partner entries, including when two endpoints of an interlace coincide. -/
theorem interlacing_product_function_mem_hull {n : ℕ}
    (a : Fin (n + 1) → ℝ) (α : Fin n → ℝ)
    (hl : ∀ i, a i.castSucc ≤ α i) (hu : ∀ i, α i ≤ a i.succ) :
    (fun b : Fin n → ℂ => ∏ i, ((α i : ℂ) + b i)) ∈
      convexHull ℝ (Set.range (partialMatchingFunction a)) := by
  classical
  induction n with
  | zero =>
    exact subset_convexHull ℝ _ ⟨Fin.castSuccEmb, by funext b; simp [partialMatchingFunction]⟩
  | succ n ih =>
    let K := convexHull ℝ (Set.range (partialMatchingFunction a (n := n + 1)))
    let p (b : Fin n → ℂ) : ℂ := ∏ i, ((α i.castSucc : ℂ) + b i)
    have hK : Convex ℝ K := convex_convexHull ℝ _
    have ha : Monotone a := Fin.monotone_iff_le_succ.mpr fun i => (hl i).trans (hu i)
    have endpoint (q : Fin (n + 2)) (hq : (Fin.last n).castSucc ≤ q) :
        (fun b => p (b ∘ Fin.castSucc) * ((a q : ℂ) + b (Fin.last n))) ∈ K := by
      have hl' (i : Fin n) : a (q.succAbove i.castSucc) ≤ α i.castSucc := by
        have hi : i.castSucc.castSucc < q :=
          (Fin.castSucc_lt_castSucc_iff.mpr (Fin.castSucc_lt_last i)).trans_le hq
        simpa only [Fin.succAbove_of_castSucc_lt q i.castSucc hi] using hl i.castSucc
      have hu' (i : Fin n) : α i.castSucc ≤ a (q.succAbove i.succ) := by
        apply (hu i.castSucc).trans
        apply ha
        rw [Fin.succ_castSucc]
        by_cases hi : i.succ.castSucc < q
        · rw [Fin.succAbove_of_castSucc_lt q i.succ hi]
        · rw [Fin.succAbove_of_le_castSucc q i.succ (le_of_not_gt hi)]
          exact Fin.castSucc_le_succ _
      let L : ((Fin n → ℂ) → ℂ) →ₗ[ℝ] ((Fin (n + 1) → ℂ) → ℂ) :=
        { toFun := fun f b => f (b ∘ Fin.castSucc) * ((a q : ℂ) + b (Fin.last n))
          map_add' := by intro f g; funext b; exact add_mul _ _ _
          map_smul' := by
            intro r f
            funext b
            change ((r : ℂ) * f (b ∘ Fin.castSucc)) * ((a q : ℂ) + b (Fin.last n)) =
              (r : ℂ) * (f (b ∘ Fin.castSucc) * ((a q : ℂ) + b (Fin.last n)))
            exact mul_assoc _ _ _ }
      change p ∈ L ⁻¹' K
      apply convexHull_min _ (hK.linear_preimage L)
        (ih (fun j => a (q.succAbove j)) (fun i => α i.castSucc) hl' hu')
      rintro _ ⟨f, rfl⟩
      apply subset_convexHull ℝ _
      let g : Fin (n + 1) ↪ Fin (n + 2) :=
        finSuccEquivLast.toEmbedding.trans (f.optionMap.trans (finSuccEquiv' q).symm.toEmbedding)
      have hcast (i : Fin n) : g i.castSucc = q.succAbove (f i) := by
        change (finSuccEquiv' q).symm (Option.map f (finSuccEquivLast i.castSucc)) = _
        simp
      have hlast : g (Fin.last n) = q := by
        change (finSuccEquiv' q).symm (Option.map f (finSuccEquivLast (Fin.last n))) = _
        simp
      refine ⟨g, ?_⟩
      funext b
      change (∏ i : Fin (n + 1), ((a (g i) : ℂ) + b i)) =
        (∏ i : Fin n, ((a (q.succAbove (f i)) : ℂ) + b i.castSucc)) *
          ((a q : ℂ) + b (Fin.last n))
      rw [Fin.prod_univ_castSucc, hlast]
      simp_rw [hcast]
    have hleft := endpoint (Fin.last n).castSucc le_rfl
    have hright := endpoint (Fin.last (n + 1)) (Fin.le_last _)
    have hsegment : α (Fin.last n) ∈
        segment ℝ (a (Fin.last n).castSucc) (a (Fin.last (n + 1))) := by
      apply Icc_subset_segment
      exact ⟨hl (Fin.last n), by simpa only [Fin.succ_last] using hu (Fin.last n)⟩
    obtain ⟨r, s, hr, hs, hrs, hval⟩ := hsegment
    have hval' := congrArg Complex.ofReal hval
    have hrs' := congrArg Complex.ofReal hrs
    simp only [smul_eq_mul, Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_one] at hval' hrs'
    have he :
        r • (fun b => p (b ∘ Fin.castSucc) * ((a (Fin.last n).castSucc : ℂ) + b (Fin.last n))) +
          s • (fun b => p (b ∘ Fin.castSucc) * ((a (Fin.last (n + 1)) : ℂ) + b (Fin.last n))) =
          (fun b : Fin (n + 1) → ℂ => ∏ i, ((α i : ℂ) + b i)) := by
      funext b
      rw [Fin.prod_univ_castSucc]
      change
        (r : ℂ) * (p (b ∘ Fin.castSucc) * ((a (Fin.last n).castSucc : ℂ) + b (Fin.last n))) +
          (s : ℂ) * (p (b ∘ Fin.castSucc) * ((a (Fin.last (n + 1)) : ℂ) + b (Fin.last n))) =
          p (b ∘ Fin.castSucc) * ((α (Fin.last n) : ℂ) + b (Fin.last n))
      calc
        _ = p (b ∘ Fin.castSucc) * (((r : ℂ) * (a (Fin.last n).castSucc : ℂ) +
          (s : ℂ) * (a (Fin.last (n + 1)) : ℂ)) + ((r : ℂ) + (s : ℂ)) * b (Fin.last n)) := by
          ring
        _ = _ := by rw [hval', hrs', one_mul]
    have hmem := hK hleft hright hr hs hrs
    rw [he] at hmem
    exact hmem

/-- A single probability law on a finite set of injections preserves
the product for every complex partner list. -/
theorem exists_interlacing_injection_weights {n : ℕ}
    (a : Fin (n + 1) → ℝ) (α : Fin n → ℝ)
    (hl : ∀ i, a i.castSucc ≤ α i) (hu : ∀ i, α i ≤ a i.succ) :
    ∃ (s : Finset (Fin n ↪ Fin (n + 1))) (w : (Fin n ↪ Fin (n + 1)) → ℝ),
      (∀ f ∈ s, 0 ≤ w f) ∧ (∑ f ∈ s, w f = 1) ∧
        ∀ b : Fin n → ℂ,
          (∑ f ∈ s, (w f : ℂ) * partialMatchingFunction a f b) =
            ∏ i, ((α i : ℂ) + b i) := by
  classical
  have h := interlacing_product_function_mem_hull a α hl hu
  rw [convexHull_range_eq_exists_affineCombination, Set.mem_setOf_eq] at h
  obtain ⟨s, w, hw, hs, hval⟩ := h
  refine ⟨s, w, hw, hs, fun b => ?_⟩
  rw [Finset.affineCombination_eq_linear_combination _ _ _ hs] at hval
  simpa only [Finset.sum_apply, Pi.smul_apply, Complex.real_smul]
    using congrFun hval b

end

end MOC
