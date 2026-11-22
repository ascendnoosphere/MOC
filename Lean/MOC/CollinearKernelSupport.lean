import MOC.MatchingKernelDephase
import MOC.MatchingProfileCompactness
import MOC.OffsetMatchingLine
import MOC.RankTwoRealKernel
import MOC.TwoValues

/-! Real matching products of a diagonal-one rank-two kernel admit
the determinant hull bound, including kernels with zero entries. -/

open BigOperators Matrix

namespace MOC

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

private theorem block_products_eq_marker (K : Matrix ι ι ℂ) (hK : VanishingThreeMinors K)
    (hd : ∀ i, K i i = 1) (S : Finset ι) (p q : ι) (hp : p ∈ S) (hq : q ∉ S)
    (hzero : ∀ i ∈ S, ∀ j ∉ S, K i j = 0) (σ : Equiv.Perm ι) :
    kernelMatchingProduct K σ = if S.map σ.toEmbedding = S then 1 else 0 := by
  classical
  by_cases hs : S.map σ.toEmbedding = S
  · rw [if_pos hs]
    have hpres (j : ι) : σ j ∈ S ↔ j ∈ S := by
      constructor
      · intro hj
        have hmem : σ j ∈ S.map σ.toEmbedding := by rwa [hs]
        rcases Finset.mem_map.mp hmem with ⟨a, ha, hσ⟩
        rwa [← (Equiv.apply_eq_iff_eq σ).mp hσ]
      · intro hj
        have hmem : σ j ∈ S.map σ.toEmbedding := Finset.mem_map.mpr ⟨j, hj, rfl⟩
        simpa only [hs] using hmem
    let t (j : ι) := if j ∈ S then p else q
    have hfactor (j : ι) : K (σ j) j = K (σ j) (t (σ j)) * K (t j) j := by
      by_cases hj : j ∈ S
      · have hi := (hpres j).mpr hj
        have hh := hK ![σ j, p, q] ![j, p, q]
        have he : K (σ j) j - K (σ j) p * K p j = 0 := by
          simpa [Matrix.det_fin_three, Matrix.submatrix_apply, hd,
            hzero (σ j) hi q hq, hzero p hp q hq] using hh
        simpa only [t, if_pos hj, if_pos hi] using (sub_eq_zero.mp he)
      · have hi : σ j ∉ S := fun h => hj ((hpres j).mp h)
        have hh := hK ![σ j, q, p] ![j, q, p]
        have he : K (σ j) j - K (σ j) q * K q j = 0 := by
          simpa [Matrix.det_fin_three, Matrix.submatrix_apply, hd,
            hzero p hp j hj, hzero p hp q hq] using hh
        simpa only [t, if_neg hj, if_neg hi] using (sub_eq_zero.mp he)
    have hdiag (j : ι) : K j (t j) * K (t j) j = 1 := by
      by_cases hj : j ∈ S
      · have hh := hK ![j, p, q] ![j, p, q]
        have he : 1 - K j p * K p j = 0 := by
          simpa [Matrix.det_fin_three, Matrix.submatrix_apply, hd,
            hzero j hj q hq, hzero p hp q hq] using hh
        simpa only [t, if_pos hj] using (sub_eq_zero.mp he).symm
      · have hh := hK ![j, q, p] ![j, q, p]
        have he : 1 - K j q * K q j = 0 := by
          simpa [Matrix.det_fin_three, Matrix.submatrix_apply, hd,
            hzero p hp j hj, hzero p hp q hq] using hh
        simpa only [t, if_neg hj] using (sub_eq_zero.mp he).symm
    unfold kernelMatchingProduct
    simp_rw [hfactor]
    rw [Finset.prod_mul_distrib, Equiv.prod_comp σ (fun j => K j (t j)), ← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one fun j _ => hdiag j
  · rw [if_neg hs]
    have hmiss : ¬ S ⊆ S.map σ.toEmbedding := by
      intro hh
      exact hs (Finset.eq_of_subset_of_card_le hh (by rw [Finset.card_map])).symm
    obtain ⟨i, hi, hni⟩ := Finset.not_subset.mp hmiss
    have hn : σ.symm i ∉ S := by simpa only [Finset.mem_map_equiv] using hni
    apply Finset.prod_eq_zero (Finset.mem_univ (σ.symm i))
    simpa only [Equiv.apply_symm_apply] using (hzero i hi (σ.symm i) hn)

/-- The real line through the origin poses no obstruction for a
diagonal-one rank-two matching kernel. -/
theorem signed_kernel_value_mem_hull_of_real_matchings (K : Matrix ι ι ℂ)
    (hK : VanishingThreeMinors K) (hd : ∀ i, K i i = 1)
    (hre : ∀ σ : Equiv.Perm ι, (kernelMatchingProduct K σ).im = 0)
    (U : Matrix ι ι ℂ) (hU : IsUnitary U) :
    (∑ σ, signedWeight U σ * kernelMatchingProduct K σ) ∈
      convexHull ℝ (Set.range (kernelMatchingProduct K)) := by
  classical
  let R (i j : ι) : Prop := Relation.ReflTransGen (fun a b => K a b ≠ 0) i j
  by_cases hconnect : ∀ i j, R i j
  · let p : ι := Classical.choice inferInstance
    obtain ⟨g, hg, hreal⟩ := exists_diagonal_dephase_of_real_matchings K p hd hre
      (hconnect p) (fun i => hconnect i p)
    let M : Matrix ι ι ℂ := Matrix.of fun i j => g i * K i j / g j
    let A : Matrix ι ι ℝ := Matrix.of fun i j => (M i j).re
    have hA (i j : ι) : (A i j : ℂ) = M i j := Complex.ext rfl (by
      simp only [Complex.ofReal_im, M, Matrix.of_apply, hreal])
    have hdM (i : ι) : M i i = 1 := by simp [M, hd, hg]
    have hdA (i : ι) : A i i ≠ 0 := by
      intro h
      have hh := hA i i
      rw [h, Complex.ofReal_zero, hdM] at hh
      exact zero_ne_one hh
    have hM : VanishingThreeMinors M := by
      simpa only [M, div_eq_mul_inv] using (threeMinors_reweight K g (fun j => (g j)⁻¹) hK)
    have hAm (p q : Fin 3 → ι) : (A.submatrix p q).det = 0 := by
      apply Complex.ofReal_injective
      change Complex.ofRealHom (A.submatrix p q).det = 0
      rw [Complex.ofRealHom.map_det]
      have hm : Complex.ofRealHom.mapMatrix (A.submatrix p q) = M.submatrix p q := by
        ext i j
        exact hA (p i) (q j)
      rw [hm, hM p q]
    have he (σ : Equiv.Perm ι) : (∏ j, (A (σ j) j : ℂ)) = kernelMatchingProduct K σ := by
      have hgn : (∏ j, g j) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => hg i
      simp only [hA, M, Matrix.of_apply, Finset.prod_div_distrib, Finset.prod_mul_distrib,
        Equiv.prod_comp σ g, kernelMatchingProduct]
      exact mul_div_cancel_left₀ _ hgn
    simpa only [he] using sum_signedWeight_mem_hull_of_real_rank_two_kernel A U hU hdA hAm
  · push_neg at hconnect
    obtain ⟨p, q, hn⟩ := hconnect
    let S := Finset.univ.filter (R p)
    have hS (i : ι) : i ∈ S ↔ R p i := by simp [S]
    have hp : p ∈ S := (hS p).mpr .refl
    have hq : q ∉ S := fun h => hn ((hS q).mp h)
    have hzero (i : ι) (hi : i ∈ S) (j : ι) (hj : j ∉ S) : K i j = 0 := by
      by_contra h
      exact hj ((hS j).mpr (((hS i).mp hi).tail h))
    let a (i : ι) : ℝ := if i ∈ S then 0 else 1
    let b (i : ι) : ℝ := if i ∈ S then 1 else 0
    have hprod : kernelMatchingProduct K = matchingProduct (fun i => (a i : ℂ)) (fun i => (b i : ℂ)) := by
      funext σ
      rw [block_products_eq_marker K hK hd S p q hp hq hzero,
        show (fun i => (a i : ℂ)) = (fun i => if i ∈ S then 0 else 1) by
          funext i; by_cases h : i ∈ S <;> simp [a, h],
        show (fun i => (b i : ℂ)) = (fun i => if i ∈ S then 1 else 0) by
          funext i; by_cases h : i ∈ S <;> simp [b, h],
        matchingProduct_subset_marker S S rfl]
    rw [hprod, signed_determinant _ _ U hU]
    exact holds_of_real_spectra a b U hU

/-- If all matching values lie on one line through zero, their hull
contains every determinant value, even for spectra with opposite entries. -/
theorem holds_of_matching_line_through_origin (a b : ι → ℂ) (η : ℂ) (hη : η ≠ 0)
    (hline : ∀ σ : Equiv.Perm ι, (η * matchingProduct a b σ).re = 0)
    (U : Matrix ι ι ℂ) (hU : IsUnitary U) : Holds a b U := by
  by_cases hzero : ∀ σ : Equiv.Perm ι, matchingProduct a b σ = 0
  · have hd : determinantValue a b U = 0 := by
      rw [← signed_determinant a b U hU]
      simp only [hzero, mul_zero, Finset.sum_const_zero]
    unfold Holds
    rw [hd, ← hzero 1]
    exact matchingProduct_mem_hull _ _ _
  push_neg at hzero
  obtain ⟨σ₀, hσ₀⟩ := hzero
  let a' (i : ι) := a (σ₀ i)
  let V : Matrix ι ι ℂ := U.submatrix σ₀ (Equiv.refl ι)
  have hV : IsUnitary V := unitary_reindex σ₀ (Equiv.refl ι) hU
  have hline' (σ : Equiv.Perm ι) : (η * matchingProduct a' b σ).re = 0 := by
    simpa only [matchingProduct, Equiv.Perm.mul_apply, a'] using hline (σ₀ * σ)
  let d (j : ι) := a' j + b j
  let D := ∏ j, d j
  have hD : D ≠ 0 := hσ₀
  have hd (j : ι) : d j ≠ 0 := Finset.prod_ne_zero_iff.mp hD j (Finset.mem_univ j)
  let K : Matrix ι ι ℂ := Matrix.of fun i j => (a' i + b j) / d j
  have hK : VanishingThreeMinors K := by
    let A : Matrix ι ι ℂ := Matrix.of fun i j => a' i + b j
    have hA : VanishingThreeMinors A := by
      intro p q
      simp only [Matrix.det_fin_three, Matrix.submatrix_apply, Matrix.of_apply, A]
      ring
    simpa only [K, A, Matrix.of_apply, one_mul, div_eq_mul_inv] using
      threeMinors_reweight A (fun _ => 1) (fun j => (d j)⁻¹) hA
  have hdiag (j : ι) : K j j = 1 := div_self (hd j)
  have hquo (σ : Equiv.Perm ι) : kernelMatchingProduct K σ = matchingProduct a' b σ / D := by
    simp only [K, kernelMatchingProduct, Matrix.of_apply, Finset.prod_div_distrib, matchingProduct, D]
  have hre (σ : Equiv.Perm ι) : (kernelMatchingProduct K σ).im = 0 := by
    rw [hquo, ← show matchingProduct a' b (1 : Equiv.Perm ι) = D from rfl,
      ← mul_div_mul_left _ _ hη, Complex.div_im, hline', hline']
    simp
  have hprod (σ : Equiv.Perm ι) : matchingProduct a' b σ = D * kernelMatchingProduct K σ :=
    ((eq_div_iff hD).mp (hquo σ)).symm.trans (mul_comm _ _)
  have hdet : determinantValue a' b V = D * ∑ σ, signedWeight V σ * kernelMatchingProduct K σ := by
    rw [← signed_determinant a' b V hV, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro σ _
    rw [hprod]
    ring
  apply (holds_reindex_iff σ₀ (Equiv.refl ι) a b U).mp
  change Holds a' b V
  exact hull_of_common_factor hdet hprod
    (signed_kernel_value_mem_hull_of_real_matchings K hK hdiag hre V hV)

/-- A collinear matching profile obeys determinant inclusion in every
finite order. Both degeneracies and lines through zero are allowed. -/
theorem holds_of_all_collinear_matching_products {n : ℕ} (a b : Fin n → ℂ)
    (η : ℂ) (hη : η ≠ 0) (H : ℝ)
    (hline : ∀ σ : Equiv.Perm (Fin n), (η * matchingProduct a b σ).re = H)
    (U : Matrix (Fin n) (Fin n) ℂ) (hU : IsUnitary U) : Holds a b U := by
  by_cases hn : n ≤ 3
  · exact conjecture_le_three hn a b U hU
  by_cases hH : H = 0
  · letI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
    exact holds_of_matching_line_through_origin a b η hη
      (fun σ => (hline σ).trans hH) U hU
  · exact holds_of_collinear_matching_products_off_origin a b η H hH hline U hU

end

end MOC
