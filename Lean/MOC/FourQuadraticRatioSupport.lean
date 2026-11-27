import MOC.FourBudgetMinor
import MOC.FourQuadraticRatioMinor
import MOC.FourQuadraticRatioSpectralCapacity
import MOC.ProjectivePole
import MOC.FourCoincidence
import MOC.TwoExceptions

/-! Zheng's order-four support inequality on the complete quadratic-ratio pattern contact set. -/

open BigOperators Matrix

namespace MOC

set_option maxHeartbeats 4000000 in
/-- For any two spectra of order four, a common lower support bound at all
matching products which is attained at the six quadratic-ratio pattern indices also bounds every
unitary determinant from below. Repeated or shared spectral points are allowed. -/
theorem fourQuadraticRatio_support (α β : Fin 4 → ℂ) (η : ℂ) (H : ℝ)
    (hn : ∀ i, H ≤ (η * matchingProduct α β (fourPerm i).symm).re)
    (hc : ∀ i ∈ fourQuadraticRatioContactIndices, (η * matchingProduct α β (fourPerm i).symm).re = H)
    (U : Matrix (Fin 4) (Fin 4) ℂ) (hU : IsUnitary U) :
    H ≤ (η * determinantValue α β U).re := by
  classical
  let g (i : Fin 24) := (η * matchingProduct α β (fourPerm i).symm).re - H
  let d := g 2 - g 13
  have hg (i : Fin 24) : 0 ≤ g i := sub_nonneg.mpr (hn i)
  by_cases hd : d ≤ 0
  · apply fourQuadraticRatio_support_of_nonpositive_mixed α β η H hn hc _ U hU
    dsimp only [d, g] at hd
    linarith only [hd]
  have hd' : 0 < d := lt_of_not_ge hd
  by_cases hna : ¬ Function.Injective α
  · exact four_lower_support_of_holds α β η H U
      (holds_four_of_repeated_spectrum α β U hU (Or.inl hna)) hn
  have ha : Function.Injective α := not_not.mp hna
  by_cases hnb : ¬ Function.Injective β
  · exact four_lower_support_of_holds α β η H U
      (holds_four_of_repeated_spectrum α β U hU (Or.inr hnb)) hn
  have hb : Function.Injective β := not_not.mp hnb
  by_cases hnab : ¬ (∀ i j, α i + β j ≠ 0)
  · push_neg at hnab
    obtain ⟨i, j, hij⟩ := hnab
    exact four_lower_support_of_holds α β η H U (holds_four_of_opposite_entries α β U hU hij) hn
  have hab : ∀ i j, α i + β j ≠ 0 := not_not.mp hnab
  by_cases hη : η = 0
  · have h := hc 0 (by decide)
    simp [hη] at h ⊢
    exact h.symm.le
  have hcap : d ^ 2 * (g 15 + g 19 + g 10 + d) < g 15 * g 19 * (g 10 - d) := by
    obtain ⟨c, X, Y, hcn, hX₁, hX₂, hX, hY, hXY, hprod⟩ :=
      exists_projective_pole_chart α β 1 2 2 (by decide) ha hb hab
    let z := X 0
    let x := X 3
    let w := Y 0
    let v := Y 1
    let t := Y 3 / v
    let ξ := η * (-c)
    let F := fourQuadraticRatioPoleProduct z x w v t
    have hξ : ξ ≠ 0 := mul_ne_zero hη (neg_ne_zero.mpr hcn)
    have hv : v ≠ 0 := by
      intro h
      exact hXY 1 1 (by decide) (hX₁.trans h.symm)
    have htv : t * v = Y 3 := div_mul_cancel₀ _ hv
    have hz : z ≠ 0 := by
      intro h
      exact (by decide : (0 : Fin 4) ≠ 1) (hX (h.trans hX₁.symm))
    have hzv : z ≠ v := hXY 0 1 (by decide)
    have hzw : z ≠ w := hXY 0 0 (by decide)
    have hwv : w ≠ v := fun h => (by decide : (0 : Fin 4) ≠ 1) (hY (by decide) (by decide) h)
    have hT : t * v ≠ 1 := by
      rw [htv, ← hX₂]
      exact (hXY 2 3 (by decide)).symm
    have hf : t * v ≠ x := by
      rw [htv]
      exact (hXY 3 3 (by decide)).symm
    have ht₁ : t ≠ 1 := by
      intro he
      have h : Y 3 = Y 1 := by rw [← htv, he, one_mul]
      exact (by decide : (3 : Fin 4) ≠ 1) (hY (by decide) (by decide) h)
    have hx₁ : x ≠ 1 := by
      intro h
      exact (by decide : (3 : Fin 4) ≠ 2) (hX (h.trans hX₂.symm))
    have ht : t ≠ 0 := by
      intro he
      have h : Y 3 = 0 := by rw [← htv, he, zero_mul]
      exact hXY 1 3 (by decide) (hX₁.trans h.symm)
    have hX' : X = ![z, 0, 1, x] := by
      funext i
      fin_cases i <;> first | rfl | exact hX₁ | exact hX₂
    have hscale (i : Fin 24) : η * matchingProduct α β (fourPerm i).symm = ξ * F i := by
      rw [hprod, show (Finset.univ : Finset (Fin 4)).erase 2 = {0, 1, 3} by decide +kernel,
        Finset.prod_insert (by decide : (0 : Fin 4) ∉ ({1, 3} : Finset (Fin 4))),
        Finset.prod_insert (by decide : (1 : Fin 4) ∉ ({3} : Finset (Fin 4))), Finset.prod_singleton]
      dsimp only [F, fourQuadraticRatioPoleProduct, ξ]
      rw [htv, hX']
      ring
    have hpc : ∀ i ∈ ({0, 1, 4, 5, 7, 8} : Finset (Fin 24)), (ξ * F i).re = H := by
      intro i hi
      rw [← hscale i]
      exact hc i hi
    have hg' (i : Fin 24) : g i = (ξ * (F i - F 0)).re := by
      rw [mul_sub, Complex.sub_re, ← hscale i, ← hscale 0, hc 0 (by decide)]
      rfl
    obtain ⟨hti, hxi, hdir, r, u, hr, _, _, hW, hZ, hwEq, hzEq⟩ :=
      fourQuadraticRatio_normalized_chart z x w v t ξ H hz hzv hzw hv hwv hT hf ht₁ hx₁ hξ hpc
    have htC : (t.re : ℂ) = t := Complex.ext (by simp) (by simpa using hti.symm)
    have hxC : (x.re : ℂ) = x := Complex.ext (by simp) (by simpa using hxi.symm)
    have htR : t.re ≠ 0 := fun he => ht (Complex.ext (by simpa using he) (by simpa using hti))
    have hrR : r ≠ 0 := Complex.ofReal_ne_zero.mp hr
    have h := fourQuadraticRatio_projective_capacity x.re t.re r u z w v ξ hv hzw htR hrR
    simp only [htC, hxC] at h
    have h' := h (sub_ne_zero.mpr hf) (sub_ne_zero.mpr hT) hW hZ hzEq hwEq hdir
      (fun i => (hg' i) ▸ hg i)
      (by simpa only [← hg'] using hd')
      (by simpa only [← hg'] using fourQuadraticRatio_gap_nine α β η H hc)
    simpa only [← hg'] using h'
  have hGram := four_budget_minor_nonneg_transpose_swap (hg 15) (hg 19) (hg 10) hd'.le hcap.le U hU
  apply sub_nonneg.mp
  rw [fourQuadraticRatio_gap_eq_budget α β η H hc U hU]
  apply add_nonneg _ hGram
  exact add_nonneg (add_nonneg (add_nonneg (mul_nonneg (hg 16) (subsetMinorSq_nonneg U _ _))
    (mul_nonneg (hg 14) (subsetMinorSq_nonneg U _ _)))
    (mul_nonneg (hg 6) (subsetMinorSq_nonneg U _ _)))
    (mul_nonneg (hg 13) (subsetMinorSq_nonneg U _ _))

end MOC
