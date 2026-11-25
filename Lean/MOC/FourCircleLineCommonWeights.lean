import MOC.CommonLawTransport
import MOC.HermitianByNormalFourProof
import MOC.ThreeValues
import MOC.TwoFreeEntries
import Mathlib.NumberTheory.Zsqrtd.GaussianInt

/-! Common permutation weights with a fixed spectrum in order four. -/

open BigOperators Finset Matrix
open scoped ComplexConjugate

namespace MOC

noncomputable section

private theorem weightedDiamondSupport_four_interval (t : ℝ) (ht : 1 < t) (ht₂ : t ≤ 2)
    (U : Matrix (Fin 4) (Fin 4) ℂ) (hU : IsUnitary U) : WeightedDiamondSupportAt t U := by
  have hs : Set.Ioo (1 : ℝ) 2 ⊆ {q : ℝ | WeightedDiamondSupportAt q U} := by
    intro s hs
    have h₁ : 0 < s - 1 := sub_pos.mpr hs.1
    have h₂ : 0 < 2 - s := sub_pos.mpr hs.2
    let u := (s - 1) / (2 - s)
    have hu : 0 < u := div_pos h₁ h₂
    have he : u / (1 + u) = s - 1 := by
      dsimp only [u]
      field_simp [h₂.ne'] <;> ring
    have hc := RayCoefficients.weightedDiamondFacetCompleteness_lower u hu
    rw [he] at hc
    have h := weightedDiamondSupport_of_facetCompleteness (s - 1) h₁.le hc U hU
    rwa [show 1 + (s - 1) = s by ring] at h
  apply closure_minimal hs (isClosed_weightedDiamondSupportAt U)
  rw [closure_Ioo (by norm_num : (1 : ℝ) ≠ 2)]
  exact ⟨ht.le, ht₂⟩

private theorem commonWeights_of_swapped_right {a : Fin 4 → ℂ}
    {U : Matrix (Fin 4) (Fin 4) ℂ} (hU : IsUnitary U)
    (w : Equiv.Perm (Fin 4) → ℝ) (hw : ∀ σ, 0 ≤ w σ) (hs : ∑ σ, w σ = 1)
    (he : ∀ b, weightedMatchingValue b a w = determinantValue b a Uᴴ) :
    HasCommonWeights a U := by
  let rev : Equiv.Perm (Equiv.Perm (Fin 4)) :=
    ⟨fun σ => σ.symm, fun σ => σ.symm, fun _ => rfl, fun _ => rfl⟩
  refine ⟨fun σ => w σ.symm, fun σ => hw σ.symm, (Equiv.sum_comp rev w).trans hs, ?_⟩
  intro b
  rw [weightedMatchingValue_swap, he]
  rw [← determinantValue_left_conjugation a b U hU, determinantValue, add_comm]

/-- Four real eigenvalues admit one law for every complex diagonal partner.
For repeated eigenvalues an adjacent two-minor coupling gives the law directly. -/
theorem commonWeights_four_real_spectrum (a : Fin 4 → ℝ) (U : Matrix (Fin 4) (Fin 4) ℂ)
    (hU : IsUnitary U) : HasCommonWeights (fun i => (a i : ℂ)) U := by
  classical
  have hUadj : IsUnitary Uᴴ :=
    ⟨by simpa only [Matrix.conjTranspose_conjTranspose] using hU.2,
      by simpa only [Matrix.conjTranspose_conjTranspose] using hU.1⟩
  by_cases hinj : Function.Injective a
  · obtain ⟨w, hw, hs, he⟩ := exists_right_weights_four_of_weightedDiamond_support_le_two
      weightedDiamondSupport_four_interval a hinj Uᴴ hUadj
    exact commonWeights_of_swapped_right hU w hw hs he
  · have h : ¬ ∀ i k, a i = a k → i = k := hinj
    push_neg at h
    obtain ⟨i, k, hik, hne⟩ := h
    have hcover : ∀ i k : Fin 4, i ≠ k → ∃ j l : Fin 4,
        ∀ m, m ≠ j → m = i ∨ m = k ∨ m = l := by decide +kernel
    obtain ⟨j, l, hjl⟩ := hcover i k hne
    let J := (Finset.univ : Finset (Fin 4)).filter (fun m => m ≠ j ∧ a m = a i)
    have hj : j ∉ J := by simp [J]
    obtain ⟨w, hw, hs, he⟩ := exists_commonWeights_three_values_one_singleton Uᴴ hUadj J j hj
    have ha : Function.update (fun m => if m ∈ J then (a i : ℂ) else (a l : ℂ)) j (a j) =
        fun m => (a m : ℂ) := by
      funext m
      by_cases hm : m = j
      · subst m
        rw [Function.update_self]
      · rw [Function.update_of_ne hm]
        by_cases hmi : a m = a i
        · simp [J, hm, hmi]
        · rcases hjl m hm with rfl | rfl | rfl
          · exact (hmi rfl).elim
          · exact (hmi hik.symm).elim
          · simp [J, hm, hmi]
    apply commonWeights_of_swapped_right hU w hw hs
    intro b
    simpa only [ha] using he b (a i) (a l) (a j)

/-- A circle or straight line containing the fixed spectrum is sufficient for
one probability law for all diagonal partners in order four. -/
theorem commonWeights_four_of_circle_or_line (a : Fin 4 → ℂ) (U : Matrix (Fin 4) (Fin 4) ℂ)
    (hU : IsUnitary U) (ha : SpectrumOnGeneralizedCircle a) : HasCommonWeights a U :=
  commonWeights_on_circle_of_real U hU (fun b => commonWeights_four_real_spectrum b U hU) a ha

end

end MOC
