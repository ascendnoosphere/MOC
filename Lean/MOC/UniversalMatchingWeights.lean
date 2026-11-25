import MOC.CommonWeights
import MOC.Small

/-! Permutation weights independent of both spectra. -/

open BigOperators Matrix

namespace MOC

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A single nonnegative permutation law represents the determinant for all spectra. -/
def HasUniversalMatchingWeights (U : Matrix ι ι ℂ) : Prop :=
  ∃ w : Equiv.Perm ι → ℝ, (∀ σ, 0 ≤ w σ) ∧ (∑ σ, w σ) = 1 ∧
    ∀ a b, determinantValue a b U = weightedMatchingValue a b w

theorem HasUniversalMatchingWeights.holds {U : Matrix ι ι ℂ}
    (h : HasUniversalMatchingWeights U) (a b : ι → ℂ) : Holds a b U := by
  obtain ⟨w, hw, hs, hd⟩ := h
  exact holds_of_weights w hw hs (hd a b).symm

theorem hasUniversalMatchingWeights_of_nonneg_realSignedWeight {U : Matrix ι ι ℂ}
    (hU : IsUnitary U) (hw : ∀ σ, 0 ≤ realSignedWeight U σ) : HasUniversalMatchingWeights U :=
  ⟨realSignedWeight U, hw, sum_realSignedWeight U hU, fun a b =>
    (real_signed_determinant a b U hU).symm⟩

/-- Independent relabeling pushes the same probability law forward on matchings. -/
theorem hasUniversalMatchingWeights_reindex_iff {κ : Type*} [Fintype κ] [DecidableEq κ]
    (eRow eCol : κ ≃ ι) (U : Matrix ι ι ℂ) :
    HasUniversalMatchingWeights (U.submatrix eRow eCol) ↔ HasUniversalMatchingWeights U := by
  let p := eCol.equivCongr eRow
  constructor
  · rintro ⟨w, hw, hs, h⟩
    refine ⟨w ∘ p.symm, fun σ => hw (p.symm σ), ?_, fun a b => ?_⟩
    · exact (Equiv.sum_comp p.symm w).trans hs
    · rw [← determinantValue_reindex eRow eCol a b U, h]
      unfold weightedMatchingValue
      simp_rw [matchingProduct_reindex]
      calc
        _ = ∑ σ, (w (p.symm (p σ)) : ℂ) * matchingProduct a b (p σ) := by
          apply Finset.sum_congr rfl
          intro σ _
          rw [Equiv.symm_apply_apply]
          rfl
        _ = _ := Equiv.sum_comp p (fun σ => (w (p.symm σ) : ℂ) * matchingProduct a b σ)
  · rintro ⟨w, hw, hs, h⟩
    refine ⟨w ∘ p, fun σ => hw (p σ), (Equiv.sum_comp p w).trans hs, fun a b => ?_⟩
    let a' := a ∘ eRow.symm
    let b' := b ∘ eCol.symm
    have ha : a' ∘ eRow = a := by funext i; simp [a']
    have hb : b' ∘ eCol = b := by funext i; simp [b']
    rw [← ha, ← hb, determinantValue_reindex, h]
    unfold weightedMatchingValue
    simp_rw [matchingProduct_reindex]
    exact (Equiv.sum_comp p (fun σ => (w σ : ℂ) * matchingProduct a' b' σ)).symm

private theorem universal_of_adjoint {U : Matrix ι ι ℂ} (hU : IsUnitary U)
    (h : HasUniversalMatchingWeights U) : HasUniversalMatchingWeights Uᴴ := by
  obtain ⟨w, hw, hs, hd⟩ := h
  let p : Equiv.Perm ι ≃ Equiv.Perm ι := ⟨Equiv.symm, Equiv.symm, Equiv.symm_symm, Equiv.symm_symm⟩
  refine ⟨w ∘ p, fun σ => hw (p σ), (Equiv.sum_comp p w).trans hs, fun a b => ?_⟩
  have hv : determinantValue a b Uᴴ = determinantValue b a U := by
    simpa [determinantValue, add_comm] using
      (determinantValue_relative a b U (1 : Matrix ι ι ℂ) hU).symm
  have hp (σ : Equiv.Perm ι) : matchingProduct a b σ = matchingProduct b a (p σ) := by
    change matchingProduct a b σ = matchingProduct b a σ.symm
    rw [matchingProduct_inverse]
    simp [matchingProduct, add_comm]
  rw [hv, hd]
  unfold weightedMatchingValue
  simp_rw [hp]
  exact (Equiv.sum_comp p (fun σ => (w σ : ℂ) * matchingProduct b a σ)).symm

/-- Taking the adjoint inverts the permutation in the universal law. -/
theorem hasUniversalMatchingWeights_adjoint_iff {U : Matrix ι ι ℂ} (hU : IsUnitary U) :
    HasUniversalMatchingWeights Uᴴ ↔ HasUniversalMatchingWeights U := by
  refine ⟨fun h => ?_, universal_of_adjoint hU⟩
  have hu : IsUnitary Uᴴ := by
    simpa only [IsUnitary, conjTranspose_conjTranspose] using And.symm hU
  simpa only [conjTranspose_conjTranspose] using universal_of_adjoint hu h

private theorem universal_of_singleton_expansion {U : Matrix ι ι ℂ} (hU : IsUnitary U)
    (hexp : ∀ a b : ι → ℂ, ∃ (c : ℂ) (f : ι → ι → ℂ), ∀ σ,
      matchingProduct a b σ = c + ∑ j, f j (σ j)) :
    HasUniversalMatchingWeights U := by
  obtain ⟨w, hw, hs, hm⟩ := exists_singleton_weights U hU
  refine ⟨w, hw, hs, fun a b => ?_⟩
  obtain ⟨c, f, hexp⟩ := hexp a b
  have heval (v : Equiv.Perm ι → ℂ) (hv : ∑ σ, v σ = 1) :
      ∑ σ, v σ * matchingProduct a b σ = c + ∑ j, ∑ i, marginal v i j * f j i := by
    simp_rw [hexp, mul_add, Finset.mul_sum]
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, hv, one_mul, Finset.sum_comm]
    simp_rw [sum_weighted_evaluation]
  have hs' : ∑ σ, (w σ : ℂ) = 1 := by
    simpa only [Complex.ofReal_sum, Complex.ofReal_one] using
      congrArg (fun t : ℝ => (t : ℂ)) hs
  unfold weightedMatchingValue
  rw [← signed_determinant a b U hU, heval _ hs',
    heval _ (sum_signedWeight U (det_ne_zero_of_unitary hU))]
  simp only [hm, marginal_signedWeight U hU]

private theorem universal_of_subsingleton [Subsingleton ι] {U : Matrix ι ι ℂ} (hU : IsUnitary U) :
    HasUniversalMatchingWeights U := by
  apply universal_of_singleton_expansion hU
  intro a b
  refine ⟨matchingProduct a b (Equiv.refl ι), fun _ _ => 0, fun σ => ?_⟩
  have hσ : σ = Equiv.refl ι := Equiv.ext fun _ => Subsingleton.elim _ _
  simp [hσ]

private theorem universal_fin_two {U : Matrix (Fin 2) (Fin 2) ℂ} (hU : IsUnitary U) :
    HasUniversalMatchingWeights U := by
  apply universal_of_singleton_expansion hU
  intro a b
  refine ⟨(∏ j, a j) + ∏ j, b j, fun j i => exceptProduct a i * b j, fun σ => ?_⟩
  have h (a b : Fin 2 → ℂ) : ∏ j, (a j + b j) =
      (∏ j, a j) + (∏ j, b j) + ∑ j, exceptProduct a j * b j := by
    simp [Fin.prod_univ_succ, Fin.sum_univ_succ, exceptProduct]
    ring
  simpa [matchingProduct, Function.comp_apply, exceptProduct_comp, Equiv.prod_comp σ] using h (a ∘ σ) b

private theorem universal_fin_three {U : Matrix (Fin 3) (Fin 3) ℂ} (hU : IsUnitary U) :
    HasUniversalMatchingWeights U := by
  apply universal_of_singleton_expansion hU
  intro a b
  refine ⟨(∏ j, a j) + ∏ j, b j, fun j i => exceptProduct a i * b j + a i * exceptProduct b j, fun σ => ?_⟩
  have h (a b : Fin 3 → ℂ) : ∏ j, (a j + b j) =
      (∏ j, a j) + (∏ j, b j) + ∑ j, (exceptProduct a j * b j + a j * exceptProduct b j) := by
    simp [Fin.prod_univ_succ, Fin.sum_univ_succ, exceptProduct]
    ring
  simpa [matchingProduct, Function.comp_apply, exceptProduct_comp, Equiv.prod_comp σ] using h (a ∘ σ) b

/-- Singleton marginals from Birkhoff determine a universal law through order three. -/
theorem hasUniversalMatchingWeights_of_card_le_three {U : Matrix ι ι ℂ}
    (hU : IsUnitary U) (hcard : Fintype.card ι ≤ 3) : HasUniversalMatchingWeights U := by
  let e := (Fintype.equivFin ι).symm
  apply (hasUniversalMatchingWeights_reindex_iff e e U).mp
  have hfin {n : ℕ} (hn : n ≤ 3) {V : Matrix (Fin n) (Fin n) ℂ} (hV : IsUnitary V) :
      HasUniversalMatchingWeights V := by
    have h : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 := by omega
    rcases h with rfl | rfl | rfl | rfl
    · exact universal_of_subsingleton hV
    · exact universal_of_subsingleton hV
    · exact universal_fin_two hV
    · exact universal_fin_three hV
  exact hfin hcard (unitary_reindex e e hU)

end MOC
