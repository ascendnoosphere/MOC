import MOC.HermitianByNormal
import MOC.WeightedDiamondPolynomial
import Mathlib.Data.Fin.Tuple.Sort

/-! A real spectrum of order four reduces to the weighted diamond with
strictly larger weight on its second middle coordinate. -/

open BigOperators Matrix

namespace MOC

noncomputable section

/-- Every weighted-diamond score of the minor profile is bounded by a permutation score. -/
def WeightedDiamondSupportAt (t : ℝ) (U : Matrix (Fin 4) (Fin 4) ℂ) : Prop :=
  ∀ f g s, ∃ σ : Equiv.Perm (Fin 4),
    (∑ τ, realSignedWeight U τ * weightedDiamondScore t f g s τ) ≤
      weightedDiamondScore t f g s σ

private theorem exists_right_weights_of_ordered_real_spectrum
    (b : Fin 4 → ℝ) (U : Matrix (Fin 4) (Fin 4) ℂ) (hU : IsUnitary U)
    (h₀₂ : b 0 < b 2) (h₂₁ : b 2 < b 1) (h₁₃ : b 1 < b 3)
    (hs : ∀ t : ℝ, 1 < t → WeightedDiamondSupportAt t U) :
    ∃ w : Equiv.Perm (Fin 4) → ℝ, (∀ σ, 0 ≤ w σ) ∧ (∑ σ, w σ = 1) ∧
      ∀ a : Fin 4 → ℂ,
        (∑ σ, (w σ : ℂ) * matchingProduct a (fun j => (b j : ℂ)) σ) =
          determinantValue a (fun j => (b j : ℂ)) U := by
  have h₂ : 0 < b 2 - b 0 := sub_pos.mpr h₀₂
  have h₁ : 0 < b 1 - b 0 := sub_pos.mpr (h₀₂.trans h₂₁)
  have h₃ : 0 < b 3 - b 0 := sub_pos.mpr (h₀₂.trans (h₂₁.trans h₁₃))
  have h₂₁' : (b 1 - b 0)⁻¹ < (b 2 - b 0)⁻¹ :=
    (inv_lt_inv₀ h₁ h₂).mpr (sub_lt_sub_right h₂₁ _)
  have h₁₃' : (b 3 - b 0)⁻¹ < (b 1 - b 0)⁻¹ :=
    (inv_lt_inv₀ h₃ h₁).mpr (sub_lt_sub_right h₁₃ _)
  let d := (b 1 - b 0)⁻¹ - (b 3 - b 0)⁻¹
  let t := ((b 2 - b 0)⁻¹ - (b 3 - b 0)⁻¹) / d
  have hd : 0 < d := sub_pos.mpr h₁₃'
  have ht : 1 < t := (lt_div_iff₀ hd).mpr (by
    simpa only [one_mul, d] using sub_lt_sub_right h₂₁' (b 3 - b 0)⁻¹)
  have hnorm : (b 2 - b 0)⁻¹ - (b 3 - b 0)⁻¹ = t * d :=
    (div_mul_cancel₀ _ hd.ne').symm
  have hb (j : Fin 4) (hj : j ≠ 0) : (b j : ℂ) - (b 0 : ℂ) ≠ 0 := by
    fin_cases j
    · exact (hj rfl).elim
    · exact_mod_cast h₁.ne'
    · exact_mod_cast h₂.ne'
    · exact_mod_cast h₃.ne'
  have hd' : ((b 1 : ℂ) - (b 0 : ℂ))⁻¹ - ((b 3 : ℂ) - (b 0 : ℂ))⁻¹ ≠ 0 := by
    simpa only [d, Complex.ofReal_sub, Complex.ofReal_inv, Complex.ofReal_zero] using
      (Complex.ofReal_ne_zero.mpr hd.ne' : (d : ℂ) ≠ 0)
  have ht' : ((b 2 : ℂ) - (b 0 : ℂ))⁻¹ - ((b 3 : ℂ) - (b 0 : ℂ))⁻¹ =
      (t : ℂ) * (((b 1 : ℂ) - (b 0 : ℂ))⁻¹ - ((b 3 : ℂ) - (b 0 : ℂ))⁻¹) := by
    simpa only [d, Complex.ofReal_sub, Complex.ofReal_inv, Complex.ofReal_mul] using
      congrArg (fun x : ℝ => (x : ℂ)) hnorm
  obtain ⟨w, hw, hsum, hscore⟩ :=
    exists_weights_of_weightedDiamond_support t (realSignedWeight U) (hs t ht)
  exact ⟨w, hw, hsum, fun a => determinantValue_eq_of_weightedDiamondScores
    a (fun j => (b j : ℂ)) U hU t w hscore hb hd' ht'⟩

/-- The normalized weighted-diamond support test provides one probability law
for every diagonal partner of a fixed simple real spectrum. -/
theorem exists_right_weights_four_of_weightedDiamond_support
    (hs : ∀ (t : ℝ), 1 < t → ∀ U : Matrix (Fin 4) (Fin 4) ℂ,
      IsUnitary U → WeightedDiamondSupportAt t U)
    (b : Fin 4 → ℝ) (hb : Function.Injective b)
    (U : Matrix (Fin 4) (Fin 4) ℂ) (hU : IsUnitary U) :
    ∃ w : Equiv.Perm (Fin 4) → ℝ, (∀ σ, 0 ≤ w σ) ∧ (∑ σ, w σ = 1) ∧
      ∀ a : Fin 4 → ℂ,
        (∑ σ, (w σ : ℂ) * matchingProduct a (fun j => (b j : ℂ)) σ) =
          determinantValue a (fun j => (b j : ℂ)) U := by
  let p := Tuple.sort b
  have hp : StrictMono (b ∘ p) := (Tuple.monotone_sort b).strictMono_of_injective
    (hb.comp p.injective)
  let e : Equiv.Perm (Fin 4) := (Equiv.swap 1 2).trans p
  let B (j : Fin 4) := b (e j)
  have h₀₂ : B 0 < B 2 := by
    simpa [B, e, Equiv.swap_apply_def] using hp (show (0 : Fin 4) < 1 by decide)
  have h₂₁ : B 2 < B 1 := by
    simpa [B, e, Equiv.swap_apply_def] using hp (show (1 : Fin 4) < 2 by decide)
  have h₁₃ : B 1 < B 3 := by
    simpa [B, e, Equiv.swap_apply_def] using hp (show (2 : Fin 4) < 3 by decide)
  let V := U.submatrix (Equiv.refl (Fin 4)) e
  have hV : IsUnitary V := unitary_reindex _ _ hU
  obtain ⟨w, hw, hsum, heq⟩ := exists_right_weights_of_ordered_real_spectrum
    B V hV h₀₂ h₂₁ h₁₃ (fun t ht => hs t ht V hV)
  let E : Equiv.Perm (Fin 4) ≃ Equiv.Perm (Fin 4) :=
    { toFun := fun σ => e.symm.trans σ
      invFun := fun σ => e.trans σ
      left_inv := by
        intro σ
        ext j
        simp
      right_inv := by
        intro σ
        ext j
        simp }
  refine ⟨fun σ => w (E.symm σ), fun σ => hw _, (Equiv.sum_comp E.symm w).trans hsum, ?_⟩
  intro a
  have hm (σ : Equiv.Perm (Fin 4)) :
      matchingProduct a (fun j => (b j : ℂ)) (E σ) =
        matchingProduct a (fun j => (B j : ℂ)) σ := by
    unfold matchingProduct
    rw [← Equiv.prod_comp e (fun j => a (E σ j) + (b j : ℂ))]
    simp [E, B]
  calc
    _ = ∑ σ, (w σ : ℂ) * matchingProduct a (fun j => (B j : ℂ)) σ := by
      rw [← Equiv.sum_comp E]
      simp only [Equiv.symm_apply_apply, hm]
    _ = determinantValue a (fun j => (B j : ℂ)) V := heq a
    _ = determinantValue a (fun j => (b j : ℂ)) U :=
      determinantValue_reindex (Equiv.refl (Fin 4)) e a (fun j => (b j : ℂ)) U

/-- It suffices to prove support for the weighted diamond with middle weight
strictly greater than one to obtain the order-four Hermitian-by-normal theorem. -/
theorem hermitianByNormal_four_of_weightedDiamond_support
    (hs : ∀ (t : ℝ), 1 < t → ∀ U : Matrix (Fin 4) (Fin 4) ℂ,
      IsUnitary U → WeightedDiamondSupportAt t U) :
    HermitianByNormal (Fin 4) := by
  intro a b U hU
  by_cases ha : Function.Injective a
  · have hU' : IsUnitary Uᴴ := ⟨by simpa using hU.2, by simpa using hU.1⟩
    obtain ⟨w, hw, hsum, heq⟩ := exists_right_weights_four_of_weightedDiamond_support
      hs a ha Uᴴ hU'
    exact (holds_swap_iff (fun j => (a j : ℂ)) b hU).mp (holds_of_weights w hw hsum (heq b))
  · apply holds_four_of_repeated_spectrum _ _ _ hU
    exact Or.inl (fun hi => ha (fun _ _ h => hi (congrArg (fun x : ℝ => (x : ℂ)) h)))

end

end MOC
