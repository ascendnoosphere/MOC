import MOC.HermitianByNormal
import MOC.WeightedDiamondPolynomial
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Tactic.Linarith

/-! A real spectrum of order four reduces to the weighted diamond with
second middle weight in `(1, 2]`. -/

open BigOperators Matrix

namespace MOC

noncomputable section

/-- Every weighted-diamond score of the minor profile is bounded by a permutation score. -/
def WeightedDiamondSupportAt (t : ℝ) (U : Matrix (Fin 4) (Fin 4) ℂ) : Prop :=
  ∀ f g s, ∃ σ : Equiv.Perm (Fin 4),
    (∑ τ, realSignedWeight U τ * weightedDiamondScore t f g s τ) ≤
      weightedDiamondScore t f g s σ

private theorem exists_right_weights_of_reciprocal_normalization
    (b : Fin 4 → ℝ) (hb : Function.Injective b)
    (U : Matrix (Fin 4) (Fin 4) ℂ) (hU : IsUnitary U)
    (e : Equiv.Perm (Fin 4)) (t : ℝ)
    (hδ : (b (e 1) - b (e 0))⁻¹ - (b (e 3) - b (e 0))⁻¹ ≠ 0)
    (hnorm : (b (e 2) - b (e 0))⁻¹ - (b (e 3) - b (e 0))⁻¹ =
      t * ((b (e 1) - b (e 0))⁻¹ - (b (e 3) - b (e 0))⁻¹))
    (hs : WeightedDiamondSupportAt t (U.submatrix (Equiv.refl (Fin 4)) e)) :
    ∃ w : Equiv.Perm (Fin 4) → ℝ, (∀ σ, 0 ≤ w σ) ∧ (∑ σ, w σ = 1) ∧
      ∀ a : Fin 4 → ℂ,
        (∑ σ, (w σ : ℂ) * matchingProduct a (fun j => (b j : ℂ)) σ) =
          determinantValue a (fun j => (b j : ℂ)) U := by
  let B (j : Fin 4) := b (e j)
  let V := U.submatrix (Equiv.refl (Fin 4)) e
  have hV : IsUnitary V := unitary_reindex _ _ hU
  have hb' (j : Fin 4) (hj : j ≠ 0) : (B j : ℂ) - (B 0 : ℂ) ≠ 0 := by
    have h : B j - B 0 ≠ 0 := sub_ne_zero.mpr fun h => hj (e.injective (hb h))
    exact_mod_cast h
  have hδ' : ((B 1 : ℂ) - (B 0 : ℂ))⁻¹ - ((B 3 : ℂ) - (B 0 : ℂ))⁻¹ ≠ 0 := by
    simpa only [Complex.ofReal_sub, Complex.ofReal_inv, Complex.ofReal_zero] using
      (Complex.ofReal_ne_zero.mpr hδ :
        (((B 1 - B 0)⁻¹ - (B 3 - B 0)⁻¹ : ℝ) : ℂ) ≠ 0)
  have hnorm' : ((B 2 : ℂ) - (B 0 : ℂ))⁻¹ - ((B 3 : ℂ) - (B 0 : ℂ))⁻¹ =
      (t : ℂ) * (((B 1 : ℂ) - (B 0 : ℂ))⁻¹ - ((B 3 : ℂ) - (B 0 : ℂ))⁻¹) := by
    simpa only [Complex.ofReal_sub, Complex.ofReal_inv, Complex.ofReal_mul] using
      congrArg (fun x : ℝ => (x : ℂ)) hnorm
  obtain ⟨w, hw, hsum, hscore⟩ :=
    exists_weights_of_weightedDiamond_support t (realSignedWeight V) hs
  have heq (a : Fin 4 → ℂ) := determinantValue_eq_of_weightedDiamondScores
    a (fun j => (B j : ℂ)) V hV t w hscore hb' hδ' hnorm'
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

/-- The weights for a fixed simple real spectrum of order four only require
the weighted-diamond support test for middle weights in `(1, 2]`. -/
theorem exists_right_weights_four_of_weightedDiamond_support_le_two
    (hs : ∀ (t : ℝ), 1 < t → t ≤ 2 → ∀ U : Matrix (Fin 4) (Fin 4) ℂ,
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
  let a := B 2 - B 0
  let d := B 1 - B 2
  let c := B 3 - B 1
  have ha : 0 < a := sub_pos.mpr h₀₂
  have hd : 0 < d := sub_pos.mpr h₂₁
  have hc : 0 < c := sub_pos.mpr h₁₃
  have had := add_pos ha hd
  have hdc := add_pos hd hc
  have hsum := add_pos had hc
  have hgap₁ : a + d = B 1 - B 0 := by dsimp only [a, d]; ring
  have hgap₃ : a + d + c = B 3 - B 0 := by dsimp only [a, d, c]; ring
  let x := d * (a + d + c) / (a * c)
  have hx : 0 < x := div_pos (mul_pos hd hsum) (mul_pos ha hc)
  by_cases hx₁ : x ≤ 1
  · have hδ : 0 < (B 1 - B 0)⁻¹ - (B 3 - B 0)⁻¹ := by
      rw [← hgap₁, ← hgap₃]
      exact sub_pos.mpr ((inv_lt_inv₀ hsum had).mpr (lt_add_of_pos_right (a + d) hc))
    have hnorm : (B 2 - B 0)⁻¹ - (B 3 - B 0)⁻¹ =
        (1 + x) * ((B 1 - B 0)⁻¹ - (B 3 - B 0)⁻¹) := by
      rw [← hgap₁, ← hgap₃]
      change a⁻¹ - (a + d + c)⁻¹ = (1 + x) * ((a + d)⁻¹ - (a + d + c)⁻¹)
      dsimp only [x]
      field_simp [ha.ne', hc.ne', had.ne', hsum.ne'] <;> ring
    exact exists_right_weights_of_reciprocal_normalization b hb U hU e (1 + x) hδ.ne' hnorm
      (hs (1 + x) (by linarith only [hx]) (by linarith only [hx₁]) _ (unitary_reindex _ _ hU))
  · -- Moving the pole to the second-smallest eigenvalue replaces x by 1 / x.
    let ρ : Equiv.Perm (Fin 4) := Equiv.swap 0 3 * Equiv.swap 0 1 * Equiv.swap 0 2
    let e' := ρ.trans e
    have hb₀ : b (e' 0) = B 2 := by
      change b (e (ρ 0)) = b (e 2)
      rw [show ρ 0 = 2 by decide]
    have hb₁ : b (e' 1) = B 3 := by
      change b (e (ρ 1)) = b (e 3)
      rw [show ρ 1 = 3 by decide]
    have hb₂ : b (e' 2) = B 1 := by
      change b (e (ρ 2)) = b (e 1)
      rw [show ρ 2 = 1 by decide]
    have hb₃ : b (e' 3) = B 0 := by
      change b (e (ρ 3)) = b (e 0)
      rw [show ρ 3 = 0 by decide]
    have h₁ : b (e' 1) - b (e' 0) = d + c := by rw [hb₁, hb₀]; dsimp only [d, c]; ring
    have h₂ : b (e' 2) - b (e' 0) = d := by simp only [hb₂, hb₀, d]
    have h₃ : b (e' 3) - b (e' 0) = -a := by rw [hb₃, hb₀]; dsimp only [a]; ring
    let y := a * c / (d * (a + d + c))
    have hy : 0 < y := div_pos (mul_pos ha hc) (mul_pos hd hsum)
    have hy₁ : y ≤ 1 := by
      apply (div_le_iff₀ (mul_pos hd hsum)).mpr
      have h := (lt_div_iff₀ (mul_pos ha hc)).mp (show 1 < x from lt_of_not_ge hx₁)
      simpa only [one_mul] using h.le
    have hδ : 0 < (b (e' 1) - b (e' 0))⁻¹ - (b (e' 3) - b (e' 0))⁻¹ := by
      rw [h₁, h₃, inv_neg, sub_neg_eq_add]
      exact add_pos (inv_pos.mpr hdc) (inv_pos.mpr ha)
    have hnorm : (b (e' 2) - b (e' 0))⁻¹ - (b (e' 3) - b (e' 0))⁻¹ =
        (1 + y) * ((b (e' 1) - b (e' 0))⁻¹ - (b (e' 3) - b (e' 0))⁻¹) := by
      simp only [h₁, h₂, h₃, inv_neg, y]
      field_simp [ha.ne', hd.ne', hdc.ne', hsum.ne'] <;> ring
    exact exists_right_weights_of_reciprocal_normalization b hb U hU e' (1 + y) hδ.ne' hnorm
      (hs (1 + y) (by linarith only [hy]) (by linarith only [hy₁]) _ (unitary_reindex _ _ hU))

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
          determinantValue a (fun j => (b j : ℂ)) U :=
  exists_right_weights_four_of_weightedDiamond_support_le_two (fun t ht _ => hs t ht) b hb U hU

/-- The weighted-diamond support test on `(1, 2]` implies the order-four
Hermitian-by-normal theorem. -/
theorem hermitianByNormal_four_of_weightedDiamond_support_le_two
    (hs : ∀ (t : ℝ), 1 < t → t ≤ 2 → ∀ U : Matrix (Fin 4) (Fin 4) ℂ,
      IsUnitary U → WeightedDiamondSupportAt t U) : HermitianByNormal (Fin 4) := by
  intro a b U hU
  by_cases ha : Function.Injective a
  · have hU' : IsUnitary Uᴴ := ⟨by simpa using hU.2, by simpa using hU.1⟩
    obtain ⟨w, hw, hsum, heq⟩ := exists_right_weights_four_of_weightedDiamond_support_le_two
      hs a ha Uᴴ hU'
    exact (holds_swap_iff (fun j => (a j : ℂ)) b hU).mp (holds_of_weights w hw hsum (heq b))
  · apply holds_four_of_repeated_spectrum _ _ _ hU
    exact Or.inl (fun hi => ha (fun _ _ h => hi (congrArg (fun x : ℝ => (x : ℂ)) h)))

/-- It suffices to prove support for the weighted diamond with middle weight
strictly greater than one to obtain the order-four Hermitian-by-normal theorem. -/
theorem hermitianByNormal_four_of_weightedDiamond_support
    (hs : ∀ (t : ℝ), 1 < t → ∀ U : Matrix (Fin 4) (Fin 4) ℂ,
      IsUnitary U → WeightedDiamondSupportAt t U) : HermitianByNormal (Fin 4) :=
  hermitianByNormal_four_of_weightedDiamond_support_le_two (fun t ht _ => hs t ht)

end

end MOC
