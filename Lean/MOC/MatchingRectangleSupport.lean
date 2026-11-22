import MOC.ContactRectangle
import MOC.MatchingQuartet
import Mathlib.Tactic.Linarith

/-! Real support restrictions coming from any two disjoint swaps, in every order. -/

namespace MOC

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- At zero support height, three contacts in a disjoint-swap rectangle force
the fourth contact if the reference product is nonzero. -/
theorem matching_disjoint_swaps_contact_of_zero_height
    (a b : ι → ℂ) (η : ℂ) (r : Equiv.Perm ι) (i j k l : ι)
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l)
    (hnz : η * matchingProduct a b r ≠ 0)
    (h₀ : (η * matchingProduct a b r).re = 0)
    (h₁ : (η * matchingProduct a b (r * Equiv.swap i j)).re = 0)
    (h₂ : (η * matchingProduct a b (r * Equiv.swap k l)).re = 0) :
    (η * matchingProduct a b (r * Equiv.swap i j * Equiv.swap k l)).re = 0 := by
  have hf := matchingProduct_disjoint_swaps_identity a b r i j k l hij hik hil hjk hjl hkl
  have hdiag :
      (η * matchingProduct a b r) *
          (η * matchingProduct a b (r * Equiv.swap i j * Equiv.swap k l)) =
        (η * matchingProduct a b (r * Equiv.swap i j)) *
          (η * matchingProduct a b (r * Equiv.swap k l)) := by
    linear_combination η ^ 2 * hf
  have him : (η * matchingProduct a b r).im ≠ 0 :=
    fun he => hnz (Complex.ext (by simpa using h₀) (by simpa using he))
  have h := rectangle_fourth_gap hdiag h₀ h₁ h₂
  simp only [zero_pow (by decide : (2 : ℕ) ≠ 0), zero_add, zero_sub, zero_mul] at h
  exact neg_eq_zero.mp ((mul_eq_zero.mp h).resolve_right (pow_ne_zero 2 him))

/-- At a strictly negative support height, two disjoint swaps cannot both be
contacts to the same side of the reference point on the supporting line. -/
theorem no_disjoint_swaps_on_one_side_of_negative_support
    (a b : ι → ℂ) (η : ℂ) (r : Equiv.Perm ι) (i j k l : ι)
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l)
    (hη : η ≠ 0) (hinj : Function.Injective (matchingProduct a b))
    (H : ℝ) (hH : H < 0)
    (hmax : ∀ σ, (η * matchingProduct a b σ).re ≤ H)
    (h₀ : (η * matchingProduct a b r).re = H)
    (h₁ : (η * matchingProduct a b (r * Equiv.swap i j)).re = H)
    (h₂ : (η * matchingProduct a b (r * Equiv.swap k l)).re = H)
    (hside₁ : (η * matchingProduct a b r).im ≤
      (η * matchingProduct a b (r * Equiv.swap i j)).im)
    (hside₂ : (η * matchingProduct a b r).im ≤
      (η * matchingProduct a b (r * Equiv.swap k l)).im) : False := by
  let z (σ : Equiv.Perm ι) : ℂ := η * matchingProduct a b σ
  have hz : Function.Injective z := fun _ _ h => hinj (mul_left_cancel₀ hη h)
  have hstrict (p q : ι) (hpq : p ≠ q)
      (hre : (z (r * Equiv.swap p q)).re = H)
      (him : (z r).im ≤ (z (r * Equiv.swap p q)).im) :
      (z r).im < (z (r * Equiv.swap p q)).im := by
    apply lt_of_le_of_ne him
    intro he
    have hf := hz (Complex.ext (h₀.trans hre.symm) he)
    exact hpq (r.injective (by
      simpa only [Equiv.Perm.mul_apply, Equiv.swap_apply_left] using
        congrArg (fun σ : Equiv.Perm ι => σ p) hf))
  have hdiag : z r * z (r * Equiv.swap i j * Equiv.swap k l) =
      z (r * Equiv.swap i j) * z (r * Equiv.swap k l) := by
    dsimp only [z]
    linear_combination η ^ 2 *
      matchingProduct_disjoint_swaps_identity a b r i j k l hij hik hil hjk hjl hkl
  have he := rectangle_fourth_gap hdiag h₀ h₁ h₂
  have hgap : 0 ≤ H - (z (r * Equiv.swap i j * Equiv.swap k l)).re :=
    sub_nonneg.mpr (hmax _)
  have hnonneg := mul_nonneg hgap (add_nonneg (sq_nonneg H) (sq_nonneg (z r).im))
  have hnegative := mul_neg_of_neg_of_pos
    (mul_neg_of_neg_of_pos hH (sub_pos.mpr (hstrict i j hij h₁ hside₁)))
    (sub_pos.mpr (hstrict k l hkl h₂ hside₂))
  rw [he] at hnonneg
  exact (not_lt_of_ge hnonneg) hnegative

end MOC
