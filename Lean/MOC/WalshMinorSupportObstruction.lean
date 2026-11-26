import MOC.FiniteMinorLaw
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Data.Matrix.Rank
import Mathlib.Data.ZMod.Basic

/-! An orthogonal Walsh matrix of order sixteen has no permutation for
which every selected size-two minor is nonzero. -/

open Matrix

namespace MOC

noncomputable section

/-- Binary four-coordinate labels for the rows and columns. -/
abbrev WalshLabel := Fin 4 → ZMod 2

private theorem bit_zero_or_one (x : ZMod 2) : x = 0 ∨ x = 1 := by
  have hx := x.val_lt
  rcases show x.val = 0 ∨ x.val = 1 by omega with h | h
  · exact Or.inl ((ZMod.val_eq_zero _).mp h)
  · exact Or.inr ((ZMod.val_eq_one (by decide) _).mp h)

private theorem bit_add_self (x : ZMod 2) : x + x = 0 := by
  rw [← two_mul, show (2 : ZMod 2) = 0 by decide, zero_mul]

private theorem walshLabel_add_self (x : WalshLabel) : x + x = 0 := by
  funext i
  exact bit_add_self (x i)

private theorem walshLabel_card : Fintype.card WalshLabel = 16 := by
  simp [WalshLabel, Fintype.card_fun, ZMod.card]

private def walshSign (b : ZMod 2) : ℂ := if b = 0 then 1 else -1

private theorem walshSign_add (x y : ZMod 2) : walshSign (x + y) = walshSign x * walshSign y := by
  rcases bit_zero_or_one x with rfl | rfl <;>
    rcases bit_zero_or_one y with rfl | rfl <;>
    simp [walshSign, bit_add_self]

/-- The normalized Walsh matrix for the binary dot product. -/
def walshMinorSupportMixer : Matrix WalshLabel WalshLabel ℂ :=
  Matrix.of fun r c => walshSign (r ⬝ᵥ c) / 4

private theorem walsh_character_sum (r : WalshLabel) (hr : r ≠ 0) :
    ∑ c : WalshLabel, walshSign (r ⬝ᵥ c) = 0 := by
  obtain ⟨i, hi⟩ : ∃ i, r i ≠ 0 := by
    by_contra! h
    exact hr (funext h)
  let s : WalshLabel := Pi.single i 1
  have hs : r ⬝ᵥ s = 1 := by
    rw [s, dotProduct_single_one]
    exact (bit_zero_or_one (r i)).resolve_left hi
  have h := Equiv.sum_comp (Equiv.addRight s) (fun c : WalshLabel => walshSign (r ⬝ᵥ c))
  change (∑ c : WalshLabel, walshSign (r ⬝ᵥ (c + s))) = ∑ c : WalshLabel, walshSign (r ⬝ᵥ c) at h
  simp_rw [dotProduct_add, hs, walshSign_add, show walshSign 1 = -1 by simp [walshSign],
    mul_neg, mul_one, Finset.sum_neg_distrib] at h
  linear_combination -(1 / 2 : ℂ) * h

theorem walshMinorSupportMixer_unitary : IsUnitary walshMinorSupportMixer := by
  have hstar (i j : WalshLabel) : star (walshMinorSupportMixer i j) = walshMinorSupportMixer i j := by
    simp only [walshMinorSupportMixer, Matrix.of_apply, walshSign, star_div₀, star_ofNat]
    split <;> simp
  have h : walshMinorSupportMixer * walshMinorSupportMixerᴴ = 1 := by
    ext r s : 1
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, hstar,
      walshMinorSupportMixer, Matrix.of_apply]
    simp_rw [show ∀ x y : ℂ, x / 4 * (y / 4) = (x * y) / 16 by intros; ring,
      ← walshSign_add, ← add_dotProduct, ← Finset.sum_div]
    by_cases hEq : r = s
    · subst s
      simp [walshLabel_add_self, walshSign, walshLabel_card, Matrix.one_apply_eq]
    · have hne : r + s ≠ 0 := by
        intro hzero
        apply hEq
        calc
          r = r + (s + s) := by rw [walshLabel_add_self, add_zero]
          _ = s := by rw [← add_assoc, hzero, zero_add]
      rw [walsh_character_sum _ hne, zero_div, Matrix.one_apply_ne hEq]
  exact ⟨h, Matrix.mul_eq_one_comm.mp h⟩

private theorem walsh_pairing_of_minor_ne_zero (r s c d : WalshLabel)
    (h : walshMinorSupportMixer r c * walshMinorSupportMixer s d -
      walshMinorSupportMixer r d * walshMinorSupportMixer s c ≠ 0) :
    (r + s) ⬝ᵥ (c + d) = 1 := by
  apply (bit_zero_or_one _).resolve_left
  intro hzero
  apply h
  have hsplit : ((r ⬝ᵥ c) + (s ⬝ᵥ d)) + ((r ⬝ᵥ d) + (s ⬝ᵥ c)) = 0 := by
    rw [show ((r ⬝ᵥ c) + (s ⬝ᵥ d)) + ((r ⬝ᵥ d) + (s ⬝ᵥ c)) = (r + s) ⬝ᵥ (c + d) by
      simp only [add_dotProduct, dotProduct_add]
      abel]
    exact hzero
  have hsum : (r ⬝ᵥ c) + (s ⬝ᵥ d) = (r ⬝ᵥ d) + (s ⬝ᵥ c) := by
    calc
      _ = ((r ⬝ᵥ c) + (s ⬝ᵥ d)) + (((r ⬝ᵥ d) + (s ⬝ᵥ c)) +
          ((r ⬝ᵥ d) + (s ⬝ᵥ c))) := by rw [bit_add_self, add_zero]
      _ = _ := by rw [← add_assoc, hsplit, zero_add]
  simp only [walshMinorSupportMixer, Matrix.of_apply]
  simp_rw [show ∀ x y : ℂ, x / 4 * (y / 4) = (x * y) / 16 by intros; ring, ← walshSign_add]
  rw [hsum, sub_self]

private theorem walsh_pairing_impossible (σ : Equiv.Perm WalshLabel)
    (h : ∀ r s : WalshLabel, r ≠ s → (r + s) ⬝ᵥ (σ r + σ s) = 1) : False := by
  classical
  let K := {r : WalshLabel // r ≠ 0}
  let d (r : WalshLabel) := σ r + σ 0
  have hdiag (r : K) : (r : WalshLabel) ⬝ᵥ d r = 1 := by
    simpa only [d, add_zero] using h r 0 r.property
  have hcross (r s : K) (hne : r ≠ s) :
      ((r : WalshLabel) ⬝ᵥ d s) + ((s : WalshLabel) ⬝ᵥ d r) = 1 := by
    have hsum : d r + d s = σ r + σ s := by
      simp only [d, add_add_add_comm (σ r) (σ 0) (σ s) (σ 0), walshLabel_add_self, add_zero]
    have ht := h r s (fun he => hne (Subtype.ext he))
    rw [← hsum, add_dotProduct, dotProduct_add, dotProduct_add, hdiag r, hdiag s] at ht
    calc
      _ = (((r : WalshLabel) ⬝ᵥ d s) + ((s : WalshLabel) ⬝ᵥ d r)) + (1 + 1) := by
        rw [bit_add_self, add_zero]
      _ = (1 + ((r : WalshLabel) ⬝ᵥ d s)) + (((s : WalshLabel) ⬝ᵥ d r) + 1) := by abel
      _ = 1 := ht
  let R : Matrix K (Fin 4) (ZMod 2) := Matrix.of fun r i => r.val i
  let D : Matrix K (Fin 4) (ZMod 2) := Matrix.of fun r i => d r i
  let J₁ : Matrix K Unit (ZMod 2) := Matrix.of fun _ _ => 1
  let J₂ : Matrix Unit K (ZMod 2) := Matrix.of fun _ _ => 1
  let L := Matrix.fromCols (Matrix.fromCols R D) J₁
  let T := Matrix.fromRows (Matrix.fromRows Dᵀ Rᵀ) J₂
  have hI : L * T = 1 := by
    simp only [L, T, Matrix.fromCols_mul_fromRows]
    ext r s : 1
    have he : (R * Dᵀ + D * Rᵀ) r s =
        ((r : WalshLabel) ⬝ᵥ d s) + ((s : WalshLabel) ⬝ᵥ d r) := by
      simp only [R, D, Matrix.add_apply, Matrix.mul_apply, Matrix.of_apply, Matrix.transpose_apply,
        dotProduct]
      apply congrArg (fun v => (∑ i, r.val i * d s i) + v)
      exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)
    rw [Matrix.add_apply, he]
    have hJ : (J₁ * J₂) r s = 1 := by
      simp [J₁, J₂, Matrix.mul_apply, Fintype.sum_unique]
    rw [hJ]
    by_cases hEq : r = s
    · subst s
      simp only [bit_add_self, zero_add, Matrix.one_apply_eq]
    · rw [hcross r s hEq, bit_add_self, Matrix.one_apply_ne hEq]
  have hrank := (Matrix.rank_mul_le_left L T).trans (Matrix.rank_le_card_width L)
  rw [hI, Matrix.rank_one] at hrank
  have hc0 : Fintype.card {r : WalshLabel // r = 0} = 1 :=
    Fintype.card_eq_one_iff.mpr ⟨⟨0, rfl⟩, fun r => Subtype.ext r.property⟩
  have hc : Fintype.card K = 15 := by
    dsimp only [K]
    rw [Fintype.card_subtype_compl (fun r : WalshLabel => r = 0), walshLabel_card, hc0]
  norm_num [hc, Fintype.card_sum] at hrank

/-- For every permutation, at least one selected two-by-two minor vanishes. -/
theorem walshMinorSupportMixer_zero_pair (σ : Equiv.Perm WalshLabel) :
    ∃ r s : WalshLabel, r ≠ s ∧ subsetMinorSq walshMinorSupportMixer {r, s} {σ r, σ s} = 0 := by
  by_contra h
  apply walsh_pairing_impossible σ
  intro r s hrs
  apply walsh_pairing_of_minor_ne_zero
  intro hz
  apply h
  refine ⟨r, s, hrs, ?_⟩
  rw [subsetMinorSq_pair _ walshMinorSupportMixer_unitary hrs (fun he => hrs (σ.injective he)), hz, map_zero]

end

end MOC
