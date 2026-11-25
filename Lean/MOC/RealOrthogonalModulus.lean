import MOC.ModulusOrderTransfer
import MOC.DoubledMatching
import MOC.RealOrthogonalDoubling

/-! Reduction of the modulus bound to real orthogonal mixers in unbounded orders. -/

open BigOperators Matrix

namespace MOC

noncomputable section

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- The modulus bound for real orthogonal mixers, with arbitrary complex spectra.
A real orthogonal mixer is represented as a unitary matrix with real entries. -/
def RealOrthogonalModulusConjecture (ι : Type*) [Fintype ι] [DecidableEq ι] : Prop :=
  ∀ (a b : ι → ℂ) (U : Matrix ι ι ℂ), IsUnitary U → (∀ i j, (U i j).im = 0) →
    ∃ σ : Equiv.Perm ι, ‖determinantValue a b U‖ ≤ ‖matchingProduct a b σ‖

private theorem realOrthogonalModulusConjecture_reindex (e : κ ≃ ι)
    (h : RealOrthogonalModulusConjecture κ) : RealOrthogonalModulusConjecture ι := by
  intro a b U hU hreal
  obtain ⟨σ, hσ⟩ := h (a ∘ e) (b ∘ e) (U.submatrix e e) (unitary_reindex e e hU)
    (fun i j => hreal (e i) (e j))
  rw [determinantValue_reindex, matchingProduct_reindex] at hσ
  exact ⟨_, hσ⟩

private theorem realOrthogonalModulusConjecture_of_option [Nonempty ι]
    (h : RealOrthogonalModulusConjecture (Option ι)) : RealOrthogonalModulusConjecture ι := by
  intro a b U hU hreal
  apply modulus_bound_of_scalar_padding a b U hU
  dsimp only
  intro σ A B
  let V := Matrix.fromBlocks (U.submatrix σ (Equiv.refl ι)) 0 0 (1 : Matrix Unit Unit ℂ)
  let e := Equiv.optionEquivSumPUnit ι
  have hV : IsUnitary V :=
    unitary_directSum (unitary_reindex σ (Equiv.refl ι) hU) (isUnitary_one (ι := Unit))
  have hVreal (i j : ι ⊕ Unit) : (V i j).im = 0 := by
    cases i with
    | inl i =>
      cases j with
      | inl j => exact hreal (σ i) j
      | inr j => exact Complex.zero_im
    | inr i =>
      cases j with
      | inl j => exact Complex.zero_im
      | inr j =>
        cases i
        cases j
        change ((1 : Matrix Unit Unit ℂ) () ()).im = 0
        rw [Matrix.one_apply_eq, Complex.one_im]
  exact h A B (V.submatrix e e) (unitary_reindex e e hV) (fun i j => hVreal (e i) (e j))

/-- The real orthogonal modulus bound passes from any larger order to a smaller order. -/
theorem realOrthogonalModulusConjecture_of_le {m n : ℕ} (h : m ≤ n) :
    RealOrthogonalModulusConjecture (Fin n) → RealOrthogonalModulusConjecture (Fin m) := by
  induction h with
  | refl => exact id
  | @step n _ ih =>
    intro hn
    apply ih
    cases n with
    | zero =>
      exact fun a b U hU _ => modulusConjecture_of_conjecture conjecture_zero a b U hU
    | succ n =>
      exact realOrthogonalModulusConjecture_of_option
        (realOrthogonalModulusConjecture_reindex (finSuccEquiv _) hn)

/-- The real orthogonal modulus bound in double order gives the complex
unitary modulus bound in the original order. -/
theorem modulusConjecture_of_realOrthogonal_double
    (h : RealOrthogonalModulusConjecture (ι ⊕ ι)) : ModulusConjecture ι := by
  intro a b U hU
  obtain ⟨τ, hτ⟩ := h (Sum.elim a a) (Sum.elim b b) (realOrthogonalDouble U)
    (realOrthogonalDouble_isUnitary U hU) (realOrthogonalDouble_im U)
  have hsum (f : ι → ℂ) : f ∘ Sum.elim id id = Sum.elim f f := by
    funext i
    cases i <;> rfl
  obtain ⟨p, q, hpq⟩ := doubled_matching_factorization a b τ
  rw [hsum a, hsum b] at hpq
  rw [determinantValue_realOrthogonalDouble, hpq, norm_pow, norm_mul] at hτ
  rcases le_total ‖matchingProduct a b p‖ ‖matchingProduct a b q‖ with hp | hq
  · refine ⟨q, (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp ?_⟩
    simp only [pow_two] at hτ ⊢
    exact hτ.trans (mul_le_mul_of_nonneg_right hp (norm_nonneg _))
  · refine ⟨p, (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp ?_⟩
    simp only [pow_two] at hτ ⊢
    exact hτ.trans (mul_le_mul_of_nonneg_left hq (norm_nonneg _))

/-- In every finite order, the complex unitary modulus bound is equivalent
to the real orthogonal bound on any unbounded set of orders. Both bounds
allow arbitrary complex spectra. -/
theorem modulusConjecture_iff_realOrthogonal_on_unbounded_orders (S : Set ℕ)
    (hS : ∀ m, ∃ n ∈ S, m ≤ n) :
    (∀ m, ModulusConjecture (Fin m)) ↔
      ∀ n ∈ S, RealOrthogonalModulusConjecture (Fin n) := by
  constructor
  · intro h n _ a b U hU _
    exact h n a b U hU
  · intro h m
    obtain ⟨n, hn, hmn⟩ := hS (m + m)
    have hd : RealOrthogonalModulusConjecture (Fin (m + m)) :=
      realOrthogonalModulusConjecture_of_le hmn (h n hn)
    exact modulusConjecture_of_realOrthogonal_double
      (realOrthogonalModulusConjecture_reindex finSumFinEquiv.symm hd)

end

end MOC
