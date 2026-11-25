import MOC.DuplicatedAssignment
import MOC.Small
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Module.Convex

/-! Downward inheritance of the maximum-modulus bound for normal matrices. -/

open BigOperators Matrix

namespace MOC

noncomputable section

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- Some matching product has modulus at least that of the determinant. -/
def ModulusConjecture (ι : Type*) [Fintype ι] [DecidableEq ι] : Prop :=
  ∀ (a b : ι → ℂ) (U : Matrix ι ι ℂ), IsUnitary U →
    ∃ σ : Equiv.Perm ι, ‖determinantValue a b U‖ ≤ ‖matchingProduct a b σ‖

omit [DecidableEq ι] in
private theorem exists_matching_norm_max (a b : ι → ℂ) :
    ∃ σ : Equiv.Perm ι, ∀ τ, ‖matchingProduct a b τ‖ ≤ ‖matchingProduct a b σ‖ := by
  classical
  obtain ⟨σ, _, hσ⟩ := Finset.exists_max_image Finset.univ
    (fun τ : Equiv.Perm ι => ‖matchingProduct a b τ‖) Finset.univ_nonempty
  exact ⟨σ, fun τ => hσ τ (Finset.mem_univ τ)⟩

theorem modulusConjecture_of_conjecture (h : Conjecture ι) : ModulusConjecture ι := by
  intro a b U hU
  obtain ⟨σ, hσ⟩ := exists_matching_norm_max a b
  refine ⟨σ, ?_⟩
  have hball : Set.range (matchingProduct a b) ⊆
      Metric.closedBall 0 ‖matchingProduct a b σ‖ := by
    rintro _ ⟨τ, rfl⟩
    simpa only [Metric.mem_closedBall, dist_zero_right] using hσ τ
  have hd := convexHull_min hball (convex_closedBall (0 : ℂ) _) (h a b U hU)
  simpa only [Metric.mem_closedBall, dist_zero_right] using hd

private theorem modulusConjecture_reindex (e : κ ≃ ι) (h : ModulusConjecture κ) :
    ModulusConjecture ι := by
  intro a b U hU
  obtain ⟨σ, hσ⟩ := h (a ∘ e) (b ∘ e) (U.submatrix e e) (unitary_reindex e e hU)
  rw [determinantValue_reindex, matchingProduct_reindex] at hσ
  exact ⟨_, hσ⟩

private theorem determinantValue_scalar_padding (a b : ι → ℂ) (U : Matrix ι ι ℂ)
    (c d : ℂ) :
    determinantValue (Sum.elim a (fun _ : Unit => c)) (Sum.elim b (fun _ : Unit => d))
      (fromBlocks U 0 0 (1 : Matrix Unit Unit ℂ)) = determinantValue a b U * (c + d) := by
  unfold determinantValue
  rw [← Matrix.fromBlocks_diagonal, ← Matrix.fromBlocks_diagonal, Matrix.fromBlocks_conjTranspose]
  simp only [Matrix.fromBlocks_multiply, Matrix.fromBlocks_add, Matrix.det_fromBlocks_zero₂₁,
    Matrix.conjTranspose_zero, Matrix.conjTranspose_one, Matrix.zero_mul, Matrix.mul_zero,
    Matrix.one_mul, Matrix.mul_one, add_zero, zero_add]
  rw [Matrix.det_unique (n := Unit)]
  simp only [Matrix.add_apply, Matrix.diagonal_apply_eq]

private theorem modulus_at_maximizing_identity (a b : ι → ℂ) (U : Matrix ι ι ℂ) (i : ι)
    (h : let e := Equiv.optionEquivSumPUnit ι
      ∀ A B : Option ι → ℂ, ∃ τ : Equiv.Perm (Option ι),
        ‖determinantValue A B ((fromBlocks U 0 0 (1 : Matrix Unit Unit ℂ)).submatrix e e)‖ ≤
          ‖matchingProduct A B τ‖)
    (hmax : ∀ σ, ‖matchingProduct a b σ‖ ≤ ‖matchingProduct a b (Equiv.refl ι)‖)
    (hpos : 0 < ‖matchingProduct a b (Equiv.refl ι)‖) :
    ‖determinantValue a b U‖ ≤ ‖matchingProduct a b (Equiv.refl ι)‖ := by
  classical
  let A := Sum.elim a (fun _ : Unit => a i)
  let B := Sum.elim b (fun _ : Unit => b i)
  let V := fromBlocks U 0 0 (1 : Matrix Unit Unit ℂ)
  let e : Option ι ≃ ι ⊕ Unit := Equiv.optionEquivSumPUnit ι
  obtain ⟨τ, hτ⟩ := h (A ∘ e) (B ∘ e)
  change ‖determinantValue (A ∘ e) (B ∘ e) (V.submatrix e e)‖ ≤ _ at hτ
  rw [determinantValue_reindex] at hτ
  have hdet : determinantValue A B V = determinantValue a b U * (a i + b i) :=
    determinantValue_scalar_padding a b U (a i) (b i)
  rw [hdet, norm_mul] at hτ
  let w (r s : ι) := ‖a r + b s‖
  have hw (σ : Equiv.Perm ι) : ‖matchingProduct a b σ‖ = ∏ j, w (σ j) j :=
    norm_prod _ _
  have hdiag : 0 < ∏ j, w j j := (hw (Equiv.refl ι)) ▸ hpos
  have hi : 0 < w i i := lt_of_le_of_ne (norm_nonneg _) (Ne.symm
    ((Finset.prod_ne_zero_iff.mp hdiag.ne') i (Finset.mem_univ i)))
  have hcost (p : Equiv.Perm ι) : (∏ j, w (p j) j) ≤ ∏ j, w j j := by
    simpa only [hw, Equiv.refl_apply] using hmax p
  have hA (j : Option ι) : A (e j) = a (j.getD i) := by cases j <;> rfl
  have hB (j : Option ι) : B (e j) = b (j.getD i) := by cases j <;> rfl
  have hnew : ‖matchingProduct (A ∘ e) (B ∘ e) τ‖ =
      ∏ j, w ((τ j).getD i) (j.getD i) := by
    simp only [matchingProduct, norm_prod, Function.comp_apply, hA, hB, w]
  rw [hnew] at hτ
  have hbound := hτ.trans (duplicated_assignment_le i w (fun _ _ => norm_nonneg _) hdiag hcost τ)
  rw [mul_comm (w i i)] at hbound
  rw [hw]
  exact le_of_mul_le_mul_right hbound hi

/-- To prove the modulus bound for a mixer, it suffices to prove it for the
scalar padding of each row permutation of that mixer, with arbitrary spectra. -/
theorem modulus_bound_of_scalar_padding [Nonempty ι] (a b : ι → ℂ)
    (U : Matrix ι ι ℂ) (hU : IsUnitary U)
    (h : let e := Equiv.optionEquivSumPUnit ι
      ∀ σ : Equiv.Perm ι, ∀ A B : Option ι → ℂ, ∃ τ : Equiv.Perm (Option ι),
        ‖determinantValue A B
          ((fromBlocks (U.submatrix σ (Equiv.refl ι)) 0 0
            (1 : Matrix Unit Unit ℂ)).submatrix e e)‖ ≤ ‖matchingProduct A B τ‖) :
    ∃ σ : Equiv.Perm ι, ‖determinantValue a b U‖ ≤ ‖matchingProduct a b σ‖ := by
  classical
  obtain ⟨σ, hσ⟩ := exists_matching_norm_max a b
  refine ⟨σ, ?_⟩
  by_cases hp : 0 < ‖matchingProduct a b σ‖
  · let e := Equiv.refl ι
    have hbest (τ : Equiv.Perm ι) : ‖matchingProduct (a ∘ σ) b τ‖ ≤
        ‖matchingProduct (a ∘ σ) b (Equiv.refl ι)‖ := hσ (τ.trans σ)
    have hv := modulus_at_maximizing_identity (a ∘ σ) (b ∘ e) (U.submatrix σ e)
      (Classical.choice (inferInstance : Nonempty ι)) (h σ) hbest hp
    rwa [determinantValue_reindex] at hv
  · have hz (τ : Equiv.Perm ι) : matchingProduct a b τ = 0 :=
      norm_eq_zero.mp (le_antisymm ((hσ τ).trans (le_of_not_gt hp)) (norm_nonneg _))
    rw [← signed_determinant a b U hU]
    simp only [hz, mul_zero, Finset.sum_const_zero, norm_zero, le_refl]

/-- If the modulus bound holds after adding one label, it holds before the addition. -/
theorem modulusConjecture_of_option [Nonempty ι] (h : ModulusConjecture (Option ι)) :
    ModulusConjecture ι := by
  intro a b U hU
  apply modulus_bound_of_scalar_padding a b U hU
  dsimp only
  intro σ A B
  let e := Equiv.optionEquivSumPUnit ι
  have hV := unitary_directSum (unitary_reindex σ (Equiv.refl ι) hU) (isUnitary_one (ι := Unit))
  exact h A B _ (unitary_reindex e e hV)

/-- In every order, a proof of the modulus bound implies the bound at the preceding order. -/
theorem modulusConjecture_of_succ (n : ℕ) (h : ModulusConjecture (Fin (n + 1))) :
    ModulusConjecture (Fin n) := by
  cases n with
  | zero => exact modulusConjecture_of_conjecture conjecture_zero
  | succ n => exact modulusConjecture_of_option (modulusConjecture_reindex (finSuccEquiv _) h)

theorem modulusConjecture_of_le {m n : ℕ} (h : m ≤ n) :
    ModulusConjecture (Fin n) → ModulusConjecture (Fin m) := by
  induction h with
  | refl => exact id
  | step _ ih => exact fun hn => ih (modulusConjecture_of_succ _ hn)

/-- Testing the modulus bound on an unbounded set of orders suffices for all orders. -/
theorem modulusConjecture_iff_on_unbounded_orders (S : Set ℕ)
    (hS : ∀ m, ∃ n ∈ S, m ≤ n) :
    (∀ m, ModulusConjecture (Fin m)) ↔ ∀ n ∈ S, ModulusConjecture (Fin n) := by
  constructor
  · exact fun h n _ => h n
  · intro h m
    obtain ⟨n, hn, hmn⟩ := hS m
    exact modulusConjecture_of_le hmn (h n hn)

/-- Convex-hull inclusion on an unbounded set of orders implies the modulus bound at every order. -/
theorem modulusConjecture_of_unbounded_conjecture (S : Set ℕ)
    (hS : ∀ m, ∃ n ∈ S, m ≤ n) (h : ∀ n ∈ S, Conjecture (Fin n)) :
    ∀ m, ModulusConjecture (Fin m) :=
  (modulusConjecture_iff_on_unbounded_orders S hS).mpr
    (fun n hn => modulusConjecture_of_conjecture (h n hn))

end

end MOC
