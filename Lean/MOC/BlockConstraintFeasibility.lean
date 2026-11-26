import MOC.SpectralMinorDecomposition
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Sigma

/-! Feasibility of subset-image constraints on distinct blocks of a finite direct sum. -/

open BigOperators

namespace MOC

noncomputable section

variable {B : Type*} [Fintype B] [DecidableEq B]
variable {X : B → Type*} [∀ k, Fintype (X k)]

/-- A product of finite probability laws gives each one-block observable its local mean. -/
theorem blockProductLaw_expectation (w : ∀ k, X k → ℝ) (hmass : ∀ k, ∑ y, w k y = 1)
    (k : B) (F : X k → ℝ) :
    (∑ x : ∀ j, X j, (∏ j, w j (x j)) * F (x k)) = ∑ y, w k y * F y := by
  classical
  let g : ∀ j, X j → ℝ := Function.update (fun j (_ : X j) => (1 : ℝ)) k F
  have hgk : g k = F := Function.update_self _ _ _
  have hgj {j : B} (hj : j ≠ k) (y : X j) : g j y = 1 := by
    simp only [g, Function.update_of_ne hj]
  have hfactor (x : ∀ j, X j) : (∏ j, g j (x j)) = F (x k) := calc
    (∏ j, g j (x j)) = g k (x k) := Finset.prod_eq_single k
      (fun j _ hj => hgj hj _) (fun h => (h (Finset.mem_univ k)).elim)
    _ = F (x k) := congrFun hgk _
  have hslot (j : B) (hj : j ≠ k) : (∑ y, w j y * g j y) = 1 := by
    simpa only [hgj hj, mul_one] using hmass j
  calc
    (∑ x : ∀ j, X j, (∏ j, w j (x j)) * F (x k)) =
        ∑ x : ∀ j, X j, ∏ j, (w j (x j) * g j (x j)) := by
          apply Finset.sum_congr rfl
          intro x _
          rw [Finset.prod_mul_distrib, hfactor]
    _ = ∏ j, ∑ y, w j y * g j y := (Fintype.prod_sum (fun j y => w j y * g j y)).symm
    _ = ∑ y, w k y * g k y := Finset.prod_eq_single k
      (fun j _ hj => hslot j hj) (fun h => (h (Finset.mem_univ k)).elim)
    _ = ∑ y, w k y * F y := by rw [hgk]

/-- For finite outcome spaces, one joint law realizes the selected one-block expectations
if and only if each block has a law realizing its own selected expectations. -/
theorem block_event_feasible_iff {C : B → Type*} (selected : ∀ k, Finset (C k))
    (event : ∀ k, C k → X k → ℝ) (target : ∀ k, C k → ℝ) :
    (∃ W : (∀ k, X k) → ℝ, (∀ x, 0 ≤ W x) ∧ (∑ x, W x) = 1 ∧
      ∀ k c ∈ selected k, (∑ x, W x * event k c (x k)) = target k c) ↔
    ∀ k, ∃ w : X k → ℝ, (∀ y, 0 ≤ w y) ∧ (∑ y, w y) = 1 ∧
      ∀ c ∈ selected k, (∑ y, w y * event k c y) = target k c := by
  classical
  constructor
  · rintro ⟨W, hW, hmass, htarget⟩ k
    let w (y : X k) := ∑ x : ∀ j, X j, if x k = y then W x else 0
    have hpush (F : X k → ℝ) : (∑ y, w y * F y) = ∑ x, W x * F (x k) := by
      simp only [w, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x _
      simp [ite_mul]
    refine ⟨w, fun y => Finset.sum_nonneg (fun x _ => ?_), ?_, fun c hc => ?_⟩
    · by_cases h : x k = y
      · simpa only [if_pos h] using hW x
      · simp only [if_neg h, le_refl]
    · have h := hpush (fun _ => 1)
      simpa only [mul_one, hmass] using h
    · exact (hpush (event k c)).trans (htarget k c hc)
  · intro h
    choose w hw hmass htarget using h
    refine ⟨fun x => ∏ j, w j (x j), fun x => Finset.prod_nonneg (fun j _ => hw j _), ?_, ?_⟩
    · rw [← Fintype.prod_sum w]
      simp only [hmass, Finset.prod_const_one]
    · intro k c hc
      exact (blockProductLaw_expectation w hmass k (event k c)).trans (htarget k c hc)

variable {ι : B → Type*} [∀ k, DecidableEq (ι k)]

/-- A block-preserving permutation maps one embedded subset to another exactly when
its component in that block maps the original subsets. -/
theorem subsetImageEvent_sigmaCongrRight (ρ : ∀ k, Equiv.Perm (ι k)) (k : B)
    (I J : Finset (ι k)) :
    subsetImageEvent (I.map (Function.Embedding.sigmaMk k)) (J.map (Function.Embedding.sigmaMk k))
      (Equiv.sigmaCongrRight ρ) = subsetImageEvent I J (ρ k) := by
  have hmap :
      (J.map (Function.Embedding.sigmaMk k)).map (Equiv.sigmaCongrRight ρ).toEmbedding =
        (J.map (ρ k).toEmbedding).map (Function.Embedding.sigmaMk k) := by
    simp only [Finset.map_map] <;> rfl
  simp only [subsetImageEvent, hmap, Finset.map_inj]

/-- For permutations preserving the blocks of a direct sum, a family of selected
subset-image constraints is feasible exactly when its restriction to each block is feasible.
The subsets in these constraints can have any cardinality. -/
theorem block_subsetImage_feasible_iff [∀ k, Fintype (ι k)] {C : B → Type*}
    (selected : ∀ k, Finset (C k)) (I J : ∀ k, C k → Finset (ι k)) (target : ∀ k, C k → ℝ) :
    (∃ W : (∀ k, Equiv.Perm (ι k)) → ℝ, (∀ ρ, 0 ≤ W ρ) ∧ (∑ ρ, W ρ) = 1 ∧
      ∀ k c ∈ selected k, (∑ ρ, W ρ * subsetImageEvent
        ((I k c).map (Function.Embedding.sigmaMk k)) ((J k c).map (Function.Embedding.sigmaMk k))
        (Equiv.sigmaCongrRight ρ)) = target k c) ↔
    ∀ k, ∃ w : Equiv.Perm (ι k) → ℝ, (∀ σ, 0 ≤ w σ) ∧ (∑ σ, w σ) = 1 ∧
      ∀ c ∈ selected k, (∑ σ, w σ * subsetImageEvent (I k c) (J k c) σ) = target k c := by
  simp only [subsetImageEvent_sigmaCongrRight]
  exact block_event_feasible_iff selected (fun k c => subsetImageEvent (I k c) (J k c)) target

end

end MOC
