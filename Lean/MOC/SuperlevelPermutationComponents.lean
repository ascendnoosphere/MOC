import MOC.StrongSupport
import Mathlib.Topology.Connected.PathConnected
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Quotient.Basic

/-! The path-component condition for determinant superlevel sets implies
the matching support inequality in every finite order. -/

open BigOperators Matrix

namespace MOC

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def determinantSuperlevel (a b : ι → ℂ) (η : ℂ) (t : ℝ) : Set (Matrix ι ι ℂ) :=
  {U | IsUnitary U ∧ t ≤ (η * determinantValue a b U).re}

/-- A permutation in the component of the current mixer gives the required support. -/
theorem holds_of_permutation_in_each_superlevel_component (a b : ι → ℂ)
    (h : ∀ η t U, U ∈ determinantSuperlevel a b η t →
      ∃ p : Equiv.Perm ι, p.permMatrix ℂ ∈ pathComponentIn U (determinantSuperlevel a b η t))
    (U : Matrix ι ι ℂ) (hU : IsUnitary U) : Holds a b U := by
  apply (holds_iff_directional a b U).mpr
  intro η
  let t := (η * determinantValue a b U).re
  obtain ⟨p, hp⟩ := h η t U ⟨hU, le_rfl⟩
  have hm : p.permMatrix ℂ ∈ determinantSuperlevel a b η t := pathComponentIn_subset hp
  have he : determinantValue a b (p.permMatrix ℂ) = matchingProduct a b p.symm := by
    rw [determinantValue, permMatrix_conjugates, Matrix.submatrix_diagonal_equiv,
      Matrix.diagonal_add, Matrix.det_diagonal, matchingProduct_inverse] <;> rfl
  refine ⟨p.symm, ?_⟩
  simpa only [← he] using hm.2

/-- Degree-zero relative singular boundaries consist of endpoint differences
of paths and points removed by the relative quotient. Every zero-chain is a cycle. -/
def relativeZeroRelations {X : Type*} [TopologicalSpace X] (V : Set X) :
    Submodule ℤ (X →₀ ℤ) :=
  Submodule.span ℤ {u | (∃ x y : X, Joined x y ∧
    u = Finsupp.single y 1 - Finsupp.single x 1) ∨
    (∃ y ∈ V, u = Finsupp.single y 1)}

/-- The integral relative zero-chain quotient vanishes exactly when the
marked set meets every path component. -/
theorem relativeZeroQuotient_trivial_iff {X : Type*} [TopologicalSpace X] (V : Set X) :
    Subsingleton ((X →₀ ℤ) ⧸ relativeZeroRelations V) ↔
      ∀ x : X, ∃ y ∈ V, Joined x y := by
  classical
  rw [Submodule.subsingleton_quotient_iff_eq_top]
  constructor
  · intro h x
    by_contra hmiss
    let L : (X →₀ ℤ) →ₗ[ℤ] ℤ :=
      Finsupp.linearCombination ℤ (fun y : X => if Joined x y then (1 : ℤ) else 0)
    have hker : relativeZeroRelations V ≤ LinearMap.ker L := by
      apply Submodule.span_le.mpr
      intro u hu
      rcases hu with ⟨v,z,hvz,rfl⟩ | ⟨v,hv,rfl⟩
      · have he : Joined x z ↔ Joined x v := ⟨fun hz => hz.trans hvz.symm, fun hx => hx.trans hvz⟩
        change L _ = 0
        simp [L, he]
      · have hvx : ¬ Joined x v := fun hj => hmiss ⟨v,hv,hj⟩
        change L _ = 0
        simp [L, hvx]
    have hx : Finsupp.single x (1 : ℤ) ∈ relativeZeroRelations V := by rw [h]; trivial
    have hbad := hker hx
    change L (Finsupp.single x 1) = 0 at hbad
    simp [L, Joined.refl] at hbad
  · intro hall
    apply eq_top_iff.mpr
    intro u _
    induction u using Finsupp.induction_linear with
    | zero => exact Submodule.zero_mem _
    | add _ _ h₁ h₂ => exact Submodule.add_mem _ h₁ h₂
    | single x a =>
      obtain ⟨y,hy,hxy⟩ := hall x
      have h₁ : Finsupp.single x 1 - Finsupp.single y 1 ∈ relativeZeroRelations V :=
        Submodule.subset_span (Or.inl ⟨y,x,hxy.symm,rfl⟩)
      have h₂ : Finsupp.single y 1 ∈ relativeZeroRelations V :=
        Submodule.subset_span (Or.inr ⟨y,hy,rfl⟩)
      have h₃ : Finsupp.single x (1 : ℤ) ∈ relativeZeroRelations V := by
        simpa using Submodule.add_mem _ h₁ h₂
      simpa only [Finsupp.smul_single_one] using (relativeZeroRelations V).smul_mem a h₃

/-- The relative zero-chain quotient condition on every closed determinant
superlevel implies the Marcus–de Oliveira inclusion for these spectra. -/
theorem holds_of_relative_superlevel_zero_quotient (a b : ι → ℂ)
    (h : ∀ (η : ℂ) (t : ℝ),
      let X := determinantSuperlevel a b η t
      let V : Set X := {W | ∃ p : Equiv.Perm ι, W.val = p.permMatrix ℂ}
      Subsingleton ((X →₀ ℤ) ⧸ relativeZeroRelations V))
    (U : Matrix ι ι ℂ) (hU : IsUnitary U) : Holds a b U := by
  apply (holds_iff_directional a b U).mpr
  intro η
  let t := (η * determinantValue a b U).re
  let X := determinantSuperlevel a b η t
  let V : Set X := {W | ∃ p : Equiv.Perm ι, W.val = p.permMatrix ℂ}
  obtain ⟨W, ⟨p,hp⟩, _⟩ := (relativeZeroQuotient_trivial_iff V).mp (h η t) ⟨U, hU, le_rfl⟩
  have he : determinantValue a b (p.permMatrix ℂ) = matchingProduct a b p.symm := by
    rw [determinantValue, permMatrix_conjugates, Matrix.submatrix_diagonal_equiv,
      Matrix.diagonal_add, Matrix.det_diagonal, matchingProduct_inverse] <;> rfl
  refine ⟨p.symm, ?_⟩
  have hs : t ≤ (η * determinantValue a b W.val).re := W.property.2
  rwa [hp, he] at hs

end

end MOC
