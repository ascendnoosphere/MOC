import MOC.ReducedTwoFrame
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! The reciprocal matching polynomials lie in the multiaffine harmonic
space after reversing the signs of the right variables. Compare Filmus and
Mossel (DOI: 10.1007/s00440-019-00900-w) for the full harmonic space;
this module proves the specific lowering identity directly. -/

open BigOperators MvPolynomial

namespace MOC

noncomputable section

variable {ρ σ κ : Type*} [Fintype κ]

/-- Polynomial for a k-edge partial matching, with right signs reversed. -/
def partialFrameHarmonicPolynomial (p : (κ ↪ ρ) × (κ ↪ σ)) :
    MvPolynomial (ρ ⊕ σ) ℂ :=
  ∏ j, (X (Sum.inl (p.1 j)) - X (Sum.inr (p.2 j)))

/-- The total lowering derivation vanishes identically on every
partial matching polynomial. No analytic or convex claim is used. -/
theorem partialFrameHarmonicPolynomial_lowering_zero (p : (κ ↪ ρ) × (κ ↪ σ)) :
    MvPolynomial.mkDerivation ℂ (fun _ : ρ ⊕ σ => (1 : MvPolynomial (ρ ⊕ σ) ℂ))
      (partialFrameHarmonicPolynomial p) = 0 := by
  classical
  let D := MvPolynomial.mkDerivation ℂ (fun _ : ρ ⊕ σ => (1 : MvPolynomial (ρ ⊕ σ) ℂ))
  change D (∏ j, (X (Sum.inl (p.1 j)) - X (Sum.inr (p.2 j)))) = 0
  have hfactor (j : κ) : D (X (Sum.inl (p.1 j)) - X (Sum.inr (p.2 j))) = 0 := by
    simp [D, MvPolynomial.mkDerivation_X]
  have h (s : Finset κ) :
      D (∏ j ∈ s, (X (Sum.inl (p.1 j)) - X (Sum.inr (p.2 j)))) = 0 := by
    induction s using Finset.induction_on with
    | empty => simp
    | insert j s hj ih =>
      rw [Finset.prod_insert hj, Derivation.leibniz, hfactor, ih, smul_zero, smul_zero, zero_add]
  exact h Finset.univ

/-- Evaluating the harmonic polynomial with the reversed right variables
recovers the source reciprocal matching exactly. -/
theorem eval_partialFrameHarmonicPolynomial
    (x : ρ → ℂ) (y : σ → ℂ) (p : (κ ↪ ρ) × (κ ↪ σ)) :
    MvPolynomial.eval (Sum.elim x (fun j => -y j)) (partialFrameHarmonicPolynomial p) =
      partialFrameMatching x y p := by
  simp [partialFrameHarmonicPolynomial, partialFrameMatching]

/-- Boolean coordinate: the harmonic value vanishes unless the chosen
labels contain exactly one endpoint of every paired edge. For a valid
selector it is the sign dictated by the number chosen on the right. -/
theorem eval_partialFrameHarmonicPolynomial_boolean
    (p : (κ ↪ ρ) × (κ ↪ σ)) (I : Finset ρ) (J : Finset σ)
    [DecidableEq ρ] [DecidableEq σ] :
    MvPolynomial.eval
        (Sum.elim (fun i => if i ∈ I then (1 : ℂ) else 0)
          (fun j => if j ∈ J then (1 : ℂ) else 0))
        (partialFrameHarmonicPolynomial p) =
      if ∀ t, p.1 t ∈ I ↔ p.2 t ∉ J then
        ∏ t, if p.2 t ∈ J then (-1 : ℂ) else 1
      else 0 := by
  classical
  simp only [partialFrameHarmonicPolynomial, map_prod, map_sub, MvPolynomial.eval_X,
    Sum.elim_inl, Sum.elim_inr]
  split_ifs with h
  · apply Finset.prod_congr rfl
    intro t _
    by_cases ht : p.2 t ∈ J
    · have hl : p.1 t ∉ I := fun e => (h t).mp e ht
      simp [hl, ht]
    · have hl : p.1 t ∈ I := (h t).mpr ht
      simp [hl, ht]
  · obtain ⟨t, ht⟩ := not_forall.mp h
    apply Finset.prod_eq_zero (Finset.mem_univ t)
    by_cases hl : p.1 t ∈ I <;> by_cases hr : p.2 t ∈ J <;> simp_all

end

end MOC
