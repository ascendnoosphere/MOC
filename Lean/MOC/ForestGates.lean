import MOC.OneBridge
import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-! A forest of two-coordinate gates has a common permutation law. -/

open BigOperators Matrix

namespace MOC

noncomputable section

/-- A gate that applies a normalized determinant-one matrix to two distinct rows. -/
structure TwoCoordinateGate (ι : Type*) where
  p : ι
  q : ι
  different : p ≠ q
  c : ℂ
  s : ℂ
  normalized : Complex.normSq c + Complex.normSq s = 1

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Apply the gates from the end of the list to the beginning. -/
def forestGateMixer : List (TwoCoordinateGate ι) → Matrix ι ι ℂ
  | [] => 1
  | g :: gs => bridgeRows (forestGateMixer gs) g.p g.q g.c g.s

/-- The product of normalized two-coordinate gates is unitary. -/
theorem forestGateMixer_unitary (gs : List (TwoCoordinateGate ι)) :
    IsUnitary (forestGateMixer gs) := by
  induction gs with
  | nil => exact isUnitary_one
  | cons g gs ih => exact bridgeRows_unitary _ ih g.different g.normalized

omit [Fintype ι] in
private theorem forestGateMixer_respects_cut (gs : List (TwoCoordinateGate ι))
    (side : ι → Bool) (hside : ∀ g ∈ gs, side g.p = side g.q) :
    ∀ i j, side i ≠ side j → forestGateMixer gs i j = 0 := by
  induction gs with
  | nil =>
    intro i j hij
    exact Matrix.one_apply_ne (fun h => hij (congrArg side h))
  | cons g gs ih =>
    have hg := hside g (List.mem_cons_self)
    have htail := ih (fun f hf => hside f (List.mem_cons_of_mem _ hf))
    intro i j hij
    change bridgeRows (forestGateMixer gs) g.p g.q g.c g.s i j = 0
    by_cases hp : i = g.p
    · subst i
      have hqj : side g.q ≠ side j := by rwa [← hg]
      simp only [bridgeRows, if_true, htail _ _ hij, htail _ _ hqj, mul_zero, add_zero]
    · by_cases hq : i = g.q
      · subst i
        have hpj : side g.p ≠ side j := by rwa [hg]
        simp only [bridgeRows, if_neg g.different.symm, if_true, htail _ _ hpj,
          htail _ _ hij, mul_zero, add_zero]
      · rw [bridgeRows, if_neg hp, if_neg hq, htail _ _ hij]

omit [Fintype ι] [DecidableEq ι] in
private theorem twoCoordinateGate_forest_cut (G : SimpleGraph ι) (hG : G.IsAcyclic)
    (g : TwoCoordinateGate ι) (h : G.Adj g.p g.q) :
    ∃ side : ι → Bool, side g.p ≠ side g.q ∧
      ∀ p q, G.Adj p q → s(p, q) ≠ s(g.p, g.q) → side p = side q := by
  classical
  let H := G \ SimpleGraph.fromEdgeSet {s(g.p, g.q)}
  let side (i : ι) := decide (H.Reachable g.p i)
  have hbridge := SimpleGraph.isAcyclic_iff_forall_adj_isBridge.mp hG h
  have hn : ¬ H.Reachable g.p g.q := (SimpleGraph.isBridge_iff.mp hbridge).2
  refine ⟨side, ?_, ?_⟩
  · simp [side, SimpleGraph.Reachable.refl, hn]
  · intro p q hpq hne
    have hadj : H.Adj p q := (SimpleGraph.sdiff_adj _ _ _ _).2
      ⟨hpq, fun h' => hne ((SimpleGraph.fromEdgeSet_adj _).mp h').1⟩
    have hstep : H.Reachable p q := hadj.reachable
    have hequiv : H.Reachable g.p p ↔ H.Reachable g.p q :=
      ⟨fun h₁ => h₁.trans hstep, fun h₁ => h₁.trans hstep.symm⟩
    simp only [side, hequiv]

private theorem forest_gate_weighted_step (a b : ι → ℂ) (τ : Equiv.Perm ι)
    (hτ : ∀ i, τ (τ i) = i) (w : Equiv.Perm ι → ℝ) (u v : ℝ) :
    weightedMatchingValue a b (fun σ => u * w σ + v * w (τ * σ)) =
      (u : ℂ) * weightedMatchingValue a b w +
      (v : ℂ) * weightedMatchingValue (a ∘ τ) b w := by
  have hreindex : ∑ σ : Equiv.Perm ι, (w (τ * σ) : ℂ) * matchingProduct a b σ =
      weightedMatchingValue (a ∘ τ) b w := by
    let f := fun σ : Equiv.Perm ι => (w σ : ℂ) * matchingProduct (a ∘ τ) b σ
    have hf := Equiv.sum_comp (Equiv.mulLeft τ) f
    have hmatch (σ : Equiv.Perm ι) :
        matchingProduct (a ∘ τ) b (τ * σ) = matchingProduct a b σ := by
      simp only [matchingProduct, Function.comp_apply, Equiv.Perm.mul_apply, hτ]
    change (∑ σ, (w (τ * σ) : ℂ) * matchingProduct (a ∘ τ) b (τ * σ)) =
      weightedMatchingValue (a ∘ τ) b w at hf
    simpa only [hmatch] using hf
  unfold weightedMatchingValue at *
  simp_rw [Complex.ofReal_add, Complex.ofReal_mul, add_mul, mul_assoc]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hreindex]

/-- Apply two-coordinate gates in any order on distinct edges of an acyclic
graph. One set of permutation weights gives the determinant for every pair
of spectra. -/
theorem forest_gate_common_weights (G : SimpleGraph ι) (hG : G.IsAcyclic)
    (gs : List (TwoCoordinateGate ι)) (hGates : ∀ g ∈ gs, G.Adj g.p g.q)
    (hDistinct : gs.Pairwise (fun g f => s(g.p, g.q) ≠ s(f.p, f.q))) :
    ∃ w : Equiv.Perm ι → ℝ, (∀ σ, 0 ≤ w σ) ∧ (∑ σ, w σ) = 1 ∧
      ∀ a b, determinantValue a b (forestGateMixer gs) = weightedMatchingValue a b w := by
  classical
  induction gs with
  | nil =>
    let w : Equiv.Perm ι → ℝ := fun σ => if σ = 1 then 1 else 0
    refine ⟨w, fun σ => by by_cases h : σ = 1 <;> simp [w, h], by simp [w], ?_⟩
    intro a b
    simp only [forestGateMixer, determinantValue, Matrix.one_mul, Matrix.conjTranspose_one,
      Matrix.mul_one, ← Matrix.diagonal_add, Matrix.det_diagonal, Pi.add_apply]
    simp [weightedMatchingValue, w, matchingProduct, apply_ite, ite_mul]
  | cons g gs ih =>
    obtain ⟨hd, hds⟩ := List.pairwise_cons.mp hDistinct
    obtain ⟨w, hw, hsum, hvalue⟩ := ih
      (fun f hf => hGates f (List.mem_cons_of_mem _ hf)) hds
    obtain ⟨side, hpq, hside⟩ := twoCoordinateGate_forest_cut G hG g
      (hGates g List.mem_cons_self)
    have hblock := forestGateMixer_respects_cut gs side
      (fun f hf => hside _ _ (hGates f (List.mem_cons_of_mem _ hf)) (hd f hf).symm)
    let u := Complex.normSq g.c
    let v := Complex.normSq g.s
    let τ := Equiv.swap g.p g.q
    have hτ (i : ι) : τ (τ i) = i := Equiv.swap_apply_self _ _ _
    refine ⟨fun σ => u * w σ + v * w (τ * σ), ?_, ?_, ?_⟩
    · intro σ
      exact add_nonneg (mul_nonneg (Complex.normSq_nonneg _) (hw σ))
        (mul_nonneg (Complex.normSq_nonneg _) (hw _))
    · have hr : ∑ σ, w (τ * σ) = ∑ σ, w σ := Equiv.sum_comp (Equiv.mulLeft τ) w
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hr, hsum, mul_one,
        mul_one]
      exact g.normalized
    · intro a b
      change determinantValue a b (bridgeRows (forestGateMixer gs) g.p g.q g.c g.s) = _
      rw [bridge_determinantValue a b _ (forestGateMixer_unitary gs) side hblock hpq g.normalized]
      change (u : ℂ) * determinantValue a b (forestGateMixer gs) +
        (v : ℂ) * determinantValue (a ∘ τ) b (forestGateMixer gs) = _
      rw [hvalue a b, hvalue (a ∘ τ) b, forest_gate_weighted_step a b τ hτ]

/-- A forest of two-coordinate gates obeys determinant inclusion in every order. -/
theorem holds_forest_gate_mixer (G : SimpleGraph ι) (hG : G.IsAcyclic)
    (gs : List (TwoCoordinateGate ι)) (hGates : ∀ g ∈ gs, G.Adj g.p g.q)
    (hDistinct : gs.Pairwise (fun g f => s(g.p, g.q) ≠ s(f.p, f.q)))
    (a b : ι → ℂ) : Holds a b (forestGateMixer gs) := by
  obtain ⟨w, hw, hsum, hvalue⟩ := forest_gate_common_weights G hG gs hGates hDistinct
  exact holds_of_weights w hw hsum (hvalue a b).symm

private theorem bridgeRows_one_mul (U : Matrix ι ι ℂ) {p q : ι} (hpq : p ≠ q) (c s : ℂ) :
    bridgeRows (1 : Matrix ι ι ℂ) p q c s * U = bridgeRows U p q c s := by
  ext i j : 1
  have hrow (l : ι) : (∑ k, (1 : Matrix ι ι ℂ) l k * U k j) = U l j := by
    rw [← Matrix.mul_apply, Matrix.one_mul]
  rw [Matrix.mul_apply]
  by_cases hi : i = p
  · subst i
    simp only [bridgeRows, if_true, add_mul, mul_assoc, Finset.sum_add_distrib,
      ← Finset.mul_sum, hrow]
  · by_cases hi' : i = q
    · subst i
      simp only [bridgeRows, if_neg hpq.symm, if_true, add_mul, mul_assoc,
        Finset.sum_add_distrib, ← Finset.mul_sum, hrow]
    · simp only [bridgeRows, if_neg hi, if_neg hi', hrow]

/-- The row operations give the ordered product of the embedded gate matrices. -/
theorem forestGateMixer_eq_prod (gs : List (TwoCoordinateGate ι)) :
    forestGateMixer gs =
      (gs.map fun g => bridgeRows (1 : Matrix ι ι ℂ) g.p g.q g.c g.s).prod := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    rw [forestGateMixer, List.map_cons, List.prod_cons, ← ih, bridgeRows_one_mul _ g.different]

end

end MOC
