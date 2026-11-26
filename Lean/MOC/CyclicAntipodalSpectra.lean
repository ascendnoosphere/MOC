import MOC.TwoLayerOrthogonalEndpoints

/-! Complementary switch assignments have nonnegative combined mass.
This gives determinant inclusion when both gate spectra have opposite
pair sums, with no restriction on the gate probabilities or phases. -/

open BigOperators Finset Matrix

namespace MOC

noncomputable section

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

private def complementSwitchEquiv (α : Type*) : (α → Bool) ≃ (α → Bool) where
  toFun x i := !(x i)
  invFun x i := !(x i)
  left_inv x := by funext i; exact Bool.not_not _
  right_inv x := by funext i; exact Bool.not_not _

/-- Give each assignment half the combined signed mass of it and its complement. -/
def cyclicPairedSwitchWeight (s : Equiv.Perm κ) (L R : κ → Matrix Bool Bool ℂ)
    (x : κ ⊕ κ → Bool) : ℝ :=
  (cyclicIndependentWeight L R x + cyclicIndependentWeight L R (fun z => !(x z))) / 2 +
    cyclicGateInterference s L R * switchParity x

/-- Each paired mass is half a squared absolute value. -/
theorem cyclicPairedSwitchWeight_nonneg (s : Equiv.Perm κ) (L R : κ → Matrix Bool Bool ℂ)
    (hL : ∀ k, IsUnitary (L k)) (hR : ∀ k, IsUnitary (R k))
    (x : κ ⊕ κ → Bool) : 0 ≤ cyclicPairedSwitchWeight s L R x := by
  let xl := x ∘ Sum.inl
  let xr := x ∘ Sum.inr
  have hsplit : Sum.elim xl xr = x := by funext z; cases z <;> rfl
  have hpar : switchParity x = switchParity xl * switchParity xr := by
    unfold switchParity
    rw [Fintype.prod_sum_type]
    rfl
  have hn : 0 ≤ Complex.normSq ((∏ l, L l (xl l) false * R l false (xr l)) +
      ((s.sign : ℤ) : ℂ) * ∏ l, L (s l) (xl (s l)) true * R l true (xr l)) :=
    Complex.normSq_nonneg _
  rw [cyclic_two_products_independent_normSq s L R hL hR, hsplit,
    mul_assoc (2 : ℝ), ← hpar] at hn
  unfold cyclicPairedSwitchWeight
  nlinarith only [hn]

/-- The paired masses form a probability law on every nonempty gate family. -/
theorem cyclicPairedSwitchWeight_sum (s : Equiv.Perm κ) (L R : κ → Matrix Bool Bool ℂ)
    (hL : ∀ k, IsUnitary (L k)) (hR : ∀ k, IsUnitary (R k)) (k₀ : κ) :
    ∑ x, cyclicPairedSwitchWeight s L R x = 1 := by
  have hpar : ∑ x : κ ⊕ κ → Bool, switchParity x = 0 :=
    sum_switchParity_eq_zero (Sum.inl k₀) univ (fun _ => by simp)
  have hcomp : ∑ x : κ ⊕ κ → Bool,
      cyclicIndependentWeight L R (fun z => !(x z)) = 1 :=
    (Equiv.sum_comp (complementSwitchEquiv (κ ⊕ κ)) (cyclicIndependentWeight L R)).trans
      (cyclicIndependentWeight_sum L R hL hR)
  unfold cyclicPairedSwitchWeight
  rw [Finset.sum_add_distrib, ← Finset.sum_div, Finset.sum_add_distrib,
    cyclicIndependentWeight_sum L R hL hR, hcomp, ← Finset.mul_sum, hpar]
  norm_num

/-- Complement symmetry of the matching values permits the positive paired law. -/
theorem cyclic_paired_switch_determinant (s : Equiv.Perm κ)
    (hs : TraversesAllIndices s) (hne : s ≠ 1) (L R : κ → Matrix Bool Bool ℂ)
    (hL : ∀ k, IsUnitary (L k)) (hR : ∀ k, IsUnitary (R k)) (a b : κ × Bool → ℂ)
    (hpair : ∀ x : κ ⊕ κ → Bool,
      matchingProduct a b (twoLayerSwitch (Equiv.refl _) (cyclicRightChart s) (fun z => !(x z))) =
        matchingProduct a b (twoLayerSwitch (Equiv.refl _) (cyclicRightChart s) x)) :
    (∑ x, (cyclicPairedSwitchWeight s L R x : ℂ) *
      matchingProduct a b (twoLayerSwitch (Equiv.refl _) (cyclicRightChart s) x)) =
        determinantValue a b (cyclicGateMixer s L R) := by
  let q (x : κ ⊕ κ → Bool) :=
    matchingProduct a b (twoLayerSwitch (Equiv.refl _) (cyclicRightChart s) x)
  have hq (x : κ ⊕ κ → Bool) : q (fun z => !(x z)) = q x := hpair x
  have hcomp : (∑ x : κ ⊕ κ → Bool,
      (cyclicIndependentWeight L R (fun z => !(x z)) : ℂ) * q x) =
      ∑ x : κ ⊕ κ → Bool, (cyclicIndependentWeight L R x : ℂ) * q x := by
    calc
      _ = ∑ x : κ ⊕ κ → Bool,
          (cyclicIndependentWeight L R (fun z => !(x z)) : ℂ) * q (fun z => !(x z)) := by
        apply Finset.sum_congr rfl
        intro x _
        rw [hq]
      _ = _ := Equiv.sum_comp (complementSwitchEquiv (κ ⊕ κ))
        (fun x => (cyclicIndependentWeight L R x : ℂ) * q x)
  have hcast (x : κ ⊕ κ → Bool) :
      (cyclicPairedSwitchWeight s L R x : ℂ) * q x =
        ((cyclicIndependentWeight L R x : ℂ) * q x +
          (cyclicIndependentWeight L R (fun z => !(x z)) : ℂ) * q x) / 2 +
        (cyclicGateInterference s L R : ℂ) * ((switchParity x : ℂ) * q x) := by
    simp only [cyclicPairedSwitchWeight, Complex.ofReal_add, Complex.ofReal_div,
      Complex.ofReal_mul, Complex.ofReal_ofNat]
    ring
  rw [cyclic_gate_determinant_eq_independent_add_interference s hs hne L R hL hR]
  change (∑ x, (cyclicPairedSwitchWeight s L R x : ℂ) * q x) =
    (∑ x, (cyclicIndependentWeight L R x : ℂ) * q x) +
      (cyclicGateInterference s L R : ℂ) * ∑ x, (switchParity x : ℂ) * q x
  simp_rw [hcast]
  rw [Finset.sum_add_distrib, ← Finset.sum_div, Finset.sum_add_distrib, hcomp,
    ← Finset.mul_sum]
  ring

/-- Matching values invariant under complementing every gate satisfy MOC at all biases. -/
theorem holds_cyclic_gate_of_complement_matching (s : Equiv.Perm κ)
    (hs : TraversesAllIndices s) (hne : s ≠ 1) (L R : κ → Matrix Bool Bool ℂ)
    (hL : ∀ k, IsUnitary (L k)) (hR : ∀ k, IsUnitary (R k)) (a b : κ × Bool → ℂ)
    (hpair : ∀ x : κ ⊕ κ → Bool,
      matchingProduct a b (twoLayerSwitch (Equiv.refl _) (cyclicRightChart s) (fun z => !(x z))) =
        matchingProduct a b (twoLayerSwitch (Equiv.refl _) (cyclicRightChart s) x)) :
    Holds a b (cyclicGateMixer s L R) := by
  classical
  have hk : Nonempty κ := by
    by_contra h
    haveI : IsEmpty κ := not_nonempty_iff.mp h
    exact hne (Equiv.ext fun k => isEmptyElim k)
  obtain ⟨k₀⟩ := hk
  unfold Holds
  refine mem_convexHull_of_exists_fintype (cyclicPairedSwitchWeight s L R)
    (fun x => matchingProduct a b (twoLayerSwitch (Equiv.refl _) (cyclicRightChart s) x))
    (cyclicPairedSwitchWeight_nonneg s L R hL hR)
    (cyclicPairedSwitchWeight_sum s L R hL hR k₀)
    (fun x => ⟨twoLayerSwitch (Equiv.refl _) (cyclicRightChart s) x, rfl⟩) ?_
  simpa only [Complex.real_smul] using cyclic_paired_switch_determinant s hs hne L R hL hR a b hpair

omit [Fintype κ] [DecidableEq κ] in
private theorem blockSwitch_complement_spectrum {ι : Type*} (e : κ × Bool ≃ ι)
    (v : ι → ℂ) (c : ℂ) (h : ∀ k, v (e (k, false)) + v (e (k, true)) = c)
    (x : κ → Bool) (j : ι) :
    v (blockSwitch e (fun k => !(x k)) j) = c - v (blockSwitch e x j) := by
  obtain ⟨⟨k, b⟩, rfl⟩ := e.surjective j
  cases hx : x k <;> cases b <;>
    simp only [blockSwitch_apply, hx, Bool.not_false, Bool.not_true, Bool.false_eq_true,
      if_false, if_true] <;> linear_combination h k

omit [Fintype κ] [DecidableEq κ] in
private theorem matchingProduct_twoLayerSwitch {ι : Type*} [Fintype ι] [DecidableEq ι]
    (eL eR : κ × Bool ≃ ι) (a b : ι → ℂ) (x : κ ⊕ κ → Bool) :
    matchingProduct a b (twoLayerSwitch eL eR x) =
      ∏ j, (a (blockSwitch eL (x ∘ Sum.inl) j) + b (blockSwitch eR (x ∘ Sum.inr) j)) := by
  let τ := blockSwitch eR (x ∘ Sum.inr)
  unfold matchingProduct
  rw [← Equiv.prod_comp τ.symm (fun j => a (twoLayerSwitch eL eR x j) + b j)]
  apply Finset.prod_congr rfl
  intro j _
  change a (blockSwitch eL (x ∘ Sum.inl) (τ (τ.symm j))) + b (τ.symm j) = _
  rw [τ.apply_symm_apply, show τ.symm = τ from blockSwitch_symm _ _]

/-- In every even cycle order, opposite pair sums in the two spectra give
inclusion for arbitrary unitary gates, probabilities, and phases. -/
theorem holds_cyclic_gate_of_antipodal_spectral_pairs (s : Equiv.Perm κ)
    (hs : TraversesAllIndices s) (hne : s ≠ 1) (L R : κ → Matrix Bool Bool ℂ)
    (hL : ∀ k, IsUnitary (L k)) (hR : ∀ k, IsUnitary (R k))
    (a b : κ × Bool → ℂ) (c : ℂ)
    (ha : ∀ k, a (k, false) + a (k, true) = c)
    (hb : ∀ k, b (cyclicRightChart s (k, false)) + b (cyclicRightChart s (k, true)) = -c) :
    Holds a b (cyclicGateMixer s L R) := by
  apply holds_cyclic_gate_of_complement_matching s hs hne L R hL hR a b
  intro x
  rw [matchingProduct_twoLayerSwitch, matchingProduct_twoLayerSwitch]
  have hterm (j : κ × Bool) :
      a (blockSwitch (Equiv.refl _) ((fun z => !(x z)) ∘ Sum.inl) j) +
        b (blockSwitch (cyclicRightChart s) ((fun z => !(x z)) ∘ Sum.inr) j) =
      -(a (blockSwitch (Equiv.refl _) (x ∘ Sum.inl) j) +
        b (blockSwitch (cyclicRightChart s) (x ∘ Sum.inr) j)) := by
    change a (blockSwitch (Equiv.refl _) (fun k => !(x (Sum.inl k))) j) +
      b (blockSwitch (cyclicRightChart s) (fun k => !(x (Sum.inr k))) j) = _
    rw [blockSwitch_complement_spectrum (Equiv.refl _) a c ha,
      blockSwitch_complement_spectrum (cyclicRightChart s) b (-c) hb]
    simp only [Function.comp_def]
    ring
  calc
    _ = ∏ j, -(a (blockSwitch (Equiv.refl _) (x ∘ Sum.inl) j) +
        b (blockSwitch (cyclicRightChart s) (x ∘ Sum.inr) j)) :=
      Finset.prod_congr rfl (fun j _ => hterm j)
    _ = _ := by
      simp only [Fintype.prod_prod_type, Fintype.prod_bool, neg_mul_neg]

end

end MOC
