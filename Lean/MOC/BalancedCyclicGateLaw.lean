import MOC.CyclicSwitchMinor

/-! Two layers of balanced complex gates on a cycle have one common minor law. -/

open BigOperators Finset Matrix

namespace MOC

noncomputable section

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- The relative interference coefficient in the balanced cyclic law. -/
def cyclicGateParityCoefficient (s : Equiv.Perm κ) (L R : κ → Matrix Bool Bool ℂ) : ℝ :=
  cyclicGateInterference s L R / (1 / 2 : ℝ) ^ Fintype.card (κ ⊕ κ)

private theorem cyclic_parity_coefficient_bound (s : Equiv.Perm κ)
    (L R : κ → Matrix Bool Bool ℂ) (hL : ∀ k, BalancedGate (L k)) (hR : ∀ k, BalancedGate (R k)) :
    |cyclicGateParityCoefficient s L R| ≤ 1 := by
  have hd : 0 < (1 / 2 : ℝ) ^ Fintype.card (κ ⊕ κ) := by positivity
  rw [cyclicGateParityCoefficient, abs_div, abs_of_pos hd, div_le_one hd, Fintype.card_sum]
  exact cyclicGateInterference_bound s L R hL hR

omit [DecidableEq κ] in
private theorem switchParity_sum (x : κ ⊕ κ → Bool) :
    switchParity x = switchParity (x ∘ Sum.inl) * switchParity (x ∘ Sum.inr) := by
  unfold switchParity
  rw [Fintype.prod_sum_type]
  rfl

/-- The parity-corrected distribution gives all squared minors of the product
of two balanced layers on an alternating cycle. -/
theorem balanced_cyclic_gate_minor_law (s : Equiv.Perm κ) (hs : TraversesAllIndices s)
    (hne : s ≠ 1) (L R : κ → Matrix Bool Bool ℂ)
    (hL : ∀ k, BalancedGate (L k)) (hR : ∀ k, BalancedGate (R k)) :
    let w := cyclicSwitchWeight (κ := κ ⊕ κ) (cyclicGateParityCoefficient s L R)
    (∀ x, 0 ≤ w x) ∧ (∑ x, w x) = 1 ∧
      ∀ I J : Finset (κ × Bool), subsetMinorSq (cyclicGateMixer s L R) I J =
        ∑ x ∈ univ.filter (fun x => J.map
          (twoLayerSwitch (Equiv.refl _) (cyclicRightChart s) x).toEmbedding = I), w x := by
  classical
  haveI : Nonempty κ := by
    by_contra h
    apply hne
    ext k
    exact False.elim (h ⟨k⟩)
  let c := cyclicGateParityCoefficient s L R
  refine ⟨cyclicSwitchWeight_nonneg c
    (cyclic_parity_coefficient_bound s L R hL hR), sum_cyclicSwitchWeight c, ?_⟩
  intro I J
  let eL : κ × Bool ≃ κ × Bool := Equiv.refl _
  let eR := cyclicRightChart s
  let E := univ.filter (fun x => J.map (twoLayerSwitch eL eR x).toEmbedding = I)
  let U := cyclicGateMixer s L R
  let t := cyclicGateInterference s L R
  let d := (1 / 2 : ℝ) ^ Fintype.card (κ ⊕ κ)
  have hd : ((2 : ℝ) ^ Fintype.card (κ ⊕ κ))⁻¹ = d := by
    change _ = (1 / 2 : ℝ) ^ Fintype.card (κ ⊕ κ)
    rw [one_div, inv_pow]
  have hcd : c * d = t := div_mul_cancel₀ t (by positivity)
  have hU : IsUnitary U :=
    blockGateMatrix_mul_unitary eL eR L R (fun k => (hL k).1) (fun k => (hR k).1)
  change subsetMinorSq U I J = ∑ x ∈ E, cyclicSwitchWeight c x
  rw [sum_cyclicSwitchWeight_event, div_eq_mul_inv, hd]
  by_cases hT : BlockTransversal eL I ∧ BlockTransversal eR J
  · obtain ⟨hI,hJ⟩ := hT
    let x := cyclicSwitchToFalse s I J
    have he : E = {x, fun z => !(x z)} :=
      cyclic_switch_event_eq_pair s hs I J hI hJ x (cyclicSwitchToFalse_event s I J hI hJ)
    have hne' : x ≠ fun z => !(x z) := by
      intro hh
      obtain ⟨k⟩ := ‹Nonempty κ›
      have hh' := congrFun hh (Sum.inl k)
      cases hk : x (Sum.inl k) <;> simp [hk] at hh'
    have hE : E.card = 2 := by rw [he, Finset.card_pair hne']
    have hEven : Even (Fintype.card (κ ⊕ κ)) :=
      ⟨Fintype.card κ, by rw [Fintype.card_sum]⟩
    have hpar : (∑ y ∈ E, switchParity y) = 2 * switchParity x := by
      rw [he, sum_switchParity_pair x hEven]
    have hb : subsetMinorSq U I J = 2 * d + 2 * switchParity x * t := by
      rw [subsetMinorSq_eq_normSq_det_submatrix U hU I J
        (blockTransversalEquiv eL I hI) (blockTransversalEquiv eR J hJ)]
      change Complex.normSq
        ((blockGateMatrix (Equiv.refl _) L * blockGateMatrix (cyclicRightChart s) R).submatrix
          (fun k => (k, (x ∘ Sum.inl) k))
          (fun k => cyclicRightChart s (k, (x ∘ Sum.inr) k))).det = _
      rw [cyclicSwitchMatrix_transverse_normSq s hs hne L R hL hR
        (x ∘ Sum.inl) (x ∘ Sum.inr), switchParity_sum x]
      simp only [d, t, Fintype.card_sum]
      ring
    rw [hb, hpar, hE, Nat.cast_ofNat]
    calc
      2 * d + 2 * switchParity x * t = 2 * d + (2 * switchParity x) * (c * d) := by rw [hcd]
      _ = _ := by ring
  · have hn : ¬ BlockTransversal eL I ∨ ¬ BlockTransversal eR J := by tauto
    have hpar : (∑ y ∈ E, switchParity y) = 0 :=
      twoLayerSwitch_parity_eq_zero_of_not_transversal eL eR I J hn
    have hb : subsetMinorSq U I J = ∑ _x ∈ E, d := by
      simpa only [d, Fintype.card_sum] using cyclic_nontransversal_uniform_law s hs L R hL hR I J hn
    rw [hb, hpar, mul_zero, add_zero, Finset.sum_const, nsmul_eq_mul]

/-- Determinant inclusion for any spectra and a balanced alternating-cycle mixer. -/
theorem holds_balanced_cyclic_gate_mixer (s : Equiv.Perm κ) (hs : TraversesAllIndices s)
    (hne : s ≠ 1) (L R : κ → Matrix Bool Bool ℂ)
    (hL : ∀ k, BalancedGate (L k)) (hR : ∀ k, BalancedGate (R k))
    (a b : κ × Bool → ℂ) : Holds a b (cyclicGateMixer s L R) := by
  obtain ⟨hw, hsum, hm⟩ := balanced_cyclic_gate_minor_law s hs hne L R hL hR
  exact holds_of_indexed_minor_law a b (cyclicGateMixer s L R)
    (blockGateMatrix_mul_unitary _ _ L R (fun k => (hL k).1) (fun k => (hR k).1))
    (twoLayerSwitch (Equiv.refl _) (cyclicRightChart s))
    (cyclicSwitchWeight (cyclicGateParityCoefficient s L R)) hw hsum hm

end

end MOC
