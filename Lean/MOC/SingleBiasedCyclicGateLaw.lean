import MOC.BalancedCyclicGateLaw

/-! One biased gate on an alternating cycle preserves the common minor law. -/

open BigOperators Finset Matrix

namespace MOC

noncomputable section

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

private theorem exists_free_cyclic_switch
    (eL eR : κ × Bool ≃ κ × Bool) (I J : Finset (κ × Bool)) (hc : I.card = J.card)
    (hn : ¬ BlockTransversal eL I ∨ ¬ BlockTransversal eR J) (g : κ ⊕ κ) :
    ∃ z ≠ g, ∀ x, J.map (twoLayerSwitch eL eR (toggleSwitch z x)).toEmbedding = I ↔
      J.map (twoLayerSwitch eL eR x).toEmbedding = I := by
  classical
  let D : κ ⊕ κ → ℤ := Sum.elim (fun k => blockOccupancy eL I k - 1)
    (fun k => 1 - blockOccupancy eR J k)
  have hsum : ∑ z, D z = 0 := by
    rw [Fintype.sum_sum_type]
    change (∑ k, (blockOccupancy eL I k - 1)) + (∑ k, (1 - blockOccupancy eR J k)) = 0
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib,
      sum_blockOccupancy eL I, sum_blockOccupancy eR J, hc]
    ring
  apply Classical.byContradiction
  intro he
  have hz (z : κ ⊕ κ) (hzg : z ≠ g) : D z = 0 := by
    cases z with
    | inl k =>
      change blockOccupancy eL I k - 1 = 0
      have h : ¬ (eL (k,false) ∈ I ↔ eL (k,true) ∈ I) := fun hf =>
        he ⟨Sum.inl k, hzg, twoLayerSwitch_event_toggle_left eL eR I J k hf⟩
      have h' : eL (k,false) ∈ I ↔ eL (k,true) ∉ I := by tauto
      rw [(blockOccupancy_eq_one_iff eL I k).mpr h', sub_self]
    | inr k =>
      change 1 - blockOccupancy eR J k = 0
      have h : ¬ (eR (k,false) ∈ J ↔ eR (k,true) ∈ J) := fun hf =>
        he ⟨Sum.inr k, hzg, twoLayerSwitch_event_toggle_right eL eR I J k hf⟩
      have h' : eR (k,false) ∈ J ↔ eR (k,true) ∉ J := by tauto
      rw [(blockOccupancy_eq_one_iff eR J k).mpr h', sub_self]
  have hg : D g = 0 := by
    rw [← hsum, Finset.sum_eq_single g]
    · intro z _ hz'
      exact hz z hz'
    · simp
  have hall (z : κ ⊕ κ) : D z = 0 := by
    by_cases hz' : z = g
    · rw [hz', hg]
    · exact hz z hz'
  apply hn.elim
  · intro hI
    apply hI
    intro k
    apply (blockOccupancy_eq_one_iff eL I k).mp
    have hk : blockOccupancy eL I k - 1 = 0 := hall (Sum.inl k)
    omega
  · intro hJ
    apply hJ
    intro k
    apply (blockOccupancy_eq_one_iff eR J k).mp
    have hk : 1 - blockOccupancy eR J k = 0 := hall (Sum.inr k)
    omega

private theorem sum_weighted_switchParity_eq_zero (w : (κ ⊕ κ → Bool) → ℝ)
    (k : κ ⊕ κ) (S : Finset (κ ⊕ κ → Bool)) (hS : ∀ x, toggleSwitch k x ∈ S ↔ x ∈ S)
    (hw : ∀ x, w (toggleSwitch k x) = w x) :
    ∑ x ∈ S, w x * switchParity x = 0 := by
  have he : (∑ x ∈ S, w x * switchParity x) = ∑ x ∈ S, -(w x * switchParity x) := by
    apply Finset.sum_equiv (toggleSwitch k)
    · exact fun x => (hS x).symm
    · intro x _
      rw [switchParity_toggle, hw, mul_neg, neg_neg]
  rw [Finset.sum_neg_distrib] at he
  linarith

omit [DecidableEq κ] in
private theorem cyclicIndependentWeight_prod (L R : κ → Matrix Bool Bool ℂ) (x : κ ⊕ κ → Bool) :
    cyclicIndependentWeight L R x = ∏ z, gateSwitchProbability (Sum.elim L R z) (x z) := by
  rw [Fintype.prod_sum_type]
  rfl

private theorem cyclicIndependentWeight_sum (L R : κ → Matrix Bool Bool ℂ)
    (hL : ∀ k, IsUnitary (L k)) (hR : ∀ k, IsUnitary (R k)) :
    ∑ x, cyclicIndependentWeight L R x = 1 := by
  simp_rw [cyclicIndependentWeight_prod, ← Fintype.prod_sum]
  have h (z : κ ⊕ κ) : (∑ b, gateSwitchProbability (Sum.elim L R z) b) = 1 := by
    cases z with
    | inl k => exact gateSwitchProbability_sum _ (hL k)
    | inr k => exact gateSwitchProbability_sum _ (hR k)
  simp only [h, Finset.prod_const_one]

private theorem cyclicIndependentWeight_toggle (L R : κ → Matrix Bool Bool ℂ)
    (z : κ ⊕ κ) (hz : BalancedGate (Sum.elim L R z)) (x : κ ⊕ κ → Bool) :
    cyclicIndependentWeight L R (toggleSwitch z x) = cyclicIndependentWeight L R x := by
  rw [cyclicIndependentWeight_prod, cyclicIndependentWeight_prod,
    ← Finset.prod_erase_mul _ _ (mem_univ z), ← Finset.prod_erase_mul _ _ (mem_univ z)]
  congr 1
  · apply Finset.prod_congr rfl
    intro y hy
    rw [show toggleSwitch z x y = x y by simp [toggleSwitch, (Finset.mem_erase.mp hy).1]]
  · simp only [gateSwitchProbability, hz.2]

private theorem cyclicIndependentWeight_complement_add (L R : κ → Matrix Bool Bool ℂ)
    (hL : ∀ k, IsUnitary (L k)) (hR : ∀ k, IsUnitary (R k))
    (g : κ ⊕ κ) (hg : ∀ z ≠ g, BalancedGate (Sum.elim L R z)) (x : κ ⊕ κ → Bool) :
    cyclicIndependentWeight L R x + cyclicIndependentWeight L R (fun z => !(x z)) =
      2 * (1 / 2 : ℝ) ^ Fintype.card (κ ⊕ κ) := by
  let q := gateSwitchProbability (Sum.elim L R g)
  let p : ℝ := ∏ _z ∈ (univ : Finset (κ ⊕ κ)).erase g, (1 / 2 : ℝ)
  have hP (y : κ ⊕ κ → Bool) : cyclicIndependentWeight L R y = p * q (y g) := by
    rw [cyclicIndependentWeight_prod, ← Finset.prod_erase_mul _ _ (mem_univ g)]
    congr 1
    apply Finset.prod_congr rfl
    intro z hz
    exact (hg z (Finset.mem_erase.mp hz).1).2 false (y z)
  have hp : (1 / 2 : ℝ) ^ Fintype.card (κ ⊕ κ) = p * (1 / 2 : ℝ) := by
    rw [← Finset.card_univ, ← Finset.prod_const, ← Finset.prod_erase_mul _ _ (mem_univ g)]
  have hq : ∑ b, q b = 1 := by
    cases g with
    | inl k => exact gateSwitchProbability_sum _ (hL k)
    | inr k => exact gateSwitchProbability_sum _ (hR k)
  have hsum : q (x g) + q (!(x g)) = 1 := by
    rw [Fintype.sum_bool] at hq
    cases x g <;> simpa only [Bool.not_false, Bool.not_true, add_comm] using hq
  rw [hP, hP, hp, ← mul_add, hsum]
  ring

/-- Along one alternating cycle, one gate can have arbitrary transition
probabilities. A common probability law still gives every squared minor. -/
theorem single_biased_cyclic_gate_minor_law (s : Equiv.Perm κ)
    (hs : TraversesAllIndices s) (hne : s ≠ 1)
    (L R : κ → Matrix Bool Bool ℂ) (hL : ∀ k, IsUnitary (L k)) (hR : ∀ k, IsUnitary (R k))
    (g : κ ⊕ κ) (hg : ∀ z ≠ g, BalancedGate (Sum.elim L R z)) :
    let w := fun x => cyclicIndependentWeight L R x *
      (1 + cyclicGateParityCoefficient s L R * switchParity x)
    (∀ x, 0 ≤ w x) ∧ (∑ x, w x) = 1 ∧
      ∀ I J : Finset (κ × Bool), subsetMinorSq (cyclicGateMixer s L R) I J =
        ∑ x ∈ univ.filter (fun x => J.map
          (twoLayerSwitch (Equiv.refl _) (cyclicRightChart s) x).toEmbedding = I), w x := by
  classical
  haveI : Nonempty κ := by
    cases g with
    | inl k => exact ⟨k⟩
    | inr k => exact ⟨k⟩
  let eL : κ × Bool ≃ κ × Bool := Equiv.refl _
  let eR := cyclicRightChart s
  let P := cyclicIndependentWeight L R
  let c := cyclicGateParityCoefficient s L R
  let w (x : κ ⊕ κ → Bool) := P x * (1 + c * switchParity x)
  let d := (1 / 2 : ℝ) ^ Fintype.card (κ ⊕ κ)
  let t := cyclicGateInterference s L R
  have hc : |c| ≤ 1 := by
    change |t / d| ≤ 1
    have hd : 0 < d := by positivity
    rw [abs_div, abs_of_pos hd, div_le_one hd]
    exact cyclic_interference_le_half_pow s L R hL hR
  have hcd : c * d = t := div_mul_cancel₀ t (by positivity)
  have hsplit (S : Finset (κ ⊕ κ → Bool)) :
      ∑ x ∈ S, w x = (∑ x ∈ S, P x) + c * ∑ x ∈ S, P x * switchParity x := by
    have he (x : κ ⊕ κ → Bool) : w x = P x + c * (P x * switchParity x) := by
      dsimp only [w]
      ring
    simp only [he, Finset.sum_add_distrib, ← Finset.mul_sum]
  have hU : IsUnitary (cyclicGateMixer s L R) :=
    blockGateMatrix_mul_unitary eL eR L R hL hR
  refine ⟨?_, ?_, ?_⟩
  · intro x
    change 0 ≤ w x
    apply mul_nonneg
    · change 0 ≤ cyclicIndependentWeight L R x
      rw [cyclicIndependentWeight_prod]
      exact Finset.prod_nonneg (fun z _ => Complex.normSq_nonneg _)
    · have hc' := abs_le.mp hc
      rcases switchParity_eq_one_or_neg x with hp | hp <;> rw [hp] <;> linarith
  · obtain ⟨z,hz⟩ : ∃ z : κ ⊕ κ, z ≠ g := by
      cases g with
      | inl k => exact ⟨Sum.inr k, by simp⟩
      | inr k => exact ⟨Sum.inl k, by simp⟩
    change ∑ x, w x = 1
    rw [hsplit, sum_weighted_switchParity_eq_zero P z univ (fun _ => by simp)
        (cyclicIndependentWeight_toggle L R z (hg z hz)), mul_zero, add_zero]
    exact cyclicIndependentWeight_sum L R hL hR
  · apply indexed_minor_law_of_small _ hU (twoLayerSwitch eL eR) w
    intro I J hIJ _
    let E := univ.filter (fun x => J.map (twoLayerSwitch eL eR x).toEmbedding = I)
    change subsetMinorSq (cyclicGateMixer s L R) I J = ∑ x ∈ E, w x
    by_cases hT : BlockTransversal eL I ∧ BlockTransversal eR J
    · obtain ⟨hI,hJ⟩ := hT
      let x := cyclicSwitchToFalse s I J
      have he : E = {x, fun z => !(x z)} := cyclic_switch_event_eq_pair s hs I J
        hI hJ x (cyclicSwitchToFalse_event s I J hI hJ)
      have hx : x ≠ fun z => !(x z) := by
        intro h
        have h' := congrFun h g
        cases hb : x g <;> simp [hb] at h'
      have hEven : Even (Fintype.card (κ ⊕ κ)) :=
        ⟨Fintype.card κ, by rw [Fintype.card_sum]⟩
      have hpar : switchParity x = switchParity (x ∘ Sum.inl) * switchParity (x ∘ Sum.inr) := by
        unfold switchParity
        rw [Fintype.prod_sum_type]
        rfl
      have hsum : Sum.elim (x ∘ Sum.inl) (x ∘ Sum.inr) = x := by
        funext z
        cases z <;> rfl
      rw [subsetMinorSq_eq_normSq_det_submatrix _ hU I J
        (blockTransversalEquiv eL I hI) (blockTransversalEquiv eR J hJ)]
      change Complex.normSq (((blockGateMatrix (Equiv.refl _) L * blockGateMatrix
        (cyclicRightChart s) R).submatrix (fun k => (k, (x ∘ Sum.inl) k))
        (fun k => cyclicRightChart s (k, (x ∘ Sum.inr) k))).det) = _
      rw [cyclicSwitchMatrix_transverse_det s hs hne,
        cyclic_two_products_independent_normSq s L R hL hR, hsum, mul_assoc (2 : ℝ), ← hpar,
        he, Finset.sum_pair hx]
      change P x + P (fun z => !(x z)) + 2 * switchParity x * t =
        P x * (1 + c * switchParity x) +
          P (fun z => !(x z)) * (1 + c * switchParity (fun z => !(x z)))
      have hP : P x + P (fun z => !(x z)) = 2 * d :=
        cyclicIndependentWeight_complement_add L R hL hR g hg x
      rw [switchParity_compl x hEven, ← add_mul, hP, ← hcd]

      ring
    · have hn : ¬ BlockTransversal eL I ∨ ¬ BlockTransversal eR J := by tauto
      obtain ⟨z,hz,hE⟩ := exists_free_cyclic_switch eL eR I J hIJ hn g
      have hp := sum_weighted_switchParity_eq_zero P z E
        (fun x => by simpa only [E, Finset.mem_filter, Finset.mem_univ, true_and] using hE x)
        (cyclicIndependentWeight_toggle L R z (hg z hz))
      rw [hsplit, hp, mul_zero, add_zero]
      exact cyclic_nontransversal_independent_law s hs L R hL hR I J hn

/-- Determinant inclusion for any spectra if at most one gate on the cycle is
biased. -/
theorem holds_single_biased_cyclic_gate_mixer (s : Equiv.Perm κ) (hs : TraversesAllIndices s)
    (hne : s ≠ 1) (L R : κ → Matrix Bool Bool ℂ)
    (hL : ∀ k, IsUnitary (L k)) (hR : ∀ k, IsUnitary (R k))
    (g : κ ⊕ κ) (hg : ∀ z ≠ g, BalancedGate (Sum.elim L R z))
    (a b : κ × Bool → ℂ) : Holds a b (cyclicGateMixer s L R) := by
  obtain ⟨hw, hsum, hm⟩ := single_biased_cyclic_gate_minor_law s hs hne L R hL hR g hg
  exact holds_of_indexed_minor_law a b (cyclicGateMixer s L R)
    (blockGateMatrix_mul_unitary _ _ L R hL hR)
    (twoLayerSwitch (Equiv.refl _) (cyclicRightChart s)) _ hw hsum hm

end

end MOC
