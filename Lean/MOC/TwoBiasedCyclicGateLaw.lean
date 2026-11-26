import MOC.SingleBiasedCyclicGateLaw
import MOC.UniversalMatchingWeights

/-! An affine parity correction allows two biased gates on an alternating cycle. -/

open BigOperators Finset Matrix

namespace MOC

noncomputable section

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

private def gateBias (Q : Matrix Bool Bool ℂ) : ℝ :=
  gateSwitchProbability Q false - gateSwitchProbability Q true

private theorem gate_probability_eq_bias (Q : Matrix Bool Bool ℂ) (hQ : IsUnitary Q) (b : Bool) :
    gateSwitchProbability Q b = (1 / 2 : ℝ) * (1 + gateBias Q * switchSign b) := by
  have h := gateSwitchProbability_sum Q hQ
  rw [Fintype.sum_bool] at h
  cases b <;> simp [gateBias, switchSign] <;> linarith

private theorem gateBias_abs_le_one (Q : Matrix Bool Bool ℂ) (hQ : IsUnitary Q) :
    |gateBias Q| ≤ 1 := by
  have h := gateSwitchProbability_sum Q hQ
  rw [Fintype.sum_bool] at h
  have h₀ : 0 ≤ gateSwitchProbability Q false := Complex.normSq_nonneg _
  have h₁ : 0 ≤ gateSwitchProbability Q true := Complex.normSq_nonneg _
  unfold gateBias
  exact abs_le.mpr ⟨by linarith, by linarith⟩

private def gateCycleMixed (L R : κ → Matrix Bool Bool ℂ) : κ ⊕ κ → ℂ :=
  Sum.elim (fun k => L k false false * star (L k false true))
    (fun k => R k false false * star (R k true false))

omit [Fintype κ] [DecidableEq κ] in
private theorem gateCycleMixed_norm_sq (L R : κ → Matrix Bool Bool ℂ)
    (hR : ∀ k, IsUnitary (R k)) (z : κ ⊕ κ) :
    ‖gateCycleMixed L R z‖ ^ 2 =
      gateSwitchProbability (Sum.elim L R z) false * gateSwitchProbability (Sum.elim L R z) true := by
  rw [Complex.sq_norm]
  cases z with
  | inl k =>
    change Complex.normSq (L k false false * star (L k false true)) = _
    rw [Complex.normSq_mul, Complex.star_def, Complex.normSq_conj]
    rfl
  | inr k =>
    change Complex.normSq (R k false false * star (R k true false)) = _
    rw [Complex.normSq_mul, Complex.star_def, Complex.normSq_conj,
      gateSwitchProbability_eq_normSq (R k) (hR k) true false]
    rfl
omit [Fintype κ] [DecidableEq κ] in
private theorem gateCycleMixed_circle (L R : κ → Matrix Bool Bool ℂ)
    (hL : ∀ k, IsUnitary (L k)) (hR : ∀ k, IsUnitary (R k)) (z : κ ⊕ κ) :
    4 * ‖gateCycleMixed L R z‖ ^ 2 + gateBias (Sum.elim L R z) ^ 2 = 1 := by
  have hQ : IsUnitary (Sum.elim L R z) := by
    cases z with
    | inl k => exact hL k
    | inr k => exact hR k
  have h := gateSwitchProbability_sum _ hQ
  rw [Fintype.sum_bool] at h
  rw [gateCycleMixed_norm_sq L R hR z, gateBias]
  nlinarith [congrArg (· ^ 2) h]

omit [Fintype κ] [DecidableEq κ] in
private theorem gateCycleMixed_balanced (L R : κ → Matrix Bool Bool ℂ)
    (z : κ ⊕ κ) (hz : BalancedGate (Sum.elim L R z)) :
    ‖gateCycleMixed L R z‖ = 1 / 2 := by
  cases z with
  | inl k => exact balancedGate_mixed_norm (L k) hz false false false true
  | inr k => exact balancedGate_mixed_norm (R k) hz false false true false

private theorem cyclic_two_bias_phase_bound (s : Equiv.Perm κ) (L R : κ → Matrix Bool Bool ℂ)
    (hL : ∀ k, IsUnitary (L k)) (hR : ∀ k, IsUnitary (R k))
    (g₁ g₂ : κ ⊕ κ) (hg : g₁ ≠ g₂)
    (hfair : ∀ z, z ≠ g₁ → z ≠ g₂ → BalancedGate (Sum.elim L R z)) :
    |cyclicGateInterference s L R| ≤ (1 / 2 : ℝ) ^ Fintype.card (κ ⊕ κ) *
      (1 - |gateBias (Sum.elim L R g₁) * gateBias (Sum.elim L R g₂)|) := by
  classical
  let T := (univ : Finset (κ ⊕ κ)).erase g₁
  let F := T.erase g₂
  let d : ℝ := ∏ _z ∈ F, 1 / 2
  let v (z : κ ⊕ κ) := ‖gateCycleMixed L R z‖
  let b (z : κ ⊕ κ) := gateBias (Sum.elim L R z)
  have h₂ : g₂ ∈ T := Finset.mem_erase.mpr ⟨Ne.symm hg, mem_univ _⟩
  have hE : ‖∏ k, (L k false false * star (L k false true)) *
      (R k false false * star (R k true false))‖ = d * v g₂ * v g₁ := by
    rw [Finset.prod_mul_distrib]
    change ‖(∏ k, gateCycleMixed L R (Sum.inl k)) * (∏ k, gateCycleMixed L R (Sum.inr k))‖ = _
    rw [← Fintype.prod_sum_type, Complex.norm_prod,
      ← Finset.prod_erase_mul _ _ (mem_univ g₁), ← Finset.prod_erase_mul _ _ h₂]
    congr 2
    apply Finset.prod_congr rfl
    intro z hz
    exact gateCycleMixed_balanced L R z (hfair z
      (Finset.mem_erase.mp (Finset.mem_erase.mp hz).2).1 (Finset.mem_erase.mp hz).1)
  have hd : (1 / 2 : ℝ) ^ Fintype.card (κ ⊕ κ) = d * (1 / 2) * (1 / 2) := by
    rw [← Finset.card_univ, ← Finset.prod_const, ← Finset.prod_erase_mul _ _ (mem_univ g₁),
      ← Finset.prod_erase_mul _ _ h₂]
  have hcircle₁ : 4 * v g₁ ^ 2 + |b g₁| ^ 2 = 1 := by
    rw [sq_abs]
    exact gateCycleMixed_circle L R hL hR g₁
  have hcircle₂ : 4 * v g₂ ^ 2 + |b g₂| ^ 2 = 1 := by
    rw [sq_abs]
    exact gateCycleMixed_circle L R hL hR g₂
  have hv : v g₂ * v g₁ ≤ (1 / 2) * (1 / 2) * (1 - |b g₁ * b g₂|) := by
    rw [abs_mul]
    nlinarith [sq_nonneg (2 * v g₁ - 2 * v g₂), sq_nonneg (|b g₁| - |b g₂|)]
  have hd0 : 0 ≤ d := Finset.prod_nonneg (fun _ _ => by norm_num)
  have hD : |cyclicGateInterference s L R| ≤ d * v g₂ * v g₁ := by
    have hRe := (Complex.abs_re_le_norm _).trans hE.le
    rcases Int.units_eq_one_or s.sign with hs | hs <;>
      simpa [cyclicGateInterference, hs] using hRe
  rw [hd]
  calc
    _ ≤ d * v g₂ * v g₁ := hD
    _ = d * (v g₂ * v g₁) := by ring
    _ ≤ d * ((1 / 2) * (1 / 2) * (1 - |b g₁ * b g₂|)) := mul_le_mul_of_nonneg_left hv hd0
    _ = _ := by ring

private theorem cyclicIndependentWeight_two_bias (L R : κ → Matrix Bool Bool ℂ)
    (hL : ∀ k, IsUnitary (L k)) (hR : ∀ k, IsUnitary (R k))
    (g₁ g₂ : κ ⊕ κ) (hg : g₁ ≠ g₂)
    (hfair : ∀ z, z ≠ g₁ → z ≠ g₂ → BalancedGate (Sum.elim L R z)) (x : κ ⊕ κ → Bool) :
    cyclicIndependentWeight L R x = (1 / 2 : ℝ) ^ Fintype.card (κ ⊕ κ) *
      (1 + gateBias (Sum.elim L R g₁) * switchSign (x g₁)) *
        (1 + gateBias (Sum.elim L R g₂) * switchSign (x g₂)) := by
  classical
  have hU (z : κ ⊕ κ) : IsUnitary (Sum.elim L R z) := by
    cases z with
    | inl k => exact hL k
    | inr k => exact hR k
  let T := (univ : Finset (κ ⊕ κ)).erase g₁
  let F := T.erase g₂
  have h₂ : g₂ ∈ T := Finset.mem_erase.mpr ⟨Ne.symm hg, mem_univ _⟩
  have hP : cyclicIndependentWeight L R x = ∏ z, gateSwitchProbability (Sum.elim L R z) (x z) := by
    rw [Fintype.prod_sum_type]
    rfl
  have hF : (∏ z ∈ F, gateSwitchProbability (Sum.elim L R z) (x z)) = ∏ _z ∈ F, (1 / 2 : ℝ) := by
    apply Finset.prod_congr rfl
    intro z hz
    exact (hfair z (Finset.mem_erase.mp (Finset.mem_erase.mp hz).2).1 (Finset.mem_erase.mp hz).1).2 false (x z)
  rw [hP, ← Finset.prod_erase_mul _ _ (mem_univ g₁), ← Finset.prod_erase_mul _ _ h₂, hF,
    gate_probability_eq_bias _ (hU g₁), gate_probability_eq_bias _ (hU g₂),
    ← Finset.card_univ, ← Finset.prod_const, ← Finset.prod_erase_mul _ _ (mem_univ g₁),
    ← Finset.prod_erase_mul _ _ h₂]
  ring

private theorem two_bias_affine_bound (d t b₁ b₂ : ℝ) (hd : 0 ≤ d)
    (hb₁ : |b₁| ≤ 1) (hb₂ : |b₂| ≤ 1) (ht : |t| ≤ d * (1 - |b₁ * b₂|)) :
    ∃ a₁ a₂ : ℝ, ∀ s₁ s₂ : Bool, |t + a₁ * switchSign s₁ + a₂ * switchSign s₂| ≤
      d * (1 + b₁ * switchSign s₁) * (1 + b₂ * switchSign s₂) := by
  let p := b₁ * b₂
  have hp : |p| ≤ 1 := by
    rw [abs_mul]
    nlinarith [mul_le_mul hb₁ hb₂ (abs_nonneg b₂) (by norm_num : (0 : ℝ) ≤ 1)]
  have hes (b : ℝ) (hb : |b| ≤ 1) (s : Bool) : 0 ≤ 1 + b * switchSign s := by
    obtain ⟨hl, hh⟩ := abs_le.mp hb
    cases s <;> simp [switchSign] <;> linarith
  by_cases he : |p| = 1
  · have ht0 : t = 0 := by
      change |t| ≤ d * (1 - |p|) at ht
      rw [he, sub_self, mul_zero] at ht
      exact abs_eq_zero.mp (le_antisymm ht (abs_nonneg _))
    refine ⟨0,0, ?_⟩
    intro s₁ s₂
    simp only [ht0, zero_mul, add_zero, abs_zero]
    exact mul_nonneg (mul_nonneg hd (hes b₁ hb₁ s₁)) (hes b₂ hb₂ s₂)
  · have hp' : |p| < 1 := lt_of_le_of_ne hp he
    have hden : 0 < 1 - p ^ 2 := by
      rw [← sq_abs]
      nlinarith [abs_nonneg p]
    let D := 1 - p ^ 2
    refine ⟨t * (b₁ - p * b₂) / D, t * (b₂ - p * b₁) / D, ?_⟩
    intro s₁ s₂
    let x := switchSign s₁
    let y := switchSign s₂
    let N := (1 + b₁*x) * (1 + b₂*y)
    let Z := 1 - p*x*y
    have hx : x^2 = 1 := by cases s₁ <;> norm_num [x, switchSign]
    have hy : y^2 = 1 := by cases s₂ <;> norm_num [y, switchSign]
    have hx' : |x| = 1 := by cases s₁ <;> norm_num [x, switchSign]
    have hy' : |y| = 1 := by cases s₂ <;> norm_num [y, switchSign]
    have hpabs : |p*x*y| = |p| := by rw [abs_mul, abs_mul, hx', hy', mul_one, mul_one]
    have hz0 : 0 ≤ Z := by
      have h := le_abs_self (p*x*y)
      rw [hpabs] at h
      dsimp only [Z]
      linarith
    have hz1 : Z ≤ 1 + |p| := by
      have h := (abs_le.mp (le_of_eq hpabs)).1
      dsimp only [Z]
      linarith
    have hn : 0 ≤ N := mul_nonneg (hes b₁ hb₁ s₁) (hes b₂ hb₂ s₂)
    have hpoly : D + (b₁ - p*b₂)*x + (b₂ - p*b₁)*y = N*Z := by
      dsimp only [D, N, Z]
      calc
        _ = (1 + b₁*x + b₂*y + p*x*y) * (1 - p*x*y) := by
          linear_combination p^2*y^2 * (hx) + p^2 * (hy) +
            p*b₁*y * (hx) + p*b₂*x * (hy)
        _ = _ := by dsimp only [p]; ring
    have hfactor : t + t * (b₁ - p*b₂) / D * x + t * (b₂ - p*b₁) / D * y =
        t * (N*Z) / D := by
      rw [← hpoly]
      field_simp [ne_of_gt hden]
      ring
    change |t + t * (b₁ - p*b₂) / D * x + t * (b₂ - p*b₁) / D * y| ≤ _
    rw [hfactor, abs_div, abs_of_pos hden, abs_mul, abs_of_nonneg (mul_nonneg hn hz0),
      div_le_iff₀ hden]
    have hmult : |t| * (N*Z) ≤ (d * (1 - |p|)) * (N*(1 + |p|)) :=
      mul_le_mul ht (mul_le_mul_of_nonneg_left hz1 hn) (mul_nonneg hn hz0)
        (mul_nonneg hd (by linarith))
    calc
      _ ≤ _ := hmult
      _ = _ := by
        change d * (1 - |p|) * (N * (1 + |p|)) =
          d * (1 + b₁*x) * (1 + b₂*y) * (1 - p^2)
        rw [← sq_abs p]
        dsimp only [N]
        ring

private theorem sum_affine_correction_signed (E : Finset (κ ⊕ κ → Bool)) (g₁ g₂ : κ ⊕ κ)
    (t a₁ a₂ : ℝ) (hE : ∀ g : κ ⊕ κ, ∃ z ≠ g, ∀ x, toggleSwitch z x ∈ E ↔ x ∈ E) :
    (∑ x ∈ E, (t + a₁ * switchSign (x g₁) + a₂ * switchSign (x g₂)) * switchParity x) = 0 := by
  have h (g : κ ⊕ κ) : ∑ x ∈ E, switchSign (x g) * switchParity x = 0 := by
    obtain ⟨z, hz, hf⟩ := hE g
    apply sum_weighted_switchParity_eq_zero (fun x => switchSign (x g)) z E hf
    intro x
    simp [toggleSwitch, ne_comm.mp hz]
  obtain ⟨z, _, hz⟩ := hE g₁
  have he (x : κ ⊕ κ → Bool) :
      (t + a₁ * switchSign (x g₁) + a₂ * switchSign (x g₂)) * switchParity x =
        t * switchParity x + a₁ * (switchSign (x g₁) * switchParity x) +
          a₂ * (switchSign (x g₂) * switchParity x) := by ring
  simp only [he, Finset.sum_add_distrib, ← Finset.mul_sum,
    sum_switchParity_eq_zero z E hz, h, mul_zero, add_zero]

/-- Two gates on an alternating cycle may be arbitrary while one probability
law still gives every squared minor. -/
theorem two_biased_cyclic_gate_minor_law (s : Equiv.Perm κ)
    (hs : TraversesAllIndices s) (hne : s ≠ 1)
    (L R : κ → Matrix Bool Bool ℂ) (hL : ∀ k, IsUnitary (L k)) (hR : ∀ k, IsUnitary (R k))
    (g₁ g₂ : κ ⊕ κ) (hg : g₁ ≠ g₂)
    (hfair : ∀ z, z ≠ g₁ → z ≠ g₂ → BalancedGate (Sum.elim L R z)) :
    ∃ w : (κ ⊕ κ → Bool) → ℝ, (∀ x, 0 ≤ w x) ∧ (∑ x, w x) = 1 ∧
      ∀ I J : Finset (κ × Bool), subsetMinorSq (cyclicGateMixer s L R) I J =
        ∑ x ∈ univ.filter (fun x => J.map
          (twoLayerSwitch (Equiv.refl _) (cyclicRightChart s) x).toEmbedding = I), w x := by
  classical
  haveI : Nonempty κ := by
    cases g₁ with
    | inl k => exact ⟨k⟩
    | inr k => exact ⟨k⟩
  let eL : κ × Bool ≃ κ × Bool := Equiv.refl _
  let eR := cyclicRightChart s
  let P := cyclicIndependentWeight L R
  let t := cyclicGateInterference s L R
  let d := (1 / 2 : ℝ) ^ Fintype.card (κ ⊕ κ)
  have hb (z : κ ⊕ κ) : |gateBias (Sum.elim L R z)| ≤ 1 := by
    cases z with
    | inl k => exact gateBias_abs_le_one _ (hL k)
    | inr k => exact gateBias_abs_le_one _ (hR k)
  obtain ⟨a₁, a₂, hA⟩ := two_bias_affine_bound d t _ _ (by positivity)
    (hb g₁) (hb g₂) (cyclic_two_bias_phase_bound s L R hL hR g₁ g₂ hg hfair)
  let A (x : κ ⊕ κ → Bool) := t + a₁ * switchSign (x g₁) + a₂ * switchSign (x g₂)
  let w (x : κ ⊕ κ → Bool) := P x + A x * switchParity x
  have hU : IsUnitary (cyclicGateMixer s L R) :=
    blockGateMatrix_mul_unitary eL eR L R hL hR
  refine ⟨w, ?_, ?_, ?_⟩
  · intro x
    have hbound : |A x| ≤ P x := by
      change |A x| ≤ cyclicIndependentWeight L R x
      rw [cyclicIndependentWeight_two_bias L R hL hR g₁ g₂ hg hfair x]
      exact hA (x g₁) (x g₂)
    obtain ⟨hl, hh⟩ := abs_le.mp hbound
    change 0 ≤ P x + A x * switchParity x
    rcases switchParity_eq_one_or_neg x with hp | hp <;> rw [hp] <;> linarith
  · have hh (g : κ ⊕ κ) : ∃ z : κ ⊕ κ, z ≠ g := by
      cases g with
      | inl k => exact ⟨Sum.inr k, by simp⟩
      | inr k => exact ⟨Sum.inl k, by simp⟩
    change ∑ x, (P x + (t + a₁ * switchSign (x g₁) + a₂ * switchSign (x g₂)) * switchParity x) = 1
    rw [Finset.sum_add_distrib, sum_affine_correction_signed univ g₁ g₂ t a₁ a₂
      (fun g => (hh g).imp fun z hz => ⟨hz, fun _ => by simp⟩), add_zero]
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
        have h' := congrFun h g₁
        cases hb : x g₁ <;> simp [hb] at h'
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
      rw [cyclicSwitchMatrix_transverse_det s hs hne, cyclic_two_products_independent_normSq s L R hL hR,
        hsum, mul_assoc (2 : ℝ), ← hpar, he, Finset.sum_pair hx]
      change P x + P (fun z => !(x z)) + 2 * switchParity x * t =
        P x + A x * switchParity x + (P (fun z => !(x z)) +
          A (fun z => !(x z)) * switchParity (fun z => !(x z)))
      rw [switchParity_compl x hEven]
      dsimp only [A]
      rw [switchSign_not, switchSign_not]
      ring
    · have hn : ¬ BlockTransversal eL I ∨ ¬ BlockTransversal eR J := by tauto
      have hE (g : κ ⊕ κ) : ∃ z ≠ g, ∀ x, toggleSwitch z x ∈ E ↔ x ∈ E := by
        obtain ⟨z, hz, hz'⟩ := exists_free_cyclic_switch eL eR I J hIJ hn g
        exact ⟨z, hz, fun x => by simpa only [E, Finset.mem_filter, Finset.mem_univ, true_and] using hz' x⟩
      change _ = ∑ x ∈ E, (P x + (t + a₁ * switchSign (x g₁) + a₂ * switchSign (x g₂)) * switchParity x)
      rw [Finset.sum_add_distrib, sum_affine_correction_signed E g₁ g₂ t a₁ a₂ hE, add_zero]
      exact cyclic_nontransversal_independent_law s hs L R hL hR I J hn

/-- The permutation weights for these mixers are independent of both spectra. -/
theorem hasUniversalMatchingWeights_two_biased_cyclic_gate_mixer (s : Equiv.Perm κ)
    (hs : TraversesAllIndices s) (hne : s ≠ 1) (L R : κ → Matrix Bool Bool ℂ)
    (hL : ∀ k, IsUnitary (L k)) (hR : ∀ k, IsUnitary (R k))
    (g₁ g₂ : κ ⊕ κ) (hg : g₁ ≠ g₂)
    (hfair : ∀ z, z ≠ g₁ → z ≠ g₂ → BalancedGate (Sum.elim L R z)) :
    HasUniversalMatchingWeights (cyclicGateMixer s L R) := by
  classical
  obtain ⟨w, hw, hsum, hm⟩ := two_biased_cyclic_gate_minor_law s hs hne L R hL hR g₁ g₂ hg hfair
  let p := twoLayerSwitch (Equiv.refl _) (cyclicRightChart s)
  let v (σ : Equiv.Perm (κ × Bool)) := ∑ x ∈ univ.filter (fun x => p x = σ), w x
  refine ⟨v, fun σ => Finset.sum_nonneg (fun x _ => hw x), ?_, ?_⟩
  · change ∑ σ, ∑ x ∈ univ.filter (fun x => p x = σ), w x = 1
    rw [Finset.sum_fiberwise, hsum]
  · intro a b
    rw [← determinantValue_eq_sum_of_indexed_minor_law a b (cyclicGateMixer s L R)
        (blockGateMatrix_mul_unitary _ _ L R hL hR) p w hm, ← Finset.sum_fiberwise univ p]
    apply Finset.sum_congr rfl
    intro σ _
    change (∑ x ∈ univ.filter (fun x => p x = σ), (w x : ℂ) * matchingProduct a b (p x)) =
      (v σ : ℂ) * matchingProduct a b σ
    rw [show v σ = _ from rfl, Complex.ofReal_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro x hx
    rw [(Finset.mem_filter.mp hx).2]

/-- Determinant inclusion for any spectra if all but two gates are balanced. -/
theorem holds_two_biased_cyclic_gate_mixer (s : Equiv.Perm κ) (hs : TraversesAllIndices s)
    (hne : s ≠ 1) (L R : κ → Matrix Bool Bool ℂ)
    (hL : ∀ k, IsUnitary (L k)) (hR : ∀ k, IsUnitary (R k))
    (g₁ g₂ : κ ⊕ κ) (hg : g₁ ≠ g₂)
    (hfair : ∀ z, z ≠ g₁ → z ≠ g₂ → BalancedGate (Sum.elim L R z))
    (a b : κ × Bool → ℂ) : Holds a b (cyclicGateMixer s L R) := by
  obtain ⟨w, hw, hsum, hm⟩ := two_biased_cyclic_gate_minor_law s hs hne L R hL hR g₁ g₂ hg hfair
  exact holds_of_indexed_minor_law a b (cyclicGateMixer s L R)
    (blockGateMatrix_mul_unitary _ _ L R hL hR)
    (twoLayerSwitch (Equiv.refl _) (cyclicRightChart s)) w hw hsum hm

end

end MOC
