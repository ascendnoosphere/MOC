import MOC.SingleBiasedCyclicGateLaw
import MOC.Realification

/-! At fixed switch probabilities, all phase dependence on one alternating
cycle is through its real interference term. Two real mixers give its
endpoints simultaneously for every squared minor. -/

open BigOperators Finset Matrix

namespace MOC

noncomputable section

private def realGateRotation (c d : ℝ) : Matrix Bool Bool ℂ :=
  Matrix.of fun i j => ((if i = j then c else if i then -d else d : ℝ) : ℂ)

private theorem realGateRotation_unitary {c d : ℝ} (h : c ^ 2 + d ^ 2 = 1) :
    IsUnitary (realGateRotation c d) := by
  have hsum : (c : ℂ) * (c : ℂ) + (d : ℂ) * (d : ℂ) = 1 := by
    have hr : c * c + d * d = 1 := by simpa only [pow_two] using h
    simpa only [Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_one] using
      congrArg Complex.ofReal hr
  have hm : realGateRotation c d * (realGateRotation c d)ᴴ = 1 := by
    ext i j
    cases i <;> cases j <;>
      simp [realGateRotation, Matrix.mul_apply, Matrix.conjTranspose_apply,
        Fintype.sum_bool, Matrix.one_apply, Complex.star_def, neg_mul_neg]
    · simpa only [add_comm] using hsum
    · ring
    · ring
    · simpa only [add_comm] using hsum
  exact ⟨hm, mul_eq_one_comm.mp hm⟩

private def rotationForGate (Q : Matrix Bool Bool ℂ) (negate : Bool) : Matrix Bool Bool ℂ :=
  realGateRotation ‖Q false false‖ (if negate then -‖Q false true‖ else ‖Q false true‖)

private theorem rotationForGate_unitary (Q : Matrix Bool Bool ℂ) (hQ : IsUnitary Q)
    (negate : Bool) : IsUnitary (rotationForGate Q negate) := by
  apply realGateRotation_unitary
  cases negate <;> simpa [neg_sq, Complex.sq_norm] using gate_row_probability Q hQ false

private theorem rotationForGate_probability (Q : Matrix Bool Bool ℂ) (negate x : Bool) :
    gateSwitchProbability (rotationForGate Q negate) x = gateSwitchProbability Q x := by
  cases negate <;> cases x <;>
    simp [gateSwitchProbability, rotationForGate, realGateRotation,
      Complex.normSq_ofReal, ← pow_two, Complex.sq_norm]

private theorem rotationForGate_im (Q : Matrix Bool Bool ℂ) (negate i j : Bool) :
    (rotationForGate Q negate i j).im = 0 :=
  Complex.ofReal_im _

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

private theorem nonempty_of_cycle_ne_one {s : Equiv.Perm κ} (hne : s ≠ 1) : Nonempty κ := by
  classical
  by_contra h
  haveI : IsEmpty κ := not_nonempty_iff.mp h
  exact hne (Equiv.ext fun k => isEmptyElim k)

/-- The independent switch weights plus the signed parity correction give
every squared minor for arbitrary biases on a nontrivial alternating cycle. -/
theorem cyclic_gate_signed_minor_law (s : Equiv.Perm κ) (hs : TraversesAllIndices s)
    (hne : s ≠ 1) (L R : κ → Matrix Bool Bool ℂ)
    (hL : ∀ k, IsUnitary (L k)) (hR : ∀ k, IsUnitary (R k)) :
    ∀ I J : Finset (κ × Bool), subsetMinorSq (cyclicGateMixer s L R) I J =
      ∑ x ∈ univ.filter (fun x : κ ⊕ κ → Bool => J.map
        (twoLayerSwitch (Equiv.refl (κ × Bool)) (cyclicRightChart s) x).toEmbedding = I),
        (cyclicIndependentWeight L R x + cyclicGateInterference s L R * switchParity x) := by
  classical
  obtain ⟨k₀⟩ := nonempty_of_cycle_ne_one hne
  letI : Nonempty κ := ⟨k₀⟩
  let eL : κ × Bool ≃ κ × Bool := Equiv.refl _
  let eR := cyclicRightChart s
  let P := cyclicIndependentWeight L R
  let t := cyclicGateInterference s L R
  have hU : IsUnitary (cyclicGateMixer s L R) :=
    blockGateMatrix_mul_unitary eL eR L R hL hR
  apply indexed_minor_law_of_small _ hU (twoLayerSwitch eL eR)
    (fun x => P x + t * switchParity x)
  intro I J hIJ _
  let E := univ.filter (fun x => J.map (twoLayerSwitch eL eR x).toEmbedding = I)
  change subsetMinorSq (cyclicGateMixer s L R) I J = ∑ x ∈ E, (P x + t * switchParity x)
  by_cases hT : BlockTransversal eL I ∧ BlockTransversal eR J
  · obtain ⟨hI, hJ⟩ := hT
    let x := cyclicSwitchToFalse s I J
    have he : E = {x, fun z => !(x z)} := cyclic_switch_event_eq_pair s hs I J
      hI hJ x (cyclicSwitchToFalse_event s I J hI hJ)
    have hx : x ≠ fun z => !(x z) := by
      intro h
      have hk := congrFun h (Sum.inl k₀)
      cases hb : x (Sum.inl k₀) <;> simp [hb] at hk
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
      cyclic_two_products_independent_normSq s L R hL hR, hsum,
      mul_assoc (2 : ℝ), ← hpar, he, Finset.sum_pair hx, switchParity_compl x hEven]
    change P x + P (fun z => !(x z)) + 2 * switchParity x * t =
      P x + t * switchParity x + (P (fun z => !(x z)) + t * switchParity x)
    ring
  · have hn : ¬ BlockTransversal eL I ∨ ¬ BlockTransversal eR J := by tauto
    obtain ⟨g, _, hg⟩ := exists_free_cyclic_switch eL eR I J hIJ hn (Sum.inl k₀)
    have hzero : ∑ x ∈ E, switchParity x = 0 :=
      sum_switchParity_eq_zero g E (fun x => by
        simpa only [E, Finset.mem_filter, Finset.mem_univ, true_and] using hg x)
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, hzero, mul_zero, add_zero]
    exact cyclic_nontransversal_independent_law s hs L R hL hR I J hn

/-- The cycle contribution to the determinant uses the parity-weighted
matching sum and the same scalar interference for every spectrum. -/
theorem cyclic_gate_determinant_eq_independent_add_interference (s : Equiv.Perm κ)
    (hs : TraversesAllIndices s) (hne : s ≠ 1) (L R : κ → Matrix Bool Bool ℂ)
    (hL : ∀ k, IsUnitary (L k)) (hR : ∀ k, IsUnitary (R k)) (a b : κ × Bool → ℂ) :
    let p := twoLayerSwitch (Equiv.refl _) (cyclicRightChart s)
    determinantValue a b (cyclicGateMixer s L R) =
      (∑ x, (cyclicIndependentWeight L R x : ℂ) * matchingProduct a b (p x)) +
      (cyclicGateInterference s L R : ℂ) *
        ∑ x, (switchParity x : ℂ) * matchingProduct a b (p x) := by
  dsimp only
  rw [← determinantValue_eq_sum_of_indexed_minor_law a b (cyclicGateMixer s L R)
    (blockGateMatrix_mul_unitary _ _ L R hL hR)
    (twoLayerSwitch (Equiv.refl _) (cyclicRightChart s))
    (fun x => cyclicIndependentWeight L R x + cyclicGateInterference s L R * switchParity x)
    (cyclic_gate_signed_minor_law s hs hne L R hL hR)]
  simp only [Complex.ofReal_add, Complex.ofReal_mul, add_mul, Finset.sum_add_distrib,
    Finset.mul_sum, mul_assoc]

/-- A bound on the interference by every independent switch weight
ensures determinant inclusion, with no restriction on the gate biases. -/
theorem holds_cyclic_gate_of_interference_abs_le (s : Equiv.Perm κ)
    (hs : TraversesAllIndices s) (hne : s ≠ 1) (L R : κ → Matrix Bool Bool ℂ)
    (hL : ∀ k, IsUnitary (L k)) (hR : ∀ k, IsUnitary (R k))
    (hbound : ∀ x, |cyclicGateInterference s L R| ≤ cyclicIndependentWeight L R x)
    (a b : κ × Bool → ℂ) : Holds a b (cyclicGateMixer s L R) := by
  obtain ⟨k₀⟩ := nonempty_of_cycle_ne_one hne
  have hsum : ∑ x : κ ⊕ κ → Bool, switchParity x = 0 :=
    sum_switchParity_eq_zero (Sum.inl k₀) univ (fun _ => by simp)
  refine holds_of_indexed_minor_law a b (cyclicGateMixer s L R)
    (blockGateMatrix_mul_unitary _ _ L R hL hR)
    (twoLayerSwitch (Equiv.refl _) (cyclicRightChart s))
    (fun x => cyclicIndependentWeight L R x + cyclicGateInterference s L R * switchParity x)
    ?_ ?_ (cyclic_gate_signed_minor_law s hs hne L R hL hR)
  · intro x
    change 0 ≤ cyclicIndependentWeight L R x + cyclicGateInterference s L R * switchParity x
    obtain ⟨hl, hh⟩ := abs_le.mp (hbound x)
    rcases switchParity_eq_one_or_neg x with he | he <;> rw [he] <;> linarith
  · rw [Finset.sum_add_distrib, ← Finset.mul_sum, hsum, mul_zero, add_zero]
    exact cyclicIndependentWeight_sum L R hL hR

private theorem cyclicIndependentWeight_congr_prob (L R L' R' : κ → Matrix Bool Bool ℂ)
    (hL : ∀ k x, gateSwitchProbability (L' k) x = gateSwitchProbability (L k) x)
    (hR : ∀ k x, gateSwitchProbability (R' k) x = gateSwitchProbability (R k) x)
    (x : κ ⊕ κ → Bool) :
    cyclicIndependentWeight L' R' x = cyclicIndependentWeight L R x := by
  simp only [cyclicIndependentWeight, hL, hR]

private theorem cyclicGate_minor_affine (s : Equiv.Perm κ) (hs : TraversesAllIndices s)
    (hne : s ≠ 1) (L R L₀ R₀ L₁ R₁ : κ → Matrix Bool Bool ℂ)
    (hL : ∀ k, IsUnitary (L k)) (hR : ∀ k, IsUnitary (R k))
    (hL₀ : ∀ k, IsUnitary (L₀ k)) (hR₀ : ∀ k, IsUnitary (R₀ k))
    (hL₁ : ∀ k, IsUnitary (L₁ k)) (hR₁ : ∀ k, IsUnitary (R₁ k))
    (hp₀ : ∀ x, cyclicIndependentWeight L₀ R₀ x = cyclicIndependentWeight L R x)
    (hp₁ : ∀ x, cyclicIndependentWeight L₁ R₁ x = cyclicIndependentWeight L R x)
    (t : ℝ) (ht : cyclicGateInterference s L R =
      t * cyclicGateInterference s L₀ R₀ + (1 - t) * cyclicGateInterference s L₁ R₁)
    (I J : Finset (κ × Bool)) :
    subsetMinorSq (cyclicGateMixer s L R) I J =
      t * subsetMinorSq (cyclicGateMixer s L₀ R₀) I J +
        (1 - t) * subsetMinorSq (cyclicGateMixer s L₁ R₁) I J := by
  rw [cyclic_gate_signed_minor_law s hs hne L R hL hR,
    cyclic_gate_signed_minor_law s hs hne L₀ R₀ hL₀ hR₀,
    cyclic_gate_signed_minor_law s hs hne L₁ R₁ hL₁ hR₁]
  simp only [hp₀, hp₁, ht, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  ring

private theorem abs_interference_le_rotation (s : Equiv.Perm κ)
    (L R : κ → Matrix Bool Bool ℂ) (hR : ∀ k, IsUnitary (R k)) :
    |cyclicGateInterference s L R| ≤
      |cyclicGateInterference s (fun k => rotationForGate (L k) false)
        (fun k => rotationForGate (R k) false)| := by
  let p (k : κ) : ℝ := (‖L k false false‖ * ‖L k false true‖) *
    (‖R k false false‖ * -‖R k false true‖)
  let f (k : κ) : ℂ := (L k false false * star (L k false true)) *
    (R k false false * star (R k true false))
  have hp (k : κ) :
      (rotationForGate (L k) false false false * star (rotationForGate (L k) false false true)) *
      (rotationForGate (R k) false false false * star (rotationForGate (R k) false true false)) =
      (p k : ℂ) := by
    simp [p, rotationForGate, realGateRotation, Complex.star_def, Complex.ofReal_mul]
  have hRoff (k : κ) : ‖R k true false‖ = ‖R k false true‖ := by
    have hs : Complex.normSq (R k true false) = Complex.normSq (R k false true) :=
      gateSwitchProbability_eq_normSq (R k) (hR k) true false
    simpa only [Complex.norm_def] using congrArg Real.sqrt hs
  have hnorm : ‖∏ k, f k‖ = |∏ k, p k| := by
    rw [Complex.norm_prod, Finset.abs_prod]
    apply Finset.prod_congr rfl
    intro k _
    simp only [f, p, Complex.norm_mul, Complex.star_def, Complex.norm_conj, hRoff, abs_mul,
      abs_neg, abs_of_nonneg (norm_nonneg _)]
  unfold cyclicGateInterference
  simp_rw [hp]
  rw [← Complex.ofReal_prod, Complex.ofReal_re, abs_mul, abs_mul]
  exact mul_le_mul_of_nonneg_left ((Complex.abs_re_le_norm (∏ k, f k)).trans_eq hnorm)
    (abs_nonneg _)

private theorem interference_flip_rotation (s : Equiv.Perm κ) (k₀ : κ)
    (L R : κ → Matrix Bool Bool ℂ) :
    cyclicGateInterference s (fun k => rotationForGate (L k) (decide (k = k₀)))
      (fun k => rotationForGate (R k) false) =
    -cyclicGateInterference s (fun k => rotationForGate (L k) false)
      (fun k => rotationForGate (R k) false) := by
  let f (k : κ) : ℂ :=
    (rotationForGate (L k) false false false * star (rotationForGate (L k) false false true)) *
      (rotationForGate (R k) false false false * star (rotationForGate (R k) false true false))
  let g (k : κ) : ℂ :=
    (rotationForGate (L k) (decide (k = k₀)) false false *
      star (rotationForGate (L k) (decide (k = k₀)) false true)) *
      (rotationForGate (R k) false false false * star (rotationForGate (R k) false true false))
  have he₀ : g k₀ = -f k₀ := by
    simp [f, g, rotationForGate, realGateRotation] <;> ring
  have he : ∏ k ∈ univ.erase k₀, g k = ∏ k ∈ univ.erase k₀, f k := by
    apply Finset.prod_congr rfl
    intro k hk
    simp only [g, f, decide_eq_false (Finset.mem_erase.mp hk).1]
  have hprod : ∏ k, g k = -(∏ k, f k) := by
    rw [← Finset.mul_prod_erase univ g (mem_univ k₀), he₀, he, neg_mul,
      Finset.mul_prod_erase univ f (mem_univ k₀)]
  change ((s.sign : ℤ) : ℝ) * (∏ k, g k).re = -(((s.sign : ℤ) : ℝ) * (∏ k, f k).re)
  rw [hprod, Complex.neg_re, mul_neg]

private theorem exists_opposite_endpoint_weight {x y : ℝ} (h : |x| ≤ |y|) :
    ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ x = t * y + (1 - t) * -y := by
  by_cases hy : y = 0
  · have hx : x = 0 := abs_eq_zero.mp (le_antisymm (by simpa only [hy, abs_zero] using h)
      (abs_nonneg _))
    exact ⟨0, le_rfl, zero_le_one, by simp [hx, hy]⟩
  let t := (1 + x / y) / 2
  have hquot : |x / y| ≤ 1 := by
    rw [abs_div, div_le_one (abs_pos.mpr hy)]
    exact h
  have hlo : -1 ≤ x / y := (abs_le.mp hquot).1
  have hhi : x / y ≤ 1 := (abs_le.mp hquot).2
  refine ⟨t, ?_, ?_, ?_⟩
  · dsimp only [t]
    linarith
  · dsimp only [t]
    linarith
  · dsimp only [t]
    field_simp [hy] <;> ring

private theorem orthogonal_of_real_unitary {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix ι ι ℂ) (hU : IsUnitary U) (hreal : ∀ i j, (U i j).im = 0) :
    ∃ O : Matrix.orthogonalGroup ι ℝ, Complex.ofRealHom.mapMatrix O.val = U := by
  let V : Matrix ι ι ℝ := Matrix.of fun i j => (U i j).re
  have hentry (i j : ι) : (V i j : ℂ) = U i j := by
    simpa only [V, Matrix.of_apply, hreal i j, Complex.ofReal_zero, zero_mul, add_zero] using
      Complex.re_add_im (U i j)
  have hprod : V * Vᵀ = 1 := by
    ext i j
    apply Complex.ofReal_injective
    have hone : (((1 : Matrix ι ι ℝ) i j : ℝ) : ℂ) = (1 : Matrix ι ι ℂ) i j := by
      by_cases h : i = j <;> simp [Matrix.one_apply, h]
    rw [hone, Matrix.mul_apply, Complex.ofReal_sum]
    simp only [Matrix.transpose_apply, Complex.ofReal_mul]
    have hconj (k : ι) : star (U j k) = (V j k : ℂ) := by
      rw [← hentry j k, Complex.star_def, Complex.conj_ofReal]
    have hh := congrFun (congrFun hU.1 i) j
    change (U * Uᴴ) i j = (1 : Matrix ι ι ℂ) i j at hh
    simpa only [Matrix.mul_apply, Matrix.conjTranspose_apply, hconj, hentry] using hh
  refine ⟨⟨V, (Matrix.mem_orthogonalGroup_iff _ ℝ).mpr hprod⟩, ?_⟩
  ext i j
  exact hentry i j

private theorem cyclicGateMixer_im_eq_zero (s : Equiv.Perm κ)
    (L R : κ → Matrix Bool Bool ℂ) (hL : ∀ k i j, (L k i j).im = 0)
    (hR : ∀ k i j, (R k i j).im = 0) (i j : κ × Bool) :
    (cyclicGateMixer s L R i j).im = 0 := by
  have hgate (e : κ × Bool ≃ κ × Bool) (G : κ → Matrix Bool Bool ℂ)
      (hG : ∀ k i j, (G k i j).im = 0) (u v : κ × Bool) :
      (blockGateMatrix e G u v).im = 0 := by
    simp only [blockGateMatrix, Matrix.of_apply]
    split
    · exact hG _ _ _
    · exact Complex.zero_im
  rw [cyclicGateMixer, Matrix.mul_apply, Complex.im_sum]
  exact Finset.sum_eq_zero fun k _ => by
    rw [Complex.mul_im, hgate _ L hL, hgate _ R hR, mul_zero, zero_mul, add_zero]

/-- Two real orthogonal gate products give one convex combination for
all squared minors of a unitary gate product on an alternating cycle. -/
theorem exists_cyclic_gate_orthogonal_minor_endpoints (s : Equiv.Perm κ)
    (hs : TraversesAllIndices s) (hne : s ≠ 1) (L R : κ → Matrix Bool Bool ℂ)
    (hL : ∀ k, IsUnitary (L k)) (hR : ∀ k, IsUnitary (R k)) :
    ∃ (P Q : Matrix.orthogonalGroup (κ × Bool) ℝ) (t : ℝ), 0 ≤ t ∧ t ≤ 1 ∧
      ∀ I J : Finset (κ × Bool), subsetMinorSq (cyclicGateMixer s L R) I J =
        t * subsetMinorSq (Complex.ofRealHom.mapMatrix P.val) I J +
          (1 - t) * subsetMinorSq (Complex.ofRealHom.mapMatrix Q.val) I J := by
  classical
  let k₀ : κ := Classical.choice (nonempty_of_cycle_ne_one hne)
  let L₀ k := rotationForGate (L k) false
  let R₀ k := rotationForGate (R k) false
  let L₁ k := rotationForGate (L k) (decide (k = k₀))
  have hL₀ (k : κ) : IsUnitary (L₀ k) := rotationForGate_unitary _ (hL k) _
  have hR₀ (k : κ) : IsUnitary (R₀ k) := rotationForGate_unitary _ (hR k) _
  have hL₁ (k : κ) : IsUnitary (L₁ k) := rotationForGate_unitary _ (hL k) _
  have hflip : cyclicGateInterference s L₁ R₀ = -cyclicGateInterference s L₀ R₀ :=
    interference_flip_rotation s k₀ L R
  obtain ⟨t, ht₀, ht₁, ht⟩ := exists_opposite_endpoint_weight (abs_interference_le_rotation s L R hR)
  rw [← hflip] at ht
  have hreal₀ : ∀ i j, (cyclicGateMixer s L₀ R₀ i j).im = 0 :=
    cyclicGateMixer_im_eq_zero s L₀ R₀ (fun k => rotationForGate_im (L k) false)
      (fun k => rotationForGate_im (R k) false)
  have hreal₁ : ∀ i j, (cyclicGateMixer s L₁ R₀ i j).im = 0 :=
    cyclicGateMixer_im_eq_zero s L₁ R₀ (fun k => rotationForGate_im (L k) (decide (k = k₀)))
      (fun k => rotationForGate_im (R k) false)
  obtain ⟨P, hP⟩ := orthogonal_of_real_unitary (cyclicGateMixer s L₀ R₀)
    (blockGateMatrix_mul_unitary _ _ L₀ R₀ hL₀ hR₀) hreal₀
  obtain ⟨Q, hQ⟩ := orthogonal_of_real_unitary (cyclicGateMixer s L₁ R₀)
    (blockGateMatrix_mul_unitary _ _ L₁ R₀ hL₁ hR₀) hreal₁
  refine ⟨P, Q, t, ht₀, ht₁, ?_⟩
  rw [hP, hQ]
  exact cyclicGate_minor_affine s hs hne L R L₀ R₀ L₁ R₀ hL hR hL₀ hR₀ hL₁ hR₀
    (cyclicIndependentWeight_congr_prob L R L₀ R₀
      (fun k => rotationForGate_probability (L k) false) (fun k => rotationForGate_probability (R k) false))
    (cyclicIndependentWeight_congr_prob L R L₁ R₀
      (fun k => rotationForGate_probability (L k) (decide (k = k₀)))
      (fun k => rotationForGate_probability (R k) false))
    t ht

/-- The real orthogonal inclusion in a cycle's dimension gives the
inclusion for all two-layer unitary gate products on that cycle. -/
theorem holds_cyclic_gate_of_orthogonal (s : Equiv.Perm κ) (hs : TraversesAllIndices s)
    (hne : s ≠ 1) (L R : κ → Matrix Bool Bool ℂ)
    (hL : ∀ k, IsUnitary (L k)) (hR : ∀ k, IsUnitary (R k))
    (hO : OrthogonalConjecture (κ × Bool)) (a b : κ × Bool → ℂ) :
    Holds a b (cyclicGateMixer s L R) := by
  obtain ⟨P, Q, t, ht₀, ht₁, hm⟩ := exists_cyclic_gate_orthogonal_minor_endpoints s hs hne L R hL hR
  exact holds_of_subsetMinorSq_convex_combination a b
    (blockGateMatrix_mul_unitary _ _ L R hL hR) (isUnitary_ofReal_orthogonal P)
    (isUnitary_ofReal_orthogonal Q) t ht₀ ht₁ hm (hO a b P) (hO a b Q)

private theorem blockSwitch_preserves_equal_pair {ι : Type*} [DecidableEq ι]
    (e : κ × Bool ≃ ι) (v : ι → ℂ) (k : κ) (h : v (e (k, false)) = v (e (k, true)))
    (x y : κ → Bool) (hxy : ∀ l ≠ k, x l = y l) (j : ι) :
    v (blockSwitch e x j) = v (blockSwitch e y j) := by
  obtain ⟨⟨l, b⟩, rfl⟩ := e.surjective j
  rw [blockSwitch_apply, blockSwitch_apply]
  by_cases hl : l = k
  · subst l
    have hconstant (c d : Bool) : v (e (k, c)) = v (e (k, d)) := by
      cases c <;> cases d
      · rfl
      · exact h
      · exact h.symm
      · rfl
    exact hconstant _ _
  · rw [hxy l hl]

/-- Equal spectral values at either gate of an alternating cycle cancel the
determinant interference. Independent switches suffice for all gate biases. -/
theorem holds_cyclic_gate_of_equal_spectral_pair (s : Equiv.Perm κ)
    (hs : TraversesAllIndices s) (hne : s ≠ 1) (L R : κ → Matrix Bool Bool ℂ)
    (hL : ∀ k, IsUnitary (L k)) (hR : ∀ k, IsUnitary (R k)) (a b : κ × Bool → ℂ)
    (hpair : (∃ k, a (k, false) = a (k, true)) ∨
      ∃ k, b (cyclicRightChart s (k, false)) = b (cyclicRightChart s (k, true))) :
    Holds a b (cyclicGateMixer s L R) := by
  classical
  let eL : κ × Bool ≃ κ × Bool := Equiv.refl _
  let eR := cyclicRightChart s
  let p := twoLayerSwitch eL eR
  let q (x : κ ⊕ κ → Bool) := matchingProduct a b (p x)
  have hq (x : κ ⊕ κ → Bool) :
      q x = ∏ j, (a (blockSwitch eL (x ∘ Sum.inl) j) + b (blockSwitch eR (x ∘ Sum.inr) j)) := by
    let τ := blockSwitch eR (x ∘ Sum.inr)
    unfold q matchingProduct
    rw [← Equiv.prod_comp τ.symm (fun j => a (p x j) + b j)]
    apply Finset.prod_congr rfl
    intro j _
    change a (blockSwitch eL (x ∘ Sum.inl) (τ (τ.symm j))) + b (τ.symm j) = _
    rw [τ.apply_symm_apply, show τ.symm = τ from blockSwitch_symm _ _]
  have hflip : ∃ g : κ ⊕ κ, ∀ x, q (toggleSwitch g x) = q x := by
    rcases hpair with ⟨k, hk⟩ | ⟨k, hk⟩
    · refine ⟨Sum.inl k, fun x => ?_⟩
      rw [hq, hq]
      have hright : toggleSwitch (Sum.inl k) x ∘ Sum.inr = x ∘ Sum.inr := by
        funext l
        simp [toggleSwitch]
      apply Finset.prod_congr rfl
      intro j _
      rw [hright, blockSwitch_preserves_equal_pair eL a k hk
        (toggleSwitch (Sum.inl k) x ∘ Sum.inl) (x ∘ Sum.inl) (fun l hl => by
          simp [toggleSwitch, hl]) j]
    · refine ⟨Sum.inr k, fun x => ?_⟩
      rw [hq, hq]
      have hleft : toggleSwitch (Sum.inr k) x ∘ Sum.inl = x ∘ Sum.inl := by
        funext l
        simp [toggleSwitch]
      apply Finset.prod_congr rfl
      intro j _
      rw [hleft, blockSwitch_preserves_equal_pair eR b k hk
        (toggleSwitch (Sum.inr k) x ∘ Sum.inr) (x ∘ Sum.inr) (fun l hl => by
          simp [toggleSwitch, hl]) j]
  obtain ⟨g, hg⟩ := hflip
  have hzero : ∑ x : κ ⊕ κ → Bool, (switchParity x : ℂ) * q x = 0 := by
    apply Complex.ext
    · simpa only [Complex.re_sum, Complex.zero_re, Complex.re_ofReal_mul, mul_comm] using
        sum_weighted_switchParity_eq_zero (fun x => (q x).re) g univ (by simp)
          (fun x => congrArg Complex.re (hg x))
    · simpa only [Complex.im_sum, Complex.zero_im, Complex.im_ofReal_mul, mul_comm] using
        sum_weighted_switchParity_eq_zero (fun x => (q x).im) g univ (by simp)
          (fun x => congrArg Complex.im (hg x))
  have hd := cyclic_gate_determinant_eq_independent_add_interference s hs hne L R hL hR a b
  change determinantValue a b (cyclicGateMixer s L R) =
    (∑ x, (cyclicIndependentWeight L R x : ℂ) * q x) +
      (cyclicGateInterference s L R : ℂ) * ∑ x, (switchParity x : ℂ) * q x at hd
  unfold Holds
  rw [hd, hzero, mul_zero, add_zero]
  refine mem_convexHull_of_exists_fintype (cyclicIndependentWeight L R) q ?_
    (cyclicIndependentWeight_sum L R hL hR) (fun x => ⟨p x, rfl⟩) ?_
  · intro x
    unfold cyclicIndependentWeight gateSwitchProbability
    exact mul_nonneg (Finset.prod_nonneg fun _ _ => Complex.normSq_nonneg _)
      (Finset.prod_nonneg fun _ _ => Complex.normSq_nonneg _)
  · simp only [Complex.real_smul]

end

end MOC
