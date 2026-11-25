import MOC.ExactProfileLocus

/-! Exact zero-stratum profiles. The diagonal similarity and additive
gauge preserve each prescribed zero entry, not just vanishing products. -/

open BigOperators Matrix Set MvPolynomial
open scoped NNReal

namespace MOC

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem exists_bounded_kernel_of_normalized_profile_with_zeros
    (Z : ι → ι → Prop) (K : Matrix ι ι ℂ) (hZ : ∀ i j, Z i j → K i j = 0)
    (hd : ∀ i, K i i = 1) (hK : VanishingThreeMinors K)
    (hp : ∀ σ : Equiv.Perm ι, ‖kernelMatchingProduct K σ‖ ≤ 1) :
    ∃ M : Matrix ι ι ℂ, (∀ i j, ‖M i j‖ ≤ 1) ∧ (∀ i, M i i = 1) ∧
      VanishingThreeMinors M ∧ (∀ i j, Z i j → M i j = 0) ∧
        kernelMatchingProduct M = kernelMatchingProduct K := by
  have hp' (σ : Equiv.Perm ι) : ‖∏ i, K i (σ i)‖ ≤ 1 := by
    have he : (∏ i, K i (σ i)) = kernelMatchingProduct K σ.symm := by
      unfold kernelMatchingProduct
      rw [← Equiv.prod_comp σ (fun j => K (σ.symm j) j)]
      simp only [Function.comp_apply, Equiv.symm_apply_apply]
    rw [he]
    exact hp _
  obtain ⟨s, hs, hsb⟩ := exists_matching_norm_potential K hd hp'
  let d (i : ι) : ℂ := (s i : ℝ)
  have hpos (i : ι) : 0 < (s i : ℝ) := zero_lt_one.trans_le (by exact_mod_cast hs i)
  have hd' (i : ι) : d i ≠ 0 := Complex.ofReal_ne_zero.mpr (hpos i).ne'
  let M : Matrix ι ι ℂ := Matrix.of fun i j => (d i)⁻¹ * K i j * d j
  refine ⟨M, ?_, ?_, threeMinors_reweight K (fun i => (d i)⁻¹) d hK, ?_, ?_⟩
  · intro i j
    change ‖(d i)⁻¹ * K i j * d j‖ ≤ 1
    simp only [norm_mul, norm_inv, d, Complex.norm_real, Real.norm_of_nonneg (hpos _).le]
    rw [inv_mul_eq_div, div_mul_eq_mul_div]
    exact (div_le_one₀ (hpos i)).mpr (by exact_mod_cast hsb i j)
  · intro i
    change (d i)⁻¹ * K i i * d i = 1
    rw [hd, mul_one, inv_mul_cancel₀ (hd' i)]
  · intro i j hij
    change (d i)⁻¹ * K i j * d j = 0
    rw [hZ i j hij, mul_zero, zero_mul]
  · funext σ
    simp only [kernelMatchingProduct, M, Matrix.of_apply, Finset.prod_mul_distrib,
      Equiv.prod_comp σ (fun i => (d i)⁻¹), Finset.prod_inv_distrib]
    have hnz : (∏ i, d i) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => hd' i
    rw [mul_right_comm, inv_mul_cancel₀ hnz, one_mul]

/-- Relative to a modulus-maximizing diagonal, the normalized rank-two
matching profiles form a compact set. -/
private theorem isCompact_normalized_rankTwo_matching_profiles_with_zeros (Z : ι → ι → Prop) :
    IsCompact {p : Equiv.Perm ι → ℂ | ∃ K : Matrix ι ι ℂ,
      (∀ i, K i i = 1) ∧ VanishingThreeMinors K ∧ (∀ i j, Z i j → K i j = 0) ∧
        (∀ σ, ‖p σ‖ ≤ 1) ∧ kernelMatchingProduct K = p} := by
  let C : Set (Matrix ι ι ℂ) := Set.univ.pi fun _ =>
    Set.univ.pi fun _ => Metric.closedBall 0 1
  let H : Set (Matrix ι ι ℂ) := {K | (∀ i, K i i = 1) ∧ VanishingThreeMinors K ∧ ∀ i j, Z i j → K i j = 0}
  have hC : IsCompact C := isCompact_univ_pi fun _ =>
    isCompact_univ_pi fun _ => isCompact_closedBall _ _
  have hH : IsClosed H := by
    have hd : IsClosed {K : Matrix ι ι ℂ | ∀ i, K i i = 1} := by
      rw [Set.setOf_forall]
      exact isClosed_iInter fun i => isClosed_eq (continuous_id.matrix_elem i i) continuous_const
    have hm : IsClosed {K : Matrix ι ι ℂ | VanishingThreeMinors K} := by
      unfold VanishingThreeMinors
      simp only [Set.setOf_forall]
      refine isClosed_iInter fun a => isClosed_iInter fun b => isClosed_eq ?_ continuous_const
      exact (continuous_id.matrix_submatrix a b).matrix_det
    have hz : IsClosed {K : Matrix ι ι ℂ | ∀ i j, Z i j → K i j = 0} := by
      simp only [Set.setOf_forall]
      exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ =>
        isClosed_eq (continuous_id.matrix_elem i j) continuous_const
    exact hd.inter (hm.inter hz)
  have hc : Continuous (kernelMatchingProduct (ι := ι)) := by
    apply continuous_pi
    intro σ
    exact continuous_finset_prod _ (fun j _ => continuous_id.matrix_elem (σ j) j)
  have himage : kernelMatchingProduct '' (C ∩ H) =
      {p : Equiv.Perm ι → ℂ | ∃ K : Matrix ι ι ℂ,
        (∀ i, K i i = 1) ∧ VanishingThreeMinors K ∧ (∀ i j, Z i j → K i j = 0) ∧
          (∀ σ, ‖p σ‖ ≤ 1) ∧ kernelMatchingProduct K = p} := by
    ext p
    constructor
    · rintro ⟨K, ⟨hbound, hd, hK, hZ⟩, rfl⟩
      refine ⟨K, hd, hK, hZ, ?_, rfl⟩
      intro σ
      rw [kernelMatchingProduct, norm_prod]
      refine Finset.prod_le_one (fun j _ => norm_nonneg _) fun j _ => ?_
      have h := Set.mem_pi.mp (Set.mem_pi.mp hbound (σ j) (Set.mem_univ _))
        j (Set.mem_univ _)
      simpa only [Metric.mem_closedBall, dist_zero_right] using h
    · rintro ⟨K, hd, hK, hZ, hp, rfl⟩
      obtain ⟨M, hbound, hd', hM, hZ', hm⟩ :=
        exists_bounded_kernel_of_normalized_profile_with_zeros Z K hZ hd hK hp
      refine ⟨M, ⟨?_, hd', hM, hZ'⟩, hm⟩
      refine Set.mem_pi.mpr fun i _ => Set.mem_pi.mpr fun j _ => ?_
      simpa only [Metric.mem_closedBall, dist_zero_right] using hbound i j
  rw [← himage]
  exact (hC.inter_right hH).image hc

omit [DecidableEq ι] in
private theorem reindexed_column_scaled_profile (K : Matrix ι ι ℂ)
    (r : Equiv.Perm ι) (d : ι → ℂ) (hK : VanishingThreeMinors K) :
    let M : Matrix ι ι ℂ := Matrix.of fun i j => K (r i) j * d j
    VanishingThreeMinors M ∧ ∀ σ : Equiv.Perm ι,
      kernelMatchingProduct M σ = (∏ j, d j) * kernelMatchingProduct K (r * σ) := by
  dsimp only
  constructor
  · intro a b
    have hsub : (Matrix.of fun i j => K (r i) j * d j).submatrix a b =
        Matrix.of fun i j => d (b j) * (K.submatrix (r ∘ a) b) i j := by
      ext i j
      simp only [Matrix.submatrix_apply, Matrix.of_apply, Function.comp_apply, mul_comm]
    rw [hsub, Matrix.det_mul_row, hK (r ∘ a) b, mul_zero]
  · intro σ
    simp only [kernelMatchingProduct, Matrix.of_apply, Finset.prod_mul_distrib,
      Equiv.Perm.mul_apply]
    exact mul_comm _ _

private theorem isClosed_rankTwo_profiles_with_zeros [Nonempty ι] (Z : ι → ι → Prop) :
    IsClosed {p : Equiv.Perm ι → ℂ | ∃ K : Matrix ι ι ℂ,
      VanishingThreeMinors K ∧ (∀ i j, Z i j → K i j = 0) ∧ kernelMatchingProduct K = p} := by
  classical
  let V := Equiv.Perm ι → ℂ
  let N (r : Equiv.Perm ι) : Set V := {p | ∃ K : Matrix ι ι ℂ,
    (∀ i, K i i = 1) ∧ VanishingThreeMinors K ∧
      (∀ i j, Z (r i) j → K i j = 0) ∧ (∀ σ, ‖p σ‖ ≤ 1) ∧ kernelMatchingProduct K = p}
  have hN (r : Equiv.Perm ι) : IsCompact (N r) :=
    isCompact_normalized_rankTwo_matching_profiles_with_zeros (fun i j => Z (r i) j)
  let C (r : Equiv.Perm ι) : Set V := {p | ∃ u : N r, ∀ σ,
    p σ = p r * u.val (r⁻¹ * σ)}
  have hC (r : Equiv.Perm ι) : IsClosed (C r) := by
    letI : CompactSpace (N r) := isCompact_iff_compactSpace.mp (hN r)
    let D : Set (V × N r) := {w | ∀ σ, w.1 σ = w.1 r * w.2.val (r⁻¹ * σ)}
    have hD : IsClosed D := by
      change IsClosed {w : V × N r | ∀ σ, w.1 σ = w.1 r * w.2.val (r⁻¹ * σ)}
      rw [Set.setOf_forall]
      exact isClosed_iInter fun σ => isClosed_eq ((continuous_apply σ).comp continuous_fst)
        (((continuous_apply r).comp continuous_fst).mul
          ((continuous_apply (r⁻¹ * σ)).comp (continuous_subtype_val.comp continuous_snd)))
    have hDC : Prod.fst '' D = C r := by
      ext p
      constructor
      · rintro ⟨⟨_, u⟩, hu, rfl⟩
        exact ⟨u, hu⟩
      · rintro ⟨u, hu⟩
        exact ⟨(p, u), hu, rfl⟩
    rw [← hDC]
    exact isClosedMap_fst_of_compactSpace D hD
  have hset : {p : V | ∃ K : Matrix ι ι ℂ,
      VanishingThreeMinors K ∧ (∀ i j, Z i j → K i j = 0) ∧ kernelMatchingProduct K = p} = {0} ∪ ⋃ r, C r := by
    ext p
    constructor
    · rintro ⟨K, hK, hZ, hp⟩
      by_cases hzero : p = 0
      · exact Set.mem_union_left _ (Set.mem_singleton_iff.mpr hzero)
      obtain ⟨r, _, hr⟩ := Finset.exists_max_image Finset.univ (fun σ => ‖p σ‖)
        ⟨1, Finset.mem_univ _⟩
      have hpr : p r ≠ 0 := by
        intro hz
        apply hzero
        funext σ
        have h := hr σ (Finset.mem_univ _)
        rw [hz, norm_zero] at h
        exact norm_le_zero_iff.mp h
      have he : (∏ j, K (r j) j) = p r := congrFun hp r
      have hentry (j : ι) : K (r j) j ≠ 0 :=
        Finset.prod_ne_zero_iff.mp (he.trans_ne hpr) j (Finset.mem_univ _)
      let d (j : ι) := (K (r j) j)⁻¹
      let M : Matrix ι ι ℂ := Matrix.of fun i j => K (r i) j * d j
      obtain ⟨hM, hval⟩ := reindexed_column_scaled_profile K r d hK
      have hdprod : (∏ j, d j) = (p r)⁻¹ := by
        simp only [d, Finset.prod_inv_distrib, he]
      have hquot (σ : Equiv.Perm ι) : kernelMatchingProduct M σ = (p r)⁻¹ * p (r * σ) := by
        rw [hval σ, hdprod, congrFun hp (r * σ)]
      have hd (j : ι) : M j j = 1 := mul_inv_cancel₀ (hentry j)
      have hbound (σ : Equiv.Perm ι) : ‖kernelMatchingProduct M σ‖ ≤ 1 := by
        rw [hquot, norm_mul, norm_inv, inv_mul_eq_div]
        exact (div_le_one₀ (norm_pos_iff.mpr hpr)).mpr (hr (r * σ) (Finset.mem_univ _))
      have hZM (i j : ι) (hij : Z (r i) j) : M i j = 0 := by
        change K (r i) j * d j = 0
        rw [hZ _ _ hij, zero_mul]
      let u : N r := ⟨kernelMatchingProduct M, M, hd, hM, hZM, hbound, rfl⟩
      refine Set.mem_union_right _ (Set.mem_iUnion.mpr ⟨r, u, ?_⟩)
      intro σ
      change p σ = p r * kernelMatchingProduct M (r⁻¹ * σ)
      rw [hquot, ← mul_assoc, mul_inv_cancel₀ hpr, one_mul]
      simp
    · intro hp
      let j₀ := Classical.choice (inferInstance : Nonempty ι)
      rcases hp with hzero | hc
      · rw [Set.mem_singleton_iff.mp hzero]
        refine ⟨0, fun a b => by simp, (fun _ _ _ => rfl), ?_⟩
        funext σ
        change (∏ _ : ι, (0 : ℂ)) = 0
        exact Finset.prod_eq_zero (Finset.mem_univ j₀) rfl
      · obtain ⟨r, hr⟩ := Set.mem_iUnion.mp hc
        obtain ⟨u, hu⟩ := hr
        obtain ⟨K, _, hK, hZ, _, hval⟩ := u.property
        let d (j : ι) := if j = j₀ then p r else 1
        have hdprod : (∏ j, d j) = p r := by
          rw [Finset.prod_eq_single j₀]
          · simp [d]
          · intro j _ hj
            simp [d, hj]
          · simp
        obtain ⟨hM, hMp⟩ := reindexed_column_scaled_profile K r⁻¹ d hK
        refine ⟨Matrix.of (fun i j => K (r⁻¹ i) j * d j), hM, ?_, ?_⟩
        · intro i j hij
          change K (r⁻¹ i) j * d j = 0
          rw [hZ, zero_mul]
          simpa using hij
        · funext σ
          rw [hMp σ, hdprod, congrFun hval (r⁻¹ * σ)]
          exact (hu σ).symm
  rw [hset]
  exact isClosed_singleton.union (isClosed_iUnion_of_finite hC)


/-- Marked kernel zero constraints and the additive gauge yield the same
exact matching profile locus. The zero profile is included. -/
theorem additive_profiles_with_zeros_eq_rankTwo [Nonempty ι] (Z : ι → ι → Prop) :
    {p : Equiv.Perm ι → ℂ | ∃ a b : ι → ℂ,
      (∀ i j, Z i j → a i + b j = 0) ∧ matchingProduct a b = p} =
    {p : Equiv.Perm ι → ℂ | ∃ K : Matrix ι ι ℂ,
      VanishingThreeMinors K ∧ (∀ i j, Z i j → K i j = 0) ∧ kernelMatchingProduct K = p} := by
  classical
  ext p
  constructor
  · rintro ⟨a, b, hZ, hp⟩
    refine ⟨Matrix.of (fun i j => a i + b j), ?_, hZ, hp⟩
    intro r c
    simp only [Matrix.det_fin_three, Matrix.submatrix_apply, Matrix.of_apply]
    ring
  · rintro ⟨K, hK, hZ, hp⟩
    by_cases hz : p = 0
    · refine ⟨0, 0, fun _ _ _ => by simp, ?_⟩
      funext τ
      rw [hz]
      change (∏ j : ι, ((0 : ι → ℂ) (τ j) + (0 : ι → ℂ) j)) = 0
      exact Finset.prod_eq_zero (Finset.mem_univ (Classical.choice inferInstance)) (by simp)
    obtain ⟨σ, hσ⟩ : ∃ σ, p σ ≠ 0 := by
      contrapose! hz
      exact funext hz
    have hprod : (∏ j, K (σ j) j) ≠ 0 := (congrFun hp σ).trans_ne hσ
    have hentry (j : ι) : K (σ j) j ≠ 0 :=
      Finset.prod_ne_zero_iff.mp hprod j (Finset.mem_univ _)
    have hrow (i : ι) : ∃ j, K i j ≠ 0 :=
      ⟨σ.symm i, by simpa only [Equiv.apply_symm_apply] using hentry (σ.symm i)⟩
    obtain ⟨L, R, α, β, hL, hR, hg⟩ :=
      exists_additive_gauge_of_three_minors_eq_zero K hK hrow (fun j => ⟨σ j, hentry j⟩)
    let d := (∏ i, L i) * ∏ j, R j
    have hprofile (τ : Equiv.Perm ι) : p τ = d * matchingProduct α β τ := by
      rw [← congrFun hp τ]
      simp only [kernelMatchingProduct, hg, Finset.prod_mul_distrib, Equiv.prod_comp τ L,
        d, matchingProduct]
    obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq d (Fintype.card_pos (α := ι))
    refine ⟨fun i => c * α i, fun i => c * β i, ?_, ?_⟩
    · intro i j hij
      have he := hZ i j hij
      rw [hg] at he
      have hz' : α i + β j = 0 :=
        (mul_eq_zero.mp he).resolve_left (mul_ne_zero (hL i) (hR j))
      rw [← mul_add, hz', mul_zero]
    · funext τ
      rw [hprofile τ]
      simp only [matchingProduct, ← mul_add, Finset.prod_mul_distrib, Finset.prod_const,
        Finset.card_univ, hc]

/-- The profile image of additive spectra with any fixed set of marked
zero entries is closed, including when extra zero entries arise in a limit. -/
theorem isClosed_additive_matching_profiles_with_zeros [Nonempty ι] (Z : ι → ι → Prop) :
    IsClosed {p : Equiv.Perm ι → ℂ | ∃ a b : ι → ℂ,
      (∀ i j, Z i j → a i + b j = 0) ∧ matchingProduct a b = p} := by
  rw [additive_profiles_with_zeros_eq_rankTwo]
  exact isClosed_rankTwo_profiles_with_zeros Z


/-- Each zero entry identifies its row label with its signed column label. -/
def MarkedZeroRel (Z : ι → ι → Prop) : (ι ⊕ ι) → (ι ⊕ ι) → Prop
  | .inl i, .inr j => Z i j
  | _, _ => False

/-- One variable suffices for each equivalence class generated by the
prescribed zero entries. Column variables represent negated partners. -/
noncomputable def markedZeroProfileCoordinate (Z : ι → ι → Prop) (σ : Equiv.Perm ι) :
    MvPolynomial (Quot (MarkedZeroRel Z)) ℂ :=
  ∏ j, (X (Quot.mk (MarkedZeroRel Z) (Sum.inl (σ j))) -
    X (Quot.mk (MarkedZeroRel Z) (Sum.inr j)))

/-- The exact profile image with arbitrary prescribed zeros is the prime
zero locus of its polynomial parameterization. This does not assert that
unmarked entries are nonzero or give the dimension of the locus. -/
theorem exact_matching_profiles_with_zeros_eq_prime_zeroLocus [Nonempty ι] (Z : ι → ι → Prop) :
    {p : Equiv.Perm ι → ℂ | ∃ a b : ι → ℂ,
      (∀ i j, Z i j → a i + b j = 0) ∧ matchingProduct a b = p} =
      zeroLocus (RingHom.ker (aeval (markedZeroProfileCoordinate Z))) := by
  classical
  let q := Quot.mk (MarkedZeroRel Z)
  letI : Fintype (Quot (MarkedZeroRel Z)) :=
    Fintype.ofSurjective q (fun x => Quot.exists_rep x)
  have he : (Set.range fun x : Quot (MarkedZeroRel Z) → ℂ =>
      fun σ => eval x (markedZeroProfileCoordinate Z σ)) =
      {p : Equiv.Perm ι → ℂ | ∃ a b : ι → ℂ,
        (∀ i j, Z i j → a i + b j = 0) ∧ matchingProduct a b = p} := by
    ext p
    constructor
    · rintro ⟨x, rfl⟩
      refine ⟨fun i => x (q (Sum.inl i)), fun j => -x (q (Sum.inr j)), ?_, ?_⟩
      · intro i j hij
        have hh : q (Sum.inl i) = q (Sum.inr j) := Quot.sound hij
        change x (q (Sum.inl i)) + -x (q (Sum.inr j)) = 0
        rw [hh, add_neg_cancel]
      · funext σ
        simp only [matchingProduct, markedZeroProfileCoordinate, map_prod, map_sub, map_add,
          map_neg, eval_X, sub_eq_add_neg, q]
    · rintro ⟨a, b, hab, rfl⟩
      let f : ι ⊕ ι → ℂ := Sum.elim a (fun j => -b j)
      have hf (y z : ι ⊕ ι) (h : MarkedZeroRel Z y z) : f y = f z := by
        cases y with
        | inl i =>
          cases z with
          | inl j => exact h.elim
          | inr j => exact eq_neg_of_add_eq_zero_left (hab i j h)
        | inr i =>
          cases z <;> exact h.elim
      let x := Quot.lift f hf
      refine ⟨x, ?_⟩
      funext σ
      simp only [matchingProduct, markedZeroProfileCoordinate, map_prod, map_sub, eval_X,
        x, Quot.lift_mk, f, Sum.elim_inl, Sum.elim_inr, sub_neg_eq_add]
  rw [← he]
  apply polynomial_map_range_eq_zeroLocus_of_isClosed
  rw [he]
  exact isClosed_additive_matching_profiles_with_zeros Z

omit [DecidableEq ι] in
theorem markedZeroProfileIdeal_isPrime (Z : ι → ι → Prop) :
    (RingHom.ker (aeval (markedZeroProfileCoordinate Z) :
      MvPolynomial (Equiv.Perm ι) ℂ →ₐ[ℂ] MvPolynomial (Quot (MarkedZeroRel Z)) ℂ)).IsPrime :=
  RingHom.ker_isPrime _

end MOC
