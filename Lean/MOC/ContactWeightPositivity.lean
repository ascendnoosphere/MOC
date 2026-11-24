import MOC.MatchingTriangle
import MOC.FiniteMinorLaw
import MOC.Householder
import MOC.Support

/-!
# Contact gap certificates

The Leibniz coefficients depend on the mixer, not on the contact profile.
Their image-fiber sums, however, are squared minors. Positive certificates
and probability laws for a projected objective do not require positivity
of the individual coefficients.
-/

open BigOperators Finset Matrix

namespace MOC

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- If the real gap is a nonnegative sum of subset-image events, equality
holds exactly when every active minor vanishes. In particular any active
nonzero minor forces a strictly positive gap. -/
theorem contact_gap_zero_iff_active_minors_zero
    {κ : Type*} [Fintype κ] (a b : ι → ℂ) (η : ℂ) (H : ℝ)
    (U : Matrix ι ι ℂ) (hU : IsUnitary U) (I J : κ → Finset ι)
    (c : κ → ℝ) (hc : ∀ k, 0 ≤ c k)
    (hgap : ∀ σ : Equiv.Perm ι, (η * matchingProduct a b σ).re - H =
      ∑ k, if (J k).map σ.toEmbedding = I k then c k else 0) :
    (η * determinantValue a b U).re = H ↔
      ∀ k, 0 < c k → subsetMinorSq U (I k) (J k) = 0 := by
  rw [← sub_eq_zero, gap_eq_minor_decomposition a b η H U hU I J c hgap]
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun k _ => mul_nonneg (hc k) (subsetMinorSq_nonneg U _ _))]
  constructor
  · intro h k hk
    exact (mul_eq_zero.mp (h k (Finset.mem_univ k))).resolve_left (ne_of_gt hk)
  · intro h k _
    rcases (hc k).eq_or_lt with hz | hp
    · simp [← hz]
    · simp [h k hp]

/-- A projected matching product constant along image fibers of one subset
admits a positive law for that objective, even if the unprojected product
does not factor through that subset. The law is the squared-minor law on
the image subsets, not a common law for every minor. -/
theorem contact_projected_hull_of_subset_fiber
    (a b : ι → ℂ) (U : Matrix ι ι ℂ) (hU : IsUnitary U) (η : ℂ)
    (J : Finset ι) (g : Finset ι → ℝ)
    (hg : ∀ σ : Equiv.Perm ι, (η * matchingProduct a b σ).re = g (J.map σ.toEmbedding)) :
    (η * determinantValue a b U).re ∈ convexHull ℝ
      (Set.range (fun σ : Equiv.Perm ι => (η * matchingProduct a b σ).re)) := by
  classical
  let p (σ : Equiv.Perm ι) := J.map σ.toEmbedding
  let S := (Finset.univ : Finset (Equiv.Perm ι)).image p
  have hm (I : Finset ι) :
      (∑ σ ∈ Finset.univ.filter (fun σ : Equiv.Perm ι => p σ = I), realSignedWeight U σ) =
        subsetMinorSq U I J := by
    simpa only [Complex.re_sum, Complex.ofReal_re, realSignedWeight] using
      congrArg Complex.re (sum_signedWeight_image_eq_subsetMinorSq U hU I J)
  have hp (σ : Equiv.Perm ι) (hσ : σ ∈ Finset.univ) : p σ ∈ S :=
    Finset.mem_image_of_mem p hσ
  have hs : ∑ I ∈ S, subsetMinorSq U I J = 1 := by
    simp_rw [← hm]
    rw [Finset.sum_fiberwise_of_maps_to hp, sum_realSignedWeight U hU]
  have hd :
      (η * determinantValue a b U).re = ∑ σ, realSignedWeight U σ * g (p σ) := by
    rw [← real_signed_determinant a b U hU, Finset.mul_sum, Complex.re_sum]
    apply Finset.sum_congr rfl
    intro σ _
    rw [mul_left_comm η, Complex.re_ofReal_mul, hg]
  rw [hd, ← Finset.sum_fiberwise_of_maps_to hp]
  have he (I : Finset ι) :
      (∑ σ ∈ Finset.univ.filter (fun σ : Equiv.Perm ι => p σ = I),
        realSignedWeight U σ * g (p σ)) = subsetMinorSq U I J * g I := by
    rw [← hm I, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro σ hσ
    rw [(Finset.mem_filter.mp hσ).2]
  simp_rw [he]
  exact (convex_convexHull ℝ _).sum_mem (fun I _ => subsetMinorSq_nonneg U I J) hs
    (fun I hI => by
      obtain ⟨σ, _, rfl⟩ := Finset.mem_image.mp hI
      exact subset_convexHull ℝ _ ⟨σ, hg σ⟩)

/-- An exact test for a contact configuration with one constant, positive
off-contact gap. The relevant statistic is the signed mass of the whole
off-contact stratum, not the sign on any individual label. -/
theorem contact_two_level_support_iff
    (a b : ι → ℂ) (U : Matrix ι ι ℂ) (hU : IsUnitary U) (η : ℂ)
    (r : Equiv.Perm ι) (T : Finset (Equiv.Perm ι)) (δ : ℝ) (hδ : 0 < δ)
    (hg : ∀ σ : Equiv.Perm ι, matchingGap a b η r σ = if σ ∈ T then 0 else δ) :
    (η * determinantValue a b U).re ≤ (η * matchingProduct a b r).re ↔
      0 ≤ ∑ σ ∈ Tᶜ, realSignedWeight U σ := by
  rw [← sub_nonneg, support_gap_eq a b U hU η r]
  simp_rw [hg, mul_ite, mul_zero]
  have hsum :
      (∑ σ : Equiv.Perm ι, if σ ∈ T then 0 else realSignedWeight U σ * δ) =
        (∑ σ ∈ Tᶜ, realSignedWeight U σ) * δ := by
    rw [Finset.sum_mul, ← Finset.filter_univ_mem (Tᶜ)]
    simp [Finset.sum_filter]
  rw [hsum]
  exact mul_nonneg_iff_of_pos_right hδ


private def contactExampleA (i : Fin 5) : ℂ := if i = 0 then 2 else 1
private def contactExampleB (i : Fin 5) : ℂ := if i = 0 then -1 else 1
private def contactExampleV (_ : Fin 5) : ℂ := (Real.sqrt (1 / 5) : ℝ)

private theorem contactExampleV_sq (i j : Fin 5) :
    contactExampleV i * star (contactExampleV j) = (1 / 5 : ℂ) := by
  have h : Real.sqrt (1 / 5) * Real.sqrt (1 / 5) = (1 / 5 : ℝ) :=
    Real.mul_self_sqrt (by norm_num)
  simp only [contactExampleV, Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul]
  rw [h]
  push_cast
  rfl

private theorem contactExampleV_unit : ∑ i, star (contactExampleV i) * contactExampleV i = 1 := by
  simp_rw [mul_comm (star (contactExampleV _)), contactExampleV_sq]
  norm_num [Finset.sum_const, Fintype.card_fin]

private def contactExampleU : Matrix (Fin 5) (Fin 5) ℂ :=
  rankOnePhase contactExampleV (-1)

private theorem contactExampleU_diag (i : Fin 5) :
    contactExampleU i i = (3 / 5 : ℂ) := by
  unfold contactExampleU rankOnePhase
  rw [Matrix.add_apply, Matrix.one_apply_eq, Matrix.smul_apply, vecMulVec_apply]
  change 1 + (-1 - 1) * (contactExampleV i * star (contactExampleV i)) = _
  rw [contactExampleV_sq]
  norm_num

private theorem contactExample_negative :
    realSignedWeight contactExampleU (1 : Equiv.Perm (Fin 5)) < 0 := by
  have hd := det_rankOnePhase contactExampleV (-1) contactExampleV_unit
  rw [← contactExampleU] at hd
  simp only [realSignedWeight, signedWeight, hd, leibnizTerm, map_one,
    Equiv.Perm.one_apply, Int.cast_one, one_mul, contactExampleU_diag, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]
  norm_num [div_neg, Complex.div_re]

private theorem contactExample_product (σ : Equiv.Perm (Fin 5)) :
    matchingProduct contactExampleA contactExampleB σ =
      if σ 0 = 0 then 16 else 0 := by
  unfold matchingProduct
  by_cases hσ : σ 0 = 0
  · rw [if_pos hσ, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ (0 : Fin 5))]
    rw [show contactExampleA (σ 0) + contactExampleB 0 = 1 by
      norm_num [contactExampleA, contactExampleB, hσ]]
    rw [one_mul]
    have hf : ∀ k ∈ Finset.univ.erase (0 : Fin 5),
        contactExampleA (σ k) + contactExampleB k = 2 := by
      intro k hk
      have hk0 := Finset.ne_of_mem_erase hk
      have hs0 : σ k ≠ 0 := by
        rw [← hσ]
        exact σ.injective.ne hk0
      simp [contactExampleA, contactExampleB, hk0, hs0]
      norm_num
    rw [Finset.prod_congr rfl hf, Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ _)]
    norm_num
  · rw [if_neg hσ]
    apply Finset.prod_eq_zero (Finset.mem_univ (0 : Fin 5))
    simp [contactExampleA, contactExampleB, hσ]

private theorem contactExample_count :
    24 ≤ Fintype.card {σ : Equiv.Perm (Fin 5) // σ 0 = 0} := by
  classical
  let f (τ : Equiv.Perm {i : Fin 5 // i ≠ 0}) :
      {σ : Equiv.Perm (Fin 5) // σ 0 = 0} :=
    ⟨Equiv.Perm.ofSubtype τ, Equiv.Perm.ofSubtype_apply_of_not_mem τ (by simp)⟩
  have hf : Function.Injective f := by
    intro τ τ' h
    apply Equiv.Perm.ofSubtype_injective
    exact congrArg Subtype.val h
  have h := Fintype.card_le_of_injective f hf
  rwa [Fintype.card_perm, Fintype.card_subtype_compl, Fintype.card_fin,
    Fintype.card_subtype_eq, show Nat.factorial (5 - 1) = 24 by rfl] at h

/-- Many genuine projected contacts do not force even the signed coefficient
of a contact itself to be nonnegative. This order-five example has at least
24 maximizing permutation labels and a strict off-face stratum, while the
identity coefficient of the Householder mixer is negative. The positive
determinant law is genuine: the second spectrum has two values. -/
theorem many_contacts_with_negative_signed_weight :
    ∃ (a b : Fin 5 → ℂ) (U : Matrix (Fin 5) (Fin 5) ℂ),
      IsUnitary U ∧ Holds a b U ∧ realSignedWeight U 1 < 0 ∧
      (∀ σ : Equiv.Perm (Fin 5), (matchingProduct a b σ).re ≤ 16) ∧
      (∃ σ : Equiv.Perm (Fin 5), (matchingProduct a b σ).re < 16) ∧
      24 ≤ Fintype.card {σ : Equiv.Perm (Fin 5) // σ 0 = 0} ∧
      (∀ σ : Equiv.Perm (Fin 5), (matchingProduct a b σ).re = 16 ↔ σ 0 = 0) := by
  have hu : IsUnitary contactExampleU :=
    rankOnePhase_unitary _ _ contactExampleV_unit (by norm_num)
  refine ⟨contactExampleA, contactExampleB, contactExampleU, hu, ?_, contactExample_negative,
    ?_, ?_, contactExample_count, ?_⟩
  · simpa [contactExampleB] using
      holds_two_values contactExampleA ({0} : Finset (Fin 5)) (-1) 1 contactExampleU hu
  · intro σ
    rw [contactExample_product]
    split_ifs <;> norm_num
  · refine ⟨Equiv.swap 0 1, ?_⟩
    rw [contactExample_product]
    norm_num
  · intro σ
    rw [contactExample_product]
    split_ifs with h <;> simp [h]


/-- In each three-column matching fiber, the two relative parity classes
have the same total projected deficit. At a valid supporting line, an
entire parity class of contacts forces the other class to be contacts as
well. The reference maximizing permutation need not be in the fiber. -/
theorem matching_triangle_contact_parity_iff
    (a b : ι → ℂ) (η : ℂ) (r σ : Equiv.Perm ι) (i j k : ι)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hmax : ∀ τ, 0 ≤ matchingGap a b η r τ) :
    let g := matchingGap a b η r
    (g σ = 0 ∧ g (σ * Equiv.swap i j * Equiv.swap j k) = 0 ∧
      g (σ * Equiv.swap j k * Equiv.swap i j) = 0) ↔
    (g (σ * Equiv.swap i j) = 0 ∧ g (σ * Equiv.swap i k) = 0 ∧
      g (σ * Equiv.swap j k) = 0) := by
  let g := matchingGap a b η r
  have h := congrArg (fun z : ℂ => (η * z).re)
    (matchingProduct_triangle_identity a b σ i j k hij hik hjk)
  simp only [mul_add, Complex.add_re] at h
  have hs :
      g σ + g (σ * Equiv.swap i j * Equiv.swap j k) +
        g (σ * Equiv.swap j k * Equiv.swap i j) =
      g (σ * Equiv.swap i j) + g (σ * Equiv.swap i k) + g (σ * Equiv.swap j k) := by
    dsimp only [g, matchingGap]
    linarith only [h]
  change (_ ∧ _ ∧ _) ↔ (_ ∧ _ ∧ _)
  constructor
  · rintro ⟨h₁, h₂, h₃⟩
    change g σ = 0 at h₁
    change g (σ * Equiv.swap i j * Equiv.swap j k) = 0 at h₂
    change g (σ * Equiv.swap j k * Equiv.swap i j) = 0 at h₃
    rw [h₁, h₂, h₃] at hs
    have ha : 0 ≤ g (σ * Equiv.swap i j) := hmax _
    have hb : 0 ≤ g (σ * Equiv.swap i k) := hmax _
    have hc : 0 ≤ g (σ * Equiv.swap j k) := hmax _
    exact ⟨by linarith only [hs, ha, hb, hc], by linarith only [hs, ha, hb, hc],
      by linarith only [hs, ha, hb, hc]⟩
  · rintro ⟨h₁, h₂, h₃⟩
    change g (σ * Equiv.swap i j) = 0 at h₁
    change g (σ * Equiv.swap i k) = 0 at h₂
    change g (σ * Equiv.swap j k) = 0 at h₃
    rw [h₁, h₂, h₃] at hs
    have ha : 0 ≤ g σ := hmax _
    have hb : 0 ≤ g (σ * Equiv.swap i j * Equiv.swap j k) := hmax _
    have hc : 0 ≤ g (σ * Equiv.swap j k * Equiv.swap i j) := hmax _
    exact ⟨by linarith only [hs, ha, hb, hc], by linarith only [hs, ha, hb, hc],
      by linarith only [hs, ha, hb, hc]⟩


/-- Negativity can persist even on a noncontact label. In this proper
order-five support face, the exact off-contact mass is the nonnegative
single-entry squared modulus even though one summand is negative. -/
theorem contact_positive_gap_with_negative_summand :
    ∃ (a b : Fin 5 → ℂ) (U : Matrix (Fin 5) (Fin 5) ℂ)
      (r : Equiv.Perm (Fin 5)),
      IsUnitary U ∧ Holds a b U ∧ realSignedWeight U 1 < 0 ∧
      (∀ σ, matchingGap a b (-1) r σ = if σ 0 = 0 then 16 else 0) ∧
      (matchingGap a b (-1) r 1 = 16) ∧
      ((-1 * matchingProduct a b r).re - (-1 * determinantValue a b U).re =
        16 * Complex.normSq (U 0 0)) := by
  let r : Equiv.Perm (Fin 5) := Equiv.swap 0 1
  have hu : IsUnitary contactExampleU :=
    rankOnePhase_unitary _ _ contactExampleV_unit (by norm_num)
  have hr : matchingProduct contactExampleA contactExampleB r = 0 := by
    rw [contactExample_product]
    norm_num [r]
  have hg (σ : Equiv.Perm (Fin 5)) :
      matchingGap contactExampleA contactExampleB (-1) r σ = if σ 0 = 0 then 16 else 0 := by
    rw [matchingGap, hr, contactExample_product]
    split_ifs <;> norm_num
  refine ⟨contactExampleA, contactExampleB, contactExampleU, r, hu, ?_, contactExample_negative,
    hg, by simpa using hg 1, ?_⟩
  · simpa [contactExampleB] using
      holds_two_values contactExampleA ({0} : Finset (Fin 5)) (-1) 1 contactExampleU hu
  · rw [support_gap_eq _ _ _ hu]
    simp_rw [hg]
    have hh : (∑ σ : Equiv.Perm (Fin 5),
        realSignedWeight contactExampleU σ * (if σ 0 = 0 then 16 else 0)) =
        16 * ∑ σ : Equiv.Perm (Fin 5), if σ 0 = 0 then realSignedWeight contactExampleU σ else 0 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro σ _
      split_ifs <;> simp [mul_comm]
    rw [hh, marginal_realSignedWeight contactExampleU hu]


/-- The contact set of a nonnegative minor certificate is exactly the set
of permutations avoiding all active events. In particular a candidate
active event containing even one contact cannot appear positively
in such a certificate. -/
theorem matching_contact_iff_avoids_active_events
    {κ : Type*} [Fintype κ] (a b : ι → ℂ) (η : ℂ) (H : ℝ)
    (I J : κ → Finset ι) (c : κ → ℝ) (hc : ∀ k, 0 ≤ c k)
    (hgap : ∀ σ : Equiv.Perm ι, (η * matchingProduct a b σ).re - H =
      ∑ k, if (J k).map σ.toEmbedding = I k then c k else 0)
    (σ : Equiv.Perm ι) :
    (η * matchingProduct a b σ).re = H ↔
      ∀ k, 0 < c k → (J k).map σ.toEmbedding ≠ I k := by
  rw [← sub_eq_zero, hgap σ]
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun k _ => by split_ifs <;> simp [hc k])]
  constructor
  · intro h k hk he
    have hz := h k (Finset.mem_univ k)
    rw [if_pos he] at hz
    exact (ne_of_gt hk) hz
  · intro h k _
    by_cases he : (J k).map σ.toEmbedding = I k
    · rw [if_pos he]
      exact le_antisymm (le_of_not_gt fun hp => h k hp he) (hc k)
    · rw [if_neg he]

end

end MOC
