import MOC.SecularCauchyMinorFormula

/-! A coordinate section of a Cauchy minor is a ratio of two monic products.
Complementary coordinate sections have opposite cubic interactions. -/

open BigOperators Filter Finset
open scoped Topology

namespace MOC

noncomputable section

variable {n : ℕ}

private def cutFraction (d h : Fin n → ℝ) (S T : Finset (Fin n)) (z : ℝ) : ℝ :=
  (∏ j ∈ T, (z-h j)) / ∏ i ∈ S, (z-d i)

private def cutResidue (d h : Fin n → ℝ) (S T : Finset (Fin n)) (i : Fin n) : ℝ :=
  (∏ j ∈ T, (d i-h j)) / ∏ k ∈ S.erase i, (d i-d k)

private theorem cutFraction_eq_simpleFractions (d h : Fin n → ℝ) (S T : Finset (Fin n))
    (hst : S.card = T.card) (hd : Function.Injective d) (z : ℝ) (hz : ∀ i ∈ S, z ≠ d i) :
    cutFraction d h S T z = secularPartialFractions S d (cutResidue d h S T) z := by
  classical
  let e : S ≃ T := Fintype.equivOfCardEq (by simpa using hst)
  let a (i : S) := d i
  let b (i : S) := h (e i)
  have ha : Function.Injective a := fun i j he => Subtype.ext (hd he)
  have hnum (z' : ℝ) : (∏ j : S, (z'-b j)) = ∏ j ∈ T, (z'-h j) :=
    (Equiv.prod_comp e (fun j : T => z'-h j)).trans (Finset.prod_coe_sort T (fun j => z'-h j))
  have hr (i : S) : -secularResidue b a i = cutResidue d h S T i := by
    rw [secularResidue, neg_div, neg_neg, hnum, cutResidue]
    congr 1
    calc
      _ = ∏ j : S, if j ≠ i then d i-d j else 1 := by
        rw [← Finset.filter_ne', Finset.prod_filter]
      _ = ∏ j : S, if (j : Fin n) ≠ (i : Fin n) then d i-d j else 1 := by
        apply Finset.prod_congr rfl
        intro j _
        simp [Subtype.ext_iff]
      _ = ∏ j ∈ S, if j ≠ (i : Fin n) then d i-d j else 1 :=
        Finset.prod_coe_sort S (fun j => if j ≠ (i : Fin n) then d i-d j else 1)
      _ = _ := by rw [← Finset.prod_filter, Finset.filter_ne']
  have he := secular_ratio_eq_partialFractions a b ha z (fun i => hz i i.2)
  rw [hnum] at he
  simp only [secularPartialFractions, hr, a] at he
  rw [Finset.prod_coe_sort S (fun i => z-d i),
    Finset.sum_coe_sort S (fun i => cutResidue d h S T i / (z-d i))] at he
  exact he

private theorem secularCauchyCutRatio_compl (d h : Fin n → ℝ) (I J : Finset (Fin n))
    (hc : I.card = J.card) :
    secularCauchyCutRatio d h Iᶜ Jᶜ = secularCauchyCutRatio d h I J := by
  have hc' : Iᶜ.card = Jᶜ.card := by simp only [Finset.card_compl, hc]
  unfold secularCauchyCutRatio
  simp only [compl_compl]
  rw [secularCutProduct_reverse d d Iᶜ I, secularCutProduct_reverse h h Jᶜ J]
  have hs : (-1 : ℝ)^(I.card * Iᶜ.card) * (-1 : ℝ)^(J.card * Jᶜ.card) = 1 := by
    rw [hc, hc', ← pow_add, ← two_mul, pow_mul]
    norm_num
  rw [show ((-1 : ℝ)^(I.card*Iᶜ.card) * secularCutProduct d d I Iᶜ) *
      ((-1 : ℝ)^(J.card*Jᶜ.card) * secularCutProduct h h J Jᶜ) =
      secularCutProduct d d I Iᶜ * secularCutProduct h h J Jᶜ by
        calc
          _ = ((-1 : ℝ)^(I.card*Iᶜ.card) * (-1 : ℝ)^(J.card*Jᶜ.card)) *
            (secularCutProduct d d I Iᶜ * secularCutProduct h h J Jᶜ) := by ring
          _ = _ := by rw [hs, one_mul]]
  rw [secularCutProduct_reverse d h Iᶜ J, secularCutProduct_reverse h d Jᶜ I]
  have hnum : (-1 : ℝ)^(J.card * Iᶜ.card) * (-1 : ℝ)^(I.card * Jᶜ.card) = 1 := by
    rw [← hc, ← hc', ← pow_add, ← two_mul, pow_mul]
    norm_num
  rw [show ((-1 : ℝ)^(J.card*Iᶜ.card) * secularCutProduct h d J Iᶜ) *
      ((-1 : ℝ)^(I.card*Jᶜ.card) * secularCutProduct d h I Jᶜ) =
      secularCutProduct d h I Jᶜ * secularCutProduct h d J Iᶜ by
        calc
          _ = ((-1 : ℝ)^(J.card*Iᶜ.card) * (-1 : ℝ)^(I.card*Jᶜ.card)) *
            (secularCutProduct d h I Jᶜ * secularCutProduct h d J Iᶜ) := by ring
          _ = _ := by rw [hnum, one_mul]]

private theorem cutRatio_update_of_mem (d h : Fin n → ℝ) (I J : Finset (Fin n))
    (i : Fin n) (hi : i ∈ I) : ∃ w : ℝ, ∀ t : ℝ,
      secularCauchyCutRatio (Function.update d i t) h I J = w * cutFraction d h Iᶜ Jᶜ t := by
  let N := secularCutProduct d h (I.erase i) Jᶜ
  let N' := secularCutProduct h d J Iᶜ
  let D := secularCutProduct d d (I.erase i) Iᶜ
  let D' := secularCutProduct h h J Jᶜ
  refine ⟨N*N'/(D*D'), fun t => ?_⟩
  let g := Function.update d i t
  have hg₁ (k : Fin n) (hk : k ∈ Iᶜ) : g k = d k := by
    have hki : k ≠ i := by
      intro he
      subst k
      exact mem_compl.mp hk hi
    exact Function.update_of_ne hki _ _
  have hg₂ (k : Fin n) (hk : k ∈ I.erase i) : g k = d k :=
    Function.update_of_ne (ne_of_mem_erase hk) _ _
  have hNi : secularCutProduct g h I Jᶜ = N * ∏ l ∈ Jᶜ, (t-h l) := by
    unfold secularCutProduct
    rw [← Finset.prod_erase_mul I _ hi]
    congr 1
    · exact Finset.prod_congr rfl fun k hk => by rw [hg₂ k hk]
    · simp [g]
  have hNk : secularCutProduct h g J Iᶜ = N' := by
    unfold secularCutProduct
    apply Finset.prod_congr rfl
    intro j _
    exact Finset.prod_congr rfl fun k hk => by rw [hg₁ k hk]
  have hDi : secularCutProduct g g I Iᶜ = D * ∏ k ∈ Iᶜ, (t-d k) := by
    unfold secularCutProduct
    rw [← Finset.prod_erase_mul I _ hi]
    congr 1
    · apply Finset.prod_congr rfl
      intro k hk
      apply Finset.prod_congr rfl
      intro l hl
      rw [hg₂ k hk, hg₁ l hl]
    · apply Finset.prod_congr rfl
      intro k hk
      simp [g, Function.update_of_ne (fun he : k = i => mem_compl.mp hk (he ▸ hi))]
  change secularCauchyCutRatio g h I J = _
  rw [secularCauchyCutRatio, hNi, hNk, hDi]
  change ((N*∏ l ∈ Jᶜ, (t-h l))*N') / ((D*∏ k ∈ Iᶜ, (t-d k))*D') = _
  unfold cutFraction
  rw [div_mul_div_comm]
  congr 1 <;> ring

private theorem residue_product_of_cut (d h : Fin n → ℝ) (I J : Finset (Fin n))
    (i : Fin n) (hi : i ∈ I) : secularResidue h d i =
      -cutFraction d h Iᶜ Jᶜ (d i) * cutResidue d h I J i := by
  unfold secularResidue cutFraction cutResidue
  rw [secularResidue_denominator_split d I i hi,
    ← Finset.prod_mul_prod_compl J (fun j => d i-h j), neg_mul, div_mul_div_comm, ← neg_div]
  congr 1 <;> ring

theorem chamber_nodes_avoid_spectrum (h d : Fin n → ℝ) (hd : d ∈ secularChamber h) :
    ∀ i j, h j ≠ d i := by
  intro i j he
  have hz : (∏ j, (d i-h j)) = 0 := Finset.prod_eq_zero (mem_univ j) (sub_eq_zero.mpr he.symm)
  have hi : secularResidue h d i = 0 := by rw [secularResidue, hz, neg_zero, zero_div]
  exact (hd.2 i).ne' hi

private theorem secularProjectionMinor_charts (d h : Fin n → ℝ)
    (hh : Function.Injective h) (hd : d ∈ secularChamber h)
    (I J : Finset (Fin n)) (hIJ : I.card = J.card) :
    ∃ w : Fin n → ℝ, ∀ i,
      (fun t => secularProjectionMinor (Function.update d i t)
        (secularResidue h (Function.update d i t)) h I J) =ᶠ[𝓝 (d i)]
        fun t => w i * (if i ∈ I then secularPartialFractions Iᶜ d (cutResidue d h Iᶜ Jᶜ) t
          else secularPartialFractions I d (cutResidue d h I J) t) := by
  have hc : Iᶜ.card = Jᶜ.card := by simp only [Finset.card_compl, hIJ]
  have main (i : Fin n) : ∃ w : ℝ,
      (fun t => secularProjectionMinor (Function.update d i t)
        (secularResidue h (Function.update d i t)) h I J) =ᶠ[𝓝 (d i)]
        fun t => w * (if i ∈ I then secularPartialFractions Iᶜ d (cutResidue d h Iᶜ Jᶜ) t
          else secularPartialFractions I d (cutResidue d h I J) t) := by
    have hcont : Continuous (Function.update d i) := continuous_const.update i continuous_id
    have htend : Tendsto (Function.update d i) (𝓝 (d i)) (𝓝 d) := by
      have hc0 : ContinuousAt (Function.update d i) (d i) := hcont.continuousAt
      simpa only [Function.update_eq_self] using hc0.tendsto
    have hnear : ∀ᶠ t in 𝓝 (d i), Function.update d i t ∈ secularChamber h :=
      htend.eventually ((isOpen_secularChamber h).mem_nhds hd)
    by_cases hi : i ∈ I
    · obtain ⟨w, hw⟩ := cutRatio_update_of_mem d h I J i hi
      refine ⟨w, ?_⟩
      filter_upwards [hnear] with t ht
      have hne : ∀ j ∈ Iᶜ, t ≠ d j := by
        intro j hj
        have hji : j ≠ i := fun he => mem_compl.mp hj (he ▸ hi)
        have he := ht.1.ne hji.symm
        simpa only [Function.update_self, Function.update_of_ne hji] using he
      rw [secularProjectionMinor_eq_cutRatio _ h ht.1 hh (chamber_nodes_avoid_spectrum h _ ht) I J hIJ,
        hw, if_pos hi, cutFraction_eq_simpleFractions d h Iᶜ Jᶜ hc hd.1 t hne]
    · have hic : i ∈ Iᶜ := mem_compl.mpr hi
      obtain ⟨w, hw⟩ := cutRatio_update_of_mem d h Iᶜ Jᶜ i hic
      refine ⟨w, ?_⟩
      filter_upwards [hnear] with t ht
      have hne : ∀ j ∈ I, t ≠ d j := by
        intro j hj
        have hji : j ≠ i := fun he => hi (he ▸ hj)
        have he := ht.1.ne hji.symm
        simpa only [Function.update_self, Function.update_of_ne hji] using he
      rw [secularProjectionMinor_eq_cutRatio _ h ht.1 hh (chamber_nodes_avoid_spectrum h _ ht) I J hIJ,
        ← secularCauchyCutRatio_compl _ h I J hIJ, hw, if_neg hi]
      simp only [compl_compl, cutFraction_eq_simpleFractions d h I J hIJ hd.1 t hne]
  choose w hw using main
  exact ⟨w, hw⟩

/-- Every individual squared spectral minor is weighted harmonic in its
secular chamber, with no degree restriction on the final spectral evaluation. -/
theorem secularProjectionMinor_weighted_second_sum (d h : Fin n → ℝ)
    (hh : Function.Injective h) (hd : d ∈ secularChamber h)
    (I J : Finset (Fin n)) (hIJ : I.card = J.card) :
    (∑ i, secularResidue h d i * deriv (deriv (fun t =>
      secularProjectionMinor (Function.update d i t) (secularResidue h (Function.update d i t))
      h I J)) (d i)) = 0 := by
  have hc : Iᶜ.card = Jᶜ.card := by simp only [Finset.card_compl, hIJ]
  obtain ⟨w, hw⟩ := secularProjectionMinor_charts d h hh hd I J hIJ
  apply weighted_harmonic_of_secular_fraction_charts
    (fun d => secularProjectionMinor d (secularResidue h d) h I J) d (secularResidue h d)
    (cutResidue d h I J) (cutResidue d h Iᶜ Jᶜ) w I hd.1 hw
  · intro i hi
    rw [residue_product_of_cut d h I J i hi, cutFraction_eq_simpleFractions d h Iᶜ Jᶜ hc hd.1]
    exact fun j hj => hd.1.ne (fun he => mem_compl.mp hj (he ▸ hi))
  · intro i hi
    rw [residue_product_of_cut d h Iᶜ Jᶜ i hi]
    simp only [compl_compl]
    rw [cutFraction_eq_simpleFractions d h I J hIJ hd.1]
    exact fun j hj => hd.1.ne (fun he => mem_compl.mp hi (he.symm ▸ hj))

/-- Each coordinate section of a squared spectral minor is differentiable
in a neighborhood, and its derivative is differentiable at the chamber point. -/
theorem secularProjectionMinor_coordinate_regular (d h : Fin n → ℝ)
    (hh : Function.Injective h) (hd : d ∈ secularChamber h)
    (I J : Finset (Fin n)) (i : Fin n) :
    let F (t : ℝ) := secularProjectionMinor (Function.update d i t)
      (secularResidue h (Function.update d i t)) h I J
    (∀ᶠ t in 𝓝 (d i), DifferentiableAt ℝ F t) ∧ DifferentiableAt ℝ (deriv F) (d i) := by
  intro F
  by_cases hIJ : I.card = J.card
  · obtain ⟨w, hw⟩ := secularProjectionMinor_charts d h hh hd I J hIJ
    let S := if i ∈ I then Iᶜ else I
    let c := if i ∈ I then cutResidue d h Iᶜ Jᶜ else cutResidue d h I J
    have he : F =ᶠ[𝓝 (d i)] (fun t => w i * secularPartialFractions S d c t) := by
      by_cases hi : i ∈ I <;> simpa only [F, S, c, hi, if_true, if_false] using hw i
    have hn : i ∉ S := by
      by_cases hi : i ∈ I <;> simp [S, hi]
    have hp : ∀ j ∈ S, d i ≠ d j := fun j hj => hd.1.ne (fun he => hn (he ▸ hj))
    have hnear : ∀ᶠ t in 𝓝 (d i), ∀ j ∈ S, t ≠ d j :=
      (Filter.eventually_all_finset S).mpr fun j hj => eventually_ne_nhds (hp j hj)
    constructor
    · filter_upwards [hnear, he.eventuallyEq_nhds] with t ht he_t
      exact (((hasDerivAt_secularPartialFractions S d c t ht).const_mul _).congr_of_eventuallyEq
        he_t).differentiableAt
    · have h₂ := hasSecondDerivAt_const_mul_partialFractions S d c (w i) (d i) hp
      exact (h₂.congr_of_eventuallyEq he.deriv).differentiableAt
  · have hzero : F = fun _ => (0 : ℝ) := by
      funext t
      simp [F, secularProjectionMinor, hIJ]
    rw [hzero, deriv_const']
    exact ⟨Filter.Eventually.of_forall fun _ => differentiableAt_const _, differentiableAt_const _⟩


end

end MOC
