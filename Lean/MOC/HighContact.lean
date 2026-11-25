import MOC.AlgebraicContact
import MOC.Claim
import MOC.ContactCover
import MOC.MatchingChartPolynomial
import MOC.SpectralPerturbation

/-! Transfer to (2N-2) contacts, conditional on the existence of covering
curves in the specified regular polynomial fibers. -/

open Matrix Set

namespace MOC

noncomputable section

variable {n : ℕ}

abbrev ContactMatching (n : ℕ) := Equiv.Perm (Fin (n + 2))

/-- Complex support deficit of a matching relative to the reference. -/
def chartMatchingGap (η : ℂ) (r : ContactMatching n)
    (z : MatchingChartVariable n → ℂ) (σ : ContactMatching n) : ℂ :=
  η * (matchingChartCoordinate z r - matchingChartCoordinate z σ)

private theorem continuous_chartMatchingGap (η : ℂ) (r σ : ContactMatching n) :
    Continuous (fun z : MatchingChartVariable n → ℂ => chartMatchingGap η r z σ) := by
  have hcoord (σ' : ContactMatching n) :
      Continuous (fun z : MatchingChartVariable n → ℂ => matchingChartCoordinate z σ') := by
    change Continuous (fun z : MatchingChartVariable n → ℂ =>
      z (.inl ()) * ∏ j, (1 - matchingChartLeft z (σ' j) * matchingChartRight z j))
    have hl (i : Fin (n + 2)) : Continuous (fun z : MatchingChartVariable n → ℂ => matchingChartLeft z i) := by
      refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => ?_) j) i
      · exact continuous_const
      · exact continuous_const
      · exact continuous_apply _
    have hr (j : Fin (n + 2)) : Continuous (fun z : MatchingChartVariable n → ℂ => matchingChartRight z j) := by
      refine Fin.cases ?_ (fun k => ?_) j
      · exact continuous_const
      · exact continuous_apply _
    exact (continuous_apply _).mul (continuous_finset_prod _ fun j _ =>
      continuous_const.sub ((hl (σ' j)).mul (hr j)))
  exact continuous_const.mul ((hcoord r).sub (hcoord σ))

/-- The labels that tie with the reference in the specified support direction. -/
def chartContacts (η : ℂ) (r : ContactMatching n)
    (z : MatchingChartVariable n → ℂ) : Finset (ContactMatching n) := by
  classical
  exact Finset.univ.filter fun σ => (chartMatchingGap η r z σ).re = 0

@[simp] theorem mem_chartContacts (η : ℂ) (r σ : ContactMatching n)
    (z : MatchingChartVariable n → ℂ) :
    σ ∈ chartContacts η r z ↔ (chartMatchingGap η r z σ).re = 0 := by
  classical
  simp [chartContacts]

/-- A concrete geometric input to contact transfer. One inactive gap is a
covering projection on a regular subset of the fixed polynomial fiber. The
initial point may move within the positive chamber to avoid branch values. -/
structure MatchingChartContactCover
    (U : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ) (η : ℂ) (r : ContactMatching n)
    (z : MatchingChartVariable n → ℂ) where
  carrier : Set (MatchingChartVariable n → ℂ)
  inactive : ContactMatching n
  notContact : inactive ∉ chartContacts η r z
  exceptional : Set ℂ
  finiteExceptional : exceptional.Finite
  avoids : ∀ w : carrier, chartMatchingGap η r w inactive ∈ exceptionalᶜ
  covering : IsCoveringMap (fun w : carrier =>
    (⟨chartMatchingGap η r w inactive, avoids w⟩ : ↥exceptionalᶜ))
  regular : ∀ w : carrier, MvPolynomial.eval (w : MatchingChartVariable n → ℂ)
    (matchingChartRegularPolynomial n) ≠ 0
  sameFiber : ∀ (w : carrier) (i : Option ↥((chartContacts η r z).erase r)),
    MvPolynomial.eval (w : MatchingChartVariable n → ℂ)
      (matchingChartContactPolynomial U (chartContacts η r z) r i) =
    MvPolynomial.eval z (matchingChartContactPolynomial U (chartContacts η r z) r i)
  initial : carrier
  positive : ∀ σ ∉ chartContacts η r z, 0 < (chartMatchingGap η r initial σ).re

/-- Path lifting yields a point with strictly more contacts on the same
regular fiber and with the exact complex determinant deficit unchanged. -/
theorem exists_chart_with_more_contacts
    {U : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ} {η : ℂ} {r : ContactMatching n}
    {z : MatchingChartVariable n → ℂ} (c : MatchingChartContactCover U η r z) :
    ∃ w : MatchingChartVariable n → ℂ,
      MvPolynomial.eval w (matchingChartRegularPolynomial n) ≠ 0 ∧
      MvPolynomial.eval w (matchingChartDeficitPolynomial U r) =
        MvPolynomial.eval z (matchingChartDeficitPolynomial U r) ∧
      (∀ σ, 0 ≤ (chartMatchingGap η r w σ).re) ∧
      chartContacts η r z ⊂ chartContacts η r w := by
  classical
  let T := chartContacts η r z
  let J := Tᶜ
  have hJ (σ : ContactMatching n) : σ ∈ J ↔ σ ∉ T := Finset.mem_compl
  have hold (w : c.carrier) (σ : ContactMatching n) (hσ : σ ∈ T) :
      (chartMatchingGap η r w σ).re = 0 := by
    by_cases h : σ = r
    · subst σ
      simp [chartMatchingGap]
    · have hf := c.sameFiber w (some ⟨σ, Finset.mem_erase.mpr ⟨h, hσ⟩⟩)
      change MvPolynomial.eval (w : MatchingChartVariable n → ℂ)
        (matchingChartPolynomial r - matchingChartPolynomial σ) =
        MvPolynomial.eval z (matchingChartPolynomial r - matchingChartPolynomial σ) at hf
      simp only [map_sub, eval_matchingChartPolynomial] at hf
      rw [chartMatchingGap, hf]
      exact (mem_chartContacts η r σ z).mp hσ
  obtain ⟨w, hnew, σ, hσJ, hσw⟩ := exists_new_contact_on_covering J
    (fun σ (w : c.carrier) => chartMatchingGap η r w σ)
    (fun σ _ => (continuous_chartMatchingGap η r σ).comp continuous_subtype_val)
    ((hJ c.inactive).mpr c.notContact) c.finiteExceptional c.avoids c.covering c.initial
    (fun σ hσ => c.positive σ ((hJ σ).mp hσ))
  refine ⟨w.val, c.regular w, c.sameFiber w none, ?_, ?_⟩
  · intro τ
    by_cases ht : τ ∈ T
    · exact (hold w τ ht).ge
    · exact hnew τ ((hJ τ).mpr ht)
  · refine Finset.ssubset_iff_subset_ne.mpr
      ⟨fun τ ht => (mem_chartContacts η r τ w.val).mpr (hold w τ ht), ?_⟩
    intro he
    apply (hJ σ).mp hσJ
    change σ ∈ chartContacts η r z
    rw [he]
    exact (mem_chartContacts η r σ w.val).mpr hσw

/-- If every chart failing a terminal condition has a contact cover, the
admissible chart with the largest contact count satisfies the condition. -/
theorem exists_chart_with_terminal_contacts_of_covers
    (U : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ) (η : ℂ) (r : ContactMatching n)
    (z : MatchingChartVariable n → ℂ)
    (hz : MvPolynomial.eval z (matchingChartRegularPolynomial n) ≠ 0)
    (hmax : ∀ σ, 0 ≤ (chartMatchingGap η r z σ).re)
    {terminal : (MatchingChartVariable n → ℂ) → Prop}
    (hcover : ∀ w : MatchingChartVariable n → ℂ,
      MvPolynomial.eval w (matchingChartRegularPolynomial n) ≠ 0 →
      MvPolynomial.eval w (matchingChartDeficitPolynomial U r) =
        MvPolynomial.eval z (matchingChartDeficitPolynomial U r) →
      (∀ σ, 0 ≤ (chartMatchingGap η r w σ).re) →
      chartContacts η r z ⊆ chartContacts η r w →
      ¬ terminal w →
      Nonempty (MatchingChartContactCover U η r w)) :
    ∃ w : MatchingChartVariable n → ℂ,
      MvPolynomial.eval w (matchingChartRegularPolynomial n) ≠ 0 ∧
      MvPolynomial.eval w (matchingChartDeficitPolynomial U r) =
        MvPolynomial.eval z (matchingChartDeficitPolynomial U r) ∧
      (∀ σ, 0 ≤ (chartMatchingGap η r w σ).re) ∧
      chartContacts η r z ⊆ chartContacts η r w ∧
      terminal w := by
  classical
  let admissible (w : MatchingChartVariable n → ℂ) : Prop :=
    MvPolynomial.eval w (matchingChartRegularPolynomial n) ≠ 0 ∧
    MvPolynomial.eval w (matchingChartDeficitPolynomial U r) =
      MvPolynomial.eval z (matchingChartDeficitPolynomial U r) ∧
    (∀ σ, 0 ≤ (chartMatchingGap η r w σ).re) ∧
    chartContacts η r z ⊆ chartContacts η r w
  let sizes := (Finset.range (Fintype.card (ContactMatching n) + 1)).filter fun k =>
    ∃ w, admissible w ∧ (chartContacts η r w).card = k
  have hsize (w : MatchingChartVariable n → ℂ) (hw : admissible w) :
      (chartContacts η r w).card ∈ sizes :=
    Finset.mem_filter.mpr ⟨Finset.mem_range.mpr
      (Nat.lt_succ_of_le (Finset.card_le_univ _)), w, hw, rfl⟩
  obtain ⟨k, hk, hkmax⟩ := Finset.exists_max_image sizes id
    ⟨_, hsize z ⟨hz, rfl, hmax, Finset.Subset.rfl⟩⟩
  obtain ⟨w, hw, hkw⟩ := (Finset.mem_filter.mp hk).2
  refine ⟨w, hw.1, hw.2.1, hw.2.2.1, hw.2.2.2, ?_⟩
  by_contra hnot
  obtain ⟨c⟩ := hcover w hw.1 hw.2.1 hw.2.2.1 hw.2.2.2 hnot
  obtain ⟨w', hreg, hdef, hnonneg, hmore⟩ := exists_chart_with_more_contacts c
  have hw' : admissible w' := ⟨hreg, hdef.trans hw.2.1, hnonneg,
    hw.2.2.2.trans hmore.subset⟩
  have hbound := hkmax _ (hsize w' hw')
  change (chartContacts η r w').card ≤ k at hbound
  exact (not_le_of_gt (Finset.card_lt_card hmore)) (hbound.trans_eq hkw.symm)

/-- Contact transfer up to the nominal count `2N - 2`. -/
theorem exists_chart_with_many_contacts_of_covers
    (U : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ) (η : ℂ) (r : ContactMatching n)
    (z : MatchingChartVariable n → ℂ)
    (hz : MvPolynomial.eval z (matchingChartRegularPolynomial n) ≠ 0)
    (hmax : ∀ σ, 0 ≤ (chartMatchingGap η r z σ).re)
    (hcover : ∀ w : MatchingChartVariable n → ℂ,
      MvPolynomial.eval w (matchingChartRegularPolynomial n) ≠ 0 →
      MvPolynomial.eval w (matchingChartDeficitPolynomial U r) =
        MvPolynomial.eval z (matchingChartDeficitPolynomial U r) →
      (∀ σ, 0 ≤ (chartMatchingGap η r w σ).re) →
      chartContacts η r z ⊆ chartContacts η r w →
      (chartContacts η r w).card < 2 * (n + 2) - 2 →
      Nonempty (MatchingChartContactCover U η r w)) :
    ∃ w : MatchingChartVariable n → ℂ,
      MvPolynomial.eval w (matchingChartRegularPolynomial n) ≠ 0 ∧
      MvPolynomial.eval w (matchingChartDeficitPolynomial U r) =
        MvPolynomial.eval z (matchingChartDeficitPolynomial U r) ∧
      (∀ σ, 0 ≤ (chartMatchingGap η r w σ).re) ∧
      chartContacts η r z ⊆ chartContacts η r w ∧
      2 * (n + 2) - 2 ≤ (chartContacts η r w).card :=
  exists_chart_with_terminal_contacts_of_covers U η r z hz hmax
    (terminal := fun w => 2 * (n + 2) - 2 ≤ (chartContacts η r w).card)
    (fun w hw he hm hs hnot => hcover w hw he hm hs (lt_of_not_ge hnot))

/-- Distinct matching products force each spectrum to have distinct entries. -/
theorem injective_spectra_of_matchingProduct_injective
    {ι : Type*} [Fintype ι] [DecidableEq ι] {a b : ι → ℂ}
    (hinj : Function.Injective (matchingProduct a b)) :
    Function.Injective a ∧ Function.Injective b := by
  have hswap (f : ι → ℂ) (i j : ι) (h : f i = f j) (t : ι) :
      f (Equiv.swap i j t) = f t := by
    by_cases hi : t = i
    · subst t
      simpa only [Equiv.swap_apply_left] using h.symm
    by_cases hj : t = j
    · subst t
      simpa only [Equiv.swap_apply_right] using h
    rw [Equiv.swap_apply_of_ne_of_ne hi hj]
  constructor
  · intro i j h
    have he : matchingProduct a b (Equiv.swap i j) = matchingProduct a b 1 := by
      simp only [matchingProduct, hswap a i j h, Equiv.Perm.one_apply]
    simpa using congrArg (fun σ : Equiv.Perm ι => σ i) (hinj he).symm
  · intro i j h
    have he : matchingProduct a b (Equiv.swap i j).symm = matchingProduct a b 1 := by
      rw [matchingProduct_inverse]
      simp only [matchingProduct, hswap b i j h, Equiv.Perm.one_apply]
    have he' : Equiv.swap i j = 1 := by
      simpa only [Equiv.symm_swap] using hinj he
    simpa using congrArg (fun σ : Equiv.Perm ι => σ i) he'.symm

/-- One or two contacts already suffice to start the rational deformation
argument. This supplies three distinct contacts without a covering curve. -/
theorem exists_three_regular_matching_contacts
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (a b : ι → ℂ) (U : Matrix ι ι ℂ) (hU : IsUnitary U)
    (η : ℂ) (hη : η ≠ 0) (r : Equiv.Perm ι)
    (i j k l : ι) (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l)
    (hnz : ∀ i j, a i + b j ≠ 0) (hinj : Function.Injective (matchingProduct a b))
    (hmax : ∀ σ, 0 ≤ matchingGap a b η r σ)
    (hpos : (η * matchingProduct a b r).re < (η * determinantValue a b U).re) :
    ∃ a' b' : ι → ℂ, (∀ i j, a' i + b' j ≠ 0) ∧
      Function.Injective (matchingProduct a' b') ∧
      (∀ σ, 0 ≤ matchingGap a' b' η r σ) ∧
      (∃ s τ, s ≠ r ∧ τ ≠ r ∧ τ ≠ s ∧
        matchingGap a' b' η r s = 0 ∧ matchingGap a' b' η r τ = 0) ∧
      (η * determinantValue a' b' U).re - (η * matchingProduct a' b' r).re =
        (η * determinantValue a b U).re - (η * matchingProduct a b r).re := by
  classical
  obtain ⟨a₁, b₁, hnz₁, hinj₁, hmax₁, s, hsr, hs, hgap₁⟩ :
      ∃ a₁ b₁ : ι → ℂ, (∀ i j, a₁ i + b₁ j ≠ 0) ∧
        Function.Injective (matchingProduct a₁ b₁) ∧
        (∀ σ, 0 ≤ matchingGap a₁ b₁ η r σ) ∧
        ∃ s, s ≠ r ∧ matchingGap a₁ b₁ η r s = 0 ∧
          (η * determinantValue a₁ b₁ U).re - (η * matchingProduct a₁ b₁ r).re =
            (η * determinantValue a b U).re - (η * matchingProduct a b r).re := by
    by_cases ht : ∃ s, s ≠ r ∧ matchingGap a b η r s = 0
    · obtain ⟨s, hsr, hs⟩ := ht
      exact ⟨a, b, hnz, hinj, hmax, s, hsr, hs, rfl⟩
    · obtain ⟨ha, hb⟩ := injective_spectra_of_matchingProduct_injective hinj
      have hstart (σ : Equiv.Perm ι) (hne : σ ≠ r) : 0 < matchingGap a b η r σ :=
        lt_of_le_of_ne (hmax σ) fun he => ht ⟨σ, hne, he.symm⟩
      obtain ⟨a₁, b₁, hnz₁, hinj₁, hmax₁, _, ⟨s, hsr, _, hs⟩, hgap₁⟩ :=
        exists_third_matching_contact a b U hU η hη r r i j k l hij hik hil hjk hjl hkl
          ha hb hnz hinj (by simp [matchingGap]) (fun σ hσ _ => hstart σ hσ) hpos
      exact ⟨a₁, b₁, hnz₁, hinj₁, hmax₁, s, hsr, hs, hgap₁⟩
  by_cases ht : ∃ τ, τ ≠ r ∧ τ ≠ s ∧ matchingGap a₁ b₁ η r τ = 0
  · obtain ⟨τ, hτr, hτs, hτ⟩ := ht
    exact ⟨a₁, b₁, hnz₁, hinj₁, hmax₁, ⟨s, τ, hsr, hτr, hτs, hs, hτ⟩, hgap₁⟩
  · obtain ⟨ha, hb⟩ := injective_spectra_of_matchingProduct_injective hinj₁
    have hstart (σ : Equiv.Perm ι) (hr : σ ≠ r) (hσ : σ ≠ s) : 0 < matchingGap a₁ b₁ η r σ :=
      lt_of_le_of_ne (hmax₁ σ) fun he => ht ⟨σ, hr, hσ, he.symm⟩
    have hpos₁ : (η * matchingProduct a₁ b₁ r).re < (η * determinantValue a₁ b₁ U).re :=
      sub_pos.mp (hgap₁.symm ▸ sub_pos.mpr hpos)
    obtain ⟨a', b', hnz', hinj', hmax', hs', ⟨τ, hτr, hτs, hτ⟩, hgap'⟩ :=
      exists_third_matching_contact a₁ b₁ U hU η hη r s i j k l hij hik hil hjk hjl hkl
        ha hb hnz₁ hinj₁ hs hstart hpos₁
    exact ⟨a', b', hnz', hinj', hmax', ⟨s, τ, hsr, hτr, hτs, hs', hτ⟩, hgap'.trans hgap₁⟩

/-- The all-order support problem reduces to constructing the regular covers
and proving the terminal support inequality at (2N-2) contacts. -/
theorem mocIsTrue_of_regular_contact_covers
    (hcover : ∀ n : ℕ, 2 ≤ n →
      ∀ (U : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ) (_ : IsUnitary U)
        (η : ℂ) (r : ContactMatching n) (z : MatchingChartVariable n → ℂ),
        MvPolynomial.eval z (matchingChartRegularPolynomial n) ≠ 0 →
        (∀ σ, 0 ≤ (chartMatchingGap η r z σ).re) →
        0 < (η * MvPolynomial.eval z (matchingChartDeficitPolynomial U r)).re →
        3 ≤ (chartContacts η r z).card →
        (chartContacts η r z).card < 2 * (n + 2) - 2 →
        Nonempty (MatchingChartContactCover U η r z))
    (hterminal : ∀ n : ℕ, 2 ≤ n →
      ∀ (U : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ) (_ : IsUnitary U)
        (η : ℂ) (r : ContactMatching n) (z : MatchingChartVariable n → ℂ),
        MvPolynomial.eval z (matchingChartRegularPolynomial n) ≠ 0 →
        (∀ σ, 0 ≤ (chartMatchingGap η r z σ).re) →
        2 * (n + 2) - 2 ≤ (chartContacts η r z).card →
        (η * MvPolynomial.eval z (matchingChartDeficitPolynomial U r)).re ≤ 0) :
    MOCIsTrue := by
  classical
  apply mocIsTrue_iff_from_four.mpr
  intro N hN
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, N = n + 2 := ⟨N - 2, by omega⟩
  have hn : 2 ≤ n := by omega
  apply conjecture_iff_regular_matching_products.mpr
  intro a b U hU hnz hinj
  by_contra hfail
  rw [holds_iff_directional] at hfail
  push_neg at hfail
  obtain ⟨η, hsep⟩ := hfail
  have hη : η ≠ 0 := by
    intro he
    have h := hsep 1
    simp [he] at h
  obtain ⟨r, _, hr⟩ := Finset.exists_max_image Finset.univ
    (fun σ : ContactMatching n => (η * matchingProduct a b σ).re) ⟨1, by simp⟩
  let e : Fin 4 ↪ Fin (n + 2) := Fin.castLEEmb (by omega)
  obtain ⟨a', b', hnz', hinj', hmax', ⟨s, t, hsr, htr, hts, hs, ht⟩, hgap⟩ :=
    exists_three_regular_matching_contacts a b U hU η hη r (e 0) (e 1) (e 2) (e 3)
      (e.injective.ne (by decide)) (e.injective.ne (by decide)) (e.injective.ne (by decide))
      (e.injective.ne (by decide)) (e.injective.ne (by decide)) (e.injective.ne (by decide))
      hnz hinj (fun σ => sub_nonneg.mpr (hr σ (Finset.mem_univ _))) (hsep r)
  obtain ⟨ha, hb⟩ := injective_spectra_of_matchingProduct_injective hinj'
  have hp : ((0 : Fin (n + 1)).succ : Fin (n + 2)) ≠ 0 := Fin.succ_ne_zero _
  obtain ⟨z, hpiv, hnonzero, hcoords⟩ :=
    exists_matchingChartCoordinate_of_nonopposite a' b' hnz' (ha.ne hp) (hb.ne hp)
  have hz : MvPolynomial.eval z (matchingChartRegularPolynomial n) ≠ 0 :=
    (eval_matchingChartRegularPolynomial_ne_zero z).mpr
      ⟨hpiv, hnonzero, fun σ τ h => hinj' ((hcoords σ).trans (h.trans (hcoords τ).symm))⟩
  have hcharts (σ : ContactMatching n) : (chartMatchingGap η r z σ).re =
      matchingGap a' b' η r σ := by
    rw [chartMatchingGap, ← hcoords r, ← hcoords σ, mul_sub, Complex.sub_re, matchingGap]
  have hmax (σ : ContactMatching n) : 0 ≤ (chartMatchingGap η r z σ).re :=
    (hcharts σ).symm ▸ hmax' σ
  have hthree : 3 ≤ (chartContacts η r z).card := by
    have hsub : ({t, s, r} : Finset (ContactMatching n)) ⊆ chartContacts η r z := by
      intro σ hσ
      simp only [Finset.mem_insert, Finset.mem_singleton] at hσ
      rw [mem_chartContacts, hcharts]
      rcases hσ with rfl | rfl | rfl
      · exact ht
      · exact hs
      · simp [matchingGap]
    simpa [htr, hts, hsr] using Finset.card_le_card hsub
  have hpos : 0 < (η * MvPolynomial.eval z (matchingChartDeficitPolynomial U r)).re := by
    rw [eval_matchingChartDeficitPolynomial z a' b' U hU r hcoords, mul_sub, Complex.sub_re, hgap]
    exact sub_pos.mpr (hsep r)
  obtain ⟨w, hw, hdef, hnonneg, _, hcard⟩ := exists_chart_with_many_contacts_of_covers U η r z hz hmax
    (fun w hw he hm hsub hc => hcover n hn U hU η r w hw hm (he.symm ▸ hpos)
      (hthree.trans (Finset.card_le_card hsub)) hc)
  exact (not_lt_of_ge (hterminal n hn U hU η r w hw hnonneg hcard)) (hdef.symm ▸ hpos)

end

end MOC
