import MOC.DeficitContactTransfer
import MOC.FourMatchingRelations
import MOC.FourMixedRayCancellation
import MOC.ZhengContactReduction

/-! Regular terminal witnesses and the canonical mixed cost in order four. -/

open BigOperators Matrix

namespace MOC

noncomputable section

/-- A strict support witness has regular spectra if every pair sum is
nonzero and the matching products are pairwise distinct. -/
def FourRegularSpectra {U : Matrix (Fin 4) (Fin 4) ℂ} (w : StrictMatchingSupport U) : Prop :=
  (∀ i j, w.a i + w.b j ≠ 0) ∧ Function.Injective (matchingProduct w.a w.b)

private theorem regular_support_of_failure (a b : Fin 4 → ℂ)
    {U : Matrix (Fin 4) (Fin 4) ℂ} (h : ¬ Holds a b U) :
    ∃ w : StrictMatchingSupport U, FourRegularSpectra w := by
  classical
  rw [holds_iff_directional] at h
  push_neg at h
  obtain ⟨η, hsep⟩ := h
  obtain ⟨c, d, hnonzero, hinj, hstrict⟩ :=
    exists_regular_spectra_of_support_violation a b U η hsep
  obtain ⟨r, _, hr⟩ := Finset.exists_max_image Finset.univ
    (fun σ : FourPerm => (η * matchingProduct c d σ).re) ⟨1, Finset.mem_univ _⟩
  exact ⟨⟨c, d, η, r, fun σ => hr σ (Finset.mem_univ _), hstrict r⟩, hnonzero, hinj⟩

private theorem regular_support_chart {U : Matrix (Fin 4) (Fin 4) ℂ}
    (w : StrictMatchingSupport U) (hw : FourRegularSpectra w) :
    ∃ z : MatchingChartVariable 2 → ℂ,
      MvPolynomial.eval z (matchingChartRegularPolynomial 2) ≠ 0 ∧
      ∀ σ, matchingProduct w.a w.b σ = matchingChartCoordinate z σ := by
  obtain ⟨ha, hb⟩ := injective_spectra_of_matchingProduct_injective hw.2
  have hne : ((0 : Fin 3).succ : Fin 4) ≠ 0 := Fin.succ_ne_zero _
  obtain ⟨z, hp, hn, hz⟩ :=
    exists_matchingChartCoordinate_of_nonopposite w.a w.b hw.1 (ha.ne hne) (hb.ne hne)
  refine ⟨z, (eval_matchingChartRegularPolynomial_ne_zero z).mpr ⟨hp, hn, ?_⟩, hz⟩
  intro σ τ h
  exact hw.2 ((hz σ).trans (h.trans (hz τ).symm))

private theorem chart_gap_of_matching_products {a b : Fin 4 → ℂ} (η : ℂ)
    (r σ : FourPerm) (z : MatchingChartVariable 2 → ℂ)
    (hz : ∀ τ, matchingProduct a b τ = matchingChartCoordinate z τ) :
    (chartMatchingGap η r z σ).re = matchingGap a b η r σ := by
  rw [chartMatchingGap, ← hz r, ← hz σ, mul_sub, Complex.sub_re, matchingGap]

private theorem support_contacts_eq_chart {U : Matrix (Fin 4) (Fin 4) ℂ}
    (w : StrictMatchingSupport U) (z : MatchingChartVariable 2 → ℂ)
    (hz : ∀ σ, matchingProduct w.a w.b σ = matchingChartCoordinate z σ) :
    w.contacts = chartContacts w.η w.pivot z := by
  classical
  ext σ
  rw [mem_chartContacts, chart_gap_of_matching_products w.η w.pivot σ z hz]
  simp only [StrictMatchingSupport.contacts, Finset.mem_filter, Finset.mem_univ, true_and,
    matchingGap, sub_eq_zero]
  exact eq_comm

private theorem regular_support_of_chart {U : Matrix (Fin 4) (Fin 4) ℂ}
    (hU : IsUnitary U) (η : ℂ) (r : FourPerm) (z : MatchingChartVariable 2 → ℂ)
    (hreg : MvPolynomial.eval z (matchingChartRegularPolynomial 2) ≠ 0)
    (hmax : ∀ σ, 0 ≤ (chartMatchingGap η r z σ).re)
    (hpos : 0 < (η * MvPolynomial.eval z (matchingChartDeficitPolynomial U r)).re) :
    ∃ w : StrictMatchingSupport U, FourRegularSpectra w ∧
      w.contacts = chartContacts η r z := by
  obtain ⟨a, b, hz⟩ := exists_spectra_of_matchingChartCoordinate z
  obtain ⟨_, hn, hi⟩ := (eval_matchingChartRegularPolynomial_ne_zero z).mp hreg
  have hm (σ : FourPerm) : (η * matchingProduct a b σ).re ≤ (η * matchingProduct a b r).re := by
    apply sub_nonneg.mp
    exact (chart_gap_of_matching_products η r σ z hz) ▸ hmax σ
  have hs : (η * matchingProduct a b r).re < (η * determinantValue a b U).re := by
    rw [eval_matchingChartDeficitPolynomial z a b U hU r hz, mul_sub, Complex.sub_re] at hpos
    exact sub_pos.mp hpos
  let w : StrictMatchingSupport U := ⟨a, b, η, r, hm, hs⟩
  refine ⟨w, ⟨?_, ?_⟩, support_contacts_eq_chart w z hz⟩
  · intro i j hzero
    let σ : FourPerm := Equiv.swap j i
    have hprod : matchingProduct a b σ = 0 := Finset.prod_eq_zero (Finset.mem_univ j) (by
      simpa only [σ, Equiv.swap_apply_left] using hzero)
    exact hn σ ((hz σ).symm.trans hprod)
  · intro σ τ he
    apply hi
    rw [← hz σ, ← hz τ, he]

private theorem regular_support_increase {U : Matrix (Fin 4) (Fin 4) ℂ} (hU : IsUnitary U)
    (w : StrictMatchingSupport U) (hw : FourRegularSpectra w) (hsmall : w.contacts.card < 7) :
    ∃ v : StrictMatchingSupport U, FourRegularSpectra v ∧ w.contacts.card < v.contacts.card := by
  obtain ⟨z, hz, hcoords⟩ := regular_support_chart w hw
  have hc := support_contacts_eq_chart w z hcoords
  have hmax (σ : FourPerm) : 0 ≤ (chartMatchingGap w.η w.pivot z σ).re := by
    rw [chart_gap_of_matching_products w.η w.pivot σ z hcoords, matchingGap]
    exact sub_nonneg.mpr (w.maximal σ)
  have hpos : 0 < (w.η * MvPolynomial.eval z (matchingChartDeficitPolynomial U w.pivot)).re := by
    rw [eval_matchingChartDeficitPolynomial z w.a w.b U hU w.pivot hcoords, mul_sub, Complex.sub_re]
    exact sub_pos.mpr w.strict
  have hbound : (chartContacts w.η w.pivot z).card ≤ 2 * (2 + 2) - 2 := by
    rw [← hc]
    omega
  obtain ⟨z', hz', hp', hm', hmore⟩ :=
    exists_new_contact_at_twice_order_minus_two (n := 2) (by decide) U hU w.η w.pivot z
      hz hmax hpos hbound
  obtain ⟨v, hv, hc'⟩ := regular_support_of_chart hU w.η w.pivot z' hz' hm' hp'
  exact ⟨v, hv, by rw [hc, hc']; exact Finset.card_lt_card hmore⟩

/-- Failure in order four has a strict witness on a real orthogonal mixer
with regular spectra and at least seven contacts. -/
theorem conjecture_four_iff_no_regular_terminal_orthogonal_witness :
    Conjecture (Fin 4) ↔ ¬ ∃ O : Matrix.orthogonalGroup (Fin 4) ℝ,
      ∃ w : StrictMatchingSupport (Complex.ofRealHom.mapMatrix O.val),
        FourRegularSpectra w ∧ 7 ≤ w.contacts.card := by
  constructor
  · intro h
    rintro ⟨O, w, _⟩
    exact w.not_holds (h w.a w.b _ (isUnitary_ofReal_orthogonal O))
  · intro h
    apply conjecture_four_iff_orthogonal.mpr
    intro a b O
    by_contra hfail
    obtain ⟨w, hw⟩ := regular_support_of_failure a b hfail
    obtain ⟨v, hv, hreg⟩ := exists_strictMatchingSupport_at_least_preserving
      7 FourRegularSpectra w hw (regular_support_increase (isUnitary_ofReal_orthogonal O))
    exact h ⟨O, v, hreg, hv⟩

/-- The gap function in the row-to-column order used by the cost rays. -/
def fourTerminalGap {U : Matrix (Fin 4) (Fin 4) ℂ}
    (w : StrictMatchingSupport U) (p : Fin 24) : ℝ :=
  matchingGap w.a w.b w.η w.pivot (fourPerm p).symm

/-- The count of zero coordinates is the count of maximizing permutations. -/
theorem fourTerminalGap_zero_count {U : Matrix (Fin 4) (Fin 4) ℂ}
    (w : StrictMatchingSupport U) :
    (Finset.univ.filter fun p : Fin 24 => fourTerminalGap w p = 0).card = w.contacts.card := by
  classical
  let e : Fin 24 ≃ FourPerm := fourPermEquiv.trans (Equiv.inv FourPerm)
  let S := Finset.univ.filter fun p : Fin 24 => fourTerminalGap w p = 0
  have hmem (p : Fin 24) : p ∈ S ↔ e p ∈ w.contacts := by
    change p ∈ Finset.univ.filter (fun q => fourTerminalGap w q = 0) ↔
      (fourPerm p).symm ∈ w.contacts
    simp only [StrictMatchingSupport.contacts, Finset.mem_filter, Finset.mem_univ, true_and,
      fourTerminalGap, matchingGap, sub_eq_zero]
    exact eq_comm
  have hmap : S.map e.toEmbedding = w.contacts := by
    ext σ
    rw [Finset.mem_map]
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact (hmem p).mp hp
    · intro hσ
      exact ⟨e.symm σ, (hmem _).mpr (by simpa only [e.apply_symm_apply] using hσ),
        e.apply_symm_apply σ⟩
  change S.card = w.contacts.card
  rw [← hmap, Finset.card_map]

private theorem terminal_gap_has_coordinates {U : Matrix (Fin 4) (Fin 4) ℂ}
    (w : StrictMatchingSupport U) :
    ∃ m : Fin 14 → ℝ, fourMatchingEvaluation m = fourTerminalGap w := by
  let H := (w.η * matchingProduct w.a w.b w.pivot).re
  let c (i : Fin 14) := ((H : ℂ) * fourNoncrossingCoordinates
    (fourSpectralPoints (fun _ => 1) (fun _ => 0)) i).re
  let m (i : Fin 14) := (w.η * fourNoncrossingCoordinates (fourSpectralPoints w.a w.b) i).re
  have hc (p : Fin 24) : fourMatchingEvaluation c p = H := by
    simpa only [c, matchingProduct, add_zero, Finset.prod_const_one, mul_one, Complex.ofReal_re] using
      fourMatchingEvaluation_spectral_real_part (fun _ => 1) (fun _ => 0) (H : ℂ) p
  have hm (p : Fin 24) : fourMatchingEvaluation m p =
      (w.η * matchingProduct w.a w.b (fourPerm p).symm).re :=
    fourMatchingEvaluation_spectral_real_part w.a w.b w.η p
  refine ⟨c - m, funext fun p => ?_⟩
  have hsub : fourMatchingEvaluation (c - m) p =
      fourMatchingEvaluation c p - fourMatchingEvaluation m p := by
    fin_cases p <;> simp [fourMatchingEvaluation] <;> ring
  rw [hsub, hc, hm]
  rfl

private theorem terminal_gap_value_neg {U : Matrix (Fin 4) (Fin 4) ℂ} (hU : IsUnitary U)
    (w : StrictMatchingSupport U) : fourSupportCostValue U (fourTerminalGap w) < 0 := by
  let e : Fin 24 ≃ FourPerm := fourPermEquiv.trans (Equiv.inv FourPerm)
  let f (σ : FourPerm) := realSignedWeight U σ * matchingGap w.a w.b w.η w.pivot σ
  change (∑ p, f (e p)) < 0
  rw [Equiv.sum_comp e f]
  change (∑ σ, realSignedWeight U σ * matchingGap w.a w.b w.η w.pivot σ) < 0
  rw [← support_gap_eq w.a w.b U hU w.η w.pivot]
  exact sub_neg.mpr w.strict

private theorem orthogonal_as_submatrix (O : Matrix.orthogonalGroup (Fin 4) ℝ)
    (eRow eCol : FourPerm) :
    ∃ O' : Matrix.orthogonalGroup (Fin 4) ℝ, O'.val = O.val.submatrix eRow eCol := by
  let P := O.val.submatrix eRow eCol
  have hO := (Matrix.mem_orthogonalGroup_iff _ ℝ).mp O.property
  have hP : P * Pᵀ = 1 := by
    dsimp only [P]
    rw [Matrix.transpose_submatrix, Matrix.submatrix_mul_equiv, hO,
      Matrix.submatrix_one_equiv]
  exact ⟨⟨P, (Matrix.mem_orthogonalGroup_iff _ ℝ).mpr hP⟩, rfl⟩

private theorem matchingProduct_relabel_four (a b : Fin 4 → ℂ) (eRow eCol q : FourPerm) :
    matchingProduct (a ∘ eRow) (b ∘ eCol) q =
      matchingProduct a b (eRow * q * eCol⁻¹) := by
  unfold matchingProduct
  rw [← Equiv.prod_comp eCol (fun j => a ((eRow * q * eCol⁻¹) j) + b j)]
  apply Finset.prod_congr rfl
  intro j _
  change a (eRow (q j)) + b (eCol j) =
    a (eRow (q (eCol.symm (eCol j)))) + b (eCol j)
  rw [eCol.symm_apply_apply]

private theorem transport_regular_orthogonal_gap
    (O O' : Matrix.orthogonalGroup (Fin 4) ℝ)
    (w : StrictMatchingSupport (Complex.ofRealHom.mapMatrix O.val))
    (hw : FourRegularSpectra w) (a b : Fin 4 → ℂ) (hn : ∀ i j, a i + b j ≠ 0)
    (T : FourPerm ≃ FourPerm) {s : ℝ} (hs : 0 < s)
    (hprod : ∀ q, matchingProduct a b q = matchingProduct w.a w.b (T q))
    (hdet : determinantValue a b (Complex.ofRealHom.mapMatrix O'.val) =
      determinantValue w.a w.b (Complex.ofRealHom.mapMatrix O.val)) :
    ∃ v : StrictMatchingSupport (Complex.ofRealHom.mapMatrix O'.val),
      FourRegularSpectra v ∧ v.contacts.card = w.contacts.card ∧
      ∀ q, matchingGap v.a v.b v.η v.pivot q = s * matchingGap w.a w.b w.η w.pivot (T q) := by
  classical
  let η := (s : ℂ) * w.η
  have hscale (z : ℂ) : (η * z).re = s * (w.η * z).re := by
    simp only [η, mul_assoc, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      sub_zero]
  have hscore (q : FourPerm) : (η * matchingProduct a b q).re =
      s * (w.η * matchingProduct w.a w.b (T q)).re := by rw [hscale, hprod]
  let v : StrictMatchingSupport (Complex.ofRealHom.mapMatrix O'.val) :=
    ⟨a, b, η, T.symm w.pivot, fun q => by
      rw [hscore, hscore, T.apply_symm_apply]
      exact mul_le_mul_of_nonneg_left (w.maximal (T q)) hs.le, by
      rw [hscore, T.apply_symm_apply, hscale, hdet]
      exact mul_lt_mul_of_pos_left w.strict hs⟩
  have hcontact (q : FourPerm) : q ∈ v.contacts ↔ T q ∈ w.contacts := by
    simp only [StrictMatchingSupport.contacts, Finset.mem_filter, Finset.mem_univ, true_and]
    change (η * matchingProduct a b q).re = (η * matchingProduct a b (T.symm w.pivot)).re ↔ _
    rw [hscore, hscore, T.apply_symm_apply]
    exact ⟨mul_left_cancel₀ hs.ne', congrArg (fun x : ℝ => s * x)⟩
  have hmap : v.contacts.map T.toEmbedding = w.contacts := by
    ext q
    rw [Finset.mem_map]
    constructor
    · rintro ⟨p, hp', rfl⟩
      exact (hcontact p).mp hp'
    · intro hq
      exact ⟨T.symm q, (hcontact _).mpr (by simpa only [T.apply_symm_apply] using hq),
        T.apply_symm_apply q⟩
  refine ⟨v, ⟨hn, ?_⟩, ?_, ?_⟩
  · intro σ τ he
    apply T.injective
    apply hw.2
    exact (hprod σ).symm.trans (he.trans (hprod τ))
  · rw [← hmap, Finset.card_map]
  · intro q
    change (η * matchingProduct a b (T.symm w.pivot)).re -
        (η * matchingProduct a b q).re = s * matchingGap w.a w.b w.η w.pivot (T q)
    rw [hscore, hscore, T.apply_symm_apply, ← mul_sub, matchingGap]

/-- Independent changes of row and column labels transport a regular terminal
witness. Positive scaling changes the support direction and preserves its contacts. -/
theorem four_regular_orthogonal_gap_relabel (O : Matrix.orthogonalGroup (Fin 4) ℝ)
    (w : StrictMatchingSupport (Complex.ofRealHom.mapMatrix O.val)) (hw : FourRegularSpectra w)
    (eRow eCol : FourPerm) {s : ℝ} (hs : 0 < s) :
    ∃ O' : Matrix.orthogonalGroup (Fin 4) ℝ,
      ∃ v : StrictMatchingSupport (Complex.ofRealHom.mapMatrix O'.val),
        FourRegularSpectra v ∧ v.contacts.card = w.contacts.card ∧
        ∀ p, fourTerminalGap v p = s * fourTerminalGap w
          (fourPermIndex (eCol * fourPerm p * eRow⁻¹)) := by
  let T : FourPerm ≃ FourPerm := (Equiv.mulLeft eRow).trans (Equiv.mulRight eCol⁻¹)
  obtain ⟨O', hO'⟩ := orthogonal_as_submatrix O eRow eCol
  have hdet : determinantValue (w.a ∘ eRow) (w.b ∘ eCol) (Complex.ofRealHom.mapMatrix O'.val) =
      determinantValue w.a w.b (Complex.ofRealHom.mapMatrix O.val) := by
    rw [hO']
    exact determinantValue_reindex eRow eCol w.a w.b (Complex.ofRealHom.mapMatrix O.val)
  obtain ⟨v, hv, hc, hg⟩ := transport_regular_orthogonal_gap O O' w hw
    (w.a ∘ eRow) (w.b ∘ eCol) (fun i j => hw.1 (eRow i) (eCol j)) T hs
    (matchingProduct_relabel_four w.a w.b eRow eCol) hdet
  refine ⟨O', v, hv, hc, fun p => ?_⟩
  have he : (T (fourPerm p).symm)⁻¹ = eCol * fourPerm p * eRow⁻¹ := by
    change (eRow * (fourPerm p)⁻¹ * eCol⁻¹)⁻¹ = _
    simp only [mul_inv_rev, inv_inv, mul_assoc]
  have hi : fourPerm (fourPermIndex (eCol * fourPerm p * eRow⁻¹)) =
      eCol * fourPerm p * eRow⁻¹ := fourPermEquiv.apply_symm_apply _
  rw [fourTerminalGap, fourTerminalGap, hi]
  change matchingGap v.a v.b v.η v.pivot (fourPerm p).symm =
    s * matchingGap w.a w.b w.η w.pivot (eCol * fourPerm p * eRow⁻¹)⁻¹
  rw [← he, inv_inv]
  exact hg _

/-- Swapping the spectra and transposing the real mixer inverts the labels of
the matching gap and preserves the regular terminal witness conditions. -/
theorem four_regular_orthogonal_gap_transpose (O : Matrix.orthogonalGroup (Fin 4) ℝ)
    (w : StrictMatchingSupport (Complex.ofRealHom.mapMatrix O.val)) (hw : FourRegularSpectra w) :
    ∃ O' : Matrix.orthogonalGroup (Fin 4) ℝ,
      ∃ v : StrictMatchingSupport (Complex.ofRealHom.mapMatrix O'.val),
        FourRegularSpectra v ∧ v.contacts.card = w.contacts.card ∧
        ∀ p, fourTerminalGap v p = fourTerminalGap w (fourPermIndex (fourPerm p).symm) := by
  let U := Complex.ofRealHom.mapMatrix O.val
  let O' : Matrix.orthogonalGroup (Fin 4) ℝ :=
    ⟨O.valᵀ, (Matrix.mem_orthogonalGroup_iff' _ ℝ).mpr (by
      rw [Matrix.transpose_transpose]
      exact (Matrix.mem_orthogonalGroup_iff _ ℝ).mp O.property)⟩
  have hU' : Complex.ofRealHom.mapMatrix O'.val = Uᴴ := by
    ext i j
    change (O.val j i : ℂ) = star (O.val j i : ℂ)
    simp
  have hdet : determinantValue w.b w.a (Complex.ofRealHom.mapMatrix O'.val) =
      determinantValue w.a w.b U := by
    rw [hU']
    simpa only [determinantValue, add_comm] using
      (determinantValue_left_conjugation w.b w.a U (isUnitary_ofReal_orthogonal O)).symm
  have hprod (q : FourPerm) : matchingProduct w.b w.a q =
      matchingProduct w.a w.b (Equiv.inv FourPerm q) := by
    change matchingProduct w.b w.a q = matchingProduct w.a w.b q.symm
    rw [matchingProduct_inverse]
    simp only [matchingProduct, add_comm]
  have hn (i j : Fin 4) : w.b i + w.a j ≠ 0 := by rw [add_comm]; exact hw.1 j i
  obtain ⟨v, hv, hc, hg⟩ := transport_regular_orthogonal_gap O O' w hw w.b w.a hn
    (Equiv.inv FourPerm) (show (0 : ℝ) < 1 from zero_lt_one) hprod hdet
  refine ⟨O', v, hv, hc, fun p => ?_⟩
  have hi : fourPerm (fourPermIndex (fourPerm p).symm) = (fourPerm p).symm :=
    fourPermEquiv.apply_symm_apply _
  rw [fourTerminalGap, fourTerminalGap, hi]
  simpa only [one_mul] using hg (fourPerm p).symm

private theorem canonical_gap_of_relabel
    (O : Matrix.orthogonalGroup (Fin 4) ℝ)
    (w : StrictMatchingSupport (Complex.ofRealHom.mapMatrix O.val))
    (hw : FourRegularSpectra w) (swap : Bool) (r : FourPerm) (P : Fin 24 → ℝ)
    {t : ℝ} (ht : 0 < t) (hgap : fourTerminalGap w = fourCostRelabel swap r
      (P + t • mixedCostRay 0)) :
    ∃ O' : Matrix.orthogonalGroup (Fin 4) ℝ,
      ∃ v : StrictMatchingSupport (Complex.ofRealHom.mapMatrix O'.val),
        FourRegularSpectra v ∧ v.contacts.card = w.contacts.card ∧
        fourTerminalGap v = t⁻¹ • P + mixedCostRay 0 := by
  let d : FourPerm := fourPerm (if swap then 1 else 0)
  obtain ⟨O', v, hv, hc, hg⟩ := four_regular_orthogonal_gap_relabel O w hw r d⁻¹ (inv_pos.mpr ht)
  refine ⟨O', v, hv, hc, funext fun p => ?_⟩
  rw [hg, hgap]
  have hi : fourPerm (fourPermIndex (d⁻¹ * fourPerm p * r⁻¹)) = d⁻¹ * fourPerm p * r⁻¹ :=
    fourPermEquiv.apply_symm_apply _
  have hj : d * (d⁻¹ * fourPerm p * r⁻¹) * r = fourPerm p := by
    rw [mul_assoc d⁻¹, ← mul_assoc d d⁻¹, mul_inv_cancel, one_mul, mul_assoc, inv_mul_cancel,
      mul_one]
  change t⁻¹ * (P + t • mixedCostRay 0)
      (fourPermIndex (d * fourPerm (fourPermIndex (d⁻¹ * fourPerm p * r⁻¹)) * r)) =
    t⁻¹ * P p + mixedCostRay 0 p
  rw [hi, hj, fourPermIndex_fourPerm]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add, ← mul_assoc, inv_mul_cancel₀ ht.ne',
    one_mul]

/-- An order-four counterexample has a regular orthogonal witness with at
least seven contacts and mixed coefficient one in the canonical cost. -/
theorem exists_canonical_mixed_terminal_witness (h : ¬ Conjecture (Fin 4)) :
    ∃ O : Matrix.orthogonalGroup (Fin 4) ℝ,
      ∃ w : StrictMatchingSupport (Complex.ofRealHom.mapMatrix O.val),
        FourRegularSpectra w ∧ 7 ≤ w.contacts.card ∧
        ∃ c : Fin 34 → ℝ, (∀ j, 0 ≤ c j) ∧
          (∀ j ∉ fourCanonicalCapOrdinaryRays, c j = 0) ∧
          fourTerminalGap w = (∑ j, c j • ordinaryCostRay j) + mixedCostRay 0 := by
  classical
  have hw : ∃ O : Matrix.orthogonalGroup (Fin 4) ℝ,
      ∃ w : StrictMatchingSupport (Complex.ofRealHom.mapMatrix O.val),
        FourRegularSpectra w ∧ 7 ≤ w.contacts.card := by
    by_contra hn
    exact h (conjecture_four_iff_no_regular_terminal_orthogonal_witness.mpr hn)
  obtain ⟨O, w, hreg, hc⟩ := hw
  have hU := isUnitary_ofReal_orthogonal O
  obtain ⟨m, hm⟩ := terminal_gap_has_coordinates w
  have hnonneg (p : Fin 24) : 0 ≤ fourMatchingEvaluation m p := by
    rw [hm]
    exact sub_nonneg.mpr (w.maximal (fourPerm p).symm)
  obtain ⟨u, v, hu, hv, hdecomp⟩ := four_cost_cone_decomposition m hnonneg
  rw [hm] at hdecomp
  rcases fourSupportCost_normalForm_of_nonnegative_expansion _ u v hu hv hdecomp with
      hordinary | ⟨swap, r, P, t, hP, ht, hg⟩
  · exact False.elim ((not_lt_of_ge (fourSupportCostValue_ordinaryNonnegative _ hU hordinary))
      (terminal_gap_value_neg hU w))
  · obtain ⟨O', w', hreg', hcard, hg'⟩ := canonical_gap_of_relabel O w hreg swap r P ht hg
    obtain ⟨c, hcn, hcs, rfl⟩ := hP
    refine ⟨O', w', hreg', hcard.symm ▸ hc, fun j => t⁻¹ * c j,
      fun j => mul_nonneg (inv_nonneg.mpr ht.le) (hcn j), fun j hj => ?_, ?_⟩
    · rw [hcs j hj, mul_zero]
    · simpa only [Finset.smul_sum, smul_smul, smul_eq_mul] using hg'

/-- A nonzero support height excludes a full rectangle of two disjoint swaps
in the contact set of a regular witness. -/
theorem four_terminal_nonzero_height_no_rectangle {U : Matrix (Fin 4) (Fin 4) ℂ}
    (w : StrictMatchingSupport U) (hw : FourRegularSpectra w)
    (hH : (w.η * matchingProduct w.a w.b w.pivot).re ≠ 0)
    (q : FourPerm) (i j k l : Fin 4)
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l)
    (h₀₀ : q ∈ w.contacts) (h₀₁ : q * Equiv.swap i j ∈ w.contacts)
    (h₁₀ : q * Equiv.swap k l ∈ w.contacts) :
    q * Equiv.swap i j * Equiv.swap k l ∉ w.contacts := by
  classical
  intro h₁₁
  have hη : w.η ≠ 0 := fun h => hH (by simp [h])
  obtain ⟨ha, hb⟩ := injective_spectra_of_matchingProduct_injective hw.2
  simp only [StrictMatchingSupport.contacts, Finset.mem_filter, Finset.mem_univ, true_and]
    at h₀₀ h₀₁ h₁₀ h₁₁
  exact hH (matchingProduct_disjoint_swaps_common_height_eq_zero w.a w.b q i j k l
    hij hik hil hjk hjl hkl ha hb hw.1 hη h₀₀ h₀₁ h₁₀ h₁₁)

end

end MOC
