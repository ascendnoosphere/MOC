import MOC.FourKleinMatchingSquares

/-! The finite coordinate changes and the full prism-to-squares implication. -/

open BigOperators Matrix

namespace MOC

noncomputable section

/-- The four real sign triples with product one. -/
def kleinEvenSigns : Fin 4 → Fin 3 → ℝ := ![![1, 1, 1],
    ![-1, 1, -1],
    ![1, -1, -1],
    ![-1, -1, 1]]

private def kleinAxisChange : Fin 3 → Fin 24 → Fin 24 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23],
    ![0, 1, 5, 3, 4, 2, 6, 7, 19, 13, 18, 12, 11, 9, 21, 15, 16, 17, 10, 8, 20, 14, 22, 23],
    ![0, 2, 1, 3, 4, 5, 21, 7, 15, 9, 17, 11, 20, 22, 14, 8, 16, 10, 18, 19, 12, 6, 13, 23]]

private def kleinSignChange : Fin 4 → Fin 24 → Fin 24 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23],
    ![0, 17, 10, 11, 4, 5, 22, 7, 8, 9, 2, 3, 20, 21, 14, 15, 16, 1, 18, 19, 12, 13, 6, 23],
    ![0, 17, 2, 12, 4, 18, 22, 7, 8, 14, 10, 20, 3, 13, 9, 15, 16, 1, 5, 19, 11, 21, 6, 23],
    ![0, 1, 10, 20, 4, 18, 6, 7, 8, 14, 2, 12, 11, 21, 9, 15, 16, 17, 5, 19, 3, 13, 22, 23]]

private def kleinCycleChange : Fin 24 → Fin 24 :=
  ![0, 1, 2, 4, 3, 5, 6, 7, 12, 18, 13, 19, 8, 10, 14, 20, 16, 22, 9, 11, 15, 21, 17, 23]

private theorem kleinAxisChange_involutive (h : Fin 3) (j : Fin 24) :
    kleinAxisChange h (kleinAxisChange h j) = j := by
  revert h j
  decide +kernel

private theorem kleinSignChange_involutive (h : Fin 4) (j : Fin 24) :
    kleinSignChange h (kleinSignChange h j) = j := by
  revert h j
  decide +kernel

private theorem kleinCycleChange_involutive (j : Fin 24) :
    kleinCycleChange (kleinCycleChange j) = j := by
  revert j
  decide +kernel

private theorem klein_axis_cost (h : Fin 3) (β p q : Fin 3 → ℝ) (c₋ : ℝ) (j : Fin 24) :
    kleinMatchingCost β p q c₋ (kleinAxisChange h j) =
      kleinMatchingCost (β ∘ Equiv.swap 0 h) (p ∘ Equiv.swap 0 h)
        (q ∘ Equiv.swap 0 h) c₋ j := by
  fin_cases h <;> fin_cases j <;>
    norm_num [kleinAxisChange, kleinMatchingCost, kleinCycle, kleinFaceIndicator, kleinFaceSignPlus,
      kleinFaceSignMinus, kleinMatchingFeatureTable, Fin.sum_univ_three, Function.comp_apply,
      Equiv.swap_apply_def] <;> ring

private theorem klein_sign_cost (h : Fin 4) (β p q : Fin 3 → ℝ) (c₋ : ℝ) (j : Fin 24) :
    kleinMatchingCost β p q c₋ (kleinSignChange h j) =
      kleinMatchingCost β (fun i => kleinEvenSigns h i * p i) q c₋ j := by
  fin_cases h <;> fin_cases j <;>
    norm_num [kleinSignChange, kleinEvenSigns, kleinMatchingCost, kleinCycle, kleinFaceIndicator,
      kleinFaceSignPlus, kleinFaceSignMinus, kleinMatchingFeatureTable, Fin.sum_univ_three] <;> ring

private theorem klein_cycle_cost (β p q : Fin 3 → ℝ) (c₋ : ℝ) (j : Fin 24) :
    kleinMatchingCost β p q c₋ (kleinCycleChange j) =
      kleinMatchingCost β q p ((∑ i, β i) - c₋) j := by
  fin_cases j <;>
    norm_num [kleinCycleChange, kleinMatchingCost, kleinCycle, kleinFaceIndicator,
      kleinFaceSignPlus, kleinFaceSignMinus, kleinMatchingFeatureTable, Fin.sum_univ_three] <;> ring

private theorem klein_cost_zero (β p q : Fin 3 → ℝ) (c₋ : ℝ) (j : Fin 24)
    (hj : j ∈ normalKleinFourContacts) : kleinMatchingCost β p q c₋ j = 0 := by
  fin_cases j <;>
    norm_num [normalKleinFourContacts] at hj <;>
    norm_num [kleinMatchingCost, kleinCycle, kleinFaceIndicator, kleinFaceSignPlus,
      kleinFaceSignMinus, kleinMatchingFeatureTable, Fin.sum_univ_three]

private theorem klein_cost_mem (β p q : Fin 3 → ℝ) (c₋ : ℝ) :
    kleinMatchingCost β p q c₋ ∈ kleinMatchingSpace := by
  have heq : kleinMatchingCost β p q c₋ =
      -c₋ • kleinCycle + ∑ i : Fin 3, (β i • kleinFaceIndicator i +
        p i • kleinFaceSignPlus i + q i • kleinFaceSignMinus i) := by
    funext j
    simp only [kleinMatchingCost, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_apply]
  rw [heq]
  exact kleinMatchingSpace.add_mem (kleinMatchingSpace.smul_mem _ kleinCycle_mem)
    (kleinMatchingSpace.sum_mem fun i _ =>
      kleinMatchingSpace.add_mem
        (kleinMatchingSpace.add_mem (kleinMatchingSpace.smul_mem _ (kleinFaceIndicator_mem i))
          (kleinMatchingSpace.smul_mem _ (kleinFaceSignPlus_mem i)))
        (kleinMatchingSpace.smul_mem _ (kleinFaceSignMinus_mem i)))

private theorem klein_sos_pullback (T : Fin 24 → Fin 24)
    (hT : ∀ (β p q : Fin 3 → ℝ) (c₋ : ℝ), (kleinMatchingCost β p q c₋) ∘ T ∈ kleinMatchingSpace)
    {g : KleinMatchingFunction} (hz : ∀ j ∈ normalKleinFourContacts, g j = 0)
    (hg : IsRealMatchingSOS g) : IsRealMatchingSOS (g ∘ T) := by
  obtain ⟨n, f, hf⟩ := hg
  have hvan (i : Fin n) (j : Fin 24) (hj : j ∈ normalKleinFourContacts) :
      fourMatchingEvaluation (f i) j = 0 := by
    have hsum : (∑ k : Fin n, fourMatchingEvaluation (f k) j ^ 2) = 0 :=
      (hf j).symm.trans (hz j hj)
    exact sq_eq_zero_iff.mp ((Finset.sum_eq_zero_iff_of_nonneg
      (fun k _ => sq_nonneg (fourMatchingEvaluation (f k) j))).mp hsum i (Finset.mem_univ i))
  have hr (i : Fin n) : ∃ x : Fin 14 → ℝ,
      fourMatchingEvaluation x = (fourMatchingEvaluation (f i)) ∘ T := by
    obtain ⟨β, p, q, c₋, he⟩ := exists_kleinMatchingCost (f i) (hvan i)
    rw [he]
    exact hT β p q c₋
  choose f' h' using hr
  refine ⟨n, f', fun j => ?_⟩
  change g (T j) = _
  rw [hf (T j)]
  exact Finset.sum_congr rfl (fun i _ => congrArg (fun v : ℝ => v ^ 2) (congrFun (h' i) j).symm)

private def kleinPullThree (e : Fin 3 → Fin 3) : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ) where
  toFun x i := x (e i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def kleinScaleThree (e : Fin 3 → ℝ) : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ) where
  toFun x i := e i * x i
  map_add' x y := by funext i; exact mul_add (e i) (x i) (y i)
  map_smul' r x := by
    funext i
    change e i * (r * x i) = r * (e i * x i)
    ring

private def kleinPrismAxis (h : Fin 3) : KleinPrismSpace →ₗ[ℝ] KleinPrismSpace where
  toFun x := (kleinPullThree (Equiv.swap 0 h) x.1,
    kleinPullThree (Equiv.swap 0 h) x.2.1, kleinPullThree (Equiv.swap 0 h) x.2.2)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def kleinPrismSign (h : Fin 4) : KleinPrismSpace →ₗ[ℝ] KleinPrismSpace where
  toFun x := (kleinScaleThree (kleinEvenSigns h) x.1,
    kleinScaleThree (kleinEvenSigns h) x.2.1, x.2.2)
  map_add' x y := by
    apply Prod.ext
    · exact map_add _ _ _
    · apply Prod.ext
      · exact map_add _ _ _
      · rfl
  map_smul' r x := by
    apply Prod.ext
    · exact map_smul _ _ _
    · apply Prod.ext
      · exact map_smul _ _ _
      · rfl

private def kleinPrismSwap : KleinPrismSpace →ₗ[ℝ] KleinPrismSpace where
  toFun x := (x.1, x.2.2, x.2.1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem klein_axis_prism (h : Fin 3) (β p q : Fin 3 → ℝ) (c₋ : ℝ) (x : KleinPrismSpace) :
    kleinPrismForm β p q c₋ (kleinPrismAxis h x) =
      kleinPrismForm (β ∘ Equiv.swap 0 h) (p ∘ Equiv.swap 0 h) (q ∘ Equiv.swap 0 h) c₋ x := by
  fin_cases h <;>
    norm_num [kleinPrismAxis, kleinPullThree, kleinPrismForm, kleinPrismOff, Fin.sum_univ_three,
      Function.comp_apply, Equiv.swap_apply_def] <;> ring

private theorem klein_sign_prism (h : Fin 4) (β p q : Fin 3 → ℝ) (c₋ : ℝ) (x : KleinPrismSpace) :
    kleinPrismForm β p q c₋ (kleinPrismSign h x) =
      kleinPrismForm β (fun i => kleinEvenSigns h i * p i) q c₋ x := by
  fin_cases h <;>
    norm_num [kleinPrismSign, kleinScaleThree, kleinEvenSigns, kleinPrismForm, kleinPrismOff,
      Fin.sum_univ_three] <;> ring

private theorem klein_cycle_prism (β p q : Fin 3 → ℝ) (c₋ : ℝ) (x : KleinPrismSpace) :
    kleinPrismForm β p q c₋ (kleinPrismSwap x) =
      kleinPrismForm β q p ((∑ i, β i) - c₋) x := by
  simp only [kleinPrismSwap, LinearMap.coe_mk, AddHom.coe_mk, kleinPrismForm, sub_sub_cancel]
  ring

/-- There is no strictly negative five-dimensional compression of the prism. -/
def KleinPrismBound (β p q : Fin 3 → ℝ) (c₋ : ℝ) : Prop :=
  ∀ L : (Fin 5 → ℝ) →ₗ[ℝ] KleinPrismSpace, ∃ x ≠ 0, 0 ≤ kleinPrismForm β p q c₋ (L x)

private theorem klein_symmetry_sos {T : Fin 24 → Fin 24} {A : KleinPrismSpace →ₗ[ℝ] KleinPrismSpace}
    (hT : ∀ j, T (T j) = j)
    (hcos : ∀ (β p q : Fin 3 → ℝ) (c₋ : ℝ),
      (kleinMatchingCost β p q c₋) ∘ T ∈ kleinMatchingSpace)
    {β p q β' p' q' : Fin 3 → ℝ} {c c' : ℝ}
    (hcost : ∀ j, kleinMatchingCost β p q c (T j) = kleinMatchingCost β' p' q' c' j)
    (hprism : ∀ x, kleinPrismForm β p q c (A x) = kleinPrismForm β' p' q' c' x)
    (hpos : ∀ j, 0 ≤ kleinMatchingCost β p q c j)
    (hbound : KleinPrismBound β p q c)
    (solve : (∀ j, 0 ≤ kleinMatchingCost β' p' q' c' j) →
      KleinPrismBound β' p' q' c' → IsRealMatchingSOS (kleinMatchingCost β' p' q' c')) :
    IsRealMatchingSOS (kleinMatchingCost β p q c) := by
  have hp' (j : Fin 24) : 0 ≤ kleinMatchingCost β' p' q' c' j := by
    rw [← hcost]
    exact hpos (T j)
  have hb' : KleinPrismBound β' p' q' c' := by
    intro L
    obtain ⟨x, hx, hv⟩ := hbound (A.comp L)
    refine ⟨x, hx, ?_⟩
    simpa only [LinearMap.comp_apply, hprism] using hv
  have hg := klein_sos_pullback T hcos (klein_cost_zero β' p' q' c') (solve hp' hb')
  convert hg using 1
  funext j
  change kleinMatchingCost β p q c j = kleinMatchingCost β' p' q' c' (T j)
  rw [← hcost, hT]

private theorem klein_cost_plus_cycle (β p q : Fin 3 → ℝ) (c₋ : ℝ)
    (h : ∀ j, 0 ≤ kleinMatchingCost β p q c₋ j) (e : Fin 4) :
    0 ≤ (∑ i, β i) - c₋ + ∑ i, kleinEvenSigns e i * p i := by
  have ht := h ((![3, 11, 12, 20] : Fin 4 → Fin 24) e)
  fin_cases e <;>
    norm_num [kleinMatchingCost, kleinCycle, kleinFaceIndicator, kleinFaceSignPlus,
      kleinFaceSignMinus, kleinMatchingFeatureTable, kleinEvenSigns, Fin.sum_univ_three] at ht ⊢ <;>
    linarith only [ht]

private theorem klein_even_sign_of_absolute_failure (β p q : Fin 3 → ℝ) (c₋ : ℝ)
    (h : ∀ j, 0 ≤ kleinMatchingCost β p q c₋ j)
    (hf : (∑ i, β i) - c₋ < ∑ i, |p i|) :
    ∃ e : Fin 4, ∀ i, 0 < kleinEvenSigns e i * p i := by
  have hc0 := klein_cost_plus_cycle β p q c₋ h 0
  have hc1 := klein_cost_plus_cycle β p q c₋ h 1
  have hc2 := klein_cost_plus_cycle β p q c₋ h 2
  have hc3 := klein_cost_plus_cycle β p q c₋ h 3
  norm_num [kleinEvenSigns, Fin.sum_univ_three] at hc0 hc1 hc2 hc3 hf
  rcases lt_trichotomy (p 0) 0 with h0 | h0 | h0 <;>
    rcases lt_trichotomy (p 1) 0 with h1 | h1 | h1 <;>
    rcases lt_trichotomy (p 2) 0 with h2 | h2 | h2
  all_goals
    first
    | exact ⟨0, by intro i; fin_cases i <;> norm_num [kleinEvenSigns] <;> linarith only [h0,h1,h2]⟩
    | exact ⟨1, by intro i; fin_cases i <;> norm_num [kleinEvenSigns] <;> linarith only [h0,h1,h2]⟩
    | exact ⟨2, by intro i; fin_cases i <;> norm_num [kleinEvenSigns] <;> linarith only [h0,h1,h2]⟩
    | exact ⟨3, by intro i; fin_cases i <;> norm_num [kleinEvenSigns] <;> linarith only [h0,h1,h2]⟩
    | exfalso
      first | rw [abs_of_neg h0] at hf | rw [abs_of_pos h0] at hf | rw [h0, abs_zero] at hf
      first | rw [abs_of_neg h1] at hf | rw [abs_of_pos h1] at hf | rw [h1, abs_zero] at hf
      first | rw [abs_of_neg h2] at hf | rw [abs_of_pos h2] at hf | rw [h2, abs_zero] at hf
      linarith only [hc0, hc1, hc2, hc3, hf, h0, h1, h2]

private theorem klein_sos_of_sorted_positive (β p q : Fin 3 → ℝ) (c₋ : ℝ)
    (h : ∀ j, 0 ≤ kleinMatchingCost β p q c₋ j) (hbound : KleinPrismBound β p q c₋)
    (hp : ∀ i, 0 < p i) (hmax : ∀ i, p i ≤ p 0)
    (hf : (∑ i, β i) - c₋ < ∑ i, p i) :
    IsRealMatchingSOS (kleinMatchingCost β p q c₋) := by
  let t := (∑ i, p i) - ((∑ i, β i) - c₋)
  let u (i : Fin 3) := 2 * p i - t
  have ht : 0 < t := sub_pos.mpr hf
  have hu (i : Fin 3) : 0 ≤ u i := by
    have hc1 := klein_cost_plus_cycle β p q c₋ h 1
    have hc2 := klein_cost_plus_cycle β p q c₋ h 2
    have hc3 := klein_cost_plus_cycle β p q c₋ h 3
    fin_cases i <;> norm_num [u, t, kleinEvenSigns, Fin.sum_univ_three] at hc1 hc2 hc3 ⊢ <;>
      linarith only [hc1, hc2, hc3]
  let a := Real.sqrt (u 0)
  let b := Real.sqrt (u 1)
  let c := Real.sqrt (u 2)
  have hm (i : Fin 3) : u i ≤ u 0 := by dsimp only [u]; linarith only [hmax i]
  let v₊ (i : Fin 3) := β i - p i + q i
  let v₋ (i : Fin 3) := β i - p i - q i
  have hv₊ (i : Fin 3) : 0 ≤ v₊ i := by
    have hr := kleinMatchingCost_rectangle β p q c₋ h i
    rw [abs_of_pos (hp i)] at hr
    dsimp only [v₊]
    linarith only [hr, neg_abs_le (q i)]
  have hv₋ (i : Fin 3) : 0 ≤ v₋ i := by
    have hr := kleinMatchingCost_rectangle β p q c₋ h i
    rw [abs_of_pos (hp i)] at hr
    dsimp only [v₋]
    linarith only [hr, le_abs_self (q i)]
  have heU : (![a ^ 2, b ^ 2, c ^ 2] : Fin 3 → ℝ) = u := by
    funext i
    fin_cases i
    · exact Real.sq_sqrt (hu 0)
    · exact Real.sq_sqrt (hu 1)
    · exact Real.sq_sqrt (hu 2)
  have heP : (fun i => (t + u i) / 2) = p := by
    funext i
    dsimp only [u]
    ring
  have heβ : (fun i => p i + (v₊ i + v₋ i) / 2) = β := by
    funext i
    dsimp only [v₊, v₋]
    ring
  have heq : (fun i => (v₊ i - v₋ i) / 2) = q := by
    funext i
    dsimp only [v₊, v₋]
    ring
  have heC : (∑ i, β i) - (t + ∑ i, u i) / 2 = c₋ := by
    simp only [u, t, Fin.sum_univ_three]
    ring
  have cert := klein_mixed_cap_sos_of_no_negative_five a b c t v₊ v₋
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) (Real.sqrt_le_sqrt (hm 1))
    (Real.sqrt_le_sqrt (hm 2)) ht hv₊ hv₋
  dsimp only at cert
  simp only [heU, heP, heβ, heq, heC] at cert
  exact cert hbound

private theorem klein_sos_of_positive (β p q : Fin 3 → ℝ) (c₋ : ℝ)
    (h : ∀ j, 0 ≤ kleinMatchingCost β p q c₋ j) (hbound : KleinPrismBound β p q c₋)
    (hp : ∀ i, 0 < p i)
    (hf : (∑ i, β i) - c₋ < ∑ i, p i) :
    IsRealMatchingSOS (kleinMatchingCost β p q c₋) := by
  classical
  obtain ⟨i, _, hi⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin 3)) p Finset.univ_nonempty
  apply klein_symmetry_sos (kleinAxisChange_involutive i) _ (klein_axis_cost i β p q c₋)
    (klein_axis_prism i β p q c₋) h hbound
  · intro β' p' q' c'
    have he : (kleinMatchingCost β' p' q' c') ∘ kleinAxisChange i =
      kleinMatchingCost (β' ∘ Equiv.swap 0 i) (p' ∘ Equiv.swap 0 i) (q' ∘ Equiv.swap 0 i) c' :=
      funext (klein_axis_cost i β' p' q' c')
    rw [he]
    exact klein_cost_mem _ _ _ _
  · intro h' hb'
    apply klein_sos_of_sorted_positive _ _ _ _ h' hb' (fun j => hp _) (fun j => ?_) ?_
    · change p (Equiv.swap 0 i j) ≤ p (Equiv.swap 0 i 0)
      rw [Equiv.swap_apply_left]
      exact hi _ (Finset.mem_univ _)
    · simpa only [Function.comp_apply, Equiv.sum_comp] using hf

private theorem klein_sos_of_plus_failure (β p q : Fin 3 → ℝ) (c₋ : ℝ)
    (h : ∀ j, 0 ≤ kleinMatchingCost β p q c₋ j) (hbound : KleinPrismBound β p q c₋)
    (hf : (∑ i, β i) - c₋ < ∑ i, |p i|) :
    IsRealMatchingSOS (kleinMatchingCost β p q c₋) := by
  obtain ⟨e, he⟩ := klein_even_sign_of_absolute_failure β p q c₋ h hf
  apply klein_symmetry_sos (kleinSignChange_involutive e) _ (klein_sign_cost e β p q c₋)
    (klein_sign_prism e β p q c₋) h hbound
  · intro β' p' q' c'
    have hr : (kleinMatchingCost β' p' q' c') ∘ kleinSignChange e =
      kleinMatchingCost β' (fun i => kleinEvenSigns e i * p' i) q' c' :=
      funext (klein_sign_cost e β' p' q' c')
    rw [hr]
    exact klein_cost_mem _ _ _ _
  · intro hp hb
    apply klein_sos_of_positive _ _ _ _ hp hb he
    have ha (i : Fin 3) : kleinEvenSigns e i * p i = |p i| := by
      have hs : |kleinEvenSigns e i| = 1 := by
        fin_cases e <;> fin_cases i <;> norm_num [kleinEvenSigns]
      rw [← abs_of_pos (he i), abs_mul, hs, one_mul]
    simpa only [ha] using hf

/-- The complete prism-to-squares implication on the normal Klein-four
contact chart, with either sign sector and all boundary budgets. -/
theorem klein_matching_sos_of_prism_bound (β p q : Fin 3 → ℝ) (c₋ : ℝ)
    (h : ∀ j, 0 ≤ kleinMatchingCost β p q c₋ j) (hbound : KleinPrismBound β p q c₋) :
    IsRealMatchingSOS (kleinMatchingCost β p q c₋) := by
  by_cases hp : (∑ i, |p i|) ≤ (∑ i, β i) - c₋
  · by_cases hq : (∑ i, |q i|) ≤ c₋
    · exact klein_matching_sos_of_absolute_bounds β p q c₋
        (kleinMatchingCost_rectangle β p q c₋ h) hp hq
    · apply klein_symmetry_sos kleinCycleChange_involutive _ (klein_cycle_cost β p q c₋)
        (klein_cycle_prism β p q c₋) h hbound
      · intro β' p' q' c'
        have he : (kleinMatchingCost β' p' q' c') ∘ kleinCycleChange =
            kleinMatchingCost β' q' p' ((∑ i, β' i) - c') :=
          funext (klein_cycle_cost β' p' q' c')
        rw [he]
        exact klein_cost_mem _ _ _ _
      · intro hp' hb'
        apply klein_sos_of_plus_failure _ _ _ _ hp' hb'
        simpa only [sub_sub_cancel] using lt_of_not_ge hq
  · exact klein_sos_of_plus_failure β p q c₋ h hbound (lt_of_not_ge hp)

end
end MOC
