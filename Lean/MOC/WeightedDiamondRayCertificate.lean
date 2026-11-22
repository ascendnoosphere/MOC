import MOC.WeightedDiamondCoefficients

/-! Soundness of the integer data for one step of the weighted-diamond census. -/

open BigOperators

namespace MOC
namespace RayCoefficients

abbrev Row := Fin 24 → Poly

def rowEval (t : ℝ) (r : Row) : Fin 24 → ℝ := fun i => eval t (r i)

inductive Crossing (m n : ℕ)
  | skip (witness : Fin m)
  | keep (target : Fin n) (factor : Poly)

def Crossing.target? {m n : ℕ} : Crossing m n → Option (Fin n)
  | .skip _ => none
  | .keep l _ => some l

inductive RayOrigin (m : ℕ)
  | kept (k : Fin m)
  | crossing (p n : Fin m)

structure RayCutPlan (m n : ℕ) where
  kept : Fin m → Fin n
  crossing : Fin m → Fin m → Crossing m n
  origin : Fin n → RayOrigin m

def RayCutPlan.CrossingValid {m n : ℕ} (old : Fin m → Row) (next : Fin n → Row)
    (s : Finset (Fin 24)) (j : Fin 24) (p k : Fin m) : Crossing m n → Prop
  | .skip q => q ≠ p ∧ q ≠ k ∧
      ∀ i ∈ s, zero (old p i) = true → zero (old k i) = true → zero (old q i) = true
  | .keep l c => positive c = true ∧ ∀ i,
      equal (sub (mul (old p j) (old k i)) (mul (old k j) (old p i)))
        (mul c (next l i)) = true

instance {m n : ℕ} (old : Fin m → Row) (next : Fin n → Row)
    (s : Finset (Fin 24)) (j : Fin 24) (p k : Fin m) (choice : Crossing m n) :
    Decidable (RayCutPlan.CrossingValid old next s j p k choice) := by
  cases choice <;> unfold RayCutPlan.CrossingValid <;> infer_instance

def RayCutPlan.OriginValid {m n : ℕ} (plan : RayCutPlan m n) (old : Fin m → Row)
    (j : Fin 24) (l : Fin n) : RayOrigin m → Prop
  | .kept k => (zero (old k j) = true ∨ positive (old k j) = true) ∧ plan.kept k = l
  | .crossing p k => positive (old p j) = true ∧ negative (old k j) = true ∧
      (plan.crossing p k).target? = some l

instance {m n : ℕ} (plan : RayCutPlan m n) (old : Fin m → Row)
    (j : Fin 24) (l : Fin n) (source : RayOrigin m) :
    Decidable (plan.OriginValid old j l source) := by
  cases source <;> unfold RayCutPlan.OriginValid <;> infer_instance

structure RayCutPlan.Valid {m n : ℕ} (plan : RayCutPlan m n)
    (old : Fin m → Row) (next : Fin n → Row) (s : Finset (Fin 24)) (j : Fin 24) : Prop where
  oldSigns : ∀ k i, i ∈ s → zero (old k i) = true ∨ positive (old k i) = true
  nextSigns : ∀ l i, i ∈ s → nonneg (next l i) = true
  nextPositive : ∀ l, ∃ i ∈ s, positive (next l i) = true
  cutSigns : ∀ k, zero (old k j) = true ∨ positive (old k j) = true ∨ negative (old k j) = true
  separates : ∀ k l, k ≠ l → ∃ i ∈ s, positive (old k i) = true ∧ zero (old l i) = true
  keptValid : ∀ k, zero (old k j) = true ∨ positive (old k j) = true →
    ∀ i, equal (old k i) (next (plan.kept k) i) = true
  crossingValid : ∀ p k, positive (old p j) = true → negative (old k j) = true →
    RayCutPlan.CrossingValid old next s j p k (plan.crossing p k)
  originsValid : ∀ l, plan.OriginValid old j l (plan.origin l)

private theorem eval_eq_cross_eval {t : ℝ} {m n : ℕ} {old : Fin m → Row} {next : Fin n → Row}
    {p k : Fin m} {j : Fin 24} {l : Fin n} {c : Poly}
    (he : ∀ i, equal (sub (mul (old p j) (old k i)) (mul (old k j) (old p i)))
        (mul c (next l i)) = true) :
    eval t (old p j) • rowEval t (old k) - eval t (old k j) • rowEval t (old p) =
      eval t c • rowEval t (next l) := by
  funext i
  simpa only [rowEval, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, eval_sub, eval_mul] using
    eval_eq_of_check t (he i)

/-- Every certified next ray lies in the same linear space as the old rays. -/
theorem RayCutPlan.Valid.next_mem {m n : ℕ} {plan : RayCutPlan m n}
    {old : Fin m → Row} {next : Fin n → Row} {s : Finset (Fin 24)} {j : Fin 24}
    (h : plan.Valid old next s j) {t : ℝ} (ht : 0 < t)
    (W : Submodule ℝ (Fin 24 → ℝ)) (hold : ∀ k, rowEval t (old k) ∈ W) (l : Fin n) :
    rowEval t (next l) ∈ W := by
  have horigin := h.originsValid l
  cases hplan : plan.origin l with
  | kept k =>
    simp only [hplan, RayCutPlan.OriginValid] at horigin
    have he : rowEval t (old k) = rowEval t (next l) := by
      funext i
      have hki := h.keptValid k horigin.1 i
      rw [horigin.2] at hki
      exact eval_eq_of_check t hki
    exact he ▸ hold k
  | crossing p k =>
    simp only [hplan, RayCutPlan.OriginValid] at horigin
    obtain ⟨hp, hk, hl⟩ := horigin
    have hc := h.crossingValid p k hp hk
    cases hcplan : plan.crossing p k with
    | skip q => simp [hcplan, Crossing.target?] at hl
    | keep l' c =>
      have hll : l' = l := by simpa [hcplan, Crossing.target?] using hl
      subst l'
      simp only [hcplan, RayCutPlan.CrossingValid] at hc
      have he : eval t (old p j) • rowEval t (old k) -
          eval t (old k j) • rowEval t (old p) = eval t c • rowEval t (next l) :=
        eval_eq_cross_eval hc.2
      have hw := W.sub_mem (W.smul_mem (eval t (old p j)) (hold k))
        (W.smul_mem (eval t (old k j)) (hold p))
      rw [he] at hw
      have hw' := W.smul_mem (eval t c)⁻¹ hw
      simpa only [smul_smul, inv_mul_cancel₀ (eval_pos_of_check ht hc.1).ne', one_smul] using hw'

/-- The finite coefficient checks certify an exact ray transition at every
positive value of the chart parameter. -/
theorem RayCutPlan.Valid.generate {m n : ℕ} {plan : RayCutPlan m n}
    {old : Fin m → Row} {next : Fin n → Row} {s : Finset (Fin 24)} {j : Fin 24}
    (h : plan.Valid old next s j) {t : ℝ} (ht : 0 < t)
    (W : Submodule ℝ (Fin 24 → ℝ))
    (hzero : ∀ v ∈ W, (∀ i ∈ s, v i = 0) → v = 0)
    (hold : ∀ k, rowEval t (old k) ∈ W)
    (hgen : ∀ v ∈ W, (∀ i ∈ s, 0 ≤ v i) →
      ∃ w : Fin m → ℝ, (∀ k, 0 ≤ w k) ∧ v = ∑ k, w k • rowEval t (old k))
    (v : Fin 24 → ℝ) (hvW : v ∈ W) (hv : ∀ i ∈ s, 0 ≤ v i) (hvj : 0 ≤ v j) :
    ∃ w : Fin n → ℝ, (∀ l, 0 ≤ w l) ∧ v = ∑ l, w l • rowEval t (next l) := by
  have holdNonneg (k i) (hi : i ∈ s) : 0 ≤ rowEval t (old k) i := by
    rcases h.oldSigns k i hi with hz | hp
    · exact (eval_zero_of_check t hz).ge
    · exact (eval_pos_of_check ht hp).le
  have hnextNonneg (l i) (hi : i ∈ s) : 0 ≤ rowEval t (next l) i :=
    eval_nonneg_of_check ht.le (h.nextSigns l i hi)
  have hnextPos (l) : ∃ i ∈ s, 0 < rowEval t (next l) i := by
    obtain ⟨i, hi, hp⟩ := h.nextPositive l
    exact ⟨i, hi, eval_pos_of_check ht hp⟩
  refine exists_conic_weights_after_adjacent_cut W s j _ _ hzero hold holdNonneg ?_ hgen
    hnextNonneg hnextPos ?_ ?_ v hvW hv hvj
  · intro k l hkl
    obtain ⟨i, hi, hp, hz⟩ := h.separates k l hkl
    exact ⟨i, hi, eval_pos_of_check ht hp, eval_zero_of_check t hz⟩
  · intro k hk
    have hs : zero (old k j) = true ∨ positive (old k j) = true := by
      rcases h.cutSigns k with hz | hp | hn
      · exact Or.inl hz
      · exact Or.inr hp
      · exact (not_le_of_gt (eval_neg_of_check ht hn) hk).elim
    refine ⟨plan.kept k, 1, zero_le_one, ?_⟩
    funext i
    simpa only [rowEval, one_smul] using eval_eq_of_check t (h.keptValid k hs i)
  · intro p k hp hk ha
    have hp' : positive (old p j) = true := by
      rcases h.cutSigns p with hz | hpos | hn
      · exact (not_lt_of_ge (eval_zero_of_check t hz).le hp).elim
      · exact hpos
      · exact (not_lt_of_ge (eval_neg_of_check ht hn).le hp).elim
    have hk' : negative (old k j) = true := by
      rcases h.cutSigns k with hz | hpos | hn
      · exact (not_lt_of_ge (eval_zero_of_check t hz).ge hk).elim
      · exact (not_lt_of_ge (eval_pos_of_check ht hpos).le hk).elim
      · exact hn
    have hc := h.crossingValid p k hp' hk'
    cases hpplan : plan.crossing p k with
    | skip q =>
      simp only [hpplan, RayCutPlan.CrossingValid] at hc
      obtain ⟨i, hi, hip, hik, hiq⟩ := ha q hc.1 hc.2.1
      have hz (r : Fin m) (hr : rowEval t (old r) i = 0) : zero (old r i) = true := by
        rcases h.oldSigns r i hi with hz | hpos
        · exact hz
        · exact ((eval_pos_of_check ht hpos).ne' hr).elim
      exact ((eval_zero_of_check t (hc.2.2 i hi (hz p hip) (hz k hik))).not_gt hiq).elim
    | keep l c =>
      simp only [hpplan, RayCutPlan.CrossingValid] at hc
      exact ⟨l, eval t c, (eval_pos_of_check ht hc.1).le, eval_eq_cross_eval hc.2⟩

end RayCoefficients
end MOC
