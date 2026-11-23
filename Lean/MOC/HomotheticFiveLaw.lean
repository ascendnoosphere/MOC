import MOC.HomotheticFiveData
import MOC.LexicographicScores

/-! The first unequal lifting score selects a simplex. Each boundary
score is a nonnegative sum of squared minors. -/

open BigOperators Matrix MOC.RayCoefficients

set_option maxRecDepth 16000
set_option maxHeartbeats 2000000

namespace MOC.HomotheticFive

private def pairing (s : ℝ) (Y : Axis → ℝ) (v : Axis → Poly) : ℝ :=
  ∑ k, eval s (v k) * Y k

private theorem scale_pairing {s : ℝ} (Y : Axis → ℝ) {u v : Axis → Poly} {h k : Poly}
    (hc : ∀ i, equal (mul h (u i)) (mul k (v i)) = true) :
    eval s h * pairing s Y u = eval s k * pairing s Y v := by
  simp only [pairing, Finset.mul_sum, ← mul_assoc]
  apply Finset.sum_congr rfl
  intro i _
  have hi := eval_eq_of_check s (hc i)
  simp only [eval_mul] at hi
  rw [hi]

private theorem pairing_gap (s : ℝ) (Y : Axis → ℝ) (t : Cell) (j : Axis) (i : Priority) :
    pairing s Y (gap t j i) =
      pairing s Y (liftRow t i) * eval s (den (near t j)) -
      pairing s Y (liftRow (near t j) i) * eval s (den t) := by
  simp only [pairing, gap, eval_sub, eval_mul, Finset.sum_mul, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun _ _ => by ring

private theorem select_cell (s : ℝ) (hs : 0 < s) (Y : Axis → ℝ)
    (hF : ∀ f, 0 ≤ pairing s Y (frow f)) :
    ∃ t : Cell, ∀ j, 0 ≤ pairing s Y (b t j) := by
  let L (t : Cell) (i : Priority) := pairing s Y (liftRow t i) / eval s (den t)
  obtain ⟨t,ht⟩ := exists_maximum_score_list 20 Cell L
  have hd (k : Cell) : 0 < eval s (den k) := eval_pos_of_check hs (positive_den k)
  refine ⟨t, fun j => ?_⟩
  have hl := eval_pos_of_check hs (positive_scales t j).1
  have hr := eval_pos_of_check hs (positive_scales t j).2
  apply nonneg_of_mul_nonneg_right _ hl
  cases hj : inner t j with
  | false =>
    rw [scale_pairing Y (boundary_check t j hj)]
    exact mul_nonneg hr.le (hF _)
  | true =>
    rw [scale_pairing Y (interior_check t j hj)]
    apply mul_nonneg hr.le
    rw [pairing_gap]
    apply sub_nonneg.mpr
    apply (div_le_div_iff₀ (hd _) (hd _)).mp
    apply ht (near t j) (firstPriority t j)
    intro i hi
    have hz : pairing s Y (gap t j i) = 0 := by
      simp only [pairing, fun k => eval_zero_of_check s (prefix_check t j hj i hi k),
        zero_mul, Finset.sum_const_zero]
    rw [pairing_gap, sub_eq_zero] at hz
    exact (div_eq_div_iff (hd _).ne' (hd _).ne').mpr hz.symm

private def sumPoly : (n : ℕ) → (Fin n → Poly) → Poly
  | 0, _ => []
  | n+1, v => add (v 0) (sumPoly n (fun i => v i.succ))

private theorem eval_sumPoly (s : ℝ) (n : ℕ) (v : Fin n → Poly) :
    eval s (sumPoly n v) = ∑ e, eval s (v e) := by
  induction n with
  | zero => simp [sumPoly, eval]
  | succ n ih => rw [sumPoly, eval_add, ih, Fin.sum_univ_succ]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
private theorem event_check (f : Facet) : ∀ p : Label,
    equal (slack f p) (sumPoly 46 fun e =>
      if (eventSets f e).2.map (FivePermutations.perm p).toEmbedding = (eventSets f e).1
      then weight f e else []) = true := by
  have h : ∀ p : Label, equal (slack f p) (sumPoly 46 fun e =>
      if FiveSubsetEvents.imageAt p (eventIndex f e).2 = (eventIndex f e).1
      then weight f e else []) = true := by
    fin_cases f <;> decide +kernel
  simpa only [eventSets, FiveSubsetEvents.image_iff] using h

private def signed (U : Matrix (Fin 5) (Fin 5) ℂ) (p : Label) :=
  realSignedWeight U (FivePermutations.perm p)

private theorem event_nonneg (s : ℝ) (hs : 0 < s)
    (U : Matrix (Fin 5) (Fin 5) ℂ) (hU : IsUnitary U) (f : Facet) :
    0 ≤ ∑ p, signed U p * eval s (slack f p) := by
  classical
  have he (p : Label) : eval s (slack f p) =
      ∑ e, if (eventSets f e).2.map (FivePermutations.perm p).toEmbedding = (eventSets f e).1
        then eval s (weight f e) else 0 := by
    have h := eval_eq_of_check s (event_check f p)
    simpa only [eval_sumPoly, apply_ite, eval] using h
  simp_rw [he, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_nonneg
  intro e _
  let I := (eventSets f e).1
  let J := (eventSets f e).2
  have hm :
      (∑ p, if J.map (FivePermutations.perm p).toEmbedding = I then signed U p else 0) =
      subsetMinorSq U I J := by
    have h := congrArg Complex.re (sum_signedWeight_image_eq_subsetMinorSq U hU I J)
    have h' : (∑ σ : FivePermutations.Perm,
        if J.map σ.toEmbedding = I then realSignedWeight U σ else 0) = subsetMinorSq U I J := by
      simpa only [Finset.sum_filter, Complex.re_sum, apply_ite, Complex.zero_re,
        Complex.ofReal_re, realSignedWeight] using h
    exact (Equiv.sum_comp FivePermutations.permEquiv (fun σ =>
      if J.map σ.toEmbedding = I then realSignedWeight U σ else 0)).trans h'
  have hp (p : Label) : signed U p *
        (if J.map (FivePermutations.perm p).toEmbedding = I then eval s (weight f e) else 0) =
      (if J.map (FivePermutations.perm p).toEmbedding = I then signed U p else 0) *
        eval s (weight f e) := by split_ifs <;> simp
  change 0 ≤ ∑ p, signed U p *
    (if J.map (FivePermutations.perm p).toEmbedding = I then eval s (weight f e) else 0)
  simp_rw [hp, ← Finset.sum_mul, hm]
  exact mul_nonneg (subsetMinorSq_nonneg U I J)
    (eval_nonneg_of_check hs.le (nonnegative_weight f e))

private def moments (s : ℝ) (U : Matrix (Fin 5) (Fin 5) ℂ) (k : Axis) : ℝ :=
  ∑ p, signed U p * eval s (point p k)

private theorem facet_nonneg (s : ℝ) (hs : 0 < s)
    (U : Matrix (Fin 5) (Fin 5) ℂ) (hU : IsUnitary U) (f : Facet) :
    0 ≤ pairing s (moments s U) (frow f) := by
  have hl := eval_pos_of_check hs (positive_face f).1
  have hr := eval_pos_of_check hs (positive_face f).2
  apply nonneg_of_mul_nonneg_right _ hl
  have h (p : Label) := eval_eq_of_check s (facet_check f p)
  simp only [eval_mul, eval_dot] at h
  calc
    0 ≤ eval s (fr f) * ∑ p, signed U p * eval s (slack f p) :=
      mul_nonneg hr.le (event_nonneg s hs U hU f)
    _ = ∑ p, signed U p * (eval s (fr f) * eval s (slack f p)) := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun _ _ => by ring)
    _ = ∑ p, signed U p * (eval s (fl f) * ∑ i, eval s (frow f i) * eval s (point p i)) := by
      simp_rw [h]
    _ = _ := by
      simp only [pairing, moments, Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

private theorem reproduce (s : ℝ) (Y : Axis → ℝ) (t : Cell) (k : Axis) :
    ∑ j, pairing s Y (b t j) * eval s (point (vertex t j) k) = eval s (den t) * Y k := by
  have h (r : Axis) := eval_eq_of_check s (reconstruct t r k)
  simp only [eval_dot, apply_ite, eval] at h
  simp only [pairing, Finset.sum_mul]
  rw [Finset.sum_comm]
  calc
    _ = ∑ r, (∑ j, eval s (b t j r) * eval s (point (vertex t j) k)) * Y r := by
      simp only [Finset.sum_mul]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    _ = _ := by simp only [h, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.sum_ite_eq,
        Finset.mem_univ, if_true]

/-- One simplex of five permutations matches the four spectral coefficients and the total mass. -/
theorem exists_law (s : ℝ) (hs : 0 < s)
    (U : Matrix (Fin 5) (Fin 5) ℂ) (hU : IsUnitary U) :
    ∃ t : Cell, ∃ w : Axis → ℝ, (∀ j, 0 ≤ w j) ∧ (∑ j, w j = 1) ∧
      ∀ k, ∑ j, w j * eval s (point (vertex t j) k) =
        ∑ p, realSignedWeight U (FivePermutations.perm p) * eval s (point p k) := by
  let Y := moments s U
  obtain ⟨t,ht⟩ := select_cell s hs Y (facet_nonneg s hs U hU)
  have hd := eval_pos_of_check hs (positive_den t)
  let w (j : Axis) := pairing s Y (b t j) / eval s (den t)
  have h (k : Axis) : ∑ j, w j * eval s (point (vertex t j) k) = Y k := by
    simp only [w, div_mul_eq_mul_div, ← Finset.sum_div, reproduce]
    exact mul_div_cancel_left₀ _ hd.ne'
  have h0 (p : Label) : eval s (point p 0) = 1 := by simp [mass_coord, eval]
  have htot : ∑ p : Label, signed U p = 1 :=
    (Equiv.sum_comp FivePermutations.permEquiv (realSignedWeight U)).trans (sum_realSignedWeight U hU)
  refine ⟨t,w, fun j => div_nonneg (ht j) hd.le, ?_, h⟩
  simpa only [h0, Y, moments, mul_one, htot] using h 0

end MOC.HomotheticFive
