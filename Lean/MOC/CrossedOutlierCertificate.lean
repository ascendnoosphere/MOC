import MOC.CrossedMinorBridge
import MOC.TwoOutlierZeroSupport
import MOC.FiniteMinorLaw

/-! The crossed subset transport gives the complete height-zero threshold
for two imaginary outliers by a positive local spectral certificate.
The normalized coupling itself uses the finite shadow argument from
Lyons, *Determinantal probability measures*, DOI 10.1007/s10240-003-0016-0. -/

open BigOperators Finset Matrix

namespace MOC

noncomputable section

private def minorSkip {n : ℕ} (S : Finset (Fin n)) : Finset (Fin (n+1)) :=
  S.map (Fin.succEmb n)

private def minorTake {n : ℕ} (S : Finset (Fin n)) : Finset (Fin (n+1)) := insert 0 (minorSkip S)

@[simp] private theorem not_mem_minorSkip {n : ℕ} (S : Finset (Fin n)) :
    (0 : Fin (n+1)) ∉ minorSkip S := by
  intro h
  obtain ⟨i, _, he⟩ := mem_map.mp h
  exact i.succ_ne_zero he

@[simp] private theorem succ_mem_minorSkip {n : ℕ} (S : Finset (Fin n)) (i : Fin n) :
    i.succ ∈ minorSkip S ↔ i ∈ S := by
  change (Fin.succEmb n) i ∈ S.map (Fin.succEmb n) ↔ i ∈ S
  exact mem_map' _

@[simp] private theorem minorSkip_compl {n : ℕ} (S : Finset (Fin n)) :
    (minorSkip S)ᶜ = minorTake Sᶜ := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [minorTake]
  · simp [minorTake, Fin.succ_ne_zero]

@[simp] private theorem minorTake_compl {n : ℕ} (S : Finset (Fin n)) :
    (minorTake S)ᶜ = minorSkip Sᶜ := by
  simpa only [compl_compl] using
    (congrArg (fun T : Finset (Fin (n+1)) => Tᶜ) (minorSkip_compl Sᶜ)).symm

private theorem sum_marked_subsets {M : Type*} [AddCommMonoid M] {n : ℕ}
    (F : Finset (Fin (n+1)) → M) :
    (∑ S, F S) = (∑ S, F (minorSkip S)) + ∑ S, F (minorTake S) := by
  let e := subsetCubeEquivLabels n
  let E : Finset (Fin n) ⊕ Finset (Fin n) ≃ Finset (Fin (n+1)) :=
    (e.symm.sumCongr e.symm).trans (subsetCubeEquivLabels (n+1))
  rw [← Equiv.sum_comp E F, Fintype.sum_sum_type]
  have hs (S : Finset (Fin n)) : E (.inl S) = minorSkip S := by
    change (e (e.symm S)).map _ = _
    rw [e.apply_symm_apply]
    rfl
  have ht (S : Finset (Fin n)) : E (.inr S) = minorTake S := by
    change insert 0 ((e (e.symm S)).map _) = _
    rw [e.apply_symm_apply]
    rfl
  simp only [hs, ht]

private theorem prod_outlier_minorSkip {n : ℕ} (v : Fin (n+1) → ℝ) (h : ℝ) (S : Finset (Fin n)) :
    (∏ i ∈ minorSkip S, withImaginaryOutlier v 0 h i) = (↑(∏ i ∈ S, v i.succ) : ℂ) := by
  rw [minorSkip, prod_map, Complex.ofReal_prod]
  apply prod_congr rfl
  intro i _
  simp [withImaginaryOutlier, Fin.succ_ne_zero]

private theorem prod_outlier_minorTake {n : ℕ} (v : Fin (n+1) → ℝ) (h : ℝ) (S : Finset (Fin n)) :
    (∏ i ∈ minorTake S, withImaginaryOutlier v 0 h i) =
      Complex.I * (h : ℂ) * (↑(∏ i ∈ S, v i.succ) : ℂ) := by
  rw [minorTake, prod_insert (not_mem_minorSkip S), prod_outlier_minorSkip]
  simp [withImaginaryOutlier]

private def spectatorCost {n : ℕ} (x y : Fin (n+1) → ℝ)
    (I J : Finset (Fin n)) : ℝ :=
  (∏ i ∈ Iᶜ, x i.succ) * ∏ j ∈ J, y j.succ

/-- The real part is the difference of the crossed minor costs; the remaining
two marked membership patterns make purely imaginary contributions. -/
private theorem two_outlier_crossed_minor_expansion {n : ℕ} (x y : Fin (n+1) → ℝ) (u v : ℝ)
    (U : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) (hU : IsUnitary U) :
    (determinantValue (withImaginaryOutlier x 0 u) (withImaginaryOutlier y 0 v) U).re =
      (∑ A : Finset (Fin n) × Finset (Fin n), subsetMinorSq U (minorTake A.1) (minorSkip A.2) *
        spectatorCost x y A.1 A.2) -
      u * v * ∑ B : Finset (Fin n) × Finset (Fin n), subsetMinorSq U (minorSkip B.1) (minorTake B.2) *
        spectatorCost x y B.1 B.2 := by
  rw [determinantValue_eq_sum_subsetMinors _ _ U hU]
  simp only [Complex.re_sum, Complex.re_ofReal_mul]
  rw [sum_marked_subsets]
  simp_rw [sum_marked_subsets (n := n) (F := fun I => subsetMinorSq U I _ *
    (((∏ i ∈ Iᶜ, withImaginaryOutlier x 0 u i) *
      ∏ j ∈ _, withImaginaryOutlier y 0 v j).re))]
  simp only [minorSkip_compl, minorTake_compl, prod_outlier_minorSkip, prod_outlier_minorTake,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, zero_mul, mul_zero, one_mul, zero_add, add_zero, zero_sub, sub_zero,
    sum_const_zero, add_zero, zero_add, Fintype.sum_prod_type]
  dsimp only [spectatorCost]
  have move (a b c d e : ℝ) : a * -((b * c) * (d * e)) = -(b * d) * (a * (c * e)) := by ring
  simp_rw [move, ← mul_sum]
  rw [sum_comm (f := fun J I => subsetMinorSq U (minorTake I) (minorSkip J) *
    ((∏ i ∈ Iᶜ, x i.succ) * ∏ j ∈ J, y j.succ)), sum_comm (f := fun J I =>
      subsetMinorSq U (minorSkip I) (minorTake J) * ((∏ i ∈ Iᶜ, x i.succ) * ∏ j ∈ J, y j.succ))]
  ring


private theorem exists_insert_of_subset_card_succ {α : Type*} [DecidableEq α]
    {S T : Finset α} (hs : S ⊆ T) (ht : T.card = S.card+1) :
    ∃ i ∉ S, T = insert i S := by
  have hn : S ≠ T := by
    intro e
    rw [e] at ht
    omega
  obtain ⟨i, hiT, hiS⟩ := Finset.exists_of_ssubset (Finset.ssubset_iff_subset_ne.mpr ⟨hs, hn⟩)
  exact ⟨i, hiS, (Finset.eq_of_subset_of_card_le (insert_subset hiT hs)
    (by rw [card_insert_of_not_mem hiS, ht])).symm⟩

private theorem spectatorCost_insert_ratio {n : ℕ} (x y : Fin (n+1) → ℝ)
    (I L : Finset (Fin n)) (i j : Fin n) (hi : i ∉ I) (hj : j ∉ L) :
    spectatorCost x y I (insert j L) =
      (x i.succ * y j.succ) * spectatorCost x y (insert i I) L := by
  have hI : Iᶜ = insert i ((insert i I)ᶜ) := by
    ext t
    by_cases he : t = i
    · subst t
      simp [hi]
    · simp [he]
  unfold spectatorCost
  rw [hI, prod_insert (by simp), prod_insert hj]
  ring

private theorem source_target_pair_bound {n : ℕ}
    (U : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) (hU : IsUnitary U)
    (x y : Fin (n+1) → ℝ)
    (hx : ∀ i : Fin n, 0 ≤ x i.succ) (hy : ∀ i : Fin n, 0 ≤ y i.succ)
    (θ H : ℝ) (hH : ∀ i j : Fin n, θ * (x i.succ * y j.succ) ≤ θ * H) :
    θ * (∑ A : Finset (Fin n) × Finset (Fin n), subsetMinorSq U (minorTake A.1) (minorSkip A.2) *
        spectatorCost x y A.1 A.2)
      ≤ θ * H * ∑ B : Finset (Fin n) × Finset (Fin n), subsetMinorSq U (minorSkip B.1) (minorTake B.2) *
        spectatorCost x y B.1 B.2 := by
  obtain ⟨μ, hμ, hs, hr, hc⟩ := exists_crossed_subsetMinorSq_transport U hU
  let F (A : Finset (Fin n) × Finset (Fin n)) := θ * spectatorCost x y A.1 A.2
  let G (B : Finset (Fin n) × Finset (Fin n)) := θ * H * spectatorCost x y B.1 B.2
  have hbnd (A B : Finset (Fin n) × Finset (Fin n)) (h : μ A B ≠ 0) : F A ≤ G B := by
    obtain ⟨hr', hc', hmid⟩ := hs A B h
    have hp : 0 < μ A B := lt_of_le_of_ne (hμ _ _) (Ne.symm h)
    have hpA : 0 < subsetMinorSq U (minorTake A.1) (minorSkip A.2) := by
      change 0 < subsetMinorSq U (insert 0 (A.1.map (Fin.succEmb n))) (A.2.map (Fin.succEmb n))
      rw [← hr]
      exact hp.trans_le (single_le_sum (fun B _ => hμ A B) (mem_univ B))
    have hpB : 0 < subsetMinorSq U (minorSkip B.1) (minorTake B.2) := by
      change 0 < subsetMinorSq U (B.1.map (Fin.succEmb n)) (insert 0 (B.2.map (Fin.succEmb n)))
      rw [← hc]
      exact hp.trans_le (single_le_sum (fun A _ => hμ A B) (mem_univ A))
    have hcardA : A.2.card = A.1.card+1 := by
      by_contra hne
      have hz : (minorTake A.1).card ≠ (minorSkip A.2).card := by
        simpa [minorTake, minorSkip, card_insert_of_not_mem, not_mem_minorSkip] using (Ne.symm hne)
      simp only [subsetMinorSq, dif_neg hz, lt_irrefl] at hpA
    have hcardB : B.1.card = B.2.card+1 := by
      by_contra hne
      have hz : (minorSkip B.1).card ≠ (minorTake B.2).card := by
        simpa [minorTake, minorSkip, card_insert_of_not_mem, not_mem_minorSkip] using hne
      simp only [subsetMinorSq, dif_neg hz, lt_irrefl] at hpB
    obtain ⟨i, hi, hib⟩ := exists_insert_of_subset_card_succ hr' (by rw [hcardB, hmid])
    obtain ⟨j, hj, hja⟩ := exists_insert_of_subset_card_succ hc' (by rw [hcardA, hmid])
    have hcost : spectatorCost x y A.1 A.2 =
        (x i.succ * y j.succ) * spectatorCost x y B.1 B.2 := by
      rw [hja, hib, spectatorCost_insert_ratio x y A.1 B.2 i j hi hj]
    have hcostB : 0 ≤ spectatorCost x y B.1 B.2 :=
      mul_nonneg (prod_nonneg fun i _ => hx i) (prod_nonneg fun j _ => hy j)
    dsimp only [F, G]
    rw [hcost, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (hH i j) hcostB
  calc
    _ = ∑ A, ∑ B, μ A B * F A := by
      simp_rw [← sum_mul, hr, mul_sum, F]
      apply sum_congr rfl
      intro A _
      simp only [minorTake, minorSkip]
      ring
    _ ≤ ∑ A, ∑ B, μ A B * G B := by
      apply sum_le_sum
      intro A _
      apply sum_le_sum
      intro B _
      by_cases h : μ A B = 0
      · simp [h]
      · exact mul_le_mul_of_nonneg_left (hbnd A B h) (hμ A B)
    _ = _ := by
      simp_rw [sum_comm (f := fun A B => μ A B * G B), ← sum_mul, hc, mul_sum, G]
      apply sum_congr rfl
      intro B _
      simp only [minorTake, minorSkip]
      ring


/-- Both outlier support bounds follow from the same nonnegative crossed
minor moment. In particular the determinant gap scales linearly in the
distance of the height product from the interval of crossed products. -/
theorem two_imaginary_outlier_transport_gap {n : ℕ}
    (U : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) (hU : IsUnitary U)
    (x y : Fin (n+1) → ℝ) (u v L H : ℝ)
    (hx : ∀ i : Fin n, 0 ≤ x i.succ) (hy : ∀ i : Fin n, 0 ≤ y i.succ)
    (hL : ∀ i j : Fin n, L ≤ x i.succ * y j.succ)
    (hH : ∀ i j : Fin n, x i.succ * y j.succ ≤ H) :
    let T := ∑ B : Finset (Fin n) × Finset (Fin n),
      subsetMinorSq U (B.1.map (Fin.succEmb n)) (insert 0 (B.2.map (Fin.succEmb n))) *
      ((∏ i ∈ B.1ᶜ, x i.succ) * ∏ j ∈ B.2, y j.succ)
    let D := (determinantValue (withImaginaryOutlier x 0 u) (withImaginaryOutlier y 0 v) U).re
    0 ≤ T ∧ (L-u*v)*T ≤ D ∧ D ≤ (H-u*v)*T := by
  intro T D
  have hD := two_outlier_crossed_minor_expansion x y u v U hU
  let R := ∑ A : Finset (Fin n) × Finset (Fin n),
    subsetMinorSq U (minorTake A.1) (minorSkip A.2) * spectatorCost x y A.1 A.2
  change D = R - u * v * T at hD
  have low : L * T ≤ R := by
    have h := source_target_pair_bound U hU x y hx hy (-1) L
      (fun i j => by linarith only [hL i j])
    change (-1 : ℝ) * R ≤ (-1 : ℝ) * L * T at h
    linarith
  have high : R ≤ H * T := by
    have h := source_target_pair_bound U hU x y hx hy 1 H
      (fun i j => by simpa only [one_mul] using hH i j)
    change (1 : ℝ) * R ≤ (1 : ℝ) * H * T at h
    simpa only [one_mul] using h
  refine ⟨?_, ?_, ?_⟩
  · apply sum_nonneg
    intro B _
    exact mul_nonneg (subsetMinorSq_nonneg U _ _)
      (mul_nonneg (prod_nonneg fun i _ => hx i) (prod_nonneg fun j _ => hy j))
  · rw [sub_mul, hD]
    exact sub_le_sub_right low _
  · rw [sub_mul, hD]
    exact sub_le_sub_right high _

/-- A single crossed first minor already forces a strict gap when the
height product strictly dominates every crossed spectator product.
The bound is for the original unitary, not only for dense mixers. -/
theorem two_imaginary_outlier_off_fibre_gap {n : ℕ}
    (U : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) (hU : IsUnitary U)
    (x y : Fin (n+1) → ℝ) (u v H : ℝ) (i : Fin n)
    (hx : ∀ i : Fin n, 0 ≤ x i.succ) (hy : ∀ i : Fin n, 0 ≤ y i.succ)
    (hH : ∀ i j : Fin n, x i.succ * y j.succ ≤ H) (huv : H ≤ u*v) :
    (determinantValue (withImaginaryOutlier x 0 u) (withImaginaryOutlier y 0 v) U).re ≤
      (H-u*v) * (Complex.normSq (U i.succ 0) * ∏ k ∈ ({i} : Finset (Fin n))ᶜ, x k.succ) := by
  let f (B : Finset (Fin n) × Finset (Fin n)) :=
    subsetMinorSq U (B.1.map (Fin.succEmb n)) (insert 0 (B.2.map (Fin.succEmb n))) *
      ((∏ i ∈ B.1ᶜ, x i.succ) * ∏ j ∈ B.2, y j.succ)
  have h := (two_imaginary_outlier_transport_gap U hU x y u v 0 H hx hy
    (fun a b => mul_nonneg (hx a) (hy b)) hH).2.2
  change _ ≤ (H-u*v) * ∑ B, f B at h
  apply h.trans
  apply mul_le_mul_of_nonpos_left _ (sub_nonpos.mpr huv)
  have hb : f ({i}, ∅) ≤ ∑ B, f B := single_le_sum (f := f)
    (fun B _ => mul_nonneg (subsetMinorSq_nonneg U _ _)
      (mul_nonneg (prod_nonneg (fun k _ => hx k)) (prod_nonneg (fun k _ => hy k))))
    (mem_univ (({i}, ∅) : Finset (Fin n) × Finset (Fin n)))
  simpa [f, subsetMinorSq_singleton U hU, Fin.succEmb] using hb


/-- At strict threshold a mixer moving the marked line cannot attain the
height-zero support. A single nonzero crossed entry supplies the gap. -/
theorem two_imaginary_outlier_strict_off_fibre {n : ℕ}
    (U : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) (hU : IsUnitary U)
    (x y : Fin (n+1) → ℝ) (u v H : ℝ) (i : Fin n)
    (hx : ∀ i : Fin n, 0 < x i.succ) (hy : ∀ i : Fin n, 0 ≤ y i.succ)
    (hH : ∀ i j : Fin n, x i.succ * y j.succ ≤ H) (huv : H < u*v)
    (hentry : U i.succ 0 ≠ 0) :
    (determinantValue (withImaginaryOutlier x 0 u) (withImaginaryOutlier y 0 v) U).re < 0 :=
  (two_imaginary_outlier_off_fibre_gap U hU x y u v H i
    (fun j => (hx j).le) hy hH huv.le).trans_lt
      (mul_neg_of_neg_of_pos (sub_neg.mpr huv)
        (mul_pos (Complex.normSq_pos.mpr hentry) (prod_pos fun j _ => hx j)))


end

end MOC
