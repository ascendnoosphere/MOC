import MOC.SinglePortZeroCorner

/-! Determinant inclusion for unitary matrices with consecutive staircase
cuts that advance by at most two labels. -/

open Matrix

namespace MOC

noncomputable section

private def staircaseLeft (l : ℕ) : Fin l ⊕ Unit ≃ Fin (l + 1) :=
  (Equiv.optionEquivSumPUnit (Fin l)).symm.trans (finSuccEquiv' (Fin.last l)).symm

private def staircaseSplit (l r : ℕ) : ((Fin l ⊕ Unit) ⊕ Fin r) ≃ Fin (l + r + 1) :=
  (Equiv.sumCongr (staircaseLeft l) (Equiv.refl (Fin r))).trans
    (finSumFinEquiv.trans (finCongr (Nat.succ_add l r)))

private def staircaseTail (r : ℕ) : Unit ⊕ Fin r ≃ Fin (r + 1) :=
  (Equiv.sumComm Unit (Fin r)).trans
    ((Equiv.optionEquivSumPUnit (Fin r)).symm.trans (finSuccEquiv' 0).symm)

private theorem staircaseSplit_left_val (l r : ℕ) (j : Fin l) :
    (staircaseSplit l r (.inl (.inl j))).val = j.val := by
  simp [staircaseSplit, staircaseLeft, Fin.succAbove_last, finSumFinEquiv]

private theorem staircaseSplit_right_val (l r : ℕ) (i : Fin r) :
    (staircaseSplit l r (.inr i)).val = l + 1 + i.val := by
  rfl

private theorem staircaseTail_first_val (r : ℕ) :
    (staircaseTail r (.inl ())).val = 0 := rfl

private theorem staircaseLabel_tail_val (l r : ℕ) (i : Unit ⊕ Fin r) :
    (staircaseSplit l r ((Equiv.sumAssoc (Fin l) Unit (Fin r)).symm (.inr i))).val =
      l + (staircaseTail r i).val := by
  rcases i with ⟨⟩ | i
  · rfl
  · rw [show (Equiv.sumAssoc (Fin l) Unit (Fin r)).symm (.inr (.inr i)) = .inr i from rfl,
      staircaseSplit_right_val]
    have hi : (staircaseTail r (.inr i)).val = i.val + 1 := by
      simp [staircaseTail, Fin.succAbove_zero]
    omega

private theorem singlePort_mul_right_row {l r : ℕ}
    (V : Matrix (Fin l ⊕ Unit) (Fin l ⊕ Unit) ℂ)
    (W : Matrix (Unit ⊕ Fin r) (Unit ⊕ Fin r) ℂ) (i : Fin r) (j : Unit ⊕ Fin r) :
    (singlePortLeft (R := Fin r) V * singlePortRight (L := Fin l) W) (.inr i)
      ((Equiv.sumAssoc (Fin l) Unit (Fin r)).symm (.inr j)) = W (.inr i) j := by
  rw [Matrix.mul_apply, Fintype.sum_sum_type]
  simp only [singlePortLeft, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
    Matrix.zero_apply, zero_mul, Finset.sum_const_zero, zero_add, Matrix.one_apply,
    ite_mul, one_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp [singlePortRight]

private theorem staircase_tail_zeros {l r t : ℕ}
    (V : Matrix (Fin l ⊕ Unit) (Fin l ⊕ Unit) ℂ)
    (W : Matrix (Unit ⊕ Fin r) (Unit ⊕ Fin r) ℂ)
    (U : Matrix (Fin (l + r + 1)) (Fin (l + r + 1)) ℂ)
    (hprod : U.submatrix (staircaseSplit l r) (staircaseSplit l r) =
      singlePortLeft V * singlePortRight W)
    (hz : ∀ (i j : Fin (l + r + 1)), l + t < i.val → j.val < l + t → U i j = 0) :
    ∀ (i j : Fin (r + 1)), t < i.val → j.val < t →
      W ((staircaseTail r).symm i) ((staircaseTail r).symm j) = 0 := by
  intro i j hi hj
  let x := (staircaseTail r).symm i
  let y := (staircaseTail r).symm j
  have hx : staircaseTail r x = i := (staircaseTail r).apply_symm_apply i
  have hy : staircaseTail r y = j := (staircaseTail r).apply_symm_apply j
  change W x y = 0
  rcases hcase : x with ⟨⟩ | k
  · have hex : i.val = 0 := by rw [← hx, hcase, staircaseTail_first_val]
    omega
  · let e := staircaseSplit l r
    let s := Equiv.sumAssoc (Fin l) Unit (Fin r)
    rw [← singlePort_mul_right_row V W k y, ← hprod]
    have hrow : (e (.inr k)).val = l + i.val := by
      have he := staircaseLabel_tail_val l r (.inr k)
      change (e (.inr k)).val = l + (staircaseTail r (.inr k)).val at he
      rw [← hcase, hx] at he
      exact he
    have hcol : (e (s.symm (.inr y))).val = l + j.val := by
      rw [staircaseLabel_tail_val, hy]
    change U (e (.inr k)) (e (s.symm (.inr y))) = 0
    exact hz _ _ (by omega) (by omega)

/-- Suppose the order is one plus the sum of the sizes in `steps`.
Every size is at most two. At each prefix sum `k`, all entries in rows
strictly after `k` and columns strictly before `k` are zero. Then the
determinant inclusion holds for all complex spectra. Indices start at zero. -/
theorem holds_of_staircase_zero_corners (steps : List ℕ)
    (hsteps : ∀ k ∈ steps, k ≤ 2)
    {U : Matrix (Fin (steps.sum + 1)) (Fin (steps.sum + 1)) ℂ} (hU : IsUnitary U)
    (hz : ∀ (earlier later : List ℕ), steps = earlier ++ later →
      ∀ (i j : Fin (steps.sum + 1)), earlier.sum < i.val → j.val < earlier.sum → U i j = 0)
    (a b : Fin (steps.sum + 1) → ℂ) : Holds a b U := by
  induction steps with
  | nil => exact conjecture_le_three (by decide : 1 ≤ 3) a b U hU
  | cons l steps ih =>
    let r := steps.sum
    let e : ((Fin l ⊕ Unit) ⊕ Fin r) ≃ Fin ((l :: steps).sum + 1) :=
      staircaseSplit l r
    have hcorner : ∀ (i : Fin r) (j : Fin l),
        U (e (.inr i)) (e (.inl (.inl j))) = 0 := by
      intro i j
      apply hz [l] steps rfl
      · change l + 0 < (staircaseSplit l r (.inr i)).val
        rw [staircaseSplit_right_val]
        omega
      · change (staircaseSplit l r (.inl (.inl j))).val < l + 0
        rw [staircaseSplit_left_val]
        exact j.isLt
    obtain ⟨V, W, hV, hW, hprod⟩ :=
      exists_singlePort_factors_of_zero_corner (unitary_reindex e e hU) hcorner
    have hsmall : Fintype.card (Fin l ⊕ Unit) ≤ 3 := by
      have hl := hsteps l (List.mem_cons_self ..)
      simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_unit]
      omega
    have hWcovered : ∀ c d, Holds c d W := by
      intro c d
      let f := (staircaseTail r).symm
      apply (holds_reindex_iff f f c d W).mp
      apply ih (fun k hk => hsteps k (List.mem_cons_of_mem _ hk)) (unitary_reindex f f hW)
      intro earlier later hsplit
      apply staircase_tail_zeros V W U hprod
      intro i j hi hj
      exact hz (l :: earlier) later (by simp [hsplit]) i j hi hj
    apply (holds_reindex_iff e e a b U).mp
    rw [hprod]
    exact holds_singlePortComposition _ _ V W hV hW
      (fun c d => conjecture_of_card_le_three hsmall c d V hV) hWcovered

end

end MOC
