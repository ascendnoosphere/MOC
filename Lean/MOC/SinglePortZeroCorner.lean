import MOC.PrincipalCoisometry
import MOC.SinglePortComposition

/-! A zero rectangle with side lengths adding to one less than the order
forces a product of two coordinate blocks that meet in one index. -/

open BigOperators Matrix

namespace MOC

noncomputable section

private def finWithPort (l : ℕ) : Fin (l + 1) ≃ Fin l ⊕ Unit where
  toFun := Fin.cases (Sum.inr ()) Sum.inl
  invFun := Sum.elim Fin.succ (fun _ => 0)
  left_inv := by intro i; cases i using Fin.cases <;> rfl
  right_inv := by rintro (i | ⟨⟩) <;> rfl

private def singlePortRetainedRows {l r : ℕ}
    (U : Matrix ((Fin l ⊕ Unit) ⊕ Fin r) ((Fin l ⊕ Unit) ⊕ Fin r) ℂ) :
    Matrix (Fin l) (Fin (l + 1)) ℂ :=
  (U.submatrix (fun i => .inl (finWithPort l i)) (fun j => .inl (.inl j)))ᴴ

private theorem singlePortRetainedRows_coisometry {l r : ℕ}
    {U : Matrix ((Fin l ⊕ Unit) ⊕ Fin r) ((Fin l ⊕ Unit) ⊕ Fin r) ℂ}
    (hU : IsUnitary U) (hz : ∀ i j, U (.inr i) (.inl (.inl j)) = 0) :
    singlePortRetainedRows U * (singlePortRetainedRows U)ᴴ = 1 := by
  classical
  let ι := (Fin l ⊕ Unit) ⊕ Fin r
  let e := finWithPort l
  ext j k : 1
  let f (i : Fin l ⊕ Unit) := star (U (.inl i) (.inl (.inl j))) *
    U (.inl i) (.inl (.inl k))
  have h := congrArg (fun M : Matrix ι ι ℂ => M (.inl (.inl j)) (.inl (.inl k))) hU.2
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply] at h
  rw [Fintype.sum_sum_type] at h
  simp only [hz, mul_zero, Finset.sum_const_zero, add_zero] at h
  simp only [Matrix.mul_apply, singlePortRetainedRows, Matrix.conjTranspose_conjTranspose,
    Matrix.conjTranspose_apply, Matrix.submatrix_apply]
  change (∑ i, f (e i)) = _
  rw [Equiv.sum_comp e f]
  simpa only [Matrix.one_apply, Sum.inl.injEq] using h

private def singlePortCompletedLeft {l : ℕ} (X : Matrix (Fin (l + 1)) (Fin (l + 1)) ℂ) :
    Matrix (Fin l ⊕ Unit) (Fin l ⊕ Unit) ℂ :=
  Xᴴ.submatrix (finWithPort l).symm (finWithPort l).symm

private theorem singlePort_factors_of_completed_rows {l r : ℕ}
    {U : Matrix ((Fin l ⊕ Unit) ⊕ Fin r) ((Fin l ⊕ Unit) ⊕ Fin r) ℂ}
    (hU : IsUnitary U) (hz : ∀ i j, U (.inr i) (.inl (.inl j)) = 0)
    {X : Matrix (Fin (l + 1)) (Fin (l + 1)) ℂ} (hX : IsUnitary X)
    (hXY : X.submatrix (0 : Fin (l + 1)).succAbove id = singlePortRetainedRows U) :
    let V := singlePortCompletedLeft X
    ∃ W : Matrix (Unit ⊕ Fin r) (Unit ⊕ Fin r) ℂ,
      IsUnitary V ∧ IsUnitary W ∧ U = singlePortLeft V * singlePortRight W ∧
        singlePortRight W = (singlePortLeft V)ᴴ * U := by
  classical
  let ι := (Fin l ⊕ Unit) ⊕ Fin r
  let e := finWithPort l
  intro V
  have hV : IsUnitary V := unitary_reindex e.symm e.symm
    (show IsUnitary Xᴴ from ⟨by simpa using hX.2, by simpa using hX.1⟩)
  let L : Matrix ι ι ℂ := fromBlocks V 0 0 1
  have hL : IsUnitary L := unitary_directSum hV isUnitary_one
  have hLcol (i : ι) (j : Fin l) : L i (.inl (.inl j)) = U i (.inl (.inl j)) := by
    rcases i with i | i
    · have h := congrArg (fun M : Matrix (Fin l) (Fin (l + 1)) ℂ => M j (e.symm i)) hXY
      change X ((0 : Fin (l + 1)).succAbove j) (e.symm i) =
        star (U (.inl (e (e.symm i))) (.inl (.inl j))) at h
      have he : e.symm (.inl j) = (0 : Fin (l + 1)).succAbove j :=
        congrFun Fin.succAbove_zero.symm j
      change star (X (e.symm (.inl j)) (e.symm i)) = _
      rw [he, h, e.apply_symm_apply, star_star]
    · exact (hz i j).symm
  let R := Lᴴ * U
  have hR : IsUnitary R := relative_unitary L U hL hU
  have hRcol (i : ι) (j : Fin l) : R i (.inl (.inl j)) = (1 : Matrix ι ι ℂ) i (.inl (.inl j)) := by
    have h := congrArg (fun M : Matrix ι ι ℂ => M i (.inl (.inl j))) hL.2
    simpa only [R, Matrix.mul_apply, hLcol] using h
  have hRrow (i : Fin l) (j : ι) : R (.inl (.inl i)) j = (1 : Matrix ι ι ℂ) (.inl (.inl i)) j := by
    have h := congrArg (fun M : Matrix ι ι ℂ => M (.inl (.inl i)) j) hR.2
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, hRcol, Matrix.one_apply,
      apply_ite star, star_one, star_zero, ite_mul, one_mul, zero_mul] at h
    rw [Finset.sum_ite_eq' Finset.univ (Sum.inl (Sum.inl i) : ι) (fun k => R k j)] at h
    simpa only [Matrix.one_apply, Finset.mem_univ, if_true] using h
  let s := Equiv.sumAssoc (Fin l) Unit (Fin r)
  let W : Matrix (Unit ⊕ Fin r) (Unit ⊕ Fin r) ℂ :=
    R.submatrix (fun i => s.symm (.inr i)) (fun j => s.symm (.inr j))
  have hblocks : R.submatrix s.symm s.symm = fromBlocks (1 : Matrix (Fin l) (Fin l) ℂ) 0 0 W := by
    ext i j : 1
    rcases i with i | i <;> rcases j with j | j
    · change R (.inl (.inl i)) (.inl (.inl j)) = (1 : Matrix (Fin l) (Fin l) ℂ) i j
      simp [hRcol, Matrix.one_apply]
    · change R (.inl (.inl i)) (s.symm (.inr j)) = 0
      rw [hRrow]
      cases j <;> simp [s, Matrix.one_apply]
    · change R (s.symm (.inr i)) (.inl (.inl j)) = 0
      rw [hRcol]
      cases i <;> simp [s, Matrix.one_apply]
    · rfl
  have hW : IsUnitary W := (unitary_directSum_iff.mp (hblocks ▸ unitary_reindex s.symm s.symm hR)).2
  have hR' : R = singlePortRight W := by
    change R = (fromBlocks (1 : Matrix (Fin l) (Fin l) ℂ) 0 0 W).submatrix s s
    rw [← hblocks, Matrix.submatrix_submatrix]
    simp
  refine ⟨W, hV, hW, ?_, hR'.symm⟩
  change U = L * singlePortRight W
  rw [← hR', show R = Lᴴ * U from rfl, ← Matrix.mul_assoc, hL.1, Matrix.one_mul]

/-- Complete the retained columns on the left block. After removing this
factor, the resulting unitary fixes those columns and their rows. -/
theorem exists_singlePort_factors_of_zero_corner {l r : ℕ}
    {U : Matrix ((Fin l ⊕ Unit) ⊕ Fin r) ((Fin l ⊕ Unit) ⊕ Fin r) ℂ}
    (hU : IsUnitary U) (hz : ∀ i j, U (.inr i) (.inl (.inl j)) = 0) :
    ∃ (V : Matrix (Fin l ⊕ Unit) (Fin l ⊕ Unit) ℂ)
      (W : Matrix (Unit ⊕ Fin r) (Unit ⊕ Fin r) ℂ),
      IsUnitary V ∧ IsUnitary W ∧ U = singlePortLeft V * singlePortRight W := by
  obtain ⟨X, hX, hXY⟩ :=
    exists_unitary_retained_rows _ (singlePortRetainedRows_coisometry hU hz) 0
  obtain ⟨W, hV, hW, hprod, _⟩ := singlePort_factors_of_completed_rows hU hz hX hXY
  exact ⟨singlePortCompletedLeft X, W, hV, hW, hprod⟩

private theorem ofReal_map_conjTranspose {m n : Type*} (A : Matrix m n ℝ) :
    Aᴴ.map Complex.ofRealHom = (A.map Complex.ofRealHom)ᴴ := by
  ext i j
  simp only [Matrix.map_apply, Matrix.conjTranspose_apply, star_trivial,
    Complex.ofRealHom_eq_coe, Complex.star_def, Complex.conj_ofReal]

/-- A real unitary with the specified zero corner factors through two real
unitary blocks that meet in one coordinate. -/
theorem exists_real_singlePort_factors_of_zero_corner {l r : ℕ}
    {U : Matrix ((Fin l ⊕ Unit) ⊕ Fin r) ((Fin l ⊕ Unit) ⊕ Fin r) ℂ}
    (hU : IsUnitary U) (hreal : ∀ i j, (U i j).im = 0)
    (hz : ∀ i j, U (.inr i) (.inl (.inl j)) = 0) :
    ∃ (V : Matrix (Fin l ⊕ Unit) (Fin l ⊕ Unit) ℂ)
      (W : Matrix (Unit ⊕ Fin r) (Unit ⊕ Fin r) ℂ),
      IsUnitary V ∧ IsUnitary W ∧ U = singlePortLeft V * singlePortRight W ∧
        (∀ i j, (V i j).im = 0) ∧ ∀ i j, (W i j).im = 0 := by
  let Y := singlePortRetainedRows U
  let Yreal := Y.map Complex.re
  have hY : Y * Yᴴ = 1 := singlePortRetainedRows_coisometry hU hz
  have hYim (i : Fin l) (j : Fin (l + 1)) : (Y i j).im = 0 := by
    change (star (U (.inl (finWithPort l j)) (.inl (.inl i)))).im = 0
    rw [Complex.star_def, Complex.conj_im, hreal, neg_zero]
  have hYcast : Yreal.map Complex.ofRealHom = Y := by
    ext i j
    change ((Y i j).re : ℂ) = Y i j
    exact Complex.ext rfl (hYim i j).symm
  have hYreal : Yreal * Yrealᴴ = 1 := by
    have hc : (Yreal * Yrealᴴ).map Complex.ofRealHom =
        (1 : Matrix (Fin l) (Fin l) ℝ).map Complex.ofRealHom := by
      rw [Matrix.map_mul, ofReal_map_conjTranspose, hYcast, hY,
        Matrix.map_one _ (map_zero _) (map_one _)]
    ext i j
    exact Complex.ofReal_injective (congrArg (fun A : Matrix (Fin l) (Fin l) ℂ => A i j) hc)
  obtain ⟨Z, hZ, hZrows⟩ := exists_coisometry_retained_rows Yreal hYreal 0
  let X := Z.map Complex.ofRealHom
  have hXprod : X * Xᴴ = 1 := by
    dsimp only [X]
    rw [← ofReal_map_conjTranspose, ← Matrix.map_mul, hZ, Matrix.map_one _ (map_zero _) (map_one _)]
  have hX : IsUnitary X := ⟨hXprod, Matrix.mul_eq_one_comm.mp hXprod⟩
  have hXY : X.submatrix (0 : Fin (l + 1)).succAbove id = singlePortRetainedRows U := by
    rw [show singlePortRetainedRows U = Yreal.map Complex.ofRealHom from hYcast.symm]
    ext i j
    exact congrArg (fun A : Matrix (Fin l) (Fin (l + 1)) ℝ => (A i j : ℂ)) hZrows
  obtain ⟨W, hV, hW, hprod, hright⟩ := singlePort_factors_of_completed_rows hU hz hX hXY
  let V := singlePortCompletedLeft X
  have hVreal (i j : Fin l ⊕ Unit) : (V i j).im = 0 := by
    change (star (Complex.ofRealHom (Z ((finWithPort l).symm j) ((finWithPort l).symm i)))).im = 0
    rw [Complex.star_def, Complex.conj_im, Complex.ofRealHom_eq_coe, Complex.ofReal_im, neg_zero]
  let L := singlePortLeft (R := Fin r) V
  have hLreal (i j : (Fin l ⊕ Unit) ⊕ Fin r) : (L i j).im = 0 := by
    rcases i with i | i <;> rcases j with j | j
    · exact hVreal i j
    · exact Complex.zero_im
    · exact Complex.zero_im
    · by_cases hij : i = j
      · simpa only [L, singlePortLeft, Matrix.fromBlocks_apply₂₂, Matrix.one_apply, if_pos hij]
          using Complex.one_im
      · simpa only [L, singlePortLeft, Matrix.fromBlocks_apply₂₂, Matrix.one_apply, if_neg hij]
          using Complex.zero_im
  refine ⟨V, W, hV, hW, hprod, hVreal, ?_⟩
  intro i j
  let e := Equiv.sumAssoc (Fin l) Unit (Fin r)
  have he : singlePortRight (L := Fin l) W (e.symm (.inr i)) (e.symm (.inr j)) = W i j := by
    change (fromBlocks (1 : Matrix (Fin l) (Fin l) ℂ) 0 0 W)
      (e (e.symm (.inr i))) (e (e.symm (.inr j))) = _
    simp only [Equiv.apply_symm_apply, Matrix.fromBlocks_apply₂₂]
  rw [← he, hright]
  change ((Lᴴ * U) (e.symm (.inr i)) (e.symm (.inr j))).im = 0
  simp only [Matrix.mul_apply, Complex.im_sum, Matrix.conjTranspose_apply, Complex.mul_im,
    Complex.star_def, Complex.conj_im, hLreal, hreal, neg_zero, mul_zero, zero_mul, add_zero,
    Finset.sum_const_zero]

/-- Independent row and column relabelings put a rectangle whose side lengths
sum to one less than the order into the designated corner. -/
theorem exists_reindex_singlePort_corner {ι : Type*} [Fintype ι] [DecidableEq ι]
    (I J : Finset ι) (hcard : I.card + J.card + 1 = Fintype.card ι) :
    ∃ eRow eCol : ((Fin J.card ⊕ Unit) ⊕ Fin I.card) ≃ ι,
      (∀ i, eRow (.inr i) ∈ I) ∧ (∀ j, eCol (.inl (.inl j)) ∈ J) := by
  classical
  let sI := Equiv.sumCompl (fun i => i ∈ I)
  let sJ := Equiv.sumCompl (fun j => j ∈ J)
  have hI := Fintype.card_congr sI
  have hJ := Fintype.card_congr sJ
  simp only [Fintype.card_sum, Fintype.card_coe] at hI hJ
  let eI : Fin I.card ≃ {i // i ∈ I} := Fintype.equivOfCardEq (by simp)
  let eJ : Fin J.card ≃ {j // j ∈ J} := Fintype.equivOfCardEq (by simp)
  let eI' : Fin J.card ⊕ Unit ≃ {i // i ∉ I} := Fintype.equivOfCardEq (by
    simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_unit]
    omega)
  let eJ' : Unit ⊕ Fin I.card ≃ {j // j ∉ J} := Fintype.equivOfCardEq (by
    simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_unit]
    omega)
  let eRow := (Equiv.sumComm (Fin J.card ⊕ Unit) (Fin I.card)).trans
    ((Equiv.sumCongr eI eI').trans sI)
  let eCol := (Equiv.sumAssoc (Fin J.card) Unit (Fin I.card)).trans
    ((Equiv.sumCongr eJ eJ').trans sJ)
  exact ⟨eRow, eCol, fun i => (eI i).property, fun j => (eJ j).property⟩

/-- The determinant inclusion for a zero rectangle follows from the
conjecture in the two orders obtained by adding one to its side lengths. -/
theorem holds_of_singlePort_zero_rectangle {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a b : ι → ℂ) {U : Matrix ι ι ℂ} (hU : IsUnitary U) (I J : Finset ι)
    (hcard : I.card + J.card + 1 = Fintype.card ι)
    (hz : ∀ i ∈ I, ∀ j ∈ J, U i j = 0)
    (hleft : Conjecture (Fin (J.card + 1))) (hright : Conjecture (Fin (I.card + 1))) :
    Holds a b U := by
  obtain ⟨er, ec, her, hec⟩ := exists_reindex_singlePort_corner I J hcard
  obtain ⟨V, W, hV, hW, hprod⟩ := exists_singlePort_factors_of_zero_corner
    (unitary_reindex er ec hU) (fun i j => hz _ (her i) _ (hec j))
  have hleft' := (conjecture_reindex_iff (finWithPort J.card)).mp hleft
  have hright' := (conjecture_reindex_iff
    ((finWithPort I.card).trans (Equiv.sumComm (Fin I.card) Unit))).mp hright
  apply (holds_reindex_iff er ec a b U).mp
  rw [hprod]
  exact holds_singlePortComposition _ _ V W hV hW
    (fun c d => hleft' c d V hV) (fun c d => hright' c d W hW)

/-- An order-five mixer with a two-by-two zero rectangle satisfies the
determinant inclusion unconditionally, by the order-three theorem. -/
theorem holds_order_five_of_two_by_two_zero_corner
    (a b : Fin 5 → ℂ) {U : Matrix (Fin 5) (Fin 5) ℂ} (hU : IsUnitary U)
    (I J : Finset (Fin 5)) (hI : I.card = 2) (hJ : J.card = 2)
    (hz : ∀ i ∈ I, ∀ j ∈ J, U i j = 0) : Holds a b U := by
  exact holds_of_singlePort_zero_rectangle a b hU I J (by simp [hI, hJ]) hz
    (conjecture_le_three (by omega)) (conjecture_le_three (by omega))

end

end MOC
