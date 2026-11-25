import MOC.CrossedMinorBlocks
import MOC.CrossedMinorTransport
import MOC.ExteriorMinors

/-! Crossed squared-minor transport in the original subset coordinates.

The finite shadow transport uses the method behind Lyons,
*Determinantal probability measures*, DOI 10.1007/s10240-003-0016-0.
The common row/column deflation is what lets the two shadow transports
share their intermediate masses. -/

open BigOperators Finset Matrix

namespace MOC

noncomputable section

private def rowFactors {n k : ℕ} (W : Matrix (Fin n) (Fin n) ℂ) (I : ExteriorRows n k) :
    List (Fin n → ℂ) := List.ofFn (fun i j => W (I.row i) j)

private def colFactors {n k : ℕ} (W : Matrix (Fin n) (Fin n) ℂ) (J : ExteriorRows n k) :
    List (Fin n → ℂ) := List.ofFn (fun j i => W i (J.row j))

private theorem exterior_rows_cols {n a b : ℕ} (W : Matrix (Fin n) (Fin n) ℂ)
    (I : ExteriorRows n a) (J : ExteriorRows n b) :
    exteriorColumnVector n (rowFactors W I) J.cube =
      exteriorColumnVector n (colFactors W J) I.cube := by
  by_cases he : a = b
  · subst b
    rw [rowFactors, colFactors, exteriorColumnVector_eq_det_of_rows,
      exteriorColumnVector_eq_det_of_rows, ← Matrix.det_transpose]
    rfl
  · rw [exteriorColumnVector_eq_zero_of_rows J (rowFactors W I) (by simpa [rowFactors] using Ne.symm he),
      exteriorColumnVector_eq_zero_of_rows I (colFactors W J) (by simpa [colFactors] using he)]

private def crossedBase {n : ℕ} (W : Matrix (Fin n) (Fin n) ℂ) (I J : SubsetCube n) : ℂ :=
  exteriorColumnVector n (colFactors W (ExteriorRows.ofCube n J).2) I

private theorem crossedBase_row {n : ℕ} (W : Matrix (Fin n) (Fin n) ℂ) (I : SubsetCube n) :
    crossedBase W I = exteriorColumnVector n (rowFactors W (ExteriorRows.ofCube n I).2) := by
  funext J
  have h := exterior_rows_cols W (ExteriorRows.ofCube n I).2 (ExteriorRows.ofCube n J).2
  simpa only [ExteriorRows.ofCube_cube, crossedBase] using h.symm

private theorem crossedBase_degree {n : ℕ} (W : Matrix (Fin n) (Fin n) ℂ)
    (I J : SubsetCube n) (h : crossedBase W I J ≠ 0) :
    (subsetCubeLabels n I).card = (subsetCubeLabels n J).card := by
  let i := ExteriorRows.ofCube n I
  let j := ExteriorRows.ofCube n J
  have hI : i.2.cube = I := ExteriorRows.ofCube_cube n I
  have hJ : j.2.cube = J := ExteriorRows.ofCube_cube n J
  rw [← hI, ← hJ, ExteriorRows.card_labels, ExteriorRows.card_labels]
  by_contra hn
  apply h
  change exteriorColumnVector n (colFactors W j.2) I = 0
  rw [← hI]
  exact exteriorColumnVector_eq_zero_of_rows i.2 _ (by simpa [colFactors] using hn)

private def skipLabels {n : ℕ} (S : Finset (Fin n)) : Finset (Fin (n+1)) :=
  S.map (Fin.succEmb n)

private def takeLabels {n : ℕ} (S : Finset (Fin n)) : Finset (Fin (n+1)) :=
  insert 0 (skipLabels S)

private theorem mark_not_mem_skipLabels {n : ℕ} (S : Finset (Fin n)) :
    (0 : Fin (n+1)) ∉ skipLabels S := by
  intro h
  rcases mem_map.mp h with ⟨i, _, h⟩
  exact i.succ_ne_zero h

@[simp] private theorem card_skipLabels {n : ℕ} (S : Finset (Fin n)) :
    (skipLabels S).card = S.card := card_map _

@[simp] private theorem card_takeLabels {n : ℕ} (S : Finset (Fin n)) :
    (takeLabels S).card = S.card + 1 := by
  rw [takeLabels, card_insert_of_not_mem (mark_not_mem_skipLabels S), card_skipLabels]

private theorem subsetMinorSq_skip_take {n a : ℕ}
    (U : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) (hU : IsUnitary U)
    (I : ExteriorRows n (a+1)) (J : ExteriorRows n a) :
    subsetMinorSq U (skipLabels (subsetCubeLabels n I.cube)) (takeLabels (subsetCubeLabels n J.cube)) =
      Complex.normSq (Matrix.of
        (fun i j : Fin (a+1) => Fin.cases (U (I.row i).succ 0)
          (fun t => U (I.row i).succ (J.row t).succ) j)).det := by
  change subsetMinorSq U (subsetCubeLabels (n+1) (ExteriorRows.skip I).cube)
    (subsetCubeLabels (n+1) (ExteriorRows.take J).cube) = _
  rw [subsetMinorSq_eq_normSq_det_submatrix U hU _ _
    (ExteriorRows.skip I).equivLabels (ExteriorRows.take J).equivLabels]
  congr 2
  ext i j
  refine Fin.cases ?_ (fun t => ?_) j <;> rfl

private theorem subsetMinorSq_take_skip {n a : ℕ}
    (U : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) (hU : IsUnitary U)
    (I : ExteriorRows n a) (J : ExteriorRows n (a+1)) :
    subsetMinorSq U (takeLabels (subsetCubeLabels n I.cube)) (skipLabels (subsetCubeLabels n J.cube)) =
      Complex.normSq (Matrix.of
        (fun i j : Fin (a+1) => Fin.cases (U 0 (J.row j).succ)
          (fun t => U (I.row t).succ (J.row j).succ) i)).det := by
  change subsetMinorSq U (subsetCubeLabels (n+1) (ExteriorRows.take I).cube)
    (subsetCubeLabels (n+1) (ExteriorRows.skip J).cube) = _
  rw [subsetMinorSq_eq_normSq_det_submatrix U hU _ _
    (ExteriorRows.take I).equivLabels (ExteriorRows.skip J).equivLabels]
  congr 2
  ext i j
  refine Fin.cases ?_ (fun t => ?_) i <;> rfl


private theorem crossedMinorRow_normSq {n a b : ℕ}
    (U : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) (hU : IsUnitary U)
    (s : ℝ) (hs : s ≠ 0) (x y : Fin n → ℂ) (hx : ∀ j, U 0 j.succ = (s : ℂ) * star (x j))
    (I : ExteriorRows n a) (J : ExteriorRows n b) :
    let W : Matrix (Fin n) (Fin n) ℂ := Matrix.of
      (fun i j => U i.succ j.succ + star (U 0 0) * y i * star (x j))
    subsetMinorSq U (takeLabels (subsetCubeLabels n I.cube)) (skipLabels (subsetCubeLabels n J.cube))
      = Complex.normSq (s : ℂ) * Complex.normSq
        (exteriorColumnVector n ((fun j => star (x j)) :: rowFactors W I) J.cube) := by
  intro W
  by_cases he : b = a + 1
  · subst b
    rw [subsetMinorSq_take_skip U hU I J, det_crossed_row_of_deflation U s hs x y hx I.row J.row,
      map_mul]
    have h : ((fun j => star (x j)) :: rowFactors W I) =
      List.ofFn (fun t j => Fin.cases (star (x j)) (fun r => W (I.row r) j) t) := by
        rw [List.ofFn_succ]
        rfl
    rw [h, exteriorColumnVector_eq_det_of_rows]
    congr 2
    rw [← Matrix.det_transpose]
    rfl
  · have hz : b ≠ (((fun j => star (x j)) :: rowFactors W I) : List (Fin n → ℂ)).length := by
      simpa only [rowFactors, List.length_cons, List.length_ofFn] using he
    simp only [subsetMinorSq, card_takeLabels, card_skipLabels, ExteriorRows.card_labels, dif_neg (Ne.symm he),
      exteriorColumnVector_eq_zero_of_rows J _ hz, map_zero, mul_zero]

private theorem crossedMinorCol_normSq {n a b : ℕ}
    (U : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) (hU : IsUnitary U)
    (s : ℝ) (hs : s ≠ 0) (x y : Fin n → ℂ) (hy : ∀ i, U i.succ 0 = (s : ℂ) * y i)
    (I : ExteriorRows n a) (J : ExteriorRows n b) :
    let W : Matrix (Fin n) (Fin n) ℂ := Matrix.of
      (fun i j => U i.succ j.succ + star (U 0 0) * y i * star (x j))
    subsetMinorSq U (skipLabels (subsetCubeLabels n I.cube)) (takeLabels (subsetCubeLabels n J.cube))
      = Complex.normSq (s : ℂ) * Complex.normSq
        (exteriorColumnVector n (y :: colFactors W J) I.cube) := by
  intro W
  by_cases he : a = b + 1
  · subst a
    rw [subsetMinorSq_skip_take U hU I J, det_crossed_column_of_deflation U s hs x y hy I.row J.row,
      map_mul]
    have h : y :: colFactors W J = List.ofFn
      (fun t i => Fin.cases (y i) (fun r => W i (J.row r)) t) := by
        rw [List.ofFn_succ]
        rfl
    rw [h, exteriorColumnVector_eq_det_of_rows]
  · have hz : a ≠ (y :: colFactors W J).length := by
      simpa only [colFactors, List.length_cons, List.length_ofFn] using he
    simp only [subsetMinorSq, card_takeLabels, card_skipLabels, ExteriorRows.card_labels, dif_neg he,
      exteriorColumnVector_eq_zero_of_rows I _ hz, map_zero, mul_zero]


private theorem exists_crossed_subsetMinorSq_transport_of_normalized {n : ℕ}
    (U : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) (hU : IsUnitary U)
    (s : ℝ) (hs : s ≠ 0) (x y : Fin n → ℂ)
    (hx : ∀ j, U 0 j.succ = (s : ℂ) * star (x j))
    (hy : ∀ i, U i.succ 0 = (s : ℂ) * y i)
    (hx₁ : ∑ i, Complex.normSq (x i) = 1) (hy₁ : ∑ i, Complex.normSq (y i) = 1) :
    ∃ μ : (Finset (Fin n) × Finset (Fin n)) → (Finset (Fin n) × Finset (Fin n)) → ℝ,
      (∀ A B, 0 ≤ μ A B) ∧
      (∀ A B, μ A B ≠ 0 → A.1 ⊆ B.1 ∧ B.2 ⊆ A.2 ∧ A.1.card = B.2.card) ∧
      (∀ A, ∑ B, μ A B = subsetMinorSq U (takeLabels A.1) (skipLabels A.2)) ∧
      (∀ B, ∑ A, μ A B = subsetMinorSq U (skipLabels B.1) (takeLabels B.2)) := by
  let W : Matrix (Fin n) (Fin n) ℂ := Matrix.of
    (fun i j => U i.succ j.succ + star (U 0 0) * y i * star (x j))
  obtain ⟨hWrow, hWcol⟩ := crossed_spectator_block_annihilates U hU s hs x y hx hy hx₁ hy₁
  have hstar : ∑ i, Complex.normSq (star (x i)) = 1 := by
    simpa only [Complex.star_def, Complex.normSq_conj] using hx₁
  have hr : ∀ I, subsetContraction n (star x) *ᵥ crossedBase W I = 0 := by
    intro I
    rw [crossedBase_row]
    apply subsetContraction_mulVec_exteriorColumnVector_orthogonal
    intro f hf
    obtain ⟨t, rfl⟩ := List.mem_ofFn.mp hf
    simp only [Pi.star_apply, star_star]
    calc
      _ = ∑ j, W ((ExteriorRows.ofCube n I).2.row t) j * x j :=
        sum_congr rfl (fun j _ => mul_comm _ _)
      _ = 0 := hWrow ((ExteriorRows.ofCube n I).2.row t)
  have hc : ∀ J, subsetContraction n y *ᵥ (fun I => crossedBase W I J) = 0 := by
    intro J
    apply subsetContraction_mulVec_exteriorColumnVector_orthogonal
    intro f hf
    obtain ⟨t, rfl⟩ := List.mem_ofFn.mp hf
    exact hWcol ((ExteriorRows.ofCube n J).2.row t)
  obtain ⟨p, hp, hpS, hpR, hpC⟩ :=
    exists_crossed_exterior_transport n n (star x) y hstar hy₁ _ hr hc
  let e := subsetCubeEquivLabels n
  let E := e.prodCongr e
  let m := Complex.normSq (s : ℂ)
  let μ (A B) := m * p (E.symm A) (E.symm B)
  have hRow (I J : SubsetCube n) :
      subsetMinorSq U (takeLabels (e I)) (skipLabels (e J)) =
        m * Complex.normSq (((subsetContraction n (star x))ᴴ *ᵥ crossedBase W I) J) := by
    have h := crossedMinorRow_normSq U hU s hs x y hx
      (ExteriorRows.ofCube n I).2 (ExteriorRows.ofCube n J).2
    simp only [ExteriorRows.ofCube_cube] at h
    rw [crossedBase_row]
    exact h
  have hCol (I J : SubsetCube n) :
      subsetMinorSq U (skipLabels (e I)) (takeLabels (e J)) =
        m * Complex.normSq (((subsetContraction n y)ᴴ *ᵥ (fun K => crossedBase W K J)) I) := by
    have h := crossedMinorCol_normSq U hU s hs x y hy
      (ExteriorRows.ofCube n I).2 (ExteriorRows.ofCube n J).2
    simp only [ExteriorRows.ofCube_cube] at h
    exact h
  refine ⟨μ, fun A B => mul_nonneg (Complex.normSq_nonneg _) (hp _ _), ?_, ?_, ?_⟩
  · intro A B h
    have hp' : p (E.symm A) (E.symm B) ≠ 0 := fun he => h (by simp [μ, he])
    obtain ⟨hr', hc', hm'⟩ := hpS _ _ hp'
    have hs' := crossedBase_degree W _ _ hm'
    have hh : (e (E.symm A).1, e (E.symm A).2) = A := E.apply_symm_apply A
    have hk : (e (E.symm B).1, e (E.symm B).2) = B := E.apply_symm_apply B
    change e (E.symm A).1 ⊆ e (E.symm B).1 at hr'
    change e (E.symm B).2 ⊆ e (E.symm A).2 at hc'
    change (e (E.symm A).1).card = (e (E.symm B).2).card at hs'
    have ha₁ : e (E.symm A).1 = A.1 := congrArg Prod.fst hh
    have ha₂ : e (E.symm A).2 = A.2 := congrArg Prod.snd hh
    have hb₁ : e (E.symm B).1 = B.1 := congrArg Prod.fst hk
    have hb₂ : e (E.symm B).2 = B.2 := congrArg Prod.snd hk
    rw [ha₁, hb₁] at hr'
    rw [hb₂, ha₂] at hc'
    rw [ha₁, hb₂] at hs'
    exact ⟨hr', hc', hs'⟩
  · intro A
    obtain ⟨A, rfl⟩ := E.surjective A
    simp only [μ, Equiv.symm_apply_apply, ← Equiv.sum_comp E (fun B => m * p A (E.symm B)),
      ← mul_sum]
    rw [hpR]
    exact (hRow A.1 A.2).symm
  · intro B
    obtain ⟨B, rfl⟩ := E.surjective B
    simp only [μ, Equiv.symm_apply_apply, ← Equiv.sum_comp E (fun A => m * p (E.symm A) B),
      ← mul_sum]
    rw [hpC]
    exact (hCol B.1 B.2).symm


private theorem crossed_row_col_norm_mass {n : ℕ}
    (U : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) (hU : IsUnitary U) :
    (∑ j : Fin n, Complex.normSq (U 0 j.succ)) =
      ∑ i : Fin n, Complex.normSq (U i.succ 0) := by
  have hr : (∑ j : Fin (n+1), Complex.normSq (U 0 j)) = 1 := by
    apply Complex.ofReal_injective
    rw [Complex.ofReal_sum, Complex.ofReal_one]
    simpa only [Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.star_def,
      Complex.mul_conj, Matrix.one_apply_eq] using congrFun (congrFun hU.1 0) 0
  have hc : (∑ i : Fin (n+1), Complex.normSq (U i 0)) = 1 := by
    apply Complex.ofReal_injective
    rw [Complex.ofReal_sum, Complex.ofReal_one]
    simpa only [Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.star_def,
      ← Complex.normSq_eq_conj_mul_self, Matrix.one_apply_eq] using congrFun (congrFun hU.2 0) 0
  simp only [Fin.sum_univ_succ] at hr hc
  linarith

private theorem crossedMinorRow_of_zero {n a b : ℕ}
    (U : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) (hU : IsUnitary U)
    (hz : ∀ j, U 0 (Fin.succ j) = 0) (I : ExteriorRows n a) (J : ExteriorRows n b) :
    subsetMinorSq U (takeLabels (subsetCubeLabels n I.cube))
      (skipLabels (subsetCubeLabels n J.cube)) = 0 := by
  by_cases he : b = a+1
  · subst b
    rw [subsetMinorSq_take_skip U hU I J, Matrix.det_eq_zero_of_row_eq_zero 0]
    · simp
    · intro j
      simp [hz]
  · simp only [subsetMinorSq, card_takeLabels, card_skipLabels, ExteriorRows.card_labels, dif_neg (Ne.symm he)]

private theorem crossedMinorCol_of_zero {n a b : ℕ}
    (U : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) (hU : IsUnitary U)
    (hz : ∀ i, U (Fin.succ i) 0 = 0) (I : ExteriorRows n a) (J : ExteriorRows n b) :
    subsetMinorSq U (skipLabels (subsetCubeLabels n I.cube))
      (takeLabels (subsetCubeLabels n J.cube)) = 0 := by
  by_cases he : a = b+1
  · subst a
    rw [subsetMinorSq_skip_take U hU I J, Matrix.det_eq_zero_of_column_eq_zero 0]
    · simp
    · intro i
      simp [hz]
  · simp only [subsetMinorSq, card_takeLabels, card_skipLabels, ExteriorRows.card_labels, dif_neg he]

/-- Crossed squared minors admit positive transport. The first minor contains
the marked row but not the marked column, while the second contains
the marked column but not the marked row. The transport preserves degree
and exchanges exactly one spectator row and one spectator column. -/
theorem exists_crossed_subsetMinorSq_transport {n : ℕ}
    (U : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) (hU : IsUnitary U) :
    ∃ μ : (Finset (Fin n) × Finset (Fin n)) → (Finset (Fin n) × Finset (Fin n)) → ℝ,
      (∀ A B, 0 ≤ μ A B) ∧
      (∀ A B, μ A B ≠ 0 → A.1 ⊆ B.1 ∧ B.2 ⊆ A.2 ∧ A.1.card = B.2.card) ∧
      (∀ A, ∑ B, μ A B = subsetMinorSq U
        (insert 0 (A.1.map (Fin.succEmb n))) (A.2.map (Fin.succEmb n))) ∧
      (∀ B, ∑ A, μ A B = subsetMinorSq U
        (B.1.map (Fin.succEmb n)) (insert 0 (B.2.map (Fin.succEmb n)))) := by
  change ∃ μ : (Finset (Fin n) × Finset (Fin n)) → (Finset (Fin n) × Finset (Fin n)) → ℝ,
      (∀ A B, 0 ≤ μ A B) ∧
      (∀ A B, μ A B ≠ 0 → A.1 ⊆ B.1 ∧ B.2 ⊆ A.2 ∧ A.1.card = B.2.card) ∧
      (∀ A, ∑ B, μ A B = subsetMinorSq U (takeLabels A.1) (skipLabels A.2)) ∧
      (∀ B, ∑ A, μ A B = subsetMinorSq U (skipLabels B.1) (takeLabels B.2))
  let t := ∑ j : Fin n, Complex.normSq (U 0 j.succ)
  have tdef : t = ∑ i : Fin n, Complex.normSq (U i.succ 0) := crossed_row_col_norm_mass U hU
  by_cases ht : t = 0
  · have hr : ∀ j : Fin n, U 0 j.succ = 0 := fun j => Complex.normSq_eq_zero.mp
      ((sum_eq_zero_iff_of_nonneg (fun _ _ => Complex.normSq_nonneg _)).mp ht j (mem_univ j))
    have hc : ∀ i : Fin n, U i.succ 0 = 0 := fun i => Complex.normSq_eq_zero.mp
      ((sum_eq_zero_iff_of_nonneg (fun _ _ => Complex.normSq_nonneg _)).mp (tdef.symm.trans ht) i (mem_univ i))
    let e := subsetCubeEquivLabels n
    refine ⟨fun _ _ => 0, fun _ _ => le_rfl, fun _ _ h => (h rfl).elim, ?_, ?_⟩
    · rintro ⟨a,b⟩
      obtain ⟨A, rfl⟩ := e.surjective a
      obtain ⟨B, rfl⟩ := e.surjective b
      simpa only [sum_const_zero, ExteriorRows.ofCube_cube, eq_comm] using
        crossedMinorRow_of_zero U hU hr (ExteriorRows.ofCube n A).2 (ExteriorRows.ofCube n B).2
    · rintro ⟨a,b⟩
      obtain ⟨A, rfl⟩ := e.surjective a
      obtain ⟨B, rfl⟩ := e.surjective b
      simpa only [sum_const_zero, ExteriorRows.ofCube_cube, eq_comm] using
        crossedMinorCol_of_zero U hU hc (ExteriorRows.ofCube n A).2 (ExteriorRows.ofCube n B).2
  · have htn : 0 ≤ t := sum_nonneg fun _ _ => Complex.normSq_nonneg _
    have ht' : 0 < t := lt_of_le_of_ne htn (Ne.symm ht)
    let s := Real.sqrt t
    have hs : s ≠ 0 := (Real.sqrt_pos.2 ht').ne'
    have hsc : (s : ℂ) ≠ 0 := by exact_mod_cast hs
    have hn : Complex.normSq (s : ℂ) = t := by
      rw [Complex.normSq_ofReal, ← pow_two, Real.sq_sqrt htn]
    let x (i : Fin n) := star (U 0 i.succ) / (s : ℂ)
    let y (i : Fin n) := U i.succ 0 / (s : ℂ)
    have hx₁ : ∑ i, Complex.normSq (x i) = 1 := by
      simp only [x, Complex.normSq_div, Complex.star_def, Complex.normSq_conj, hn, ← sum_div]
      exact div_self ht
    have hy₁ : ∑ i, Complex.normSq (y i) = 1 := by
      simp only [y, Complex.normSq_div, hn, ← sum_div, ← tdef, div_self ht]
    have hx (i : Fin n) : U 0 i.succ = (s : ℂ) * star (x i) := by
      simp only [x, Complex.star_def, map_div₀, Complex.conj_ofReal, Complex.conj_conj]
      field_simp
    have hy (i : Fin n) : U i.succ 0 = (s : ℂ) * y i := by
      simp only [y]
      field_simp
    exact exists_crossed_subsetMinorSq_transport_of_normalized U hU s hs x y hx hy hx₁ hy₁


end

end MOC
