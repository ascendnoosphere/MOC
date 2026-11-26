import Mathlib.Algebra.Group.Submonoid.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Matrix.Notation
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Generation of real special orthogonal matrices by coordinate rotations. -/

open BigOperators Matrix

namespace MOC

noncomputable section

/-- The rotation on the ordered pair of coordinates `i,j`, with block
`[[c,-s],[s,c]]` and identity on the other coordinates. -/
def realCoordinateRotation {ι : Type*} [DecidableEq ι] (i j : ι) (c s : ℝ) : Matrix ι ι ℝ :=
  Matrix.of fun k l =>
    if k = i then if l = i then c else if l = j then -s else 0
    else if k = j then if l = i then s else if l = j then c else 0
    else if k = l then 1 else 0

theorem realCoordinateRotation_mulVec {ι : Type*} [Fintype ι] [DecidableEq ι]
    {i j : ι} (hij : i ≠ j) (c s : ℝ) (x : ι → ℝ) (k : ι) :
    (realCoordinateRotation i j c s *ᵥ x) k =
      if k = i then c * x i - s * x j else if k = j then s * x i + c * x j else x k := by
  change realCoordinateRotation i j c s k ⬝ᵥ x = _
  by_cases hi : k = i
  · subst k
    have hr : realCoordinateRotation i j c s i = Pi.single i c + Pi.single j (-s) := by
      funext l
      by_cases hli : l = i
      · subst l
        simp [realCoordinateRotation, Pi.single_apply, hij, hij.symm]
      · simp [realCoordinateRotation, Pi.single_apply, hli]
    rw [hr, add_dotProduct, single_dotProduct, single_dotProduct, if_pos rfl, neg_mul, sub_eq_add_neg]
  by_cases hj : k = j
  · subst k
    have hr : realCoordinateRotation i j c s j = Pi.single i s + Pi.single j c := by
      funext l
      by_cases hli : l = i
      · subst l
        simp [realCoordinateRotation, Pi.single_apply, hij, hij.symm]
      · simp [realCoordinateRotation, Pi.single_apply, hli, hij.symm]
    rw [hr, add_dotProduct, single_dotProduct, single_dotProduct, if_neg hi, if_pos rfl]
  have hr : realCoordinateRotation i j c s k = Pi.single k 1 := by
    funext l
    by_cases hkl : l = k
    · subst l
      simp [realCoordinateRotation, hi, hj]
    · simp [realCoordinateRotation, Pi.single_apply, hi, hj, hkl, hkl.symm]
  rw [hr, single_dotProduct, one_mul, if_neg hi, if_neg hj]

theorem realCoordinateRotation_transpose {ι : Type*} [DecidableEq ι]
    {i j : ι} (hij : i ≠ j) (c s : ℝ) :
    (realCoordinateRotation i j c s)ᵀ = realCoordinateRotation i j c (-s) := by
  ext k l
  by_cases hki : k = i <;> by_cases hkj : k = j <;>
    by_cases hli : l = i <;> by_cases hlj : l = j <;>
    simp_all [realCoordinateRotation, eq_comm]

theorem realCoordinateRotation_swap {ι : Type*} [DecidableEq ι]
    {i j : ι} (hij : i ≠ j) (c s : ℝ) :
    realCoordinateRotation j i c s = realCoordinateRotation i j c (-s) := by
  ext k l
  by_cases hki : k = i <;> by_cases hkj : k = j <;>
    by_cases hli : l = i <;> by_cases hlj : l = j <;>
    simp_all [realCoordinateRotation, eq_comm]

private def rotationPairEquiv {ι : Type*} [DecidableEq ι] (i j : ι) (hij : i ≠ j) :
    Fin 2 ⊕ {k : ι // k ≠ i ∧ k ≠ j} ≃ ι where
  toFun := Sum.elim (fun x => if x = 0 then i else j) Subtype.val
  invFun k := if hi : k = i then .inl 0 else if hj : k = j then .inl 1 else .inr ⟨k, hi, hj⟩
  left_inv := by
    rintro (k | ⟨k, hk, hl⟩)
    · fin_cases k <;> simp [hij.symm]
    · simp [hk, hl]
  right_inv := by
    intro k
    by_cases hk : k = i
    · subst k
      simp
    by_cases hl : k = j
    · subst k
      simp [hk]
    · simp [hk, hl]

private theorem realCoordinateRotation_blocks {ι : Type*} [DecidableEq ι]
    {i j : ι} (hij : i ≠ j) (c s : ℝ) :
    let e := rotationPairEquiv i j hij
    (realCoordinateRotation i j c s).submatrix e e = fromBlocks !![c, -s; s, c] 0 0 1 := by
  intro e
  ext (k | ⟨k, hki, hkj⟩) (l | ⟨l, hli, hlj⟩)
  · fin_cases k <;> fin_cases l <;> simp [e, rotationPairEquiv, realCoordinateRotation, hij, hij.symm]
  · fin_cases k <;> simp [e, rotationPairEquiv, realCoordinateRotation, hij, hij.symm, hli, hlj]
  · fin_cases l <;> simp [e, rotationPairEquiv, realCoordinateRotation, hki, hkj, hki.symm, hkj.symm]
  · simp [e, rotationPairEquiv, realCoordinateRotation, Matrix.one_apply, hki, hkj, Subtype.ext_iff]

theorem realCoordinateRotation_orthogonal_det {ι : Type*} [Fintype ι] [DecidableEq ι]
    {i j : ι} (hij : i ≠ j) {c s : ℝ} (hcs : c ^ 2 + s ^ 2 = 1) :
    let R := realCoordinateRotation i j c s
    Rᵀ * R = 1 ∧ R.det = 1 := by
  intro R
  let e := rotationPairEquiv i j hij
  let J : Matrix (Fin 2) (Fin 2) ℝ := !![c, -s; s, c]
  have hblock : R.submatrix e e = fromBlocks J 0 0 1 := realCoordinateRotation_blocks hij c s
  have hJ : Jᵀ * J = 1 := by
    ext k l
    fin_cases k <;> fin_cases l <;>
      simp [J, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] <;> nlinarith only [hcs]
  constructor
  · have hsub : (Rᵀ * R).submatrix e e = (1 : Matrix ι ι ℝ).submatrix e e := by
      rw [← Matrix.submatrix_mul_equiv Rᵀ R e e e, ← Matrix.transpose_submatrix, hblock,
        Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply, Matrix.submatrix_one_equiv]
      simp only [Matrix.transpose_zero, Matrix.transpose_one, Matrix.zero_mul, Matrix.mul_zero,
        add_zero, zero_add, Matrix.one_mul, hJ, Matrix.fromBlocks_one]
    ext k l
    simpa only [Matrix.submatrix_apply, e.apply_symm_apply] using
      congrArg (fun M : Matrix _ _ ℝ => M (e.symm k) (e.symm l)) hsub
  · rw [← Matrix.det_submatrix_equiv_self e R, hblock, Matrix.det_fromBlocks_zero₂₁,
      Matrix.det_one, mul_one, show J.det = c * c - (-s) * s from Matrix.det_fin_two_of c (-s) s c]
    nlinarith only [hcs]

/-- The monoid generated by all coordinate rotations. -/
def realCoordinateRotationMonoid (ι : Type*) [Fintype ι] [DecidableEq ι] :
    Submonoid (Matrix ι ι ℝ) :=
  Submonoid.closure {R | ∃ (i j : ι) (c s : ℝ), i ≠ j ∧ c ^ 2 + s ^ 2 = 1 ∧
    R = realCoordinateRotation i j c s}

theorem realCoordinateRotation_mem {ι : Type*} [Fintype ι] [DecidableEq ι]
    {i j : ι} (hij : i ≠ j) {c s : ℝ} (hcs : c ^ 2 + s ^ 2 = 1) :
    realCoordinateRotation i j c s ∈ realCoordinateRotationMonoid ι :=
  Submonoid.subset_closure ⟨i, j, c, s, hij, hcs, rfl⟩

private theorem coordinateRotationMonoid_properties {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R : Matrix ι ι ℝ} (hR : R ∈ realCoordinateRotationMonoid ι) :
    Rᵀ ∈ realCoordinateRotationMonoid ι ∧ Rᵀ * R = 1 ∧ R.det = 1 := by
  unfold realCoordinateRotationMonoid at hR
  refine Submonoid.closure_induction (motive := fun A _ =>
    Aᵀ ∈ realCoordinateRotationMonoid ι ∧ Aᵀ * A = 1 ∧ A.det = 1) ?_ ?_ ?_ hR
  · rintro _ ⟨i, j, c, s, hij, hcs, rfl⟩
    refine ⟨?_, realCoordinateRotation_orthogonal_det hij hcs⟩
    rw [realCoordinateRotation_transpose hij]
    exact realCoordinateRotation_mem hij (by simpa only [neg_sq] using hcs)
  · simp only [Matrix.transpose_one, Matrix.one_mul, Matrix.det_one, and_true]
    exact (realCoordinateRotationMonoid ι).one_mem
  · intro A B _ _ hA hB
    rw [Matrix.transpose_mul]
    refine ⟨(realCoordinateRotationMonoid ι).mul_mem hB.1 hA.1, ?_, ?_⟩
    · calc
        (Bᵀ * Aᵀ) * (A * B) = Bᵀ * (Aᵀ * A) * B := by simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hA.2.1, Matrix.mul_one, hB.2.1]
    · rw [Matrix.det_mul, hA.2.2, hB.2.2, one_mul]

private theorem exists_annihilating_coordinateRotation (x y : ℝ) :
    ∃ c s : ℝ, c ^ 2 + s ^ 2 = 1 ∧ 0 ≤ c * x - s * y ∧ s * x + c * y = 0 := by
  by_cases h : x = 0 ∧ y = 0
  · exact ⟨1, 0, by norm_num, by simp [h.1, h.2], by simp [h.1, h.2]⟩
  let d := Real.sqrt (x ^ 2 + y ^ 2)
  have hsum : 0 < x ^ 2 + y ^ 2 := by
    by_cases hx : x = 0
    · have hy : y ≠ 0 := fun he => h ⟨hx, he⟩
      simpa [hx] using sq_pos_of_ne_zero hy
    · exact add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero hx) (sq_nonneg y)
  have hd : 0 < d := Real.sqrt_pos.2 hsum
  have hd₂ : d ^ 2 = x ^ 2 + y ^ 2 := Real.sq_sqrt hsum.le
  refine ⟨x / d, -y / d, ?_, ?_, ?_⟩
  · rw [div_pow, div_pow, neg_sq, ← add_div, ← hd₂]
    exact div_self (pow_ne_zero 2 hd.ne')
  · have he : x / d * x - (-y / d) * y = d := by
      field_simp [hd.ne'] <;> nlinarith only [hd₂]
    rw [he]
    exact hd.le
  · field_simp [hd.ne'] <;> ring

private theorem matrix_mul_apply_of_basis_column {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι ℝ) (k j : ι) {p : ι}
    (h : ∀ l, B l j = (1 : Matrix ι ι ℝ) l p) : (A * B) k j = A k p := by
  change A k ⬝ᵥ (fun l => B l j) = A k p
  rw [show (fun l => B l j) = fun l => (1 : Matrix ι ι ℝ) l p from funext h]
  exact congrArg (fun M : Matrix ι ι ℝ => M k p) (Matrix.mul_one A)

/-- An orthogonal change of coordinates transports a rotation when it sends the two
coordinate vectors to coordinate vectors. -/
theorem realCoordinateRotation_conjugate {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Q : Matrix ι ι ℝ) (hQ : Qᵀ * Q = 1) {i j p q : ι} (hij : i ≠ j) (hpq : p ≠ q)
    (hi : ∀ k, Q k i = (1 : Matrix ι ι ℝ) k p)
    (hj : ∀ k, Q k j = (1 : Matrix ι ι ℝ) k q) (c s : ℝ) :
    Q * realCoordinateRotation i j c s * Qᵀ = realCoordinateRotation p q c s := by
  have hrowi (k : ι) : Q p k = (1 : Matrix ι ι ℝ) i k := by
    calc
      Q p k = (Qᵀ * Q) k i := (matrix_mul_apply_of_basis_column Qᵀ Q k i hi).symm
      _ = _ := by rw [hQ, Matrix.one_apply, Matrix.one_apply, eq_comm]
  have hrowj (k : ι) : Q q k = (1 : Matrix ι ι ℝ) j k := by
    calc
      Q q k = (Qᵀ * Q) k j := (matrix_mul_apply_of_basis_column Qᵀ Q k j hj).symm
      _ = _ := by rw [hQ, Matrix.one_apply, Matrix.one_apply, eq_comm]
  have hleft (k l : ι) :
      (Q * realCoordinateRotation i j c s) k l =
        if l = i then c * Q k i + s * Q k j
        else if l = j then -s * Q k i + c * Q k j else Q k l := by
    have he : (Q * realCoordinateRotation i j c s) k l =
        ((realCoordinateRotation i j c s)ᵀ *ᵥ Q k) l := by
      simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.transpose_apply, mul_comm]
    rw [he, realCoordinateRotation_transpose hij, realCoordinateRotation_mulVec hij]
    simp only [neg_mul, sub_neg_eq_add]
  have hright (k l : ι) :
      (realCoordinateRotation p q c s * Q) k l =
        if k = p then c * Q p l - s * Q q l
        else if k = q then s * Q p l + c * Q q l else Q k l :=
    realCoordinateRotation_mulVec hpq c s (fun m => Q m l) k
  have hcomm : Q * realCoordinateRotation i j c s = realCoordinateRotation p q c s * Q := by
    ext k l
    rw [hleft, hright]
    by_cases hkp : k = p <;> by_cases hkq : k = q <;>
      by_cases hli : l = i <;> by_cases hlj : l = j <;>
      simp_all [hi, hj, hrowi, hrowj, Matrix.one_apply, eq_comm]
  rw [hcomm, Matrix.mul_assoc, Matrix.mul_eq_one_comm.mp hQ, Matrix.mul_one]

private theorem clear_coordinates {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : ι → ℝ) (i : ι) (t : Finset ι) (hti : i ∉ t) :
    ∃ P : Matrix ι ι ℝ, P ∈ realCoordinateRotationMonoid ι ∧
      (∀ j ∈ t, (P *ᵥ x) j = 0) ∧ (t.Nonempty → 0 ≤ (P *ᵥ x) i) ∧
      (∀ j ∉ insert i t, ∀ k, P k j = (1 : Matrix ι ι ℝ) k j) := by
  classical
  induction t using Finset.induction_on with
  | empty =>
      refine ⟨1, (realCoordinateRotationMonoid ι).one_mem, ?_, ?_, ?_⟩ <;> simp
  | @insert j t hj ih =>
      have hij : i ≠ j := fun he => hti (Finset.mem_insert.mpr (Or.inl he))
      have hit : i ∉ t := fun ht => hti (Finset.mem_insert_of_mem ht)
      obtain ⟨P, hP, hzero, _, hfixed⟩ := ih hit
      let y := P *ᵥ x
      obtain ⟨c, s, hcs, hpos, hkill⟩ := exists_annihilating_coordinateRotation (y i) (y j)
      let R := realCoordinateRotation i j c s
      refine ⟨R * P, (realCoordinateRotationMonoid ι).mul_mem
        (realCoordinateRotation_mem hij hcs) hP, ?_, ?_, ?_⟩
      · intro k hk
        rw [← Matrix.mulVec_mulVec, realCoordinateRotation_mulVec hij]
        rcases Finset.mem_insert.mp hk with rfl | hk
        · simpa only [if_neg hij.symm, if_pos rfl] using hkill
        · have hki : k ≠ i := fun he => hit (he ▸ hk)
          have hkj : k ≠ j := fun he => hj (he ▸ hk)
          simp only [if_neg hki, if_neg hkj]
          exact hzero k hk
      · intro _
        rw [← Matrix.mulVec_mulVec, realCoordinateRotation_mulVec hij, if_pos rfl]
        exact hpos
      · intro l hl k
        have hli : l ≠ i := fun h => hl (Finset.mem_insert.mpr (Or.inl h))
        have hlj : l ≠ j := fun h => hl (Finset.mem_insert.mpr (Or.inr
          (Finset.mem_insert.mpr (Or.inl h))))
        have hlt : l ∉ t := fun h => hl (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))
        rw [matrix_mul_apply_of_basis_column R P k l (hfixed l (by simp [hli, hlt]))]
        by_cases hki : k = i
        · subst k
          simp [R, realCoordinateRotation, Matrix.one_apply, hli, hli.symm, hlj]
        by_cases hkj : k = j
        · subst k
          simp [R, realCoordinateRotation, Matrix.one_apply, hki, hli, hlj, hlj.symm]
        simp [R, realCoordinateRotation, Matrix.one_apply, hki, hkj]

private theorem realCoordinateRotationMonoid_of_fixed_columns
    {ι : Type*} [Fintype ι] [DecidableEq ι] (t : Finset ι) (R : Matrix ι ι ℝ)
    (hR : Rᵀ * R = 1) (hdet : R.det = 1)
    (hfixed : ∀ j ∉ t, ∀ k, R k j = (1 : Matrix ι ι ℝ) k j) :
    R ∈ realCoordinateRotationMonoid ι := by
  classical
  induction t using Finset.induction_on generalizing R with
  | empty =>
      have he : R = 1 := by
        ext k j
        exact hfixed j (by simp) k
      rw [he]
      exact (realCoordinateRotationMonoid ι).one_mem
  | @insert i t hit ih =>
      obtain ⟨P, hP, hzero, hpos, hPfixed⟩ := clear_coordinates (fun k => R k i) i t hit
      obtain ⟨hPinv, hPorth, hPdet⟩ := coordinateRotationMonoid_properties hP
      let T := P * R
      have hTorth : Tᵀ * T = 1 := by
        change (P * R)ᵀ * (P * R) = 1
        rw [Matrix.transpose_mul]
        calc
          (Rᵀ * Pᵀ) * (P * R) = Rᵀ * (Pᵀ * P) * R := by simp only [Matrix.mul_assoc]
          _ = 1 := by rw [hPorth, Matrix.mul_one, hR]
      have hTdet : T.det = 1 := by
        change (P * R).det = 1
        rw [Matrix.det_mul, hPdet, hdet, one_mul]
      have hTfixed (j : ι) (hj : j ∉ insert i t) (k : ι) :
          T k j = (1 : Matrix ι ι ℝ) k j :=
        (matrix_mul_apply_of_basis_column P R k j (hfixed j hj)).trans (hPfixed j hj k)
      have hcol (k : ι) (hki : k ≠ i) : T k i = 0 := by
        by_cases hkt : k ∈ t
        · exact hzero k hkt
        · have hk : k ∉ insert i t := by simp [hki, hkt]
          calc
            T k i = (Tᵀ * T) i k :=
              (matrix_mul_apply_of_basis_column Tᵀ T i k (hTfixed k hk)).symm
            _ = 0 := by rw [hTorth, Matrix.one_apply_ne hki.symm]
      have hpivot : T i i = 1 := by
        by_cases ht : t.Nonempty
        · have hentry := congrArg (fun A : Matrix ι ι ℝ => A i i) hTorth
          change (∑ k, T k i * T k i) = (1 : Matrix ι ι ℝ) i i at hentry
          rw [Finset.sum_eq_single i] at hentry
          · have hsq : (T i i) ^ 2 = 1 ^ 2 := by
              simpa only [pow_two, Matrix.one_apply_eq, one_mul] using hentry
            exact (sq_eq_sq₀ (hpos ht) zero_le_one).mp hsq
          · intro k _ hk
            rw [hcol k hk, zero_mul]
          · simp
        · have hempty := Finset.not_nonempty_iff_eq_empty.mp ht
          have hfix (j : ι) (hj : j ≠ i) := hTfixed j (by simp [hempty, hj])
          have hdiag : T = Matrix.diagonal (fun j => T j j) := by
            ext k j
            by_cases hkj : k = j
            · subst k
              rw [Matrix.diagonal_apply_eq]
            rw [Matrix.diagonal_apply_ne _ hkj]
            by_cases hji : j = i
            · subst j
              exact hcol k hkj
            · exact (hfix j hji k).trans (Matrix.one_apply_ne hkj)
          calc
            T i i = ∏ j, T j j := by
              symm
              refine Finset.prod_eq_single i ?_ (by simp)
              intro j _ hj
              exact (hfix j hj j).trans (Matrix.one_apply_eq j)
            _ = T.det := by
              conv_rhs => rw [hdiag, Matrix.det_diagonal]
            _ = 1 := hTdet
      have hTmem : T ∈ realCoordinateRotationMonoid ι := by
        apply ih T hTorth hTdet
        intro j hj k
        by_cases hji : j = i
        · subst j
          by_cases hki : k = i
          · subst k
            exact hpivot.trans (Matrix.one_apply_eq i).symm
          · exact (hcol k hki).trans (Matrix.one_apply_ne hki).symm
        exact hTfixed j (by simp [hji, hj]) k
      have hrecover : Pᵀ * T = R := by
        change Pᵀ * (P * R) = R
        rw [← Matrix.mul_assoc, hPorth, Matrix.one_mul]
      rw [← hrecover]
      exact (realCoordinateRotationMonoid ι).mul_mem hPinv hTmem

/-- Every real orthogonal matrix with determinant one is a product of coordinate rotations. -/
theorem realCoordinateRotationMonoid_of_orthogonal_det
    {ι : Type*} [Fintype ι] [DecidableEq ι] (R : Matrix ι ι ℝ)
    (hR : Rᵀ * R = 1) (hdet : R.det = 1) : R ∈ realCoordinateRotationMonoid ι :=
  realCoordinateRotationMonoid_of_fixed_columns Finset.univ R hR hdet (by simp)

end

end MOC
