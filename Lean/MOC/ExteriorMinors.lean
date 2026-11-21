import MOC.SubsetContraction
import MOC.TwoValues
import Mathlib.Data.List.OfFn
import Mathlib.Tactic.Ring

/-! Coefficients of the exterior column vector are ordinary ordered minors. -/

open BigOperators Matrix

namespace MOC

noncomputable section

/-- A row subset with its cardinality tracked in the type. -/
inductive ExteriorRows : ℕ → ℕ → Type
  | empty : ExteriorRows 0 0
  | skip : ExteriorRows n k → ExteriorRows (n + 1) k
  | take : ExteriorRows n k → ExteriorRows (n + 1) (k + 1)

namespace ExteriorRows

def cube : ExteriorRows n k → SubsetCube n
  | .empty => ()
  | .skip I => .inl I.cube
  | .take I => .inr I.cube

def row : ExteriorRows n k → Fin k → Fin n
  | .empty => Fin.elim0
  | .skip I => fun j => (I.row j).succ
  | .take I => Fin.cases 0 (fun j => (I.row j).succ)

def erase : {n k : ℕ} → ExteriorRows n (k + 1) → Fin (k + 1) → ExteriorRows n k
  | _, _, .skip I, j => .skip (I.erase j)
  | _, 0, .take I, _ => .skip I
  | _, _ + 1, .take I, j => Fin.cases (.skip I) (fun t => .take (I.erase t)) j

theorem erase_row {n k : ℕ} (I : ExteriorRows n (k + 1)) (j : Fin (k + 1)) (i : Fin k) :
    (I.erase j).row i = I.row (j.succAbove i) := by
  induction n generalizing k with
  | zero => cases I
  | succ n ih =>
    cases I with
    | skip I =>
      simp only [erase, row, ih I j i]
    | take I =>
      cases k with
      | zero => exact Fin.elim0 i
      | succ k =>
        refine Fin.cases ?_ (fun j => ?_) j
        · simp [erase, row]
        · refine Fin.cases ?_ (fun i => ?_) i
          · simp [erase, row, Fin.succ_succAbove_zero]
          · simp [erase, row, ih I j i]

end ExteriorRows

private theorem wedge_blocks (x : Fin (n + 1) → ℂ) :
    (subsetContraction (n + 1) x)ᴴ =
      let C := subsetContraction n (fun j => x j.succ)
      fromBlocks Cᴴ 0 (x 0 • 1) (-Cᴴ) := by
  let C := subsetContraction n (fun j => x j.succ)
  change (fromBlocks C (star (x 0) • 1) 0 (-C))ᴴ = fromBlocks Cᴴ 0 (x 0 • 1) (-Cᴴ)
  rw [Matrix.fromBlocks_conjTranspose]
  simp only [Matrix.conjTranspose_zero, Matrix.conjTranspose_smul, Matrix.conjTranspose_one,
    star_star, Matrix.conjTranspose_neg]

private theorem wedge_at_skip (x : Fin (n + 1) → ℂ) (v : SubsetCube (n + 1) → ℂ)
    (I : SubsetCube n) :
    ((subsetContraction (n + 1) x)ᴴ *ᵥ v) (.inl I) =
      ((subsetContraction n (fun j => x j.succ))ᴴ *ᵥ (v ∘ Sum.inl)) I := by
  rw [wedge_blocks, Matrix.fromBlocks_mulVec]
  simp only [Sum.elim_inl,
    Matrix.zero_mulVec, Pi.add_apply, Pi.zero_apply, add_zero]

private theorem wedge_at_take (x : Fin (n + 1) → ℂ) (v : SubsetCube (n + 1) → ℂ)
    (I : SubsetCube n) :
    ((subsetContraction (n + 1) x)ᴴ *ᵥ v) (.inr I) =
      x 0 * v (.inl I) - ((subsetContraction n (fun j => x j.succ))ᴴ *ᵥ (v ∘ Sum.inr)) I := by
  rw [wedge_blocks, Matrix.fromBlocks_mulVec]
  simp only [Sum.elim_inr, Matrix.neg_mulVec,
    Matrix.smul_mulVec_assoc, Matrix.one_mulVec, Pi.add_apply, Pi.neg_apply,
    Pi.smul_apply, smul_eq_mul, Function.comp_apply, sub_eq_add_neg]

private theorem wedge_at_empty (I : ExteriorRows n 0) (x : Fin n → ℂ)
    (v : SubsetCube n → ℂ) : ((subsetContraction n x)ᴴ *ᵥ v) I.cube = 0 := by
  induction n with
  | zero => simp [subsetContraction]
  | succ n ih =>
    cases I with
    | skip I => rw [ExteriorRows.cube, wedge_at_skip, ih]

private theorem wedge_at_step (I : ExteriorRows n (k + 1)) (x : Fin n → ℂ)
    (v : SubsetCube n → ℂ) : ((subsetContraction n x)ᴴ *ᵥ v) I.cube =
      ∑ j : Fin (k + 1), (-1 : ℂ) ^ (j : ℕ) * x (I.row j) * v (I.erase j).cube := by
  induction n generalizing k with
  | zero => cases I
  | succ n ih =>
    cases I with
    | skip I =>
      simp only [ExteriorRows.cube, wedge_at_skip, ih, ExteriorRows.row,
        ExteriorRows.erase, Function.comp_apply]
    | take I =>
      rw [ExteriorRows.cube, wedge_at_take, Fin.sum_univ_succ]
      cases k with
      | zero =>
        rw [wedge_at_empty I]
        simp [ExteriorRows.row, ExteriorRows.erase, ExteriorRows.cube]
      | succ k =>
        rw [ih I, sub_eq_add_neg, ← Finset.sum_neg_distrib]
        simp only [ExteriorRows.row, ExteriorRows.erase, ExteriorRows.cube,
          Fin.cases_zero, Fin.cases_succ, Fin.val_zero, Fin.val_succ, pow_zero,
          pow_succ', one_mul, neg_one_mul, neg_mul, Function.comp_apply, sub_eq_add_neg]

/-- The exterior coefficient indexed by ordered rows is their determinant. -/
theorem exteriorColumnVector_eq_det_of_rows (I : ExteriorRows n k) (x : Fin k → Fin n → ℂ) :
    exteriorColumnVector n (List.ofFn x) I.cube =
      (Matrix.of fun i j : Fin k => x j (I.row i)).det := by
  induction k with
  | zero =>
    have h : exteriorColumnVector n [] I.cube = 1 := by
      induction n with
      | zero => cases I; exact exteriorColumnVector_nil_zero
      | succ n ih =>
        cases I with
        | skip I =>
          simpa only [ExteriorRows.cube, exteriorColumnVector_nil_skip] using ih I Fin.elim0
    simpa [h]
  | succ k ih =>
    rw [List.ofFn_succ, exteriorColumnVector, wedge_at_step, Matrix.det_succ_column_zero]
    apply Finset.sum_congr rfl
    intro j _
    have hm : (Matrix.of fun i l : Fin (k + 1) => x l (I.row i)).submatrix
        j.succAbove Fin.succ = Matrix.of (fun i l => x l.succ ((I.erase j).row i)) := by
      ext i l : 1
      simp [Matrix.submatrix_apply, ExteriorRows.erase_row]
    rw [ih (I.erase j), hm] <;> rfl

private theorem exteriorColumnVector_eq_zero_of_rows (I : ExteriorRows n k)
    (columns : List (Fin n → ℂ)) (h : k ≠ columns.length) :
    exteriorColumnVector n columns I.cube = 0 := by
  induction columns generalizing k with
  | nil =>
    cases k with
    | zero => exact False.elim (h rfl)
    | succ k =>
      induction n generalizing k with
      | zero => cases I
      | succ n ih =>
        cases I with
        | skip I =>
          simpa only [ExteriorRows.cube, exteriorColumnVector_nil_skip]
            using ih k I (Nat.succ_ne_zero _)
        | take I => exact exteriorColumnVector_nil_take I.cube
  | cons x columns ih =>
    rw [exteriorColumnVector]
    cases k with
    | zero => exact wedge_at_empty I x _
    | succ k =>
      rw [wedge_at_step]
      apply Finset.sum_eq_zero
      intro j _
      rw [ih (I.erase j) (fun he => h (congrArg Nat.succ he)), mul_zero]

namespace ExteriorRows

def ofCube : (n : ℕ) → SubsetCube n → Σ k, ExteriorRows n k
  | 0, _ => ⟨0, .empty⟩
  | n + 1, .inl I => ⟨(ofCube n I).1, .skip (ofCube n I).2⟩
  | n + 1, .inr I => ⟨(ofCube n I).1 + 1, .take (ofCube n I).2⟩

@[simp] theorem ofCube_cube (n : ℕ) (I : SubsetCube n) : (ofCube n I).2.cube = I := by
  induction n with
  | zero => cases I; rfl
  | succ n ih => cases I <;> simp [ofCube, cube, ih]

private theorem row_injective (I : ExteriorRows n k) : Function.Injective I.row := by
  induction I with
  | empty => intro i; exact Fin.elim0 i
  | skip I ih => intro i j h; exact ih (Fin.succ_inj.mp h)
  | take I ih =>
    intro i j
    refine Fin.cases ?_ (fun i => ?_) i <;>
      refine Fin.cases ?_ (fun j => ?_) j
    · intro _; rfl
    · intro h; exact (Fin.succ_ne_zero _ h.symm).elim
    · intro h; exact (Fin.succ_ne_zero _ h).elim
    · intro h; exact congrArg Fin.succ (ih (Fin.succ_inj.mp h))

private theorem mem_labels_iff (I : ExteriorRows n k) (i : Fin n) :
    i ∈ subsetCubeLabels n I.cube ↔ ∃ j, I.row j = i := by
  induction I with
  | empty => exact Fin.elim0 i
  | skip I ih =>
    rw [cube, subsetCubeLabels, Finset.mem_map]
    constructor
    · rintro ⟨l, hl, rfl⟩
      obtain ⟨j, rfl⟩ := (ih l).mp hl
      exact ⟨j, rfl⟩
    · rintro ⟨j, rfl⟩
      exact ⟨I.row j, (ih _).mpr ⟨j, rfl⟩, rfl⟩
  | take I ih =>
    rw [cube, subsetCubeLabels, Finset.mem_insert, Finset.mem_map]
    constructor
    · rintro (rfl | ⟨l, hl, rfl⟩)
      · exact ⟨0, rfl⟩
      · obtain ⟨j, rfl⟩ := (ih l).mp hl
        exact ⟨j.succ, rfl⟩
    · rintro ⟨j, rfl⟩
      refine Fin.cases ?_ (fun j => ?_) j
      · exact Or.inl rfl
      · exact Or.inr ⟨I.row j, (ih _).mpr ⟨j, rfl⟩, rfl⟩

def equivLabels (I : ExteriorRows n k) : Fin k ≃ subsetCubeLabels n I.cube :=
  Equiv.ofBijective (fun j => ⟨I.row j, (mem_labels_iff I _).mpr ⟨j, rfl⟩⟩)
    ⟨fun i j h => row_injective I (congrArg Subtype.val h),
      fun i => by
        obtain ⟨j, hj⟩ := (mem_labels_iff I i.val).mp i.property
        exact ⟨j, Subtype.ext hj⟩⟩

@[simp] theorem card_labels (I : ExteriorRows n k) :
    (subsetCubeLabels n I.cube).card = k := by
  simpa using (Fintype.card_congr I.equivLabels).symm

end ExteriorRows

/-- The probability at an exterior coordinate equals its unitary squared minor. -/
theorem normSq_exteriorColumnVector_eq_minor (U : Matrix (Fin n) (Fin n) ℂ)
    (hU : IsUnitary U) {k : ℕ} {J : Finset (Fin n)} (e : Fin k ≃ J) (I : SubsetCube n) :
    Complex.normSq (exteriorColumnVector n (List.ofFn (fun j i => U i (e j).val)) I) =
      subsetMinorSq U (subsetCubeLabels n I) J := by
  have hI := ExteriorRows.ofCube_cube n I
  generalize ExteriorRows.ofCube n I = pair at hI
  cases pair with
  | mk l rows =>
    change rows.cube = I at hI
    subst I
    by_cases hcard : l = k
    · subst l
      rw [exteriorColumnVector_eq_det_of_rows,
        subsetMinorSq_eq_normSq_det_submatrix U hU _ _ rows.equivLabels e] <;> rfl
    · have hJ : J.card = k := by simpa using (Fintype.card_congr e).symm
      have hne : (subsetCubeLabels n rows.cube).card ≠ J.card := by
        simpa only [ExteriorRows.card_labels, hJ] using hcard
      rw [exteriorColumnVector_eq_zero_of_rows rows _ (by simpa using hcard),
        Complex.normSq_zero, subsetMinorSq, dif_neg hne]

private def cubeOfLabels : (n : ℕ) → Finset (Fin n) → SubsetCube n
  | 0, _ => ()
  | n + 1, S =>
    let T := Finset.univ.filter fun i : Fin n => i.succ ∈ S
    if 0 ∈ S then .inr (cubeOfLabels n T) else .inl (cubeOfLabels n T)

private theorem cubeOfLabels_leftInverse (n : ℕ) :
    Function.LeftInverse (cubeOfLabels n) (subsetCubeLabels n) := by
  intro I
  induction n with
  | zero => cases I; rfl
  | succ n ih =>
    have h₀ (J : SubsetCube n) : (0 : Fin (n + 1)) ∉
        (subsetCubeLabels n J).map (Fin.succEmb n) := by
      intro h
      obtain ⟨i, _, hi⟩ := Finset.mem_map.mp h
      exact Fin.succ_ne_zero i hi
    have htail (J : SubsetCube n) : (Finset.univ.filter fun i : Fin n =>
        i.succ ∈ (subsetCubeLabels n J).map (Fin.succEmb n)) = subsetCubeLabels n J := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact Finset.mem_map' (Fin.succEmb n)
    have htail' (J : SubsetCube n) : (Finset.univ.filter fun i : Fin n =>
        i.succ ∈ insert 0 ((subsetCubeLabels n J).map (Fin.succEmb n))) =
          subsetCubeLabels n J := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Fin.succ_ne_zero, false_or]
      exact Finset.mem_map' (Fin.succEmb n)
    cases I with
    | inl J => simp only [cubeOfLabels, subsetCubeLabels, h₀ J, if_false, htail, ih]
    | inr J =>
      simp only [cubeOfLabels, subsetCubeLabels, Finset.mem_insert_self, if_true, htail', ih]

private theorem cubeOfLabels_rightInverse (n : ℕ) :
    Function.RightInverse (cubeOfLabels n) (subsetCubeLabels n) := by
  intro S
  induction n with
  | zero => ext i; exact Fin.elim0 i
  | succ n ih =>
    let T := Finset.univ.filter fun i : Fin n => i.succ ∈ S
    have hmap (i : Fin n) : i.succ ∈ T.map (Fin.succEmb n) ↔ i.succ ∈ S := by
      rw [show i.succ ∈ T.map (Fin.succEmb n) ↔ i ∈ T from Finset.mem_map' (Fin.succEmb n)]
      simp [T]
    have h₀ : (0 : Fin (n + 1)) ∉ T.map (Fin.succEmb n) := by
      intro h
      obtain ⟨i, _, hi⟩ := Finset.mem_map.mp h
      exact Fin.succ_ne_zero i hi
    by_cases h : (0 : Fin (n + 1)) ∈ S
    · change subsetCubeLabels (n + 1) (if 0 ∈ S then .inr (cubeOfLabels n T)
        else .inl (cubeOfLabels n T)) = S
      rw [if_pos h, subsetCubeLabels, ih]
      ext i
      refine Fin.cases ?_ (fun i => ?_) i
      · simp [h]
      · simpa only [Finset.mem_insert, Fin.succ_ne_zero, false_or] using hmap i
    · change subsetCubeLabels (n + 1) (if 0 ∈ S then .inr (cubeOfLabels n T)
        else .inl (cubeOfLabels n T)) = S
      rw [if_neg h, subsetCubeLabels, ih]
      ext i
      refine Fin.cases ?_ (fun i => hmap i) i
      simp [h₀, h]

/-- Exterior coordinates and finite row subsets have the same labels. -/
def subsetCubeEquivLabels (n : ℕ) : SubsetCube n ≃ Finset (Fin n) where
  toFun := subsetCubeLabels n
  invFun := cubeOfLabels n
  left_inv := cubeOfLabels_leftInverse n
  right_inv := cubeOfLabels_rightInverse n

private def Finset.prependEquiv {J : Finset (Fin n)} {j : Fin n} (hj : j ∉ J)
    (e : Fin k ≃ J) : Fin (k + 1) ≃ (insert j J : Finset (Fin n)) :=
  Equiv.ofBijective (Fin.cases ⟨j, Finset.mem_insert_self ..⟩ (fun i =>
    ⟨(e i).val, Finset.mem_insert_of_mem (e i).property⟩)) (by
      constructor
      · intro a b
        refine Fin.cases ?_ (fun a => ?_) a <;>
          refine Fin.cases ?_ (fun b => ?_) b
        · intro _; rfl
        · intro h
          have he : j = (e b).val := congrArg Subtype.val h
          exact False.elim (hj (by simpa only [he] using (e b).property))
        · intro h
          have he : (e a).val = j := congrArg Subtype.val h
          exact False.elim (hj (he ▸ (e a).property))
        · intro h
          have he : (e a).val = (e b).val :=
            congrArg (fun v : (insert j J : Finset (Fin n)) => v.val) h
          exact congrArg Fin.succ (e.injective (Subtype.ext he))
      · intro a
        rcases Finset.mem_insert.mp a.property with h | h
        · exact ⟨0, Subtype.ext h.symm⟩
        · obtain ⟨b, hb⟩ := e.surjective ⟨a.val, h⟩
          have he : (e b).val = a.val := congrArg (fun v : J => v.val) hb
          exact ⟨b.succ, Subtype.ext he⟩)

/-- The squared-minor law for an extra orthogonal unitary column dominates
the preceding law on every upper shadow. -/
theorem subsetMinorSq_shadow_bound (U : Matrix (Fin n) (Fin n) ℂ) (hU : IsUnitary U)
    (J : Finset (Fin n)) (j : Fin n) (hj : j ∉ J) (S : Finset (Finset (Fin n))) :
    ∑ I ∈ S, subsetMinorSq U I J ≤
      ∑ K ∈ Finset.univ.filter (fun K => ∃ I ∈ S, I ⊆ K), subsetMinorSq U K (insert j J) := by
  classical
  let e : Fin J.card ≃ J := Fintype.equivOfCardEq (by simp)
  let e' := Finset.prependEquiv hj e
  let u (i : Fin n) := U i j
  let columns := List.ofFn (fun t i => U i (e t).val)
  have hcols : u :: columns = List.ofFn (fun t i => U i (e' t).val) := by
    rw [List.ofFn_succ] <;> rfl
  have hunit : ∑ i, Complex.normSq (u i) = 1 := by
    have h := congrArg (fun A : Matrix (Fin n) (Fin n) ℂ => A j j) hU.2
    apply Complex.ofReal_injective
    simpa only [Complex.ofReal_sum, Complex.ofReal_one, Matrix.mul_apply, u,
      Matrix.conjTranspose_apply, Matrix.one_apply_eq, Complex.normSq_eq_conj_mul_self] using h
  have horth : ∀ x ∈ columns, (∑ i, star (u i) * x i) = 0 := by
    intro x hx
    obtain ⟨t, rfl⟩ := List.mem_ofFn.mp hx
    have hn : j ≠ (e t).val := fun he => hj (he.symm ▸ (e t).property)
    have h := congrArg (fun A : Matrix (Fin n) (Fin n) ℂ => A j (e t).val) hU.2
    simpa only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply_ne hn, u] using h
  let E := subsetCubeEquivLabels n
  let P := S.map E.symm.toEmbedding
  have h := exteriorColumnVector_shadow_bound n u hunit columns horth P
  simp only [columns, normSq_exteriorColumnVector_eq_minor U hU e] at h
  rw [hcols] at h
  simp only [normSq_exteriorColumnVector_eq_minor U hU e'] at h
  have hleft : (∑ I ∈ P, subsetMinorSq U (subsetCubeLabels n I) J) =
      ∑ I ∈ S, subsetMinorSq U I J := by
    rw [Finset.sum_map]
    apply Finset.sum_congr rfl
    intro I _
    exact congrArg (fun K => subsetMinorSq U K J) (E.apply_symm_apply I)
  have hright :
      (∑ K ∈ Finset.univ.filter (fun K => ∃ I ∈ P, subsetCubeLabels n I ⊆ subsetCubeLabels n K),
          subsetMinorSq U (subsetCubeLabels n K) (insert j J)) =
        ∑ K ∈ Finset.univ.filter (fun K => ∃ I ∈ S, I ⊆ K), subsetMinorSq U K (insert j J) := by
    rw [Finset.sum_filter, Finset.sum_filter]
    apply Fintype.sum_equiv E
    intro K
    have he : (∃ I ∈ P, subsetCubeLabels n I ⊆ subsetCubeLabels n K) ↔
        (∃ I ∈ S, I ⊆ E K) := by
      constructor
      · rintro ⟨I, hI, hsub⟩
        exact ⟨E I, Finset.mem_map_equiv.mp hI, hsub⟩
      · rintro ⟨I, hI, hsub⟩
        exact ⟨E.symm I, Finset.mem_map_equiv.mpr (by simpa using hI),
          by change E (E.symm I) ⊆ E K; simpa using hsub⟩
    exact if_congr he (by rfl) (by rfl)
  rwa [hleft, hright] at h

end

end MOC
