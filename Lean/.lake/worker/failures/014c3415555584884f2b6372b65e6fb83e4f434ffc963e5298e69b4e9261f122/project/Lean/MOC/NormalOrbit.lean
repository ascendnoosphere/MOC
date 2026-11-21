import MOC.Jacobi
import MOC.Normal
import MOC.Singular
import MOC.Small
import MOC.Variational

/-! A normal sum at a determinant support maximum with maximal Frobenius norm
admits a common eigenbasis for the two summands. -/

open BigOperators Matrix

namespace MOC

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Squared Frobenius norm, expressed in the coordinates of the phase move. -/
def frobeniusSq (M : Matrix ι ι ℂ) : ℝ :=
  ∑ i, ∑ j, Complex.normSq (M i j)

private def unitaryConj (W X : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  W * X * Wᴴ

private theorem unitary_star {W : Matrix ι ι ℂ} (hW : IsUnitary W) : IsUnitary Wᴴ := by
  simpa only [IsUnitary, Matrix.conjTranspose_conjTranspose] using And.intro hW.2 hW.1

private theorem unitary_mul {V W : Matrix ι ι ℂ} (hV : IsUnitary V) (hW : IsUnitary W) :
    IsUnitary (V * W) := by
  simpa only [Matrix.conjTranspose_conjTranspose] using relative_unitary Vᴴ W (unitary_star hV) hW

private theorem unitaryConj_comp (V W X : Matrix ι ι ℂ) :
    unitaryConj V (unitaryConj W X) = unitaryConj (V * W) X := by
  simp only [unitaryConj, Matrix.conjTranspose_mul, Matrix.mul_assoc]

private theorem unitaryConj_inverse (W X : Matrix ι ι ℂ) (hW : IsUnitary W) :
    unitaryConj W (unitaryConj Wᴴ X) = X := by
  rw [unitaryConj_comp, hW.1]
  simp [unitaryConj]

private theorem unitaryConj_add (W X Y : Matrix ι ι ℂ) :
    unitaryConj W (X + Y) = unitaryConj W X + unitaryConj W Y := by
  simp only [unitaryConj, Matrix.mul_add, Matrix.add_mul]

private theorem unitaryConj_mul (W X Y : Matrix ι ι ℂ) (hW : IsUnitary W) :
    unitaryConj W X * unitaryConj W Y = unitaryConj W (X * Y) := by
  simp only [unitaryConj, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc Wᴴ W, hW.2, Matrix.one_mul]

private theorem unitaryConj_adjoint (W X : Matrix ι ι ℂ) :
    (unitaryConj W X)ᴴ = unitaryConj W Xᴴ := by
  simp only [unitaryConj, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    Matrix.mul_assoc]

private theorem unitaryConj_normal (W X : Matrix ι ι ℂ) (hW : IsUnitary W)
    (hX : X * Xᴴ = Xᴴ * X) :
    unitaryConj W X * (unitaryConj W X)ᴴ = (unitaryConj W X)ᴴ * unitaryConj W X := by
  rw [unitaryConj_adjoint, unitaryConj_mul _ _ _ hW, unitaryConj_mul _ _ _ hW, hX]

private theorem frobeniusSq_eq_trace (M : Matrix ι ι ℂ) :
    frobeniusSq M = (M * Mᴴ).trace.re := by
  simp only [frobeniusSq, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Complex.re_sum, Complex.star_def, Complex.mul_conj,
    Complex.ofReal_re]

private theorem frobeniusSq_unitaryConj (W X : Matrix ι ι ℂ) (hW : IsUnitary W) :
    frobeniusSq (unitaryConj W X) = frobeniusSq X := by
  rw [frobeniusSq_eq_trace, frobeniusSq_eq_trace, unitaryConj_adjoint,
    unitaryConj_mul _ _ _ hW, unitaryConj, Matrix.trace_mul_cycle, ← Matrix.mul_assoc, hW.2,
    Matrix.one_mul]

private theorem blockDiag'_blockDiagonal_mul {α : Type*} [Fintype α] [DecidableEq α]
    {κ : α → Type*} [∀ x, Fintype (κ x)]
    (W : ∀ x, Matrix (κ x) (κ x) ℂ) (M : Matrix (Sigma κ) (Sigma κ) ℂ) (x : α) :
    Matrix.blockDiag' (Matrix.blockDiagonal' W * M) x = W x * Matrix.blockDiag' M x := by
  ext i j : 1
  simp only [Matrix.blockDiag'_apply, Matrix.mul_apply, ← Finset.univ_sigma_univ, Finset.sum_sigma]
  rw [Fintype.sum_eq_single x]
  · simp only [Matrix.blockDiagonal'_apply_eq]
  · intro y hy
    exact Finset.sum_eq_zero fun k _ => by
      rw [Matrix.blockDiagonal'_apply_ne _ _ _ (Ne.symm hy), zero_mul]

private theorem blockDiag'_mul_blockDiagonal {α : Type*} [Fintype α] [DecidableEq α]
    {κ : α → Type*} [∀ x, Fintype (κ x)]
    (M : Matrix (Sigma κ) (Sigma κ) ℂ) (W : ∀ x, Matrix (κ x) (κ x) ℂ) (x : α) :
    Matrix.blockDiag' (M * Matrix.blockDiagonal' W) x = Matrix.blockDiag' M x * W x := by
  have h := blockDiag'_blockDiagonal_mul (fun y => (W y)ᴴ) Mᴴ x
  rw [← Matrix.blockDiagonal'_conjTranspose] at h
  simpa only [← Matrix.blockDiag'_conjTranspose, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose] using congrArg Matrix.conjTranspose h

/-- With a diagonal sum of normal summands, diagonalize every compression of
the second summand inside an eigenspace of that sum. -/
private theorem exists_unitary_for_eigenvalue_compressions
    (h : ι → ℂ) (B : Matrix ι ι ℂ) (hB : B * Bᴴ = Bᴴ * B)
    (hA : (diagonal h - B) * (diagonal h - B)ᴴ = (diagonal h - B)ᴴ * (diagonal h - B)) :
    ∃ Q : Matrix ι ι ℂ, IsUnitary Q ∧ Commute (diagonal h) Q ∧
      ∀ i j, h i = h j → i ≠ j → (Qᴴ * B * Q) i j = 0 := by
  classical
  let α : Type := Set.range h
  letI : Fintype α := (Set.finite_range h).fintype
  let κ (x : α) := {i : ι // h i = x.val}
  let e : Sigma κ ≃ ι :=
    { toFun := fun k => k.2.val
      invFun := fun i => ⟨⟨h i, ⟨i, rfl⟩⟩, ⟨i, rfl⟩⟩
      left_inv := by
        rintro ⟨⟨z, hz⟩, ⟨i, hi⟩⟩
        change h i = z at hi
        subst z
        rfl
      right_inv := fun _ => rfl }
  let C (x : α) : Matrix (κ x) (κ x) ℂ := B.submatrix Subtype.val Subtype.val
  have hc (x : α) : IsStarNormal (C x) := by
    constructor
    change (C x)ᴴ * C x = C x * (C x)ᴴ
    exact (normal_eigenvalue_submatrix h B hB hA x.val).symm
  choose b W hw hdiag using fun x => exists_unitary_diagonalization (C x) (hc x)
  let P := Matrix.blockDiagonal' W
  have hp : IsUnitary P := by
    constructor
    · simp only [P, Matrix.blockDiagonal'_conjTranspose, ← Matrix.blockDiagonal'_mul,
        ← Matrix.blockDiagonal'_one]
      exact congrArg Matrix.blockDiagonal' (funext fun x => (hw x).1)
    · simp only [P, Matrix.blockDiagonal'_conjTranspose, ← Matrix.blockDiagonal'_mul,
        ← Matrix.blockDiagonal'_one]
      exact congrArg Matrix.blockDiagonal' (funext fun x => (hw x).2)
  let Q := P.submatrix e.symm e.symm
  refine ⟨Q, unitary_reindex e.symm e.symm hp, ?_, ?_⟩
  · have hD : (diagonal h).submatrix e e =
          Matrix.blockDiagonal' (fun x => Matrix.scalar (κ x) x.val) := by
      rw [Matrix.submatrix_diagonal_equiv]
      let d : ∀ x : α, κ x → ℂ := fun x _ => x.val
      change diagonal (h ∘ e) = Matrix.blockDiagonal' (fun x => diagonal (d x))
      rw [Matrix.blockDiagonal'_diagonal d]
      exact congrArg Matrix.diagonal (funext fun x : Sigma κ => x.2.property)
    have hPcomm : Commute ((diagonal h).submatrix e e) P := by
      change (diagonal h).submatrix e e * P = P * (diagonal h).submatrix e e
      rw [hD]
      simp only [P, ← Matrix.blockDiagonal'_mul]
      exact congrArg Matrix.blockDiagonal' (funext fun x =>
        (Matrix.scalar_commute x.val (Commute.all _) (W x)).eq)
    have he := congrArg (fun M : Matrix (Sigma κ) (Sigma κ) ℂ =>
      M.submatrix e.symm e.symm) hPcomm.eq
    have hleft := Matrix.submatrix_mul_equiv ((diagonal h).submatrix e e) P
      e.symm e.symm e.symm
    have hright := Matrix.submatrix_mul_equiv P ((diagonal h).submatrix e e)
      e.symm e.symm e.symm
    change diagonal h * Q = Q * diagonal h
    simpa only [Q, Matrix.submatrix_submatrix, Equiv.self_comp_symm,
      Matrix.submatrix_id_id] using hleft.trans (he.trans hright.symm)
  · intro i j hij hne
    have hblock (x : α) :
        Matrix.blockDiag' (Pᴴ * B.submatrix e e * P) x = diagonal (b x) := by
      dsimp only [P]
      rw [Matrix.blockDiagonal'_conjTranspose, blockDiag'_mul_blockDiagonal,
        blockDiag'_blockDiagonal_mul]
      change (W x)ᴴ * C x * W x = diagonal (b x)
      rw [hdiag x]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (W x)ᴴ (W x)]
      simp only [(hw x).2, Matrix.one_mul, Matrix.mul_one]
    have hq : Qᴴ * B * Q = (Pᴴ * B.submatrix e e * P).submatrix e.symm e.symm := by
      rw [← Matrix.submatrix_mul_equiv _ _ e.symm e.symm e.symm,
        ← Matrix.submatrix_mul_equiv _ _ e.symm e.symm e.symm]
      simp only [Q, Matrix.conjTranspose_submatrix, Matrix.submatrix_submatrix,
        Equiv.self_comp_symm, Matrix.submatrix_id_id]
    let x : α := ⟨h i, ⟨i, rfl⟩⟩
    let i' : κ x := ⟨i, rfl⟩
    let j' : κ x := ⟨j, hij.symm⟩
    have hi : e.symm i = ⟨x, i'⟩ := rfl
    have hj : e.symm j = ⟨x, j'⟩ := e.symm_apply_eq.mpr rfl
    rw [hq, Matrix.submatrix_apply, hi, hj]
    change Matrix.blockDiag' (Pᴴ * B.submatrix e e * P) x i' j' = 0
    rw [hblock]
    exact Matrix.diagonal_apply_ne _ (fun he => hne (congrArg Subtype.val he))

/-- A nonsingular normal sum at a support maximum with the largest squared
Frobenius norm among all ties gives a common unitary eigenbasis. -/
theorem joint_diagonalization_of_normal_support_frobenius_maximum
    (A B : Matrix ι ι ℂ) (η : ℂ)
    (hA : A * Aᴴ = Aᴴ * A) (hB : B * Bᴴ = Bᴴ * B)
    (hC : IsStarNormal (A + B)) (hdet : (A + B).det ≠ 0)
    (hmax : ∀ R : Matrix ι ι ℂ, IsUnitary R →
      (η * (A + R * B * Rᴴ).det).re ≤ (η * (A + B).det).re)
    (htie : ∀ R : Matrix ι ι ℂ, IsUnitary R →
      (η * (A + R * B * Rᴴ).det).re = (η * (A + B).det).re →
      frobeniusSq (A + R * B * Rᴴ) ≤ frobeniusSq (A + B)) :
    ∃ (a b : ι → ℂ) (W : Matrix ι ι ℂ), IsUnitary W ∧
      A = W * diagonal a * Wᴴ ∧ B = W * diagonal b * Wᴴ := by
  obtain ⟨h, V, hV, hdiag⟩ := exists_unitary_diagonalization (A + B) hC
  change A + B = unitaryConj V (diagonal h) at hdiag
  let B₀ := unitaryConj Vᴴ B
  have hA₀ : unitaryConj Vᴴ A = diagonal h - B₀ := by
    apply eq_sub_of_add_eq
    rw [← unitaryConj_add, hdiag]
    simpa only [Matrix.conjTranspose_conjTranspose] using
      unitaryConj_inverse Vᴴ (diagonal h) (unitary_star hV)
  obtain ⟨Q, hQ, hcQ, hcompress⟩ := exists_unitary_for_eigenvalue_compressions h B₀
    (unitaryConj_normal Vᴴ B (unitary_star hV) hB) (hA₀ ▸ unitaryConj_normal Vᴴ A (unitary_star hV) hA)
  have hQh : unitaryConj Q (diagonal h) = diagonal h := by
    rw [unitaryConj, hcQ.symm.eq, Matrix.mul_assoc, hQ.1, Matrix.mul_one]
  let W := V * Q
  let B' := unitaryConj Wᴴ B
  have hW : IsUnitary W := unitary_mul hV hQ
  have hsum : A + B = unitaryConj W (diagonal h) := by
    change A + B = unitaryConj (V * Q) (diagonal h)
    rw [← unitaryConj_comp, hQh]
    exact hdiag
  have hA' : unitaryConj Wᴴ A = diagonal h - B' := by
    apply eq_sub_of_add_eq
    rw [← unitaryConj_add, hsum]
    simpa only [Matrix.conjTranspose_conjTranspose] using
      unitaryConj_inverse Wᴴ (diagonal h) (unitary_star hW)
  have hnormalA := unitaryConj_normal Wᴴ A (unitary_star hW) hA
  rw [hA'] at hnormalA
  have hnormalB := unitaryConj_normal Wᴴ B (unitary_star hW) hB
  have hB' : B' = Qᴴ * B₀ * Q := by
    have he : B' = unitaryConj Qᴴ B₀ := by
      change unitaryConj (V * Q)ᴴ B = unitaryConj Qᴴ (unitaryConj Vᴴ B)
      rw [Matrix.conjTranspose_mul, unitaryConj_comp]
    simpa only [unitaryConj, Matrix.conjTranspose_conjTranspose] using he
  have hnz (i : ι) : h i ≠ 0 := by
    intro hi
    apply hdet
    rw [hsum, unitaryConj, det_unitary_conjugation _ _ hW, Matrix.det_diagonal]
    exact Finset.prod_eq_zero (Finset.mem_univ i) hi
  have horbit (R : Matrix ι ι ℂ) :
      unitaryConj W (diagonal h - B' + R * B' * Rᴴ) = A + (W * R * Wᴴ) * B * (W * R * Wᴴ)ᴴ := by
    change unitaryConj W (diagonal h - B' + unitaryConj R B') =
      A + unitaryConj (W * R * Wᴴ) B
    rw [← hA', unitaryConj_add, unitaryConj_inverse _ _ hW, unitaryConj_comp]
    exact congrArg (A + ·) (unitaryConj_comp (W * R) Wᴴ B)
  have hd (R : Matrix ι ι ℂ) :
      (diagonal h - B' + R * B' * Rᴴ).det = (A + (W * R * Wᴴ) * B * (W * R * Wᴴ)ᴴ).det := by
    rw [← horbit, unitaryConj, det_unitary_conjugation _ _ hW]
  have hf (R : Matrix ι ι ℂ) :
      frobeniusSq (diagonal h - B' + R * B' * Rᴴ) =
        frobeniusSq (A + (W * R * Wᴴ) * B * (W * R * Wᴴ)ᴴ) := by
    rw [← horbit, frobeniusSq_unitaryConj _ _ hW]
  have hd₀ : (A + B).det = (diagonal h).det := by
    rw [hsum, unitaryConj, det_unitary_conjugation _ _ hW]
  have hf₀ : frobeniusSq (A + B) = frobeniusSq (diagonal h) := by
    rw [hsum, frobeniusSq_unitaryConj _ _ hW]
  have hWmul (R : Matrix ι ι ℂ) (hR : IsUnitary R) : IsUnitary (W * R * Wᴴ) :=
    unitary_mul (unitary_mul hW hR) (unitary_star hW)
  have hmax' (R : Matrix ι ι ℂ) (hR : IsUnitary R) :
      (η * (diagonal h - B' + R * B' * Rᴴ).det).re ≤ (η * (diagonal h).det).re := by
    rw [hd, ← hd₀]
    exact hmax _ (hWmul R hR)
  have htie' (R : Matrix ι ι ℂ) (hR : IsUnitary R) :
      (η * (diagonal h - B' + R * B' * Rᴴ).det).re = (η * (diagonal h).det).re →
        frobeniusSq (diagonal h - B' + R * B' * Rᴴ) ≤ frobeniusSq (diagonal h) := by
    rw [hd, hf, ← hd₀, ← hf₀]
    exact htie _ (hWmul R hR)
  have hBd : B' = diagonal fun i => B' i i :=
    diagonal_of_support_frobenius_max h B' η hnz hnormalB hnormalA hmax' htie'
      (by simpa only [hB'] using hcompress)
  refine ⟨fun i => h i - B' i i, fun i => B' i i, W, hW, ?_, ?_⟩
  · change A = unitaryConj W (diagonal fun i => h i - B' i i)
    rw [← Matrix.diagonal_sub, ← hBd, ← hA', unitaryConj_inverse _ _ hW]
  · change B = unitaryConj W (diagonal fun i => B' i i)
    rw [← hBd]
    exact (unitaryConj_inverse W B hW).symm

/-- Choose a unitary support maximizer with the highest squared Frobenius norm
among all support maximizers. -/
theorem exists_support_frobenius_maximizer (a b : ι → ℂ) (η : ℂ) :
    ∃ U : Matrix ι ι ℂ, IsUnitary U ∧
      (∀ V : Matrix ι ι ℂ, IsUnitary V →
        (η * determinantValue a b V).re ≤ (η * determinantValue a b U).re) ∧
      ∀ V : Matrix ι ι ℂ, IsUnitary V →
        (η * determinantValue a b V).re = (η * determinantValue a b U).re →
        frobeniusSq (diagonal a + V * diagonal b * Vᴴ) ≤ frobeniusSq (diagonal a + U * diagonal b * Uᴴ) := by
  obtain ⟨W, hW, hmax⟩ := exists_support_maximizer a b η
  let f (V : Matrix ι ι ℂ) := (η * determinantValue a b V).re
  let F (V : Matrix ι ι ℂ) := frobeniusSq (diagonal a + V * diagonal b * Vᴴ)
  let K : Set (Matrix ι ι ℂ) := {V | IsUnitary V} ∩ {V | f V = f W}
  have hc : Continuous f := by unfold f determinantValue; fun_prop
  have hK : IsCompact K :=
    isCompact_setOf_isUnitary.inter_right (isClosed_eq hc continuous_const)
  have hF : Continuous F := by
    unfold F frobeniusSq
    exact continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ =>
      Complex.continuous_normSq.comp (by fun_prop)
  obtain ⟨U, hU, hFmax⟩ := hK.exists_isMaxOn ⟨W, hW, rfl⟩ hF.continuousOn
  refine ⟨U, hU.1, ?_, ?_⟩
  · intro V hV
    change f V ≤ f U
    rw [hU.2]
    exact hmax V hV
  · intro V hV he
    exact hFmax ⟨hV, he.trans hU.2⟩

private theorem diagonal_mul_adjoint_comm (a : ι → ℂ) :
    diagonal a * (diagonal a)ᴴ = (diagonal a)ᴴ * diagonal a := by
  simp only [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
  exact congrArg Matrix.diagonal (funext fun i => mul_comm (a i) (star a i))

/-- A support and Frobenius maximizer with normal sum satisfies the determinant
hull inclusion. A singular maximum is covered by the singular-sum theorem. -/
theorem holds_of_normal_support_frobenius_maximum (a b : ι → ℂ)
    {U : Matrix ι ι ℂ} (hU : IsUnitary U) (η : ℂ)
    (hC : IsStarNormal (diagonal a + U * diagonal b * Uᴴ))
    (hmax : ∀ V : Matrix ι ι ℂ, IsUnitary V →
      (η * determinantValue a b V).re ≤ (η * determinantValue a b U).re)
    (htie : ∀ V : Matrix ι ι ℂ, IsUnitary V →
      (η * determinantValue a b V).re = (η * determinantValue a b U).re →
      frobeniusSq (diagonal a + V * diagonal b * Vᴴ) ≤
        frobeniusSq (diagonal a + U * diagonal b * Uᴴ)) :
    Holds a b U := by
  by_cases hdet : determinantValue a b U = 0
  · exact holds_of_singular a b hU hdet
  let A := diagonal a
  let B := U * diagonal b * Uᴴ
  have hmax' (R : Matrix ι ι ℂ) (hR : IsUnitary R) :
      (η * (A + R * B * Rᴴ).det).re ≤ (η * (A + B).det).re := by
    simpa only [determinantValue, A, B, Matrix.conjTranspose_mul, Matrix.mul_assoc] using
      hmax (R * U) (unitary_mul hR hU)
  have htie' (R : Matrix ι ι ℂ) (hR : IsUnitary R) :
      (η * (A + R * B * Rᴴ).det).re = (η * (A + B).det).re →
      frobeniusSq (A + R * B * Rᴴ) ≤ frobeniusSq (A + B) := by
    simpa only [determinantValue, A, B, Matrix.conjTranspose_mul, Matrix.mul_assoc] using
      htie (R * U) (unitary_mul hR hU)
  obtain ⟨x, y, W, hW, hx, hy⟩ := joint_diagonalization_of_normal_support_frobenius_maximum
    A B η (diagonal_mul_adjoint_comm a)
    (unitaryConj_normal U (diagonal b) hU (diagonal_mul_adjoint_comm b)) hC hdet hmax' htie'
  exact holds_of_joint_unitary_diagonalization a b x y hU hW hx hy

end

end MOC
