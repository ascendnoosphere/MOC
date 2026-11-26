import MOC.Normal
import MOC.StrongSupport
import MOC.Variational
import Mathlib.Analysis.Complex.Circle

/-! Determinant superlevels on the spectral orbit and its diagonal-torus fixed points. -/

open Matrix

namespace MOC

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The matrix realization of the orbit of a diagonal normal matrix. -/
def spectralFlagOrbit (b : ι → ℂ) : Set (Matrix ι ι ℂ) :=
  {X | ∃ U : Matrix ι ι ℂ, IsUnitary U ∧ U * diagonal b * Uᴴ = X}

theorem isCompact_spectralFlagOrbit (b : ι → ℂ) : IsCompact (spectralFlagOrbit b) := by
  change IsCompact ((fun U : Matrix ι ι ℂ => U * diagonal b * Uᴴ) '' {U | IsUnitary U})
  exact isCompact_setOf_isUnitary.image (by fun_prop)

/-- Diagonal unitary associated with a point of the coordinate torus. -/
def coordinateTorusDiagonal (t : ι → Circle) : Matrix ι ι ℂ :=
  diagonal (fun i => (t i : ℂ))

private theorem circle_mul_star (z : Circle) : (z : ℂ) * star (z : ℂ) = 1 := by
  rw [Complex.star_def, Complex.mul_conj, Circle.normSq_coe, Complex.ofReal_one]

theorem coordinateTorusDiagonal_unitary (t : ι → Circle) :
    IsUnitary (coordinateTorusDiagonal t) := by
  have h : coordinateTorusDiagonal t * (coordinateTorusDiagonal t)ᴴ = 1 := by
    rw [coordinateTorusDiagonal, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal,
      ← Matrix.diagonal_one]
    exact congrArg diagonal (funext fun i => circle_mul_star (t i))
  exact ⟨h, Matrix.mul_eq_one_comm.mp h⟩

/-- Conjugation by the diagonal unitary of the torus point. -/
def coordinateTorusConj (t : ι → Circle) (X : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  coordinateTorusDiagonal t * X * (coordinateTorusDiagonal t)ᴴ

theorem coordinateTorusConj_entry (t : ι → Circle) (X : Matrix ι ι ℂ) (i j : ι) :
    coordinateTorusConj t X i j = (t i : ℂ) * X i j * star (t j : ℂ) := by
  rw [coordinateTorusConj, coordinateTorusDiagonal, Matrix.diagonal_conjTranspose,
    Matrix.mul_diagonal, Matrix.diagonal_mul] <;> rfl

@[simp] theorem coordinateTorusConj_one (X : Matrix ι ι ℂ) :
    coordinateTorusConj (1 : ι → Circle) X = X := by
  ext i j : 1
  simp only [coordinateTorusConj_entry, Pi.one_apply, Circle.coe_one, one_mul, star_one, mul_one]

theorem coordinateTorusConj_mul (s t : ι → Circle) (X : Matrix ι ι ℂ) :
    coordinateTorusConj (s * t) X = coordinateTorusConj s (coordinateTorusConj t X) := by
  ext i j : 1
  simp only [coordinateTorusConj_entry, Pi.mul_apply, Circle.coe_mul, StarMul.star_mul]
  ring

/-- The ambient matrix representation is complex linear at each torus point. -/
def coordinateTorusConjLinear (t : ι → Circle) : Matrix ι ι ℂ →ₗ[ℂ] Matrix ι ι ℂ where
  toFun := coordinateTorusConj t
  map_add' X Y := by
    simp only [coordinateTorusConj, Matrix.mul_add, Matrix.add_mul]
  map_smul' c X := by
    change coordinateTorusConj t (c • X) = c • coordinateTorusConj t X
    simp only [coordinateTorusConj, Matrix.mul_smul, Matrix.smul_mul]

theorem continuous_coordinateTorusConj :
    Continuous (fun p : (ι → Circle) × Matrix ι ι ℂ => coordinateTorusConj p.1 p.2) := by
  have hc (i : ι) : Continuous (fun p : (ι → Circle) × Matrix ι ι ℂ => (p.1 i : ℂ)) :=
    continuous_subtype_val.comp ((continuous_apply i).comp continuous_fst)
  apply continuous_matrix
  intro i j
  simp only [coordinateTorusConj_entry]
  exact ((hc i).mul (continuous_snd.matrix_elem i j)).mul (hc j).star

theorem coordinateTorusConj_mem_spectralFlagOrbit {b : ι → ℂ} {X : Matrix ι ι ℂ}
    (hX : X ∈ spectralFlagOrbit b) (t : ι → Circle) :
    coordinateTorusConj t X ∈ spectralFlagOrbit b := by
  obtain ⟨U, hU, rfl⟩ := hX
  let D := coordinateTorusDiagonal t
  have hD := coordinateTorusDiagonal_unitary t
  have hDstar : IsUnitary Dᴴ := by
    simpa only [D, IsUnitary, Matrix.conjTranspose_conjTranspose] using And.symm hD
  have hmul : IsUnitary (D * U) := by
    simpa only [Matrix.conjTranspose_conjTranspose] using relative_unitary Dᴴ U hDstar hU
  refine ⟨D * U, hmul, ?_⟩
  simp only [coordinateTorusConj, D, Matrix.conjTranspose_mul, Matrix.mul_assoc]

instance spectralFlagOrbitTorusAction (b : ι → ℂ) : MulAction (ι → Circle) (spectralFlagOrbit b) where
  smul t X := ⟨coordinateTorusConj t X.val,
    coordinateTorusConj_mem_spectralFlagOrbit X.property t⟩
  one_smul X := Subtype.ext (coordinateTorusConj_one X.val)
  mul_smul s t X := Subtype.ext (coordinateTorusConj_mul s t X.val)

instance spectralFlagOrbitContinuousSMul (b : ι → ℂ) :
    ContinuousSMul (ι → Circle) (spectralFlagOrbit b) where
  continuous_smul := (continuous_coordinateTorusConj.comp
    (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).subtype_mk _

@[simp] theorem coordinateTorusConj_diagonal (t : ι → Circle) (d : ι → ℂ) :
    coordinateTorusConj t (diagonal d) = diagonal d := by
  ext i j : 1
  rw [coordinateTorusConj_entry]
  by_cases hij : i = j
  · subst j
    rw [Matrix.diagonal_apply_eq, mul_right_comm, circle_mul_star, one_mul]
  · rw [Matrix.diagonal_apply_ne _ hij, mul_zero, zero_mul]

/-- A circle rotation of one coordinate, fixing all remaining coordinates. -/
def coordinateCircle (i : ι) (z : Circle) : ι → Circle :=
  Function.update 1 i z

theorem coordinateTorusConj_coordinateCircle_entry (X : Matrix ι ι ℂ)
    {i j : ι} (hij : i ≠ j) (z : Circle) :
    coordinateTorusConj (coordinateCircle i z) X i j = (z : ℂ) * X i j := by
  rw [coordinateTorusConj_entry]
  simp only [coordinateCircle, Function.update_self, Function.update_of_ne hij.symm,
    Pi.one_apply, Circle.coe_one, star_one, mul_one]

/-- A matrix is fixed by all coordinate phases exactly when it is diagonal. -/
theorem fixed_coordinateTorusConj_iff (X : Matrix ι ι ℂ) :
    (∀ t : ι → Circle, coordinateTorusConj t X = X) ↔ ∃ d : ι → ℂ, X = diagonal d := by
  constructor
  · intro h
    let z : Circle := ⟨-1, Metric.mem_sphere_zero_iff_norm.mpr (by simp)⟩
    refine ⟨X.diag, ?_⟩
    ext i j : 1
    by_cases hij : i = j
    · subst j
      rw [Matrix.diagonal_apply_eq, Matrix.diag_apply]
    · have he := congrArg (fun M : Matrix ι ι ℂ => M i j) (h (coordinateCircle i z))
      change coordinateTorusConj (coordinateCircle i z) X i j = X i j at he
      rw [coordinateTorusConj_coordinateCircle_entry X hij] at he
      change (-1 : ℂ) * X i j = X i j at he
      have hz : (2 : ℂ) * X i j = 0 := by linear_combination -he
      rw [Matrix.diagonal_apply_ne _ hij]
      exact (mul_eq_zero.mp hz).resolve_left (by norm_num)
  · rintro ⟨d, rfl⟩ t
    exact coordinateTorusConj_diagonal t d

/-- The fixed matrices on the spectral orbit are precisely the permuted diagonals.
Repeated spectral labels may give the same diagonal matrix. -/
theorem spectralFlagOrbit_fixed_iff (b : ι → ℂ) (X : Matrix ι ι ℂ) :
    X ∈ spectralFlagOrbit b ∧ (∀ t : ι → Circle, coordinateTorusConj t X = X) ↔
      ∃ p : Equiv.Perm ι, X = diagonal (b ∘ p) := by
  constructor
  · rintro ⟨⟨U, hU, hUX⟩, hfix⟩
    obtain ⟨d, rfl⟩ := (fixed_coordinateTorusConj_iff X).mp hfix
    have hb := roots_unitary_diagonalization b hU
    rw [hUX] at hb
    have hd := roots_unitary_diagonalization d isUnitary_one
    simp only [Matrix.one_mul, Matrix.conjTranspose_one, Matrix.mul_one] at hd
    obtain ⟨p, hp⟩ := exists_perm_of_equal_multisets d b (hd.symm.trans hb)
    exact ⟨p, congrArg diagonal hp⟩
  · rintro ⟨p, rfl⟩
    refine ⟨⟨p.permMatrix ℂ, isUnitary_permMatrix p, ?_⟩, ?_⟩
    · rw [permMatrix_conjugates, Matrix.submatrix_diagonal_equiv]
    · exact (fixed_coordinateTorusConj_iff _).mpr ⟨_, rfl⟩

/-- Real support of the determinant at one matrix on the orbit. -/
def flagDeterminantScore (a : ι → ℂ) (η : ℂ) (X : Matrix ι ι ℂ) : ℝ :=
  (η * (diagonal a + X).det).re

theorem continuous_flagDeterminantScore (a : ι → ℂ) (η : ℂ) :
    Continuous (flagDeterminantScore a η) := by
  unfold flagDeterminantScore
  fun_prop

theorem flagDeterminantScore_torusInvariant (a : ι → ℂ) (η : ℂ) (t : ι → Circle)
    (X : Matrix ι ι ℂ) :
    flagDeterminantScore a η (coordinateTorusConj t X) = flagDeterminantScore a η X := by
  have hsum : coordinateTorusConj t (diagonal a + X) =
      diagonal a + coordinateTorusConj t X := by
    conv_rhs => rw [← coordinateTorusConj_diagonal t a]
    simp only [coordinateTorusConj, Matrix.mul_add, Matrix.add_mul]
  rw [flagDeterminantScore, ← hsum, coordinateTorusConj,
    det_unitary_conjugation _ _ (coordinateTorusDiagonal_unitary t)] <;> rfl

theorem flagDeterminantScore_permutation (a b : ι → ℂ) (η : ℂ) (p : Equiv.Perm ι) :
    flagDeterminantScore a η (diagonal (b ∘ p)) = (η * matchingProduct a b p.symm).re := by
  rw [flagDeterminantScore, ← Matrix.diagonal_add, Matrix.det_diagonal,
    matchingProduct_inverse] <;> rfl

/-- The strict support superlevel, as a subset of the ambient matrix space. -/
def flagDeterminantSuperlevel (a b : ι → ℂ) (η : ℂ) (r : ℝ) : Set (Matrix ι ι ℂ) :=
  spectralFlagOrbit b ∩ {X | r < flagDeterminantScore a η X}

theorem flagDeterminantSuperlevel_relativelyOpen (a b : ι → ℂ) (η : ℂ) (r : ℝ) :
    IsOpen {X : spectralFlagOrbit b | X.val ∈ flagDeterminantSuperlevel a b η r} := by
  have he : {X : spectralFlagOrbit b | X.val ∈ flagDeterminantSuperlevel a b η r} =
      {X : spectralFlagOrbit b | r < flagDeterminantScore a η X.val} := by
    ext X
    exact ⟨fun h => h.2, fun h => ⟨X.property, h⟩⟩
  rw [he]
  exact isOpen_lt continuous_const ((continuous_flagDeterminantScore a η).comp continuous_subtype_val)

theorem coordinateTorusConj_mem_flagDeterminantSuperlevel {a b : ι → ℂ} {η : ℂ} {r : ℝ}
    {X : Matrix ι ι ℂ} (hX : X ∈ flagDeterminantSuperlevel a b η r) (t : ι → Circle) :
    coordinateTorusConj t X ∈ flagDeterminantSuperlevel a b η r :=
  ⟨coordinateTorusConj_mem_spectralFlagOrbit hX.1 t,
    (flagDeterminantScore_torusInvariant a η t X).symm ▸ hX.2⟩

/-- For a simple spectrum, the fixed points above the threshold are in
bijection with the permutation labels whose matching products exceed it. -/
def flagSuperlevelFixedEquiv (a b : ι → ℂ) (η : ℂ) (r : ℝ) (hb : Function.Injective b) :
    {p : Equiv.Perm ι // r < (η * matchingProduct a b p).re} ≃
      {X : Matrix ι ι ℂ // X ∈ flagDeterminantSuperlevel a b η r ∧
        ∀ t : ι → Circle, coordinateTorusConj t X = X} := by
  let f (p : {p : Equiv.Perm ι // r < (η * matchingProduct a b p).re}) :
      {X : Matrix ι ι ℂ // X ∈ flagDeterminantSuperlevel a b η r ∧
        ∀ t : ι → Circle, coordinateTorusConj t X = X} := by
    have h := (spectralFlagOrbit_fixed_iff b (diagonal (b ∘ p.val.symm))).mpr ⟨_, rfl⟩
    refine ⟨_, ⟨h.1, ?_⟩, h.2⟩
    simpa only [flagDeterminantScore_permutation, Equiv.symm_symm] using p.property
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · intro p q hpq
    apply Subtype.ext
    suffices h : p.val.symm = q.val.symm by simpa only [Equiv.symm_symm] using congrArg Equiv.symm h
    ext i : 1
    apply hb
    have he := congrArg (fun X => (X.val : Matrix ι ι ℂ) i i) hpq
    simpa only [f, Matrix.diagonal_apply_eq, Function.comp_apply] using he
  · intro X
    obtain ⟨p, hp⟩ := (spectralFlagOrbit_fixed_iff b X.val).mp ⟨X.property.1.1, X.property.2⟩
    have hlt := X.property.1.2
    change r < flagDeterminantScore a η X.val at hlt
    rw [hp, flagDeterminantScore_permutation] at hlt
    refine ⟨⟨p.symm, hlt⟩, Subtype.ext ?_⟩
    simpa only [f, Equiv.symm_symm] using hp.symm

/-- A strict determinant superlevel contains a fixed point whenever it is
nonempty exactly when the conjecture holds in this order. -/
theorem conjecture_iff_flagSuperlevel_fixed : Conjecture ι ↔
    ∀ (a b : ι → ℂ) (η : ℂ) (r : ℝ), (flagDeterminantSuperlevel a b η r).Nonempty →
      ∃ X ∈ flagDeterminantSuperlevel a b η r,
        ∀ t : ι → Circle, coordinateTorusConj t X = X := by
  constructor
  · rintro h a b η r ⟨X, ⟨U, hU, rfl⟩, hX⟩
    obtain ⟨p, hp⟩ := (holds_iff_directional a b U).mp (h a b U hU) η
    have hfix := (spectralFlagOrbit_fixed_iff b (diagonal (b ∘ p.symm))).mpr ⟨_, rfl⟩
    refine ⟨_, ⟨hfix.1, ?_⟩, hfix.2⟩
    change r < flagDeterminantScore a η (diagonal (b ∘ p.symm))
    rw [flagDeterminantScore_permutation, Equiv.symm_symm]
    exact hX.trans_le hp
  · intro h a b U hU
    apply (holds_iff_directional a b U).mpr
    intro η
    by_contra! hbad
    obtain ⟨p, _, hmax⟩ := Finset.exists_max_image Finset.univ
      (fun p : Equiv.Perm ι => (η * matchingProduct a b p).re) Finset.univ_nonempty
    let r := (η * matchingProduct a b p).re
    have hnonempty : (flagDeterminantSuperlevel a b η r).Nonempty :=
      ⟨U * diagonal b * Uᴴ, ⟨U, hU, rfl⟩, hbad p⟩
    obtain ⟨X, hX, hfix⟩ := h a b η r hnonempty
    obtain ⟨q, rfl⟩ := (spectralFlagOrbit_fixed_iff b X).mp ⟨hX.1, hfix⟩
    have hlt := hX.2
    change r < flagDeterminantScore a η (diagonal (b ∘ q)) at hlt
    rw [flagDeterminantScore_permutation] at hlt
    exact (not_lt_of_ge (hmax q.symm (Finset.mem_univ _))) hlt

end

end MOC
