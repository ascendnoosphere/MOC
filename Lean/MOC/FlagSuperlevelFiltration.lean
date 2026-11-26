import MOC.FlagSuperlevelCircle
import Mathlib.Topology.LocallyClosed

/-! The closed zero-coordinate filtration of the determinant superlevel. -/

open BigOperators Matrix Set

namespace MOC

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ}

/-- The first `k` off-diagonal coordinates in a fixed enumeration vanish. -/
def offDiagonalZeroFiltration
    (e : Fin m ≃ {p : ι × ι // p.1 ≠ p.2}) (k : ℕ) : Set (Matrix ι ι ℂ) :=
  {X | ∀ p : Fin m, p.val < k → X (e p).val.1 (e p).val.2 = 0}

theorem isClosed_offDiagonalZeroFiltration
    (e : Fin m ≃ {p : ι × ι // p.1 ≠ p.2}) (k : ℕ) :
    IsClosed (offDiagonalZeroFiltration e k) := by
  have he : offDiagonalZeroFiltration e k =
      ⋂ (p : Fin m) (_ : p.val < k), {X : Matrix ι ι ℂ | X (e p).val.1 (e p).val.2 = 0} := by
    ext X
    simp only [offDiagonalZeroFiltration, Set.mem_setOf_eq, Set.mem_iInter]
  rw [he]
  exact isClosed_iInter fun p => isClosed_iInter fun _ =>
    isClosed_eq (continuous_id.matrix_elem (e p).val.1 (e p).val.2) continuous_const

theorem offDiagonalZeroFiltration_antitone
    (e : Fin m ≃ {p : ι × ι // p.1 ≠ p.2}) : Antitone (offDiagonalZeroFiltration e) := by
  intro k l hkl X hx p hp
  exact hx p (hp.trans_le hkl)

theorem coordinateTorusConj_mem_offDiagonalZeroFiltration
    (e : Fin m ≃ {p : ι × ι // p.1 ≠ p.2}) (k : ℕ) (t : ι → Circle)
    {X : Matrix ι ι ℂ} (hX : X ∈ offDiagonalZeroFiltration e k) :
    coordinateTorusConj t X ∈ offDiagonalZeroFiltration e k := by
  intro p hp
  rw [coordinateTorusConj_entry, hX p hp, mul_zero, zero_mul]

@[simp] theorem offDiagonalZeroFiltration_zero (e : Fin m ≃ {p : ι × ι // p.1 ≠ p.2}) :
    offDiagonalZeroFiltration e 0 = univ := by
  ext X
  simp [offDiagonalZeroFiltration]

theorem offDiagonalZeroFiltration_succ
    (e : Fin m ≃ {p : ι × ι // p.1 ≠ p.2}) (j : Fin m) :
    offDiagonalZeroFiltration e (j.val + 1) =
      offDiagonalZeroFiltration e j.val ∩ {X | X (e j).val.1 (e j).val.2 = 0} := by
  ext X
  constructor
  · intro hx
    exact ⟨offDiagonalZeroFiltration_antitone e (Nat.le_succ _) hx, hx j (Nat.lt_succ_self _)⟩
  · rintro ⟨hx, hz⟩ p hp
    by_cases hlt : p.val < j.val
    · exact hx p hlt
    · have he : p = j := Fin.ext (by omega)
      subst p
      exact hz

/-- The last closed layer consists of the diagonal-torus fixed matrices. -/
theorem offDiagonalZeroFiltration_last
    (e : Fin m ≃ {p : ι × ι // p.1 ≠ p.2}) :
    offDiagonalZeroFiltration e m = {X | ∀ t : ι → Circle, coordinateTorusConj t X = X} := by
  ext X
  constructor
  · intro h
    apply (fixed_coordinateTorusConj_iff X).mpr
    refine ⟨X.diag, ?_⟩
    ext i j : 1
    by_cases hij : i = j
    · subst j
      rw [Matrix.diagonal_apply_eq, Matrix.diag_apply]
    · let p := e.symm ⟨(i, j), hij⟩
      have hzero := h p p.isLt
      have hp : e p = ⟨(i, j), hij⟩ := e.apply_symm_apply _
      rw [hp] at hzero
      rw [Matrix.diagonal_apply_ne _ hij]
      exact hzero
  · intro h
    obtain ⟨d, hd⟩ := (fixed_coordinateTorusConj_iff X).mp h
    intro p _
    rw [hd, Matrix.diagonal_apply_ne _ (e p).property]

/-- The stratum with its first nonzero off-diagonal entry at position `j`. -/
def flagSuperlevelFirstNonzero (a b : ι → ℂ) (η : ℂ) (r : ℝ)
    (e : Fin m ≃ {p : ι × ι // p.1 ≠ p.2}) (j : Fin m) : Set (Matrix ι ι ℂ) :=
  flagSuperlevelCircleStratum a b η r ((fun p => (e p).val) '' Set.Iio j)
    (e j).val.1 (e j).val.2

theorem flagSuperlevelFirstNonzero_eq_diff (a b : ι → ℂ) (η : ℂ) (r : ℝ)
    (e : Fin m ≃ {p : ι × ι // p.1 ≠ p.2}) (j : Fin m) :
    flagSuperlevelFirstNonzero a b η r e j = flagDeterminantSuperlevel a b η r ∩
      (offDiagonalZeroFiltration e j.val \ offDiagonalZeroFiltration e (j.val + 1)) := by
  rw [offDiagonalZeroFiltration_succ]
  ext X
  constructor
  · rintro ⟨hx, hn, hz⟩
    have hz' : X ∈ offDiagonalZeroFiltration e j.val := fun p hp =>
      hz (e p).val ⟨p, hp, rfl⟩
    exact ⟨hx, hz', fun h => hn h.2⟩
  · rintro ⟨hx, hz, hnext⟩
    refine ⟨hx, fun h => hnext ⟨hz, h⟩, ?_⟩
    rintro _ ⟨p, hp, rfl⟩
    exact hz p hp

theorem isLocallyClosed_flagDeterminantSuperlevel (a b : ι → ℂ) (η : ℂ) (r : ℝ) :
    IsLocallyClosed (flagDeterminantSuperlevel a b η r) := by
  refine ⟨{X | r < flagDeterminantScore a η X}, spectralFlagOrbit b,
    isOpen_lt continuous_const (continuous_flagDeterminantScore a η),
    (isCompact_spectralFlagOrbit b).isClosed, ?_⟩
  exact inter_comm _ _

theorem isLocallyClosed_flagSuperlevelFirstNonzero (a b : ι → ℂ) (η : ℂ) (r : ℝ)
    (e : Fin m ≃ {p : ι × ι // p.1 ≠ p.2}) (j : Fin m) :
    IsLocallyClosed (flagSuperlevelFirstNonzero a b η r e j) := by
  rw [flagSuperlevelFirstNonzero_eq_diff]
  apply (isLocallyClosed_flagDeterminantSuperlevel a b η r).inter
  exact ⟨(offDiagonalZeroFiltration e (j.val + 1))ᶜ, offDiagonalZeroFiltration e j.val,
    (isClosed_offDiagonalZeroFiltration e (j.val + 1)).isOpen_compl,
    isClosed_offDiagonalZeroFiltration e j.val, by
      ext X
      exact and_comm⟩

/-- Within the superlevel, a boundary point of a first-nonzero stratum
has its pivot equal to zero as well. -/
theorem flagSuperlevelFirstNonzero_relativeBoundary_subset_next
    (a b : ι → ℂ) (η : ℂ) (r : ℝ)
    (e : Fin m ≃ {p : ι × ι // p.1 ≠ p.2}) (j : Fin m) :
    (closure (flagSuperlevelFirstNonzero a b η r e j) \ flagSuperlevelFirstNonzero a b η r e j) ∩
      flagDeterminantSuperlevel a b η r ⊆ offDiagonalZeroFiltration e (j.val + 1) := by
  rw [flagSuperlevelFirstNonzero_eq_diff]
  have hsub : flagDeterminantSuperlevel a b η r ∩
      (offDiagonalZeroFiltration e j.val \ offDiagonalZeroFiltration e (j.val + 1)) ⊆
      offDiagonalZeroFiltration e j.val := fun _ h => h.2.1
  have hc := closure_minimal hsub (isClosed_offDiagonalZeroFiltration e j.val)
  rintro X ⟨⟨hX, hnot⟩, hsuper⟩
  by_contra hnext
  exact hnot ⟨hsuper, hc hX, hnext⟩

/-- The superlevel is the union of the last closed layer and the finitely
many strata that have a first nonzero off-diagonal entry. -/
theorem flagDeterminantSuperlevel_eq_fixed_union_firstNonzero
    (a b : ι → ℂ) (η : ℂ) (r : ℝ) (e : Fin m ≃ {p : ι × ι // p.1 ≠ p.2}) :
    flagDeterminantSuperlevel a b η r =
      {X | X ∈ flagDeterminantSuperlevel a b η r ∧
        ∀ t : ι → Circle, coordinateTorusConj t X = X} ∪
      ⋃ j : Fin m, flagSuperlevelFirstNonzero a b η r e j := by
  classical
  ext X
  constructor
  · intro hx
    by_cases hlast : X ∈ offDiagonalZeroFiltration e m
    · rw [offDiagonalZeroFiltration_last] at hlast
      exact Or.inl ⟨hx, hlast⟩
    · let J := Finset.univ.filter (fun p : Fin m => X (e p).val.1 (e p).val.2 ≠ 0)
      have hJ : J.Nonempty := by
        by_contra hempty
        apply hlast
        intro p _
        by_contra hne
        exact hempty ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩⟩
      let j := J.min' hJ
      have hj : j ∈ J := Finset.min'_mem J hJ
      refine Or.inr (Set.mem_iUnion.mpr ⟨j, hx, (Finset.mem_filter.mp hj).2, ?_⟩)
      rintro _ ⟨p, hp, rfl⟩
      by_contra hne
      have hmem : p ∈ J := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩
      exact (not_le_of_gt hp) (Finset.min'_le J p hmem)
  · rintro (⟨hx, _⟩ | hs)
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hs
    exact hj.1

/-- Distinct first nonzero positions give disjoint strata. -/
theorem pairwiseDisjoint_flagSuperlevelFirstNonzero
    (a b : ι → ℂ) (η : ℂ) (r : ℝ) (e : Fin m ≃ {p : ι × ι // p.1 ≠ p.2}) :
    Pairwise (fun p q : Fin m =>
      Disjoint (flagSuperlevelFirstNonzero a b η r e p)
        (flagSuperlevelFirstNonzero a b η r e q)) := by
  intro p q hpq
  apply Set.disjoint_left.mpr
  intro X hp hq
  rcases lt_or_gt_of_ne hpq with hlt | hlt
  · exact hp.2.1 (hq.2.2 (e p).val ⟨p, hlt, rfl⟩)
  · exact hq.2.1 (hp.2.2 (e q).val ⟨q, hlt, rfl⟩)

theorem disjoint_fixed_flagSuperlevelFirstNonzero
    (a b : ι → ℂ) (η : ℂ) (r : ℝ) (e : Fin m ≃ {p : ι × ι // p.1 ≠ p.2})
    (j : Fin m) :
    Disjoint {X | X ∈ flagDeterminantSuperlevel a b η r ∧
      ∀ t : ι → Circle, coordinateTorusConj t X = X}
      (flagSuperlevelFirstNonzero a b η r e j) := by
  apply Set.disjoint_left.mpr
  intro X hfix hj
  obtain ⟨d, hd⟩ := (fixed_coordinateTorusConj_iff X).mp hfix.2
  apply hj.2.1
  rw [hd, Matrix.diagonal_apply_ne _ (e j).property]

theorem finite_flagDeterminantSuperlevel_fixed (a b : ι → ℂ) (η : ℂ) (r : ℝ) :
    {X | X ∈ flagDeterminantSuperlevel a b η r ∧
      ∀ t : ι → Circle, coordinateTorusConj t X = X}.Finite := by
  apply (Set.finite_range (fun p : Equiv.Perm ι => diagonal (b ∘ p))).subset
  intro X hX
  obtain ⟨p, hp⟩ := (spectralFlagOrbit_fixed_iff b X).mp ⟨hX.1.1, hX.2⟩
  exact ⟨p, hp.symm⟩

/-- Every nondiagonal stratum is a product of the circle and its positive-entry slice. -/
def flagSuperlevelFirstNonzeroHomeomorph (a b : ι → ℂ) (η : ℂ) (r : ℝ)
    (e : Fin m ≃ {p : ι × ι // p.1 ≠ p.2}) (j : Fin m) :
    let S := flagSuperlevelFirstNonzero a b η r e j
    S ≃ₜ Circle × {X : Matrix ι ι ℂ // X ∈ S ∧
      X (e j).val.1 (e j).val.2 = (‖X (e j).val.1 (e j).val.2‖ : ℂ)} :=
  flagSuperlevelCircleStratumHomeomorph a b η r ((fun p => (e p).val) '' Set.Iio j) (e j).property

/-- Normality and the characteristic polynomial give exact equations for the
spectral orbit, including repeated eigenvalues. -/
theorem mem_spectralFlagOrbit_iff_normal_charpoly (b : ι → ℂ) (X : Matrix ι ι ℂ) :
    X ∈ spectralFlagOrbit b ↔ IsStarNormal X ∧
      X.charpoly = ∏ j, (Polynomial.X - Polynomial.C (b j)) := by
  classical
  constructor
  · rintro ⟨U, hU, rfl⟩
    refine ⟨isStarNormal_unitary_diagonalization b hU, ?_⟩
    let p := (U * diagonal b * Uᴴ).charpoly
    change p = _
    have hroots : p.roots = (Finset.univ : Finset ι).val.map b :=
      roots_unitary_diagonalization b hU
    have hmonic : p.Monic := Matrix.charpoly_monic _
    rw [p.eq_prod_roots_of_monic_of_splits_id hmonic (IsAlgClosed.splits p),
      hroots, Multiset.map_map] <;> rfl
  · rintro ⟨hnormal, hpoly⟩
    have hroots : X.charpoly.roots = (Finset.univ : Finset ι).val.map b := by
      rw [hpoly]
      simpa only [Finset.prod_eq_multiset_prod, Multiset.map_map, Function.comp_apply] using
        Polynomial.roots_multiset_prod_X_sub_C ((Finset.univ : Finset ι).val.map b)
    obtain ⟨c, U, hU, hX⟩ := exists_unitary_diagonalization X hnormal
    rw [hX, roots_unitary_diagonalization c hU] at hroots
    obtain ⟨q, hq⟩ := exists_perm_of_equal_multisets c b hroots
    let P := q.permMatrix ℂ
    have hP : IsUnitary P := isUnitary_permMatrix q
    have hUstar : IsUnitary Uᴴ := by
      simpa only [IsUnitary, Matrix.conjTranspose_conjTranspose] using And.symm hU
    have hUP : IsUnitary (U * P) := by
      simpa only [Matrix.conjTranspose_conjTranspose] using relative_unitary Uᴴ P hUstar hP
    have hconj : P * diagonal b * Pᴴ = diagonal c := by
      rw [P, permMatrix_conjugates, Matrix.submatrix_diagonal_equiv, hq]
    refine ⟨U * P, hUP, ?_⟩
    calc
      _ = U * (P * diagonal b * Pᴴ) * Uᴴ := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = X := by rw [hconj, ← hX]

end

end MOC
