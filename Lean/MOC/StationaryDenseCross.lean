import MOC.FourZeroDiagonal
import MOC.OrderFourIndependent
import MOC.PhaseHessianReduction

open Matrix Finset
namespace MOC

private theorem unique_zero_of_three_nonzero (f : Fin 4 → ℂ)
    (h : 3 ≤ (Finset.univ.filter fun j => f j ≠ 0).card) {j k : Fin 4}
    (hj : f j = 0) (hk : f k = 0) : j = k := by
  classical
  by_contra hn
  have hs : (Finset.univ.filter fun i => f i ≠ 0) ⊆
      ((Finset.univ : Finset (Fin 4)).erase j).erase k := by
    intro i hi
    have hf := (Finset.mem_filter.mp hi).2
    exact Finset.mem_erase.mpr
      ⟨fun he => hf (he.symm ▸ hk), Finset.mem_erase.mpr
        ⟨fun he => hf (he.symm ▸ hj), Finset.mem_univ i⟩⟩
  have hm := Finset.card_le_card hs
  have he : (((Finset.univ : Finset (Fin 4)).erase j).erase k).card = 2 := by
    simp [Finset.card_erase_of_mem, (Ne.symm hn), Fintype.card_fin]
  omega

/-- If all columns have at least three nonzero entries and no row is dense,
the row zeros can be aligned to the diagonal. -/
theorem four_holds_orthogonal_of_no_dense_row
    (a b : Fin 4 → ℂ) (O : Matrix.orthogonalGroup (Fin 4) ℝ)
    (hcol : ∀ j, 3 ≤ (supportColumns (Complex.ofRealHom.mapMatrix O.val)ᴴ {j}).card)
    (hzero : ∀ i, ∃ j, O.val i j = 0) :
    Holds a b (Complex.ofRealHom.mapMatrix O.val) := by
  classical
  choose f hf using hzero
  let V := Complex.ofRealHom.mapMatrix O.val
  have hinj : Function.Injective f := by
    intro i k he
    have hc : 3 ≤ (Finset.univ.filter fun l => Vᴴ (f i) l ≠ 0).card := by
      simpa [supportColumns, V] using hcol (f i)
    apply unique_zero_of_three_nonzero (fun l => Vᴴ (f i) l) hc
    · simp [V, hf i]
    · simp [V, he, hf k]
  let e : Equiv.Perm (Fin 4) :=
    Equiv.ofBijective f ⟨hinj, Finite.surjective_of_injective hinj⟩
  have hOO : O.val * O.valᵀ = 1 := (Matrix.mem_orthogonalGroup_iff _ _).mp O.property
  let O' : Matrix.orthogonalGroup (Fin 4) ℝ :=
    ⟨O.val.submatrix (Equiv.refl _) e, (Matrix.mem_orthogonalGroup_iff _ _).mpr (by
      change O.val.submatrix (Equiv.refl _) e * (O.val.submatrix (Equiv.refl _) e)ᵀ = 1
      rw [Matrix.transpose_submatrix, Matrix.submatrix_mul_equiv,
        hOO, Matrix.submatrix_one_equiv])⟩
  have hh := four_holds_zero_diagonal_orthogonal a (b ∘ e) O' (fun i => hf i)
  exact (holds_reindex_iff (Equiv.refl _) e a b V).mp hh

/-- Every counterexample in the regular stationary orthogonal reduction
has a dense row (and hence admits the three-variable phase gauge). -/
theorem four_exists_dense_row_of_orthogonal_violation
    (a b : Fin 4 → ℂ) (O : Matrix.orthogonalGroup (Fin 4) ℝ)
    (hcol : ∀ j, 3 ≤ (supportColumns (Complex.ofRealHom.mapMatrix O.val)ᴴ {j}).card)
    (hbad : ¬ Holds a b (Complex.ofRealHom.mapMatrix O.val)) :
    ∃ i, ∀ j, O.val i j ≠ 0 := by
  by_contra! hn
  exact hbad (four_holds_orthogonal_of_no_dense_row a b O hcol hn)

/-- A row-dense and column-dense witness suffice for the exact stationary reduction. -/
theorem not_conjecture_four_iff_dense_cross_stationary_witness :
    (¬ Conjecture (Fin 4)) ↔
      ∃ (a b : Fin 4 → ℂ) (η : ℂ) (O : Matrix.orthogonalGroup (Fin 4) ℝ),
        let V := Complex.ofRealHom.mapMatrix O.val
        (∀ i j, a i + b j ≠ 0) ∧ Function.Injective (matchingProduct a b) ∧
        (∀ i, 3 ≤ (supportColumns V {i}).card) ∧
        (∀ j, 3 ≤ (supportColumns Vᴴ {j}).card) ∧
        (∃ r, ∀ j, O.val r j ≠ 0) ∧
        (∃ c, ∀ i, O.val i c ≠ 0) ∧
        (∀ W : Matrix (Fin 4) (Fin 4) ℂ, IsUnitary W →
          (η * determinantValue a b W).re ≤ (η * determinantValue a b V).re) ∧
        Reformulations.SatisfiesStationaryEquations a b O η ∧
        ∀ p : Equiv.Perm (Fin 4),
          (η * matchingProduct a b p).re < (η * determinantValue a b V).re := by
  classical
  constructor
  · intro h
    obtain ⟨a, b, η, O, hnonzero, hinj, hrow, hcol, hmax, hstat, hgap⟩ :=
      not_conjecture_four_iff_regular_stationary_orthogonal_witness.mp h
    let V := Complex.ofRealHom.mapMatrix O.val
    have hbad : ¬ Holds a b V := by
      intro hh
      obtain ⟨p, hp⟩ := (holds_iff_directional _ _ _).mp hh η
      exact (not_lt_of_ge hp) (hgap p)
    have hr := four_exists_dense_row_of_orthogonal_violation a b O hcol hbad
    let Ot : Matrix.orthogonalGroup (Fin 4) ℝ :=
      ⟨O.valᵀ, (Matrix.mem_orthogonalGroup_iff _ _).mpr (by
        change O.valᵀ * O.val = 1
        exact (Matrix.mem_orthogonalGroup_iff' _ _).mp O.property)⟩
    have hOt : Complex.ofRealHom.mapMatrix Ot.val = Vᴴ := by
      ext i j
      simp [Ot, V]
    have hcol' : ∀ j, 3 ≤ (supportColumns (Complex.ofRealHom.mapMatrix Ot.val)ᴴ {j}).card := by
      rw [hOt, Matrix.conjTranspose_conjTranspose]
      exact hrow
    have hbad' : ¬ Holds b a (Complex.ofRealHom.mapMatrix Ot.val) := by
      rw [hOt]
      exact fun hh => hbad ((holds_swap_iff a b (isUnitary_ofReal_orthogonal O)).mp hh)
    obtain ⟨c, hc⟩ := four_exists_dense_row_of_orthogonal_violation b a Ot hcol' hbad'
    exact ⟨a, b, η, O, hnonzero, hinj, hrow, hcol, hr, ⟨c, hc⟩, hmax, hstat, hgap⟩
  · rintro ⟨a, b, η, O, hnonzero, hinj, hrow, hcol, _, _, hmax, hstat, hgap⟩
    exact not_conjecture_four_iff_regular_stationary_orthogonal_witness.mpr
      ⟨a, b, η, O, hnonzero, hinj, hrow, hcol, hmax, hstat, hgap⟩

end MOC
