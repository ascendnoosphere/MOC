import MOC.AffineGapCover
import MOC.Realification
import MOC.SinglePortHallExpansion
import MOC.SparseRow

/-! Sparse deletion and contact transfer within the real orthogonal class. -/

open Matrix

namespace MOC

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The orthogonal conjecture applies to a complex unitary all of whose entries are real. -/
theorem holds_of_orthogonalConjecture_of_im_eq_zero (h : OrthogonalConjecture ι)
    (a b : ι → ℂ) {U : Matrix ι ι ℂ} (hU : IsUnitary U)
    (hreal : ∀ i j, (U i j).im = 0) : Holds a b U := by
  let R : Matrix ι ι ℝ := U.map Complex.re
  let f : Matrix ι ι ℝ →+* Matrix ι ι ℂ := Complex.ofRealHom.mapMatrix
  have hR : f R = U := by
    ext i j
    change ((U i j).re : ℂ) = U i j
    exact Complex.ext rfl (hreal i j).symm
  have ht : f Rᵀ = Uᴴ := by
    ext i j
    change ((U j i).re : ℂ) = star (U j i)
    apply Complex.ext
    · simp [Complex.star_def]
    · simp [Complex.star_def, hreal j i]
  have hm : f (R * Rᵀ) = f 1 := by rw [f.map_mul, hR, ht, hU.1, f.map_one]
  have hmul : R * Rᵀ = 1 := by
    ext i j
    exact Complex.ofReal_injective (congrArg (fun W : Matrix ι ι ℂ => W i j) hm)
  have hstar : R * star R = 1 := by
    simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
      using hmul
  let O : Matrix.orthogonalGroup ι ℝ := ⟨R, (Matrix.mem_orthogonalGroup_iff ι ℝ).mpr hstar⟩
  have hh := h a b O
  change Holds a b (f R) at hh
  exact hR ▸ hh

private theorem holds_real_unitary_of_reindexed_orthogonalConjecture
    {κ : Type*} [Fintype κ] [DecidableEq κ] (e : κ ≃ ι) (h : OrthogonalConjecture κ)
    (a b : ι → ℂ) {U : Matrix ι ι ℂ} (hU : IsUnitary U)
    (hreal : ∀ i j, (U i j).im = 0) : Holds a b U :=
  (holds_reindex_iff e e a b U).mp
    (holds_of_orthogonalConjecture_of_im_eq_zero h (a ∘ e) (b ∘ e)
      (unitary_reindex e e hU) (fun i j => hreal (e i) (e j)))

private theorem normalizedSparseRowMinor_im_eq_zero {n : ℕ}
    {U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (hreal : ∀ i j, (U i j).im = 0)
    (i j k : Fin (n + 1)) (r s : Fin n) : (normalizedSparseRowMinor U i j k r s).im = 0 := by
  rw [normalizedSparseRowMinor, Matrix.mul_diagonal, Matrix.submatrix_apply, Complex.mul_im,
    hreal, zero_mul, add_zero]
  change (U (i.succAbove r) (j.succAbove s)).re *
    (if j.succAbove s = k then (U i j)⁻¹ else (1 : ℂ)).im = 0
  by_cases hs : j.succAbove s = k
  · rw [if_pos hs, Complex.inv_im, hreal, neg_zero, zero_div, mul_zero]
  · rw [if_neg hs, Complex.one_im, mul_zero]

/-- A row with at most two nonzero entries reduces to the orthogonal conjecture
one order smaller. The surviving column is divided by a real pivot. -/
theorem holds_of_real_row_degree_le_two {n : ℕ} (hSmall : OrthogonalConjecture (Fin n))
    (a b : Fin (n + 1) → ℂ) {U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hU : IsUnitary U) (hreal : ∀ i j, (U i j).im = 0)
    (i : Fin (n + 1)) (hi : (supportColumns U {i}).card ≤ 2) : Holds a b U := by
  obtain ⟨j, k, hzero⟩ := exists_row_support_pair i hi
  apply holds_of_two_supported_row_of_minors a b hU i j k hzero
  intro p _ hV
  exact holds_of_orthogonalConjecture_of_im_eq_zero hSmall _ _ hV
    (normalizedSparseRowMinor_im_eq_zero hreal i p (if p = j then k else j))

/-- A column with at most two nonzero entries reduces to the orthogonal conjecture
one order smaller. -/
theorem holds_of_real_column_degree_le_two {n : ℕ} (hSmall : OrthogonalConjecture (Fin n))
    (a b : Fin (n + 1) → ℂ) {U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hU : IsUnitary U) (hreal : ∀ i j, (U i j).im = 0)
    (j : Fin (n + 1)) (hj : (supportColumns Uᴴ {j}).card ≤ 2) : Holds a b U := by
  have hV : IsUnitary Uᴴ := by
    exact ⟨by simpa only [Matrix.conjTranspose_conjTranspose] using hU.2,
      by simpa only [Matrix.conjTranspose_conjTranspose] using hU.1⟩
  have hVreal (r s : Fin (n + 1)) : (Uᴴ r s).im = 0 := by
    rw [Matrix.conjTranspose_apply, Complex.star_def, Complex.conj_im, hreal, neg_zero]
  exact (holds_swap_iff a b hU).mp (holds_of_real_row_degree_le_two hSmall b a hV hVreal j hj)

/-- A zero rectangle whose side lengths add to one less than the order
reduces the real orthogonal inclusion to two mixers whose orders are the
side lengths with one added. -/
theorem holds_of_real_singlePort_zero_rectangle (a b : ι → ℂ)
    {U : Matrix ι ι ℂ} (hU : IsUnitary U) (hreal : ∀ i j, (U i j).im = 0)
    (I J : Finset ι) (hcard : I.card + J.card + 1 = Fintype.card ι)
    (hz : ∀ i ∈ I, ∀ j ∈ J, U i j = 0)
    (hleft : OrthogonalConjecture (Fin (J.card + 1)))
    (hright : OrthogonalConjecture (Fin (I.card + 1))) : Holds a b U := by
  obtain ⟨er, ec, her, hec⟩ := exists_reindex_singlePort_corner I J hcard
  obtain ⟨V, W, hV, hW, hprod, hVr, hWr⟩ := exists_real_singlePort_factors_of_zero_corner
    (unitary_reindex er ec hU) (fun i j => hreal (er i) (ec j))
    (fun i j => hz _ (her i) _ (hec j))
  let el : Fin (J.card + 1) ≃ Fin J.card ⊕ Unit := Fintype.equivOfCardEq (by simp)
  let eR : Fin (I.card + 1) ≃ Unit ⊕ Fin I.card := Fintype.equivOfCardEq (by simp [add_comm])
  apply (holds_reindex_iff er ec a b U).mp
  rw [hprod]
  exact holds_singlePortComposition _ _ V W hV hW
    (fun c d => holds_real_unitary_of_reindexed_orthogonalConjecture el hleft c d hV hVr)
    (fun c d => holds_real_unitary_of_reindexed_orthogonalConjecture eR hright c d hW hWr)

/-- At an order whose smaller real orthogonal cases hold, every strict real
orthogonal violation has additive-two support expansion. -/
theorem additive_two_support_expansion_of_real_failure {n : ℕ}
    (hbelow : ∀ m < n, OrthogonalConjecture (Fin m)) (a b : Fin n → ℂ)
    {U : Matrix (Fin n) (Fin n) ℂ} (hU : IsUnitary U) (hreal : ∀ i j, (U i j).im = 0)
    (hfail : ¬ Holds a b U) :
    ∀ R : Finset (Fin n), R.Nonempty → R.card + 2 ≤ n →
      R.card + 2 ≤ (supportColumns U R).card := by
  have hnone := (additiveTwoSupportExpansion_iff_no_zero_rectangle U).mpr ?_
  · simpa only [Fintype.card_fin] using hnone
  rintro ⟨R, C, hR, hC, hsize, hz⟩
  rw [Fintype.card_fin] at hsize
  have hRpos := Finset.card_pos.mpr hR
  have hCpos := Finset.card_pos.mpr hC
  have hdim : R.card + C.card + 1 = Fintype.card (Fin n) := by
    rw [Fintype.card_fin]
    omega
  exact hfail (holds_of_real_singlePort_zero_rectangle a b hU hreal R C hdim hz
    (hbelow _ (by omega)) (hbelow _ (by omega)))

/-- The all-order real orthogonal conjecture is equivalent to excluding strict
violations with at least `2n - 1` contacts and additive-two support expansion.
Both restrictions apply to the same mixer. -/
theorem orthogonalConjecture_all_orders_iff_terminal_contacts_and_expansion :
    (∀ n : ℕ, OrthogonalConjecture (Fin n)) ↔
      ∀ n : ℕ, 4 ≤ n → ¬ ∃ (O : Matrix.orthogonalGroup (Fin n) ℝ),
        let U := Complex.ofRealHom.mapMatrix O.val
        (∀ R : Finset (Fin n), R.Nonempty → R.card + 2 ≤ n →
          R.card + 2 ≤ (supportColumns U R).card) ∧
        ∃ w : StrictMatchingSupport U, 2 * n - 1 ≤ w.contacts.card := by
  constructor
  · rintro h n _ ⟨O, _, w, _⟩
    exact w.not_holds (h n w.a w.b O)
  · intro h n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro a b O
      let U := Complex.ofRealHom.mapMatrix O.val
      have hU : IsUnitary U := isUnitary_ofReal_orthogonal O
      have hreal (i j : Fin n) : (U i j).im = 0 := Complex.ofReal_im _
      by_cases hn : n ≤ 3
      · exact conjecture_le_three hn a b U hU
      · have hn4 : 4 ≤ n := by omega
        by_contra hbad
        have hexpand := additive_two_support_expansion_of_real_failure ih a b hU hreal hbad
        obtain ⟨w⟩ := nonempty_strictMatchingSupport_of_failure a b hbad
        obtain ⟨v, hv⟩ := exists_strictMatchingSupport_at_least (2 * n - 1) w (fun u hu => by
          have hbound : u.contacts.card ≤ 2 * Fintype.card (Fin n) - 2 := by
            rw [Fintype.card_fin]
            omega
          obtain ⟨v, _, _, hinc, _⟩ := global_varying_gap_contact_transfer
            (affineGapContinuation (Equiv.Perm (Fin n))) hU u hbound
          exact ⟨v, Finset.card_lt_card hinc⟩)
        exact h n hn4 ⟨O, hexpand, v, hv⟩

end MOC
