import MOC.NormalRelativeInclusion
import MOC.CommonCommutant

/-! Determinant inclusion for normal summands with normal product.
The proof reduces along Hermitian elements of the common commutant.
The induction hypothesis applies only to smaller normal-product pairs.
No lower-order instance of the unrestricted conjecture is assumed. -/

open Matrix

namespace MOC

noncomputable section

private theorem product_conjugation {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix ι ι ℂ) (hU : IsUnitary U) (A B : Matrix ι ι ℂ) :
    (U * A * Uᴴ) * (U * B * Uᴴ) = U * (A * B) * Uᴴ := by
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc Uᴴ U, hU.2, Matrix.one_mul]

private theorem normal_conjugation {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix ι ι ℂ) (hU : IsUnitary U) (A : Matrix ι ι ℂ) (hA : IsStarNormal A) :
    IsStarNormal (U * A * Uᴴ) := by
  have hAe : Aᴴ * A = A * Aᴴ := hA.star_comm_self.eq
  constructor
  change (U * A * Uᴴ)ᴴ * (U * A * Uᴴ) = (U * A * Uᴴ) * (U * A * Uᴴ)ᴴ
  have hstar : (U * A * Uᴴ)ᴴ = U * Aᴴ * Uᴴ := by
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  rw [hstar, product_conjugation U hU Aᴴ A, product_conjugation U hU A Aᴴ,
    hAe]

private theorem normal_reindex {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (e : κ ≃ ι) (A : Matrix ι ι ℂ) (hA : IsStarNormal A) :
    IsStarNormal (A.submatrix e e) := by
  have hAe : Aᴴ * A = A * Aᴴ := hA.star_comm_self.eq
  constructor
  change (A.submatrix e e)ᴴ * A.submatrix e e = A.submatrix e e * (A.submatrix e e)ᴴ
  rw [Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv _ _ e e e,
    Matrix.submatrix_mul_equiv _ _ e e e, hAe]

private theorem normal_blocks {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (A : Matrix ι ι ℂ) (B : Matrix κ κ ℂ)
    (h : IsStarNormal (fromBlocks A 0 0 B)) : IsStarNormal A ∧ IsStarNormal B := by
  have hnormal : (fromBlocks A 0 0 B)ᴴ * fromBlocks A 0 0 B =
      fromBlocks A 0 0 B * (fromBlocks A 0 0 B)ᴴ := h.star_comm_self.eq
  have he : fromBlocks (Aᴴ * A) 0 0 (Bᴴ * B) = fromBlocks (A * Aᴴ) 0 0 (B * Bᴴ) := by
    simpa only [Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_zero,
      Matrix.fromBlocks_multiply, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add]
      using hnormal
  have hparts := Matrix.fromBlocks_inj.mp he
  exact ⟨⟨hparts.1⟩, ⟨hparts.2.2.2⟩⟩

private theorem spectral_product_reindex {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (eRow eCol : κ ≃ ι) (a b : ι → ℂ) (U : Matrix ι ι ℂ) :
    diagonal (a ∘ eRow) * (U.submatrix eRow eCol * diagonal (b ∘ eCol) *
      (U.submatrix eRow eCol)ᴴ) =
      (diagonal a * (U * diagonal b * Uᴴ)).submatrix eRow eRow := by
  rw [Matrix.conjTranspose_submatrix, ← Matrix.submatrix_diagonal_equiv a eRow,
    ← Matrix.submatrix_diagonal_equiv b eCol,
    Matrix.submatrix_mul_equiv _ _ eRow eCol eCol,
    Matrix.submatrix_mul_equiv _ _ eRow eCol eRow,
    Matrix.submatrix_mul_equiv _ _ eRow eRow eRow]

private theorem normal_product_in_relative_basis {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι ℂ) (a b : ι → ℂ) (V W : Matrix ι ι ℂ) (hV : IsUnitary V)
    (ha : A = V * diagonal a * Vᴴ) (hb : B = W * diagonal b * Wᴴ)
    (hAB : IsStarNormal (A * B)) :
    IsStarNormal (diagonal a * ((Vᴴ * W) * diagonal b * (Vᴴ * W)ᴴ)) := by
  have hVs : IsUnitary Vᴴ := ⟨by simpa only [Matrix.conjTranspose_conjTranspose] using hV.2,
    by simpa only [Matrix.conjTranspose_conjTranspose] using hV.1⟩
  have hleft : Vᴴ * A * V = diagonal a := by
    rw [ha]
    calc
      _ = (Vᴴ * V) * diagonal a * (Vᴴ * V) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hV.2, Matrix.one_mul, Matrix.mul_one]
  have hright : Vᴴ * B * V = (Vᴴ * W) * diagonal b * (Vᴴ * W)ᴴ := by
    rw [hb]
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  have he : diagonal a * ((Vᴴ * W) * diagonal b * (Vᴴ * W)ᴴ) = Vᴴ * (A * B) * V := by
    rw [← hleft, ← hright]
    simpa only [Matrix.conjTranspose_conjTranspose] using product_conjugation Vᴴ hVs A B
  rw [he]
  simpa only [Matrix.conjTranspose_conjTranspose] using normal_conjugation Vᴴ hVs (A * B) hAB

private theorem holds_normal_product_of_paired_blocks {n : ℕ}
    (hbelow : ∀ m < n, ∀ (a b : Fin m → ℂ) (U : Matrix (Fin m) (Fin m) ℂ),
      IsUnitary U → IsStarNormal (diagonal a * (U * diagonal b * Uᴴ)) → Holds a b U)
    (a b : Fin n → ℂ) (U : Matrix (Fin n) (Fin n) ℂ) (hU : IsUnitary U)
    (hprod : IsStarNormal (diagonal a * (U * diagonal b * Uᴴ)))
    (hblocks : HasProperPairedBlocks U) : Holds a b U := by
  obtain ⟨m, k, eRow, eCol, V, W, hm, hk, hsplit⟩ := hblocks
  obtain ⟨hmn, hkn⟩ := paired_block_orders_lt eRow hm hk
  have hunit : IsUnitary (fromBlocks V 0 0 W) := hsplit ▸ unitary_reindex eRow eCol hU
  obtain ⟨hV, hW⟩ := unitary_directSum_iff.mp hunit
  let aL (i : Fin m) := a (eRow (.inl i))
  let aR (i : Fin k) := a (eRow (.inr i))
  let bL (i : Fin m) := b (eCol (.inl i))
  let bR (i : Fin k) := b (eCol (.inr i))
  have ha : a ∘ eRow = Sum.elim aL aR := by funext i; cases i <;> rfl
  have hb : b ∘ eCol = Sum.elim bL bR := by funext i; cases i <;> rfl
  have hprod' := normal_reindex eRow _ hprod
  have he : (diagonal a * (U * diagonal b * Uᴴ)).submatrix eRow eRow =
      fromBlocks (diagonal aL * (V * diagonal bL * Vᴴ)) 0 0
        (diagonal aR * (W * diagonal bR * Wᴴ)) := by
    rw [← spectral_product_reindex eRow eCol a b U, hsplit, ha, hb,
      ← Matrix.fromBlocks_diagonal, ← Matrix.fromBlocks_diagonal]
    simp only [Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_zero,
      Matrix.fromBlocks_multiply, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add]
  rw [he] at hprod'
  obtain ⟨hL, hR⟩ := normal_blocks _ _ hprod'
  have hincl := holds_directSum aL bL aR bR V W
    (hbelow m hmn aL bL V hV hL) (hbelow k hkn aR bR W hW hR)
  apply (holds_reindex_iff eRow eCol a b U).mp
  simpa only [hsplit, ha, hb] using hincl

private theorem holds_of_normal_product_fin (n : ℕ) :
    ∀ (a b : Fin n → ℂ) (U : Matrix (Fin n) (Fin n) ℂ), IsUnitary U →
      IsStarNormal (diagonal a * (U * diagonal b * Uᴴ)) → Holds a b U := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro a b U hU hprod
    by_cases hn : n ≤ 3
    · exact conjecture_le_three hn a b U hU
    letI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
    let A := diagonal a
    let B := U * diagonal b * Uᴴ
    have hA : IsStarNormal A := by
      simpa only [Matrix.one_mul, Matrix.conjTranspose_one, Matrix.mul_one] using
        isStarNormal_unitary_diagonalization a isUnitary_one
    have hB : IsStarNormal B := isStarNormal_unitary_diagonalization b hU
    by_cases hcentral : ∀ H : Matrix (Fin n) (Fin n) ℂ, H.IsHermitian →
        Commute A H → Commute B H → ∃ c : ℂ, H = c • (1 : Matrix (Fin n) (Fin n) ℂ)
    · exact holds_of_commuting_grams_of_scalar_hermitian_commutant a b U hU
        (commute_gram_of_normal_relative a B hB hprod).symm
        (commute_right_gram_of_normal_product a B hB hprod) hcentral
    push_neg at hcentral
    obtain ⟨H, hH, hAH, hBH, hns⟩ := hcentral
    obtain ⟨a', d, V, hV, hAV, hd⟩ := exists_joint_normal_hermitian_diagonalization A H hA hH hAH
    obtain ⟨b', e, W, hW, hBW, he⟩ := exists_joint_normal_hermitian_diagonalization B H hB hH hBH
    have hdV : Vᴴ * H = diagonal d * Vᴴ := by
      calc
        _ = (Vᴴ * V) * diagonal d * Vᴴ := by rw [hd]; simp only [Matrix.mul_assoc]
        _ = _ := by rw [hV.2, Matrix.one_mul]
    have heW : H * W = W * diagonal e := by
      rw [he, Matrix.mul_assoc (W * diagonal e), hW.2, Matrix.mul_one]
    have hde : diagonal d * (Vᴴ * W) = (Vᴴ * W) * diagonal e := by
      calc
        _ = (Vᴴ * H) * W := by rw [hdV, Matrix.mul_assoc]
        _ = Vᴴ * (W * diagonal e) := by rw [Matrix.mul_assoc, heW]
        _ = _ := by rw [Matrix.mul_assoc]
    have hR := relative_unitary V W hV hW
    have hblocks : HasProperPairedBlocks (Vᴴ * W) := by
      by_contra hno
      obtain ⟨c, hc⟩ := constant_left_labels_of_diagonal_intertwining hR
        (card_lt_supportColumns_of_no_paired_blocks hR hno) d e hde
      apply hns c
      rw [hd, hc, ← Matrix.smul_one_eq_diagonal, Matrix.mul_smul, Matrix.mul_one,
        Matrix.smul_mul, hV.1]
    have hprod' := normal_product_in_relative_basis A B a' b' V W hV hAV hBW hprod
    apply (holds_iff_relative_to_diagonalizations a b a' b' hU hV hW hAV hBW).mpr
    exact holds_normal_product_of_paired_blocks (fun m hm => ih m hm) a' b' (Vᴴ * W) hR hprod' hblocks

/-- Two normal summands with normal product satisfy the determinant inclusion.
The order and both spectra are arbitrary. Either summand may be singular. -/
theorem holds_of_normal_product {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a b : ι → ℂ) (U : Matrix ι ι ℂ) (hU : IsUnitary U)
    (hprod : IsStarNormal (diagonal a * (U * diagonal b * Uᴴ))) : Holds a b U := by
  let e := (Fintype.equivFin ι).symm
  have hprod' := normal_reindex e _ hprod
  rw [← spectral_product_reindex e e a b U] at hprod'
  exact (holds_reindex_iff e e a b U).mp
    (holds_of_normal_product_fin (Fintype.card ι) (a ∘ e) (b ∘ e)
      (U.submatrix e e) (unitary_reindex e e hU) hprod')

/-- A normal relative product gives inclusion without a commutant condition
or an assumption about lower orders. -/
theorem holds_of_normal_relative {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a b : ι → ℂ) (U : Matrix ι ι ℂ) (hU : IsUnitary U)
    (ha : IsUnit (diagonal a).det)
    (hrelative : IsStarNormal ((diagonal a)⁻¹ * (U * diagonal b * Uᴴ))) : Holds a b U := by
  let A := diagonal a
  let B := U * diagonal b * Uᴴ
  let W := A⁻¹ * B
  have hAW : A * W = B := by
    simp only [W, ← Matrix.mul_assoc, A.mul_nonsing_inv ha, Matrix.one_mul]
  have hA : IsStarNormal A := by
    simpa only [Matrix.one_mul, Matrix.conjTranspose_one, Matrix.mul_one] using
      isStarNormal_unitary_diagonalization a isUnitary_one
  have hB : IsStarNormal B := isStarNormal_unitary_diagonalization b hU
  have hAWnormal : IsStarNormal (diagonal a * W) := by
    rw [show diagonal a * W = B from hAW]
    exact hB
  obtain ⟨_, hBP, hAQ, _⟩ := common_grams_of_normal_relative a W ha hrelative hAWnormal
  rw [show diagonal a * W = B from hAW] at hBP hAQ
  exact holds_of_normal_product a b U hU (isStarNormal_mul_of_commuting_grams A B hA hB hAQ hBP)

/-- Matrix form: normality of both summands and their product implies MOC.
The supplied lists enumerate the characteristic roots with multiplicity. -/
theorem determinant_mem_matchingHull_of_normal_product {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι ℂ) (a b : ι → ℂ) (hA : IsStarNormal A) (hB : IsStarNormal B)
    (hAB : IsStarNormal (A * B))
    (ha : A.charpoly.roots = (Finset.univ : Finset ι).val.map a)
    (hb : B.charpoly.roots = (Finset.univ : Finset ι).val.map b) :
    (A + B).det ∈ convexHull ℝ (Set.range (matchingProduct a b)) := by
  obtain ⟨a', V, hV, hAV⟩ := exists_unitary_diagonalization A hA
  obtain ⟨b', W, hW, hBW⟩ := exists_unitary_diagonalization B hB
  have hprod := normal_product_in_relative_basis A B a' b' V W hV hAV hBW hAB
  have hincl := holds_of_normal_product a' b' (Vᴴ * W) (relative_unitary V W hV hW) hprod
  rw [hAV, roots_unitary_diagonalization a' hV] at ha
  rw [hBW, roots_unitary_diagonalization b' hW] at hb
  obtain ⟨e, he⟩ := exists_perm_of_equal_multisets a a' ha.symm
  obtain ⟨f, hf⟩ := exists_perm_of_equal_multisets b b' hb.symm
  have hdet : (A + B).det = determinantValue a' b' (Vᴴ * W) := by
    rw [hAV, hBW]
    exact determinantValue_relative a' b' V W hV
  rw [he, hf, matchingRange_relabel, hdet]
  exact hincl

/-- Matrix form of the normal-relative-product theorem. -/
theorem determinant_mem_matchingHull_of_normal_relative {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι ℂ) (a b : ι → ℂ) (hA : IsStarNormal A) (hB : IsStarNormal B)
    (hAdet : IsUnit A.det) (hrelative : IsStarNormal (A⁻¹ * B))
    (ha : A.charpoly.roots = (Finset.univ : Finset ι).val.map a)
    (hb : B.charpoly.roots = (Finset.univ : Finset ι).val.map b) :
    (A + B).det ∈ convexHull ℝ (Set.range (matchingProduct a b)) := by
  obtain ⟨a', V, hV, hAV⟩ := exists_unitary_diagonalization A hA
  obtain ⟨b', W, hW, hBW⟩ := exists_unitary_diagonalization B hB
  have hAinv : A⁻¹ = V * diagonal (Ring.inverse a') * Vᴴ := by
    rw [hAV, Matrix.mul_inv_rev, Matrix.mul_inv_rev,
      Matrix.inv_eq_left_inv hV.1, Matrix.inv_eq_left_inv hV.2, Matrix.inv_diagonal]
    simp only [Matrix.mul_assoc]
  have hrel := normal_product_in_relative_basis A⁻¹ B (Ring.inverse a') b' V W hV hAinv hBW hrelative
  rw [← Matrix.inv_diagonal] at hrel
  have hdiag : IsUnit (diagonal a').det := by
    rwa [hAV, det_unitary_conjugation V _ hV] at hAdet
  have hincl := holds_of_normal_relative a' b' (Vᴴ * W) (relative_unitary V W hV hW) hdiag hrel
  rw [hAV, roots_unitary_diagonalization a' hV] at ha
  rw [hBW, roots_unitary_diagonalization b' hW] at hb
  obtain ⟨e, he⟩ := exists_perm_of_equal_multisets a a' ha.symm
  obtain ⟨f, hf⟩ := exists_perm_of_equal_multisets b b' hb.symm
  have hdet : (A + B).det = determinantValue a' b' (Vᴴ * W) := by
    rw [hAV, hBW]
    exact determinantValue_relative a' b' V W hV
  rw [he, hf, matchingRange_relabel, hdet]
  exact hincl

end

end MOC
