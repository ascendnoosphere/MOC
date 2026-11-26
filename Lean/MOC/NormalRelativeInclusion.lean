import MOC.RelativeUnitaryGram
import MOC.ConcentricPerturbation
import MOC.JointNormalHermitian

/-! A normal relative product reduces an irreducible pair to the concentric case. -/

open Matrix

namespace MOC

private theorem diagonal_gram {ι : Type*} [Fintype ι] [DecidableEq ι] (a : ι → ℂ) :
    (diagonal a)ᴴ * diagonal a = diagonal (fun i => (Complex.normSq (a i) : ℂ)) := by
  rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
  apply congrArg diagonal
  funext i
  simp only [Pi.mul_apply, Pi.star_apply, Complex.star_def, ← Complex.normSq_eq_conj_mul_self]

private theorem conjugated_diagonal_gram {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : ι → ℂ) (U : Matrix ι ι ℂ) (hU : IsUnitary U) :
    let B := U * diagonal b * Uᴴ
    Bᴴ * B = U * diagonal (fun i => (Complex.normSq (b i) : ℂ)) * Uᴴ := by
  intro B
  calc
    _ = U * ((diagonal b)ᴴ * (Uᴴ * U) * diagonal b) * Uᴴ := by
      simp only [B, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
    _ = _ := by rw [hU.2, Matrix.mul_one, diagonal_gram]

private theorem normal_conjugated_diagonal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : ι → ℂ) (U : Matrix ι ι ℂ) (hU : IsUnitary U) : IsStarNormal (U * diagonal b * Uᴴ) := by
  let B := U * diagonal b * Uᴴ
  constructor
  change Bᴴ * B = B * Bᴴ
  rw [conjugated_diagonal_gram b U hU]
  have hbb : (diagonal b)ᴴ * diagonal b = diagonal b * (diagonal b)ᴴ := by
    rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    exact congrArg diagonal (funext fun i => mul_comm _ _)
  calc
    _ = U * (diagonal b * (diagonal b)ᴴ) * Uᴴ := by rw [← diagonal_gram b, hbb]
    _ = U * (diagonal b * (Uᴴ * U) * (diagonal b)ᴴ) * Uᴴ := by rw [hU.2, Matrix.mul_one]
    _ = _ := by
      simp only [B, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]

/-- Common Gram matrices and a scalar common Hermitian commutant force
constant spectral moduli and give the inclusion. -/
theorem holds_of_commuting_grams_of_scalar_hermitian_commutant {n : ℕ} (a b : Fin n → ℂ)
    (U : Matrix (Fin n) (Fin n) ℂ) (hU : IsUnitary U)
    (hBP : Commute (U * diagonal b * Uᴴ) ((diagonal a)ᴴ * diagonal a))
    (hAQ : Commute (diagonal a) ((U * diagonal b * Uᴴ)ᴴ * (U * diagonal b * Uᴴ)))
    (hcentral : ∀ Y : Matrix (Fin n) (Fin n) ℂ, Y.IsHermitian →
      Commute (diagonal a) Y → Commute (U * diagonal b * Uᴴ) Y →
      ∃ c : ℂ, Y = c • (1 : Matrix (Fin n) (Fin n) ℂ)) : Holds a b U := by
  let A := diagonal a
  let B := U * diagonal b * Uᴴ
  let c (i : Fin n) := (Complex.normSq (b i) : ℂ)
  have hBg : Bᴴ * B = U * diagonal c * Uᴴ := conjugated_diagonal_gram b U hU
  have hBnormal : IsStarNormal B := normal_conjugated_diagonal b U hU
  have hAP : Commute A (Aᴴ * A) := by
    rw [show Aᴴ * A = diagonal (fun i => (Complex.normSq (a i) : ℂ)) from diagonal_gram a]
    change diagonal a * diagonal _ = diagonal _ * diagonal a
    rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    exact congrArg diagonal (funext fun i => mul_comm _ _)
  have hBQ : Commute B (Bᴴ * B) := hBnormal.star_comm_self.symm.mul_right (Commute.refl B)
  have hself (Y : Matrix (Fin n) (Fin n) ℂ) : (Yᴴ * Y).IsHermitian := by
    change (Yᴴ * Y)ᴴ = Yᴴ * Y
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  obtain ⟨α, hα⟩ := hcentral (Aᴴ * A) (hself A) hAP hBP
  obtain ⟨β, hβ⟩ := hcentral (Bᴴ * B) (hself B)
    hAQ hBQ
  have hDβ : diagonal c = β • (1 : Matrix (Fin n) (Fin n) ℂ) := by
    calc
      _ = (Uᴴ * (U * diagonal c * Uᴴ)) * U := by
        simp only [← Matrix.mul_assoc, hU.2, Matrix.one_mul]
        rw [Matrix.mul_assoc (diagonal c) Uᴴ U, hU.2, Matrix.mul_one]
      _ = Uᴴ * (Bᴴ * B) * U := by rw [hBg]
      _ = _ := by rw [hβ, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hU.2]
  have ha' (i : Fin n) : Complex.normSq (a i) = α.re := by
    rw [show Aᴴ * A = _ from diagonal_gram a] at hα
    simpa only [Matrix.diagonal_apply_eq, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply_eq,
      mul_one, Complex.ofReal_re] using congrArg (fun M : Matrix (Fin n) (Fin n) ℂ => (M i i).re) hα
  have hb' (i : Fin n) : Complex.normSq (b i) = β.re := by
    simpa only [c, Matrix.diagonal_apply_eq, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply_eq,
      mul_one, Complex.ofReal_re] using congrArg (fun M : Matrix (Fin n) (Fin n) ℂ => (M i i).re) hDβ
  exact holds_of_concentric_circles a b α.re β.re ha' hb' U hU

/-- If the common Hermitian commutant contains only scalars, normality of
the relative product forces concentric spectra and gives the inclusion. -/
theorem holds_of_normal_relative_of_scalar_hermitian_commutant {n : ℕ} (a b : Fin n → ℂ)
    (U : Matrix (Fin n) (Fin n) ℂ) (hU : IsUnitary U) (ha : IsUnit (diagonal a).det)
    (hW : IsStarNormal ((diagonal a)⁻¹ * (U * diagonal b * Uᴴ)))
    (hcentral : ∀ Y : Matrix (Fin n) (Fin n) ℂ, Y.IsHermitian →
      Commute (diagonal a) Y → Commute (U * diagonal b * Uᴴ) Y →
      ∃ c : ℂ, Y = c • (1 : Matrix (Fin n) (Fin n) ℂ)) : Holds a b U := by
  let A := diagonal a
  let B := U * diagonal b * Uᴴ
  let W := A⁻¹ * B
  have hAW : A * W = B := by simp only [W, ← Matrix.mul_assoc, A.mul_nonsing_inv ha, Matrix.one_mul]
  have hB : IsStarNormal (diagonal a * W) := by
    change IsStarNormal (A * W)
    rw [hAW]
    exact normal_conjugated_diagonal b U hU
  obtain ⟨_, hBP, hAQ, _⟩ := common_grams_of_normal_relative a W ha hW hB
  rw [show diagonal a * W = B from hAW] at hBP hAQ
  exact holds_of_commuting_grams_of_scalar_hermitian_commutant a b U hU hBP hAQ hcentral

/-- A scalar common commutant is sufficient for the normal-relative-product
inclusion. -/
theorem holds_of_normal_relative_of_scalar_commutant {n : ℕ} (a b : Fin n → ℂ)
    (U : Matrix (Fin n) (Fin n) ℂ) (hU : IsUnitary U) (ha : IsUnit (diagonal a).det)
    (hW : IsStarNormal ((diagonal a)⁻¹ * (U * diagonal b * Uᴴ)))
    (hcentral : ∀ Y : Matrix (Fin n) (Fin n) ℂ,
      Commute (diagonal a) Y → Commute (U * diagonal b * Uᴴ) Y →
      ∃ c : ℂ, Y = c • (1 : Matrix (Fin n) (Fin n) ℂ)) : Holds a b U :=
  holds_of_normal_relative_of_scalar_hermitian_commutant a b U hU ha hW (fun Y _ => hcentral Y)

/-- In the least failing order with simple spectra, the relative product
of the normal summands cannot be normal when the first is invertible. -/
theorem holds_of_simple_normal_relative_of_smaller_orders {n : ℕ}
    (hbelow : ∀ m < n, Conjecture (Fin m)) (a b : Fin n → ℂ)
    (haInj : Function.Injective a) (hbInj : Function.Injective b)
    (U : Matrix (Fin n) (Fin n) ℂ) (hU : IsUnitary U) (ha : IsUnit (diagonal a).det)
    (hW : IsStarNormal ((diagonal a)⁻¹ * (U * diagonal b * Uᴴ))) : Holds a b U := by
  by_cases hn : n ≤ 3
  · exact conjecture_le_three hn a b U hU
  have hnpos : 0 < n := Nat.lt_trans (by decide : 0 < 3) (Nat.lt_of_not_ge hn)
  letI : Nonempty (Fin n) := ⟨⟨0, hnpos⟩⟩
  by_contra hbad
  have hcut : ¬ HasProperPairedBlocks U := mt (holds_of_proper_paired_blocks hbelow a b hU) hbad
  exact hbad (holds_of_normal_relative_of_scalar_commutant a b U hU ha hW
    (scalar_of_commute_simple_summands hU hcut haInj hbInj))

/-- A counterexample of least order with an invertible first summand has
a nonnormal relative product, even when its spectra repeat. -/
theorem holds_of_normal_relative_of_smaller_orders {n : ℕ}
    (hbelow : ∀ m < n, Conjecture (Fin m)) (a b : Fin n → ℂ)
    (U : Matrix (Fin n) (Fin n) ℂ) (hU : IsUnitary U) (ha : IsUnit (diagonal a).det)
    (hW : IsStarNormal ((diagonal a)⁻¹ * (U * diagonal b * Uᴴ))) : Holds a b U := by
  by_cases hn : n ≤ 3
  · exact conjecture_le_three hn a b U hU
  have hnpos : 0 < n := Nat.lt_trans (by decide : 0 < 3) (Nat.lt_of_not_ge hn)
  letI : Nonempty (Fin n) := ⟨⟨0, hnpos⟩⟩
  by_contra hbad
  apply hbad (holds_of_normal_relative_of_scalar_hermitian_commutant a b U hU ha hW ?_)
  intro H hH hAH hBH
  apply Classical.byContradiction
  intro hns
  have hA : IsStarNormal (diagonal a) := by
    simpa only [Matrix.one_mul, Matrix.conjTranspose_one, Matrix.mul_one] using
      normal_conjugated_diagonal a (1 : Matrix (Fin n) (Fin n) ℂ) isUnitary_one
  have hB := normal_conjugated_diagonal b U hU
  obtain ⟨a', d, V, hV, hAV, hd⟩ :=
    exists_joint_normal_hermitian_diagonalization (diagonal a) H hA hH hAH
  obtain ⟨b', e, W, hW', hBW, he⟩ :=
    exists_joint_normal_hermitian_diagonalization (U * diagonal b * Uᴴ) H hB hH hBH
  have hdV : Vᴴ * H = diagonal d * Vᴴ := by
    calc
      _ = (Vᴴ * V) * diagonal d * Vᴴ := by rw [hd]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [hV.2, Matrix.one_mul]
  have heW : H * W = W * diagonal e := by
    rw [he, Matrix.mul_assoc (W * diagonal e), hW'.2, Matrix.mul_one]
  have hde : diagonal d * (Vᴴ * W) = (Vᴴ * W) * diagonal e := by
    calc
      _ = (Vᴴ * H) * W := by rw [hdV, Matrix.mul_assoc]
      _ = Vᴴ * (W * diagonal e) := by rw [Matrix.mul_assoc, heW]
      _ = _ := by rw [Matrix.mul_assoc]
  have hR := relative_unitary V W hV hW'
  have hblocks : HasProperPairedBlocks (Vᴴ * W) := by
    by_contra hno
    obtain ⟨μ, hμ⟩ := constant_left_labels_of_diagonal_intertwining hR
      (card_lt_supportColumns_of_no_paired_blocks hR hno) d e hde
    apply hns
    refine ⟨μ, ?_⟩
    rw [hd, hμ, ← Matrix.smul_one_eq_diagonal, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hV.1]
  apply hbad
  apply (holds_iff_relative_to_diagonalizations a b a' b' hU hV hW' hAV hBW).mpr
  exact holds_of_proper_paired_blocks hbelow a' b' hR hblocks

/-- Every regular opposite shift of a least-order violation has a
nonnormal relative product. -/
theorem not_normal_relative_shift_of_least_order {n : ℕ}
    (hbelow : ∀ m < n, Conjecture (Fin m)) (a b : Fin n → ℂ)
    (U : Matrix (Fin n) (Fin n) ℂ) (hU : IsUnitary U) (hbad : ¬ Holds a b U)
    (z : ℂ) (hz : ∀ i, a i + z ≠ 0) :
    ¬ IsStarNormal ((diagonal fun i => a i + z)⁻¹ * (U * diagonal (fun i => b i - z) * Uᴴ)) := by
  intro hnormal
  have hinv : IsUnit (diagonal (fun i => a i + z)).det := by
    rw [Matrix.det_diagonal, isUnit_iff_ne_zero]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => hz i
  exact hbad ((holds_shift_iff a b hU z).mp
    (holds_of_normal_relative_of_smaller_orders hbelow _ _ U hU hinv hnormal))

end MOC
