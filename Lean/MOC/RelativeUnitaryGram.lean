import MOC.Normal
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! The row and column energies of a relative product control the moduli. -/

open BigOperators Matrix

namespace MOC

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem diagonal_normSq_gram (a : ι → ℂ) :
    (diagonal a)ᴴ * diagonal a = diagonal (fun i => (Complex.normSq (a i) : ℂ)) := by
  rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
  apply congrArg diagonal
  funext i
  simp only [Pi.mul_apply, Pi.star_apply, Complex.star_def, ← Complex.normSq_eq_conj_mul_self]

private theorem normal_row_col_energy (M : Matrix ι ι ℂ) (hM : IsStarNormal M) (i : ι) :
    (∑ j, Complex.normSq (M i j)) = ∑ j, Complex.normSq (M j i) := by
  have he := congrArg (fun X : Matrix ι ι ℂ => (X i i).re) hM.star_comm_self.eq
  change ((Mᴴ * M) i i).re = ((M * Mᴴ) i i).re at he
  simpa only [Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.star_def, Complex.mul_conj,
    ← Complex.normSq_eq_conj_mul_self, Complex.re_sum, Complex.ofReal_re] using he.symm

/-- If `diagonal a * W` is normal, the squared Gram-value differences
along the entries of `W` sum to a weighted column-minus-row energy. -/
theorem relative_modulus_energy_eq_row_column_defect (a : ι → ℂ) (W : Matrix ι ι ℂ)
    (hB : IsStarNormal (diagonal a * W)) :
    (∑ i, ∑ j, Complex.normSq (W j i) * (Complex.normSq (a i) - Complex.normSq (a j)) ^ 2) =
      ∑ i, Complex.normSq (a i) ^ 2 *
        ((∑ j, Complex.normSq (W j i)) - ∑ j, Complex.normSq (W i j)) := by
  let q (i : ι) := Complex.normSq (a i)
  let m (i j : ι) := Complex.normSq (W i j)
  let c (i : ι) := ∑ j, m j i
  let r (i : ι) := ∑ j, m i j
  let b (i : ι) := (q i) ^ 2 * r i
  have hbalance (i : ι) : q i * r i = ∑ j, m j i * q j := by
    have he := normal_row_col_energy (diagonal a * W) hB i
    simp only [Matrix.diagonal_mul, Complex.normSq_mul, ← Finset.mul_sum] at he
    calc
      _ = ∑ j, q j * m j i := he
      _ = _ := Finset.sum_congr rfl (fun j _ => mul_comm (q j) (m j i))
  have hrow (i : ι) :
      (∑ j, m j i * (q i - q j) ^ 2) = q i ^ 2 * c i - 2 * b i + ∑ j, m j i * q j ^ 2 := by
    calc
      _ = ∑ j, ((q i) ^ 2 * m j i - (2 * q i) * (m j i * q j) + m j i * (q j) ^ 2) := by
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
          ← hbalance i]
        change (q i) ^ 2 * c i - (2 * q i) * (q i * r i) + _ = _
        dsimp only [b]
        ring
  have hcross : (∑ i, ∑ j, m j i * (q j) ^ 2) = ∑ i, b i := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_mul]
    exact mul_comm _ _
  change (∑ i, ∑ j, m j i * (q i - q j) ^ 2) = ∑ i, q i ^ 2 * (c i - r i)
  simp_rw [hrow, mul_sub]
  change (∑ i, (q i ^ 2 * c i - 2 * b i + (∑ j, m j i * q j ^ 2))) =
    ∑ i, (q i ^ 2 * c i - b i)
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hcross,
    Finset.sum_sub_distrib]
  ring

/-- A normal relative product has zero weighted Gram-value discrepancy. -/
theorem normal_relative_modulus_energy_eq_zero (a : ι → ℂ) (W : Matrix ι ι ℂ)
    (hW : IsStarNormal W) (hB : IsStarNormal (diagonal a * W)) :
    ∑ i, ∑ j, Complex.normSq (W j i) * (Complex.normSq (a i) - Complex.normSq (a j)) ^ 2 = 0 := by
  rw [relative_modulus_energy_eq_row_column_defect a W hB]
  simp only [normal_row_col_energy W hW, sub_self, mul_zero, Finset.sum_const_zero]

/-- Row and column energy balance of the relative product already implies
that it preserves the eigenspaces of the first summand's Gram matrix. -/
theorem commute_gram_of_balanced_relative (a : ι → ℂ) (W : Matrix ι ι ℂ)
    (hW : ∀ i, (∑ j, Complex.normSq (W i j)) = ∑ j, Complex.normSq (W j i))
    (hB : IsStarNormal (diagonal a * W)) :
    Commute ((diagonal a)ᴴ * diagonal a) W := by
  rw [diagonal_normSq_gram]
  change diagonal (fun i => (Complex.normSq (a i) : ℂ)) * W =
    W * diagonal (fun i => (Complex.normSq (a i) : ℂ))
  ext i j : 1
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases hz : W i j = 0
  · simp [hz]
  have hnonneg (i j : ι) : 0 ≤ Complex.normSq (W j i) *
      (Complex.normSq (a i) - Complex.normSq (a j)) ^ 2 :=
    mul_nonneg (Complex.normSq_nonneg _) (sq_nonneg _)
  have henergy :
      (∑ i, ∑ j, Complex.normSq (W j i) * (Complex.normSq (a i) - Complex.normSq (a j)) ^ 2) = 0 := by
    rw [relative_modulus_energy_eq_row_column_defect a W hB]
    simp only [hW, sub_self, mul_zero, Finset.sum_const_zero]
  have hrows := (Finset.sum_eq_zero_iff_of_nonneg
    (fun i _ => Finset.sum_nonneg fun j _ => hnonneg i j)).mp henergy
  have hentry := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => hnonneg j k)).mp
    (hrows j (Finset.mem_univ _)) i (Finset.mem_univ _)
  have hdiff := (mul_eq_zero.mp hentry).resolve_left (Complex.normSq_pos.mpr hz).ne'
  have he := sub_eq_zero.mp (sq_eq_zero_iff.mp hdiff)
  rw [he, mul_comm]

/-- A normal relative product preserves the eigenspaces of the first
summand's Gram matrix. -/
theorem commute_gram_of_normal_relative (a : ι → ℂ) (W : Matrix ι ι ℂ)
    (hW : IsStarNormal W) (hB : IsStarNormal (diagonal a * W)) :
    Commute ((diagonal a)ᴴ * diagonal a) W :=
  commute_gram_of_balanced_relative a W (normal_row_col_energy W hW) hB

/-- If two normal factors have normal product, the first factor commutes
with the second factor's Gram matrix. Zero eigenvalues are allowed. -/
theorem commute_right_gram_of_normal_product (a : ι → ℂ) (W : Matrix ι ι ℂ)
    (hW : IsStarNormal W) (hAW : IsStarNormal (diagonal a * W)) :
    Commute (diagonal a) (Wᴴ * W) := by
  let A := diagonal a
  let P := Aᴴ * A
  let Q := Wᴴ * W
  have hPW : Commute P W := commute_gram_of_normal_relative a W hW hAW
  have hP : Pᴴ = P := by simp only [P, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose]
  have hQ : Qᴴ = Q := by simp only [Q, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose]
  have hstar : Wᴴ * P = P * Wᴴ := by
    have he := hPW.star_star.eq
    change Pᴴ * Wᴴ = Wᴴ * Pᴴ at he
    rw [hP] at he
    exact he.symm
  have hPQ : P * Q = (A * W)ᴴ * (A * W) := by
    calc
      _ = (P * Wᴴ) * W := by simp only [Q, Matrix.mul_assoc]
      _ = (Wᴴ * P) * W := by rw [hstar]
      _ = _ := by simp only [P, Matrix.conjTranspose_mul, Matrix.mul_assoc]
  have hsandwich : A * Q * Aᴴ = P * Q := by
    calc
      _ = (A * W) * (A * W)ᴴ := by
        rw [show Q = W * Wᴴ from hW.star_comm_self.eq]
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := hAW.star_comm_self.eq.symm.trans hPQ.symm
  have hentry (i j : ι) (hi : a i ≠ 0) (hq : Q i j ≠ 0) : a i = a j := by
    have he := congrArg (fun M : Matrix ι ι ℂ => M i j) hsandwich
    simp only [A, P, Matrix.diagonal_conjTranspose, Matrix.mul_diagonal,
      Matrix.diagonal_mul, Matrix.diagonal_mul_diagonal, Pi.star_apply, Pi.mul_apply] at he
    have hz : (a i * Q i j) * (star (a j) - star (a i)) = 0 := by
      linear_combination he
    exact (star_injective (sub_eq_zero.mp
      ((mul_eq_zero.mp hz).resolve_left (mul_ne_zero hi hq)))).symm
  change A * Q = Q * A
  ext i j : 1
  rw [show A = diagonal a from rfl, Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases hq : Q i j = 0
  · rw [hq, mul_zero, zero_mul]
  have hqji : Q j i ≠ 0 := by
    intro hz
    have he := congrArg (fun M : Matrix ι ι ℂ => M i j) hQ
    change star (Q j i) = Q i j at he
    rw [hz, star_zero] at he
    exact hq he.symm
  have haij : a i = a j := by
    by_cases hi : a i = 0
    · by_cases hj : a j = 0
      · exact hi.trans hj.symm
      · exact (hentry j i hj hqji).symm
    · exact hentry i j hi hq
  rw [haij, mul_comm]

/-- Commutation with the opposite Gram matrices makes the product normal. -/
theorem isStarNormal_mul_of_commuting_grams (A B : Matrix ι ι ℂ)
    (hA : IsStarNormal A) (hB : IsStarNormal B)
    (hAQ : Commute A (Bᴴ * B)) (hBP : Commute B (Aᴴ * A)) : IsStarNormal (A * B) := by
  have hAe : Aᴴ * A = A * Aᴴ := hA.star_comm_self.eq
  have hBe : Bᴴ * B = B * Bᴴ := hB.star_comm_self.eq
  constructor
  change (A * B)ᴴ * (A * B) = (A * B) * (A * B)ᴴ
  calc
    _ = Bᴴ * ((Aᴴ * A) * B) := by simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = (Bᴴ * B) * (Aᴴ * A) := by rw [← hBP.eq, Matrix.mul_assoc]
    _ = (Bᴴ * B) * (A * Aᴴ) := by rw [hAe]
    _ = (A * (Bᴴ * B)) * Aᴴ := by rw [← Matrix.mul_assoc, ← hAQ.eq]
    _ = _ := by rw [hBe]; simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]

/-- If the normal summands have scalar common commutant and `diagonal a`
is invertible, the relative product is energy-balanced in this eigenbasis
exactly when the first spectrum has constant modulus. -/
theorem balanced_relative_iff_constant_normSq (a : ι → ℂ) (W : Matrix ι ι ℂ)
    (ha : ∀ i, a i ≠ 0) (hB : IsStarNormal (diagonal a * W))
    (hcentral : ∀ Y : Matrix ι ι ℂ, Commute (diagonal a) Y →
      Commute (diagonal a * W) Y → ∃ c : ℂ, Y = c • (1 : Matrix ι ι ℂ)) :
    (∀ i, (∑ j, Complex.normSq (W i j)) = ∑ j, Complex.normSq (W j i)) ↔
      ∃ r : ℝ, ∀ i, Complex.normSq (a i) = r := by
  constructor
  · intro hW
    let P := (diagonal a)ᴴ * diagonal a
    have hAP : Commute (diagonal a) P := by
      change Commute (diagonal a) ((diagonal a)ᴴ * diagonal a)
      rw [diagonal_normSq_gram]
      change diagonal a * diagonal _ = diagonal _ * diagonal a
      rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
      exact congrArg diagonal (funext fun i => mul_comm _ _)
    have hWP : Commute W P := (commute_gram_of_balanced_relative a W hW hB).symm
    obtain ⟨c, hc⟩ := hcentral P hAP (hAP.mul_left hWP)
    refine ⟨c.re, fun i => ?_⟩
    change (diagonal a)ᴴ * diagonal a = _ at hc
    rw [diagonal_normSq_gram] at hc
    simpa only [Matrix.diagonal_apply_eq, Matrix.smul_apply, smul_eq_mul,
      Matrix.one_apply_eq, mul_one, Complex.ofReal_re] using
      congrArg (fun M : Matrix ι ι ℂ => (M i i).re) hc
  · rintro ⟨r, hr⟩ i
    have hrne : r ≠ 0 := by
      rw [← hr i]
      exact (Complex.normSq_pos.mpr (ha i)).ne'
    have he := normal_row_col_energy (diagonal a * W) hB i
    simp only [Matrix.diagonal_mul, Complex.normSq_mul, hr, ← Finset.mul_sum] at he
    exact mul_left_cancel₀ hrne he

/-- With an invertible diagonal first summand and a normal relative product,
the Gram matrices of both summands lie in the common commutant. -/
theorem common_grams_of_normal_relative (a : ι → ℂ) (W : Matrix ι ι ℂ)
    (hA : IsUnit (diagonal a).det) (hW : IsStarNormal W)
    (hB : IsStarNormal (diagonal a * W)) :
    let A := diagonal a
    let B := A * W
    Commute A (Aᴴ * A) ∧ Commute B (Aᴴ * A) ∧
      Commute A (Bᴴ * B) ∧ Commute B (Bᴴ * B) := by
  intro A B
  let P := Aᴴ * A
  let Q := Wᴴ * W
  have haa : Commute Aᴴ A := by
    change (diagonal a)ᴴ * diagonal a = diagonal a * (diagonal a)ᴴ
    rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    exact congrArg diagonal (funext fun i => mul_comm _ _)
  have hww : Commute Wᴴ W := hW.star_comm_self
  have hbb : Commute Bᴴ B := hB.star_comm_self
  have hAP : Commute A P := haa.symm.mul_right (Commute.refl A)
  have hPW : Commute P W := commute_gram_of_normal_relative a W hW hB
  have hBP : Commute B P := hAP.mul_left hPW.symm
  have hPQ : P * Q = Bᴴ * B := by
    have hwc : Wᴴ * P = P * Wᴴ := by
      have h := hPW.star_star
      change Pᴴ * Wᴴ = Wᴴ * Pᴴ at h
      have hP : Pᴴ = P := by simp [P, Matrix.conjTranspose_mul]
      rw [hP] at h
      exact h.symm
    calc
      _ = (P * Wᴴ) * W := by simp only [Q, Matrix.mul_assoc]
      _ = (Wᴴ * P) * W := by rw [hwc]
      _ = _ := by simp only [P, B, Matrix.conjTranspose_mul, Matrix.mul_assoc]
  have hAQAh : A * Q * Aᴴ = B * Bᴴ := by
    calc
      _ = A * (W * Wᴴ) * Aᴴ := by dsimp only [Q]; rw [hww.eq]
      _ = _ := by simp only [B, Matrix.conjTranspose_mul, Matrix.mul_assoc]
  have hQstar : Commute Q Aᴴ := by
    change Q * Aᴴ = Aᴴ * Q
    have he : A * (Q * Aᴴ) = A * (Aᴴ * Q) := calc
      _ = A * Q * Aᴴ := (Matrix.mul_assoc A Q Aᴴ).symm
      _ = P * Q := hAQAh.trans (hbb.eq.symm.trans hPQ.symm)
      _ = _ := by simp only [P, haa.eq, Matrix.mul_assoc]
    have hi := congrArg (fun M : Matrix ι ι ℂ => A⁻¹ * M) he
    simpa only [← Matrix.mul_assoc A⁻¹ A, A.nonsing_inv_mul hA, Matrix.one_mul] using hi
  have hQ : Qᴴ = Q := by simp [Q, Matrix.conjTranspose_mul]
  have hAQ : Commute A Q := by
    have h := hQstar.star_star
    change Commute Qᴴ (Aᴴ)ᴴ at h
    simpa only [hQ, Matrix.conjTranspose_conjTranspose] using h.symm
  refine ⟨hAP, hBP, ?_, hbb.symm.mul_right (Commute.refl B)⟩
  rw [← hPQ]
  exact hAP.mul_right hAQ

/-- If both `A` and `A * W` are normal and `W` is unitary, the Gram matrix
of `A` commutes with both summands. With scalar common commutant it is scalar. -/
theorem scalar_gram_of_normal_unitary_product (A W : Matrix ι ι ℂ)
    (hA : IsStarNormal A) (hB : IsStarNormal (A * W)) (hW : IsUnitary W)
    (hcentral : ∀ Y : Matrix ι ι ℂ, Commute A Y → Commute (A * W) Y →
      ∃ c : ℂ, Y = c • (1 : Matrix ι ι ℂ)) :
    ∃ c : ℂ, Aᴴ * A = c • (1 : Matrix ι ι ℂ) := by
  let G := Aᴴ * A
  have hAeq : G = A * Aᴴ := hA.star_comm_self.eq
  have hBeq : (A * W)ᴴ * (A * W) = (A * W) * (A * W)ᴴ := hB.star_comm_self.eq
  have hfix : Wᴴ * G * W = G := calc
    _ = (A * W)ᴴ * (A * W) := by simp only [G, Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = (A * W) * (A * W)ᴴ := hBeq
    _ = A * (W * Wᴴ) * Aᴴ := by simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = G := by rw [hW.1, Matrix.mul_one, ← hAeq]
  have hAW : Commute W G := by
    change W * G = G * W
    calc
      _ = W * (Wᴴ * G * W) := by rw [hfix]
      _ = _ := by simp only [← Matrix.mul_assoc, hW.1, Matrix.one_mul]
  have hAG : Commute A G := hA.star_comm_self.symm.mul_right (Commute.refl A)
  exact hcentral G hAG (hAG.mul_left hAW)

end MOC
