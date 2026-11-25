import MOC.Core
import Mathlib.Data.Matrix.Rank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination

/-! The inverse-coordinate determinant of a spectral matching profile. -/

open BigOperators Matrix

namespace MOC
namespace SpectralProfile

noncomputable section

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- The signed Leibniz evaluation of a matching profile. -/
def signedEvaluation (g : Equiv.Perm κ → ℂ) (S : Matrix κ κ ℂ) : ℂ :=
  ∑ σ, ((Equiv.Perm.sign σ : ℤ) : ℂ) * g σ * ∏ j, S (σ j) j

theorem signedEvaluation_matchingProduct (a b : κ → ℂ) (S : Matrix κ κ ℂ) :
    signedEvaluation (matchingProduct a b) S = (diagonal a * S + S * diagonal b).det := by
  rw [signedEvaluation, Matrix.det_apply']
  apply Finset.sum_congr rfl
  intro σ _
  have hentry (j : κ) :
      (diagonal a * S + S * diagonal b) (σ j) j = (a (σ j) + b j) * S (σ j) j := by
    simp only [Matrix.add_apply, Matrix.diagonal_mul, Matrix.mul_diagonal]
    ring
  simp only [hentry, Finset.prod_mul_distrib, matchingProduct]
  ring

/-- The bordered matrix used after removing the constant coordinate. -/
def border (u : Matrix (Fin 1) κ ℂ) (v : Matrix κ (Fin 1) ℂ)
    (T : Matrix κ κ ℂ) : Matrix (Fin 1 ⊕ κ) (Fin 1 ⊕ κ) ℂ :=
  fromBlocks 0 u v T

/-- Embed a matrix on the complementary coordinates, with zero constant row and column. -/
def centeredEmbed (E C : Matrix (Fin 1 ⊕ κ) (Fin 1 ⊕ κ) ℂ) (K : Matrix κ κ ℂ) :
    Matrix (Fin 1 ⊕ κ) (Fin 1 ⊕ κ) ℂ :=
  E * fromBlocks (0 : Matrix (Fin 1) (Fin 1) ℂ) 0 0 K * C

/-- The inverse-coordinate core is complex linear in the transpose-inverse variable. -/
def inverseCore (A B : Matrix κ κ ℂ) : Matrix κ κ ℂ →ₗ[ℂ] Matrix κ κ ℂ where
  toFun H := Hᵀ * A + B * Hᵀ
  map_add' H J := by
    simp only [Matrix.transpose_add, Matrix.add_mul, Matrix.mul_add]
    abel
  map_smul' c H := by
    simp only [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_add] <;> rfl

private theorem det_inverse_border
    (u : Matrix (Fin 1) κ ℂ) (v : Matrix κ (Fin 1) ℂ)
    (A B K H : Matrix κ κ ℂ) (hHK : Hᵀ * K = 1) (hKH : K * Hᵀ = 1) :
    (border (u * K) (K * v) (A * K + K * B)).det =
      K.det ^ 2 * (border u v (inverseCore A B H)).det := by
  let D : Matrix (Fin 1 ⊕ κ) (Fin 1 ⊕ κ) ℂ := fromBlocks 1 0 0 K
  have hD : D.det = K.det := by
    dsimp only [D]
    rw [Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, one_mul]
  have hM : D * border u v (inverseCore A B H) * D =
      border (u * K) (K * v) (A * K + K * B) := by
    simp only [D, border, Matrix.fromBlocks_multiply, inverseCore, LinearMap.coe_mk,
      AddHom.coe_mk, Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul, Matrix.mul_zero,
      add_zero, zero_add]
    congr 1
    rw [Matrix.mul_add, ← Matrix.mul_assoc K Hᵀ A, hKH, Matrix.one_mul,
      Matrix.add_mul, Matrix.mul_assoc (K * B) Hᵀ K, hHK, Matrix.mul_one]
  rw [← hM, Matrix.det_mul, Matrix.det_mul, hD]
  ring

/-- The bordered polynomial agrees with the signed spectral evaluation
after clearing the square of the original determinant. -/
theorem signedEvaluation_inverseCoordinates
    (a b : Fin 1 ⊕ κ → ℂ) (E C : Matrix (Fin 1 ⊕ κ) (Fin 1 ⊕ κ) ℂ)
    (hEC : E * C = 1) (hCE : C * E = 1) (K H : Matrix κ κ ℂ)
    (hHK : Hᵀ * K = 1) (hKH : K * Hᵀ = 1) :
    let A := C * diagonal a * E
    let B := C * diagonal b * E
    signedEvaluation (matchingProduct a b) (centeredEmbed E C K) =
      K.det ^ 2 * (border A.toBlocks₁₂ B.toBlocks₂₁
        (inverseCore A.toBlocks₂₂ B.toBlocks₂₂ H)).det := by
  intro A B
  let D : Matrix (Fin 1 ⊕ κ) (Fin 1 ⊕ κ) ℂ := fromBlocks 0 0 0 K
  have hA : E * A = diagonal a * E := by
    dsimp only [A]
    rw [← Matrix.mul_assoc E (C * diagonal a) E, ← Matrix.mul_assoc E C (diagonal a)]
    rw [hEC, Matrix.one_mul]
  have hB : B * C = C * diagonal b := by
    dsimp only [B]
    rw [Matrix.mul_assoc (C * diagonal b) E C, hEC, Matrix.mul_one]
  have hWeighted : diagonal a * centeredEmbed E C K + centeredEmbed E C K * diagonal b =
      E * (A * D + D * B) * C := by
    change diagonal a * (E * D * C) + (E * D * C) * diagonal b =
      E * (A * D + D * B) * C
    have hleft : E * (A * D) * C = diagonal a * (E * D * C) := by
      rw [← Matrix.mul_assoc E A D, hA]
      simp only [Matrix.mul_assoc]
    have hright : E * (D * B) * C = (E * D * C) * diagonal b := by
      calc
        _ = (E * D) * (B * C) := by simp only [Matrix.mul_assoc]
        _ = _ := by rw [hB, ← Matrix.mul_assoc]
    rw [Matrix.mul_add, Matrix.add_mul, hleft, hright]
  have hD : A * D + D * B =
      border (A.toBlocks₁₂ * K) (K * B.toBlocks₂₁)
        (A.toBlocks₂₂ * K + K * B.toBlocks₂₂) := by
    conv_lhs =>
      rw [← Matrix.fromBlocks_toBlocks A, ← Matrix.fromBlocks_toBlocks B]
    simp only [D, border, Matrix.fromBlocks_multiply, Matrix.fromBlocks_add,
      Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
  have hdet : E.det * C.det = 1 := by rw [← Matrix.det_mul, hEC, Matrix.det_one]
  rw [signedEvaluation_matchingProduct, hWeighted, Matrix.det_mul, Matrix.det_mul,
    mul_right_comm, hdet, one_mul, hD]
  exact det_inverse_border _ _ _ _ _ _ hHK hKH

theorem signedEvaluation_inverse
    (a b : Fin 1 ⊕ κ → ℂ) (E C : Matrix (Fin 1 ⊕ κ) (Fin 1 ⊕ κ) ℂ)
    (hEC : E * C = 1) (hCE : C * E = 1) (K : Matrix κ κ ℂ)
    (hK : IsUnit K.det) :
    let A := C * diagonal a * E
    let B := C * diagonal b * E
    signedEvaluation (matchingProduct a b) (centeredEmbed E C K) / K.det ^ 2 =
      (border A.toBlocks₁₂ B.toBlocks₂₁
        (inverseCore A.toBlocks₂₂ B.toBlocks₂₂ ((K⁻¹)ᵀ))).det := by
  intro A B
  have hHK : ((K⁻¹)ᵀ)ᵀ * K = 1 := by rw [Matrix.transpose_transpose, Matrix.nonsing_inv_mul K hK]
  have hKH : K * ((K⁻¹)ᵀ)ᵀ = 1 := by rw [Matrix.transpose_transpose, Matrix.mul_nonsing_inv K hK]
  apply (div_eq_iff (pow_ne_zero 2 hK.ne_zero)).mpr
  rw [mul_comm]
  exact signedEvaluation_inverseCoordinates a b E C hEC hCE K ((K⁻¹)ᵀ) hHK hKH

theorem signedEvaluation_const_centeredEmbed
    (c : ℂ) (E C : Matrix (Fin 1 ⊕ κ) (Fin 1 ⊕ κ) ℂ) (K : Matrix κ κ ℂ) :
    signedEvaluation (fun _ => c) (centeredEmbed E C K) = 0 := by
  let S := centeredEmbed E C K
  have hD : (fromBlocks (0 : Matrix (Fin 1) (Fin 1) ℂ)
      (0 : Matrix (Fin 1) κ ℂ) (0 : Matrix κ (Fin 1) ℂ) K).det = 0 := by
    rw [Matrix.det_fromBlocks_zero₂₁,
      Matrix.det_zero (show Nonempty (Fin 1) from ⟨0⟩), zero_mul]
  have hS : S.det = 0 := by
    simp only [S, centeredEmbed, Matrix.det_mul, hD, mul_zero, zero_mul]
  have h : signedEvaluation (fun _ => c) S = c * S.det := by
    rw [signedEvaluation, Matrix.det_apply', Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro σ _
    ring
  rw [h, hS, mul_zero]

private theorem det_eliminate_border
    (A Ai : Matrix (Fin 2) (Fin 2) ℂ) (B : Matrix (Fin 2) κ ℂ)
    (C : Matrix κ (Fin 2) ℂ) (D : Matrix κ κ ℂ) (hAi : Ai * A = 1) :
    (fromBlocks A B C D).det = A.det * (D - C * Ai * B).det := by
  let L : Matrix (Fin 2 ⊕ κ) (Fin 2 ⊕ κ) ℂ := fromBlocks 1 0 (-(C * Ai)) 1
  have hL : L.det = 1 := by
    dsimp only [L]
    rw [Matrix.det_fromBlocks_zero₁₂, Matrix.det_one, Matrix.det_one, one_mul]
  have hkill : -(C * Ai) * A + C = 0 := by
    rw [Matrix.neg_mul, Matrix.mul_assoc, hAi, Matrix.mul_one, neg_add_cancel]
  have hcorner : -(C * Ai) * B + D = D - C * Ai * B := by
    rw [Matrix.neg_mul, sub_eq_add_neg, add_comm]
  have hP : L * fromBlocks A B C D = fromBlocks A B 0 (D - C * Ai * B) := by
    simp only [L, Matrix.fromBlocks_multiply, Matrix.one_mul, Matrix.zero_mul, add_zero,
      hkill, hcorner]
  have h := congrArg Matrix.det hP
  rwa [Matrix.det_mul, hL, one_mul, Matrix.det_fromBlocks_zero₂₁] at h

private def borderMinor (u : Matrix (Fin 1) (Fin 1 ⊕ κ) ℂ)
    (v : Matrix (Fin 1 ⊕ κ) (Fin 1) ℂ) :
    Matrix (Fin 1 ⊕ κ) (Fin 1 ⊕ κ) ℂ →ₗ[ℂ] Matrix κ κ ℂ where
  toFun T i j :=
    T (.inr i) (.inr j) -
      v (.inr i) 0 / v (.inl 0) 0 * T (.inl 0) (.inr j) -
      T (.inr i) (.inl 0) * (u 0 (.inr j) / u 0 (.inl 0)) +
      v (.inr i) 0 / v (.inl 0) 0 * T (.inl 0) (.inl 0) *
        (u 0 (.inr j) / u 0 (.inl 0))
  map_add' X Y := by
    ext i j
    simp only [Matrix.add_apply]
    ring
  map_smul' c X := by
    ext i j
    simp only [Matrix.smul_apply, smul_eq_mul]
    ring

private theorem border_det_at_first_pivots
    (u : Matrix (Fin 1) (Fin 1 ⊕ κ) ℂ) (v : Matrix (Fin 1 ⊕ κ) (Fin 1) ℂ)
    (hu : u 0 (.inl 0) ≠ 0) (hv : v (.inl 0) 0 ≠ 0)
    (T : Matrix (Fin 1 ⊕ κ) (Fin 1 ⊕ κ) ℂ) :
    (border u v T).det = -(u 0 (.inl 0) * v (.inl 0) 0) * (borderMinor u v T).det := by
  let p := u 0 (.inl 0)
  let q := v (.inl 0) 0
  let t := T (.inl 0) (.inl 0)
  let A : Matrix (Fin 2) (Fin 2) ℂ := !![0, p; q, t]
  let Ai : Matrix (Fin 2) (Fin 2) ℂ := !![-t / (p * q), 1 / q; 1 / p, 0]
  let X : Matrix (Fin 2) κ ℂ := fun i j => ![u 0 (.inr j), T (.inl 0) (.inr j)] i
  let Y : Matrix κ (Fin 2) ℂ := fun i j => ![v (.inr i) 0, T (.inr i) (.inl 0)] j
  let D : Matrix κ κ ℂ := T.submatrix Sum.inr Sum.inr
  let e : Fin 2 ⊕ κ ≃ Fin 1 ⊕ (Fin 1 ⊕ κ) :=
    (Equiv.sumCongr (finSumFinEquiv.symm : Fin 2 ≃ Fin 1 ⊕ Fin 1) (Equiv.refl κ)).trans
      (Equiv.sumAssoc (Fin 1) (Fin 1) κ)
  have hp : p ≠ 0 := hu
  have hq : q ≠ 0 := hv
  have he₀ : e (.inl 0) = .inl 0 := rfl
  have he₁ : e (.inl 1) = .inr (.inl 0) := rfl
  have he₂ (i : κ) : e (.inr i) = .inr (.inr i) := rfl
  have hBlocks : (border u v T).submatrix e e = fromBlocks A X Y D := by
    ext (i | i) (j | j)
    · fin_cases i <;> fin_cases j <;>
        simp [Matrix.submatrix_apply, he₀, he₁, border, A, p, q, t]
    · fin_cases i <;> simp [Matrix.submatrix_apply, he₀, he₁, he₂, border, X]
    · fin_cases j <;> simp [Matrix.submatrix_apply, he₀, he₁, he₂, border, Y]
    · simp [Matrix.submatrix_apply, he₂, border, D]
  have hAi : Ai * A = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Ai, A, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] <;>
      field_simp [hp, hq] <;> ring
  have hA : A.det = -(p * q) := by
    simp [A, Matrix.det_fin_two]
  have hD : D - Y * Ai * X = borderMinor u v T := by
    ext i j
    change (D - Y * Ai * X) i j =
      T (.inr i) (.inr j) -
        v (.inr i) 0 / q * T (.inl 0) (.inr j) -
        T (.inr i) (.inl 0) * (u 0 (.inr j) / p) +
        v (.inr i) 0 / q * t * (u 0 (.inr j) / p)
    simp only [D, Matrix.submatrix_apply, Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_two,
      X, Y, Ai, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.of_apply]
    field_simp [hp, hq] <;> ring
  rw [← Matrix.det_submatrix_equiv_self e (border u v T), hBlocks,
    det_eliminate_border A Ai X Y D hAi, hA, hD]

private def doubleSubmatrixLinear {n : ℕ}
    (r c : Fin 1 ⊕ Fin n ≃ Fin (n + 1)) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ →ₗ[ℂ]
      Matrix (Fin 1 ⊕ Fin n) (Fin 1 ⊕ Fin n) ℂ where
  toFun T := T.submatrix r c
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The determinant of a zero-corner border is a constant times a determinant
on one fewer coordinate of the core. The new core is linear in the old one. -/
theorem border_det_small {n : ℕ}
    (u : Matrix (Fin 1) (Fin (n + 1)) ℂ) (v : Matrix (Fin (n + 1)) (Fin 1) ℂ) :
    ∃ c : ℂ, ∃ F : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ,
      ∀ T : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, (border u v T).det = c * (F T).det := by
  classical
  by_cases hu : ∃ j, u 0 j ≠ 0
  · by_cases hv : ∃ i, v i 0 ≠ 0
    · obtain ⟨j, hj⟩ := hu
      obtain ⟨i, hi⟩ := hv
      let e : Fin 1 ⊕ Fin n ≃ Fin (n + 1) :=
        finSumFinEquiv.trans (finCongr (Nat.add_comm 1 n))
      let p := Equiv.swap (e (.inl 0)) i
      let q := Equiv.swap (e (.inl 0)) j
      let P : Equiv.Perm (Fin 1 ⊕ Fin (n + 1)) := Equiv.sumCongr (Equiv.refl _) p
      let Q : Equiv.Perm (Fin 1 ⊕ Fin (n + 1)) := Equiv.sumCongr (Equiv.refl _) q
      let r := e.trans p
      let c := e.trans q
      let u' := u.submatrix id c
      let v' := v.submatrix r id
      have hu' : u' 0 (.inl 0) ≠ 0 := by
        simpa only [u', c, Matrix.submatrix_apply, Equiv.trans_apply, Equiv.swap_apply_left, id_eq]
          using hj
      have hv' : v' (.inl 0) 0 ≠ 0 := by
        simpa only [v', r, Matrix.submatrix_apply, Equiv.trans_apply, Equiv.swap_apply_left, id_eq]
          using hi
      let sp : ℂ := ((Equiv.Perm.sign P.symm : ℤ) : ℂ)
      let sq : ℂ := ((Equiv.Perm.sign Q.symm : ℤ) : ℂ)
      refine ⟨sq * sp * -(u' 0 (.inl 0) * v' (.inl 0) 0),
        (borderMinor u' v').comp (doubleSubmatrixLinear r c), fun T => ?_⟩
      let M := border u v T
      let M' := M.submatrix P Q
      let e' : Fin 1 ⊕ (Fin 1 ⊕ Fin n) ≃ Fin 1 ⊕ Fin (n + 1) :=
        Equiv.sumCongr (Equiv.refl _) e
      have hM' : M'.submatrix e' e' = border u' v' (T.submatrix r c) := by
        ext (a | a) (b | b) <;> rfl
      have hrestore : (M'.submatrix P.symm id).submatrix id Q.symm = M := by
        ext a b
        simp only [M', Matrix.submatrix_apply, id_eq, Equiv.apply_symm_apply]
      have hdet : M.det = sq * (sp * M'.det) := by
        rw [← hrestore, Matrix.det_permute', Matrix.det_permute] <;> rfl
      have hsmall : M'.det = -(u' 0 (.inl 0) * v' (.inl 0) 0) *
          (borderMinor u' v' (T.submatrix r c)).det := by
        rw [← Matrix.det_submatrix_equiv_self e' M', hM']
        exact border_det_at_first_pivots u' v' hu' hv' (T.submatrix r c)
      change M.det = _ * (borderMinor u' v' (T.submatrix r c)).det
      rw [hdet, hsmall]
      ring
    · refine ⟨0, 0, fun T => ?_⟩
      rw [zero_mul]
      apply Matrix.det_eq_zero_of_column_eq_zero (j := Sum.inl 0)
      rintro (i | i)
      · rfl
      · exact not_not.mp (fun hi => hv ⟨i, hi⟩)
  · refine ⟨0, 0, fun T => ?_⟩
    rw [zero_mul]
    apply Matrix.det_eq_zero_of_row_eq_zero (i := Sum.inl 0)
    rintro (j | j)
    · rfl
    · exact not_not.mp (fun hj => hu ⟨j, hj⟩)

/-- In order `n + 2`, the inverse-coordinate spectral polynomial is
a determinant of order `n` with complex-linear entries. -/
theorem actualInverseProfile_small {n : ℕ}
    (a b : Fin 1 ⊕ Fin (n + 1) → ℂ)
    (E C : Matrix (Fin 1 ⊕ Fin (n + 1)) (Fin 1 ⊕ Fin (n + 1)) ℂ) :
    let A := C * diagonal a * E
    let B := C * diagonal b * E
    ∃ c : ℂ, ∃ F : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ,
      ∀ H, (border A.toBlocks₁₂ B.toBlocks₂₁ (inverseCore A.toBlocks₂₂ B.toBlocks₂₂ H)).det =
        c * (F H).det := by
  intro A B
  obtain ⟨c, F, h⟩ := border_det_small A.toBlocks₁₂ B.toBlocks₂₁
  exact ⟨c, F.comp (inverseCore A.toBlocks₂₂ B.toBlocks₂₂),
    fun H => h (inverseCore A.toBlocks₂₂ B.toBlocks₂₂ H)⟩

private def matrixEntry {V : Type*} [AddCommGroup V] [Module ℂ V]
    (T : V →ₗ[ℂ] Matrix (Fin 2) (Fin 2) ℂ) (i j : Fin 2) : V →ₗ[ℂ] ℂ where
  toFun x := T x i j
  map_add' x y := by rw [map_add, Matrix.add_apply]
  map_smul' c x := by rw [map_smul, Matrix.smul_apply] <;> rfl

/-- In order four, the bordered polynomial times any complex phase is
the sum of four squares of complex linear functions. -/
theorem border_det_four_complex_squares {V : Type*} [AddCommGroup V] [Module ℂ V]
    (u : Matrix (Fin 1) (Fin 3) ℂ) (v : Matrix (Fin 3) (Fin 1) ℂ)
    (T : V →ₗ[ℂ] Matrix (Fin 3) (Fin 3) ℂ) (η : ℂ) :
    ∃ L : Fin 4 → V →ₗ[ℂ] ℂ, ∀ x, η * (border u v (T x)).det = ∑ i, (L i x) ^ 2 := by
  obtain ⟨c, F, hF⟩ := border_det_small (n := 2) u v
  let A := (η * c) • matrixEntry (F.comp T) 0 0
  let B := (η * c) • matrixEntry (F.comp T) 0 1
  let C := matrixEntry (F.comp T) 1 0
  let D := matrixEntry (F.comp T) 1 1
  let L : Fin 4 → V →ₗ[ℂ] ℂ :=
    ![(1 / 2 : ℂ) • (A + D), Complex.I • ((1 / 2 : ℂ) • (A - D)),
      (1 / 2 : ℂ) • (B - C), Complex.I • ((1 / 2 : ℂ) • (B + C))]
  refine ⟨L, fun x => ?_⟩
  rw [hF (T x), Matrix.det_fin_two, Fin.sum_univ_four]
  simp only [L, A, B, C, D, Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one,
    LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    matrixEntry, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.comp_apply, smul_eq_mul]
  simp only [mul_pow, Complex.I_sq]
  ring

private theorem positive_dimension_le_four_from_squares {W : Type*}
    [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ W]
    (P N : Fin 4 → W →ₗ[ℝ] ℝ)
    (hpos : ∀ x : W, x ≠ 0 → 0 < (∑ i, (P i x) ^ 2) - ∑ i, (N i x) ^ 2) :
    Module.finrank ℝ W ≤ 4 := by
  let S : W →ₗ[ℝ] (Fin 4 → ℝ) := LinearMap.pi P
  have hS : Function.Injective S := by
    intro x y hxy
    apply sub_eq_zero.mp
    by_contra hne
    have hz : S (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    have hf (i : Fin 4) : P i (x - y) = 0 := congrFun hz i
    have hN : 0 ≤ ∑ i, (N i (x - y)) ^ 2 :=
      Finset.sum_nonneg (fun i _ => sq_nonneg _)
    have h := hpos (x - y) hne
    simp only [hf, zero_pow (by decide : (2 : ℕ) ≠ 0), Finset.sum_const_zero, zero_sub] at h
    exact (not_lt_of_ge (neg_nonpos.mpr hN)) h
  simpa only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] using
    LinearMap.finrank_le_finrank_of_injective hS

/-- Each strictly positive or strictly negative real subspace for the
order-four source polynomial has dimension at most four. The sign is
absorbed into the phase, so the same theorem covers both indices. -/
theorem border_det_four_positive_dimension
    {V W : Type*} [AddCommGroup V] [Module ℂ V] [Module ℝ V] [IsScalarTower ℝ ℂ V]
    [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ W]
    (u : Matrix (Fin 1) (Fin 3) ℂ) (v : Matrix (Fin 3) (Fin 1) ℂ)
    (T : V →ₗ[ℂ] Matrix (Fin 3) (Fin 3) ℂ) (η : ℂ) (J : W →ₗ[ℝ] V)
    (hpos : ∀ x : W, x ≠ 0 → 0 < (η * (border u v (T (J x))).det).re) :
    Module.finrank ℝ W ≤ 4 := by
  obtain ⟨L, hL⟩ := border_det_four_complex_squares u v T η
  let P (i : Fin 4) : W →ₗ[ℝ] ℝ := Complex.reLm.comp (((L i).restrictScalars ℝ).comp J)
  let N (i : Fin 4) : W →ₗ[ℝ] ℝ := Complex.imLm.comp (((L i).restrictScalars ℝ).comp J)
  apply positive_dimension_le_four_from_squares P N
  intro x hx
  have h := hpos x hx
  rw [hL (J x), Complex.re_sum] at h
  simp only [pow_two, Complex.mul_re, Finset.sum_sub_distrib] at h
  change 0 < (∑ i, ((L i (J x)).re) ^ 2) - ∑ i, ((L i (J x)).im) ^ 2
  simpa only [pow_two] using h

theorem border_det_four_negative_dimension
    {V W : Type*} [AddCommGroup V] [Module ℂ V] [Module ℝ V] [IsScalarTower ℝ ℂ V]
    [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ W]
    (u : Matrix (Fin 1) (Fin 3) ℂ) (v : Matrix (Fin 3) (Fin 1) ℂ)
    (T : V →ₗ[ℂ] Matrix (Fin 3) (Fin 3) ℂ) (η : ℂ) (J : W →ₗ[ℝ] V)
    (hneg : ∀ x : W, x ≠ 0 → (η * (border u v (T (J x))).det).re < 0) :
    Module.finrank ℝ W ≤ 4 := by
  apply border_det_four_positive_dimension u v T (-η) J
  intro x hx
  simpa only [neg_mul, Complex.neg_re] using neg_pos.mpr (hneg x hx)

/-- A symmetric complex matrix of a form that is a sum of four linear
squares factors through a space of dimension four. -/
theorem rank_le_four_of_linear_squares (Q : Matrix κ κ ℂ) (hQ : Qᵀ = Q)
    (L : Fin 4 → (κ → ℂ) →ₗ[ℂ] ℂ)
    (hL : ∀ x : κ → ℂ, x ⬝ᵥ (Q *ᵥ x) = ∑ i, (L i x) ^ 2) : Q.rank ≤ 4 := by
  let C : Matrix κ (Fin 4) ℂ := fun i r => L r (Pi.single i 1)
  have hdiag (i : κ) : Q i i = ∑ r, (L r (Pi.single i 1)) ^ 2 := by
    simpa only [Matrix.mulVec_single_one, single_dotProduct, one_mul] using hL (Pi.single i 1)
  have heq : Q = C * Cᵀ := by
    ext i j
    have hsym : Q j i = Q i j := congrArg (fun M : Matrix κ κ ℂ => M i j) hQ
    have hexpand : (∑ r, (L r (Pi.single i 1 + Pi.single j 1)) ^ 2) =
        (∑ r, (L r (Pi.single i 1)) ^ 2) + (∑ r, (L r (Pi.single j 1)) ^ 2) +
          2 * (C * Cᵀ) i j := by
      rw [Matrix.mul_apply, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro r _
      simp only [map_add, C, Matrix.transpose_apply]
      ring
    have h := hL (Pi.single i 1 + Pi.single j 1)
    rw [hexpand, ← hdiag i, ← hdiag j] at h
    simp only [Matrix.mulVec_add, add_dotProduct, dotProduct_add, Matrix.mulVec_single_one,
      single_dotProduct, one_mul, hsym] at h
    linear_combination (1 / 2 : ℂ) * h
  rw [heq]
  simpa only [Fintype.card_fin] using
    (Matrix.rank_mul_le_left C Cᵀ).trans (Matrix.rank_le_card_width C)

/-- The rank bound applies to every symmetric coefficient matrix which
represents the actual bordered spectral polynomial. -/
theorem rank_le_four_of_border_det (Q : Matrix κ κ ℂ) (hQ : Qᵀ = Q)
    (u : Matrix (Fin 1) (Fin 3) ℂ) (v : Matrix (Fin 3) (Fin 1) ℂ)
    (T : (κ → ℂ) →ₗ[ℂ] Matrix (Fin 3) (Fin 3) ℂ) (η : ℂ)
    (hT : ∀ x : κ → ℂ, x ⬝ᵥ (Q *ᵥ x) = η * (border u v (T x)).det) : Q.rank ≤ 4 := by
  obtain ⟨L, hL⟩ := border_det_four_complex_squares u v T η
  exact rank_le_four_of_linear_squares Q hQ L (fun x => (hT x).trans (hL x))

private theorem exists_symmetric_matrix_of_linear_squares
    (L : Fin 4 → (κ → ℂ) →ₗ[ℂ] ℂ) :
    ∃ Q : Matrix κ κ ℂ, Qᵀ = Q ∧ Q.rank ≤ 4 ∧
      ∀ x : κ → ℂ, x ⬝ᵥ (Q *ᵥ x) = ∑ i, (L i x) ^ 2 := by
  let C : Matrix κ (Fin 4) ℂ := fun i r => L r (Pi.single i 1)
  have hrank : (C * Cᵀ).rank ≤ 4 := by
    simpa only [Fintype.card_fin] using
      (Matrix.rank_mul_le_left C Cᵀ).trans (Matrix.rank_le_card_width C)
  refine ⟨C * Cᵀ, by rw [Matrix.transpose_mul, Matrix.transpose_transpose], hrank, fun x => ?_⟩
  have hC : Cᵀ *ᵥ x = fun i => L i x := by
    funext r
    change (∑ i, C i r * x i) = L r x
    rw [LinearMap.pi_apply_eq_sum_univ (L r) x]
    apply Finset.sum_congr rfl
    intro i _
    have he : Pi.single i (1 : ℂ) = fun j => if i = j then 1 else 0 := by
      funext j
      simp [Pi.single_apply, eq_comm]
    simp only [C, he, smul_eq_mul, mul_comm]
  rw [← Matrix.mulVec_mulVec x C Cᵀ, dotProduct_mulVec, ← Matrix.mulVec_transpose, hC]
  simp only [dotProduct, pow_two]

private def tetrahedralFrameFin : Matrix (Fin 4) (Fin 4) ℂ :=
  (1 / 2 : ℂ) • !![1, 1, 1, 1; 1, 1, -1, -1; 1, -1, 1, -1; 1, -1, -1, 1]

/-- The tetrahedral coordinates, with the constant direction as the first column. -/
def tetrahedralFrame : Matrix (Fin 1 ⊕ Fin 3) (Fin 1 ⊕ Fin 3) ℂ :=
  tetrahedralFrameFin.submatrix finSumFinEquiv finSumFinEquiv

private theorem tetrahedralFrameFin_mul_transpose :
    tetrahedralFrameFin * tetrahedralFrameFinᵀ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [tetrahedralFrameFin, Matrix.mul_apply, Matrix.transpose_apply,
      Matrix.smul_apply, smul_eq_mul, Matrix.one_apply, Fin.sum_univ_four, Matrix.cons_val] <;> ring

theorem tetrahedralFrame_mul_transpose : tetrahedralFrame * tetrahedralFrameᵀ = 1 := by
  unfold tetrahedralFrame
  rw [Matrix.transpose_submatrix, Matrix.submatrix_mul_equiv,
    tetrahedralFrameFin_mul_transpose, Matrix.submatrix_one_equiv]

theorem tetrahedralFrame_transpose_mul : tetrahedralFrameᵀ * tetrahedralFrame = 1 :=
  Matrix.mul_eq_one_comm.mp tetrahedralFrame_mul_transpose

/-- The actual spectral polynomial, including singular inverse coordinates,
in the tetrahedral chart used for the order-four coefficient matrix. -/
def tetrahedralInverseProfile (a b : Fin 4 → ℂ) (H : Matrix (Fin 3) (Fin 3) ℂ) : ℂ :=
  let E := tetrahedralFrame
  let A := Eᵀ * diagonal (a ∘ finSumFinEquiv) * E
  let B := Eᵀ * diagonal (b ∘ finSumFinEquiv) * E
  (border A.toBlocks₁₂ B.toBlocks₂₁ (inverseCore A.toBlocks₂₂ B.toBlocks₂₂ H)).det

theorem tetrahedralInverseProfile_eq_signedEvaluation (a b : Fin 4 → ℂ)
    (K : Matrix (Fin 3) (Fin 3) ℂ) (hK : IsUnit K.det) :
    signedEvaluation (matchingProduct (a ∘ finSumFinEquiv) (b ∘ finSumFinEquiv))
      (centeredEmbed tetrahedralFrame tetrahedralFrameᵀ K) / K.det ^ 2 =
      tetrahedralInverseProfile a b ((K⁻¹)ᵀ) :=
  signedEvaluation_inverse (a ∘ finSumFinEquiv) (b ∘ finSumFinEquiv)
    tetrahedralFrame tetrahedralFrameᵀ tetrahedralFrame_mul_transpose
    tetrahedralFrame_transpose_mul K hK

theorem tetrahedralInverseProfile_four_squares (a b : Fin 4 → ℂ) (η : ℂ) :
    ∃ L : Fin 4 → Matrix (Fin 3) (Fin 3) ℂ →ₗ[ℂ] ℂ,
      ∀ H, η * tetrahedralInverseProfile a b H = ∑ i, (L i H) ^ 2 := by
  let E := tetrahedralFrame
  let A := Eᵀ * diagonal (a ∘ finSumFinEquiv) * E
  let B := Eᵀ * diagonal (b ∘ finSumFinEquiv) * E
  exact border_det_four_complex_squares A.toBlocks₁₂ B.toBlocks₂₁
    (inverseCore A.toBlocks₂₂ B.toBlocks₂₂) η

/-- A coefficient matrix for all nine entries of the tetrahedral variable. -/
theorem tetrahedralInverseProfile_exists_rank_four_matrix (a b : Fin 4 → ℂ) (η : ℂ) :
    ∃ Q : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ, Qᵀ = Q ∧ Q.rank ≤ 4 ∧
      ∀ x : Fin 3 × Fin 3 → ℂ,
        x ⬝ᵥ (Q *ᵥ x) = η * tetrahedralInverseProfile a b (fun i j => x (i, j)) := by
  let unvec : (Fin 3 × Fin 3 → ℂ) →ₗ[ℂ] Matrix (Fin 3) (Fin 3) ℂ where
    toFun x i j := x (i, j)
    map_add' _ _ := rfl
    map_smul' _ _ := rfl
  obtain ⟨L, hL⟩ := tetrahedralInverseProfile_four_squares a b η
  obtain ⟨Q, hQ, hr, hf⟩ := exists_symmetric_matrix_of_linear_squares (fun i => (L i).comp unvec)
  refine ⟨Q, hQ, hr, fun x => (hf x).trans ?_⟩
  exact (hL (unvec x)).symm

end

end SpectralProfile
end MOC
