import MOC.Geometry
import MOC.Normal
import MOC.Small
import Mathlib.Data.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-! Order-three pole compression with a normal effective matrix on the retained plane. -/

open BigOperators Matrix

namespace MOC

noncomputable section

/-- The two retained coordinates of a three-dimensional unitary conjugation. -/
def activeCompression (b : Unit ⊕ Fin 2 → ℂ)
    (U : Matrix (Unit ⊕ Fin 2) (Unit ⊕ Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (U * diagonal b * Uᴴ).toBlocks₂₂

/-- An assignment of two retained labels to the effective spectrum. -/
def effectiveCompressionVertex (x : Fin 2 → ℂ) (b : Unit ⊕ Fin 2 → ℂ)
    (σ : Equiv.Perm (Unit ⊕ Fin 2)) : ℂ :=
  ∏ k : Fin 2, (1 + x k * b (σ.symm (Sum.inr k)))

private theorem det_diagonal_activeCompression_mem_hull (x : Fin 2 → ℂ)
    (b : Unit ⊕ Fin 2 → ℂ) (U : Matrix (Unit ⊕ Fin 2) (Unit ⊕ Fin 2) ℂ)
    (hU : IsUnitary U) (hb : ∀ j, b j ≠ 0) :
    (1 + diagonal x * activeCompression b U).det ∈
      convexHull ℝ (Set.range (effectiveCompressionVertex x b)) := by
  let a : Unit ⊕ Fin 2 → ℂ := Sum.elim 0 x
  let c : Unit ⊕ Fin 2 → ℂ := fun j => (b j)⁻¹
  let B := U * diagonal b * Uᴴ
  let Bi := U * diagonal c * Uᴴ
  let K : ℂ := ∏ j, c j
  have hK : K ≠ 0 := Finset.prod_ne_zero_iff.mpr fun j _ => inv_ne_zero (hb j)
  have hdiag : diagonal b * diagonal c = 1 := by
    simp [c, Matrix.diagonal_mul_diagonal, mul_inv_cancel₀, hb]
  have hBi : B * Bi = 1 := by
    calc
      _ = U * (diagonal b * (Uᴴ * U) * diagonal c) * Uᴴ := by
        simp only [B, Bi, Matrix.mul_assoc]
      _ = _ := by rw [hU.2, Matrix.mul_one, hdiag, Matrix.mul_one, hU.1]
  have hA : diagonal a = fromBlocks (0 : Matrix Unit Unit ℂ) 0 0 (diagonal x) := by
    have hzero : diagonal (0 : Unit → ℂ) = 0 := by
      ext i j : 1
      simp [Matrix.diagonal_apply]
    dsimp only [a]
    rw [← Matrix.fromBlocks_diagonal, hzero]
  have hL : (1 + diagonal a * B).det = (1 + diagonal x * activeCompression b U).det := by
    have hblock : 1 + diagonal a * B = fromBlocks (1 : Matrix Unit Unit ℂ) 0
        (diagonal x * B.toBlocks₂₁) (1 + diagonal x * B.toBlocks₂₂) := by
      conv_lhs =>
        rw [hA, ← Matrix.fromBlocks_one (l := Unit) (m := Fin 2),
          ← Matrix.fromBlocks_toBlocks B, Matrix.fromBlocks_multiply, Matrix.fromBlocks_add]
      simp only [Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add]
    rw [hblock, Matrix.det_fromBlocks_zero₁₂, Matrix.det_one, one_mul]
    rfl
  have hD : determinantValue a c U = K * (1 + diagonal x * activeCompression b U).det := by
    change (diagonal a + Bi).det = _
    have hmul : (1 + diagonal a * B) * Bi = diagonal a + Bi := by
      rw [Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc, hBi, Matrix.mul_one]
      exact add_comm Bi (diagonal a)
    rw [← hmul, Matrix.det_mul, hL]
    have hdet : Bi.det = K := by
      rw [show Bi = U * diagonal c * Uᴴ from rfl, det_unitary_conjugation U _ hU,
        Matrix.det_diagonal]
    rw [hdet]
    exact mul_comm _ _
  have hvertex (σ : Equiv.Perm (Unit ⊕ Fin 2)) :
      matchingProduct a c σ = K * effectiveCompressionVertex x b σ := by
    have hterm (j : Unit ⊕ Fin 2) : a (σ j) + c j = c j * (1 + a (σ j) * b j) := by
      dsimp only [c]
      rw [mul_add, mul_one, mul_left_comm ((b j)⁻¹) (a (σ j)) (b j),
        inv_mul_cancel₀ (hb j), mul_one]
      exact add_comm _ _
    unfold matchingProduct
    simp_rw [hterm, Finset.prod_mul_distrib]
    congr 1
    unfold effectiveCompressionVertex
    rw [← Equiv.prod_comp σ.symm (fun j => 1 + a (σ j) * b j)]
    simp only [Equiv.apply_symm_apply, Fintype.prod_sum_type, a, Sum.elim_inl, Pi.zero_apply,
      zero_mul, add_zero, Finset.prod_const_one, one_mul, Sum.elim_inr]
  have hsmall : Conjecture (Unit ⊕ Fin 2) := conjecture_of_card_le_three (by simp)
  exact (hull_common_factor_iff hK hD hvertex).mp (hsmall a c U hU)

/-- The strict upper entry of an effective matrix in Schur form changes
the active determinant by exactly one product. -/
theorem det_upper_effective_correction (x : Fin 2 → ℂ) (γ : ℂ)
    (C : Matrix (Fin 2) (Fin 2) ℂ) :
    (1 + (!![x 0, γ; 0, x 1] : Matrix (Fin 2) (Fin 2) ℂ) * C).det -
      (1 + diagonal x * C).det = γ * C 1 0 := by
  simp [Matrix.det_fin_two, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two,
    Matrix.one_apply, Matrix.diagonal_apply] <;> ring

/-- In fixed Schur coordinates, subtracting the exact upper-entry correction
places the active determinant in the normal-deletion hull for its diagonal. -/
theorem det_upper_activeCompression_sub_mem_hull (x : Fin 2 → ℂ) (γ : ℂ)
    (b : Unit ⊕ Fin 2 → ℂ) (U : Matrix (Unit ⊕ Fin 2) (Unit ⊕ Fin 2) ℂ)
    (hU : IsUnitary U) (hb : ∀ j, b j ≠ 0) :
    let C := activeCompression b U
    (1 + (!![x 0, γ; 0, x 1] : Matrix (Fin 2) (Fin 2) ℂ) * C).det - γ * C 1 0 ∈
      convexHull ℝ (Set.range (effectiveCompressionVertex x b)) := by
  intro C
  have he : (1 + (!![x 0, γ; 0, x 1] : Matrix (Fin 2) (Fin 2) ℂ) * C).det -
      γ * C 1 0 = (1 + diagonal x * C).det := by
    apply sub_eq_iff_eq_add.mpr
    simpa only [add_comm] using sub_eq_iff_eq_add.mp (det_upper_effective_correction x γ C)
  rw [he]
  exact det_diagonal_activeCompression_mem_hull x b U hU hb

/-- A normal effective matrix preserves the lower-order matching hull for the
determinant of the active compression. The reciprocal right labels are nonzero. -/
theorem det_normal_activeCompression_mem_hull (X : Matrix (Fin 2) (Fin 2) ℂ)
    (hX : IsStarNormal X) (b : Unit ⊕ Fin 2 → ℂ)
    (U : Matrix (Unit ⊕ Fin 2) (Unit ⊕ Fin 2) ℂ)
    (hU : IsUnitary U) (hb : ∀ j, b j ≠ 0) :
    ∃ (x : Fin 2 → ℂ) (V : Matrix (Fin 2) (Fin 2) ℂ), IsUnitary V ∧
      X = V * diagonal x * Vᴴ ∧
      (1 + X * activeCompression b U).det ∈
        convexHull ℝ (Set.range (effectiveCompressionVertex x b)) := by
  obtain ⟨x, V, hV, hx⟩ := exists_unitary_diagonalization X hX
  let R := fromBlocks (1 : Matrix Unit Unit ℂ) 0 0 V
  let B := U * diagonal b * Uᴴ
  let C := activeCompression b U
  have hR : IsUnitary R := unitary_directSum (by simp [IsUnitary]) hV
  have hcomp : activeCompression b (Rᴴ * U) = Vᴴ * C * V := by
    have hconj : (Rᴴ * U) * diagonal b * (Rᴴ * U)ᴴ = Rᴴ * B * R := by
      simp only [B, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
    unfold activeCompression
    rw [hconj]
    change (Rᴴ * B * R).toBlocks₂₂ = Vᴴ * C * V
    conv_lhs =>
      rw [show R = fromBlocks (1 : Matrix Unit Unit ℂ) 0 0 V from rfl,
        Matrix.fromBlocks_conjTranspose, ← Matrix.fromBlocks_toBlocks B,
        Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply, Matrix.toBlocks_fromBlocks₂₂]
    simp only [Matrix.conjTranspose_zero, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add]
    rfl
  have hmul : V * (diagonal x * (Vᴴ * C * V)) * Vᴴ = (V * diagonal x * Vᴴ) * C := by
    calc
      _ = V * (diagonal x * (Vᴴ * C * (V * Vᴴ))) := by simp only [Matrix.mul_assoc]
      _ = _ := by
        rw [hV.1, Matrix.mul_one]
        simp only [Matrix.mul_assoc]
  have hdet : (1 + X * C).det = (1 + diagonal x * (Vᴴ * C * V)).det := by
    calc
      _ = (V * (1 + diagonal x * (Vᴴ * C * V)) * Vᴴ).det := by
        rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hV.1, hmul, hx]
      _ = _ := det_unitary_conjugation V _ hV
  refine ⟨x, V, hV, hx, ?_⟩
  rw [show activeCompression b U = C from rfl, hdet, ← hcomp]
  exact det_diagonal_activeCompression_mem_hull x b (Rᴴ * U) (relative_unitary R U hR hU) hb

private theorem det_effective_update {κ : Type*} [Fintype κ] [DecidableEq κ]
    (M : Matrix κ κ ℂ) (hM : M.det ≠ 0) (E : Matrix κ (Fin 2) ℂ)
    (C : Matrix (Fin 2) (Fin 2) ℂ) :
    (M + E * C * Eᴴ).det = M.det * (1 + (Eᴴ * M⁻¹ * E) * C).det := by
  have hu : IsUnit M.det := isUnit_iff_ne_zero.mpr hM
  have hfactor : M + E * C * Eᴴ = M * (1 + (M⁻¹ * E) * (C * Eᴴ)) := by
    rw [Matrix.mul_add, Matrix.mul_one, ← Matrix.mul_assoc M (M⁻¹ * E),
      ← Matrix.mul_assoc M M⁻¹ E, Matrix.mul_nonsing_inv M hu, Matrix.one_mul,
      Matrix.mul_assoc E C Eᴴ]
  have hcomm : (C * Eᴴ) * (M⁻¹ * E) = C * (Eᴴ * M⁻¹ * E) := by
    simp only [Matrix.mul_assoc]
  rw [hfactor, Matrix.det_mul, Matrix.det_one_add_mul_comm (M⁻¹ * E) (C * Eᴴ), hcomm,
    Matrix.det_one_add_mul_comm C (Eᴴ * M⁻¹ * E)]

/-- An embedded active plane need not reduce the background matrix. Normality
of the compressed inverse is enough for the order-three hull after a rank-two update. -/
theorem det_activeCompression_update_mem_hull {κ : Type*} [Fintype κ] [DecidableEq κ]
    (M : Matrix κ κ ℂ) (hM : M.det ≠ 0) (E : Matrix κ (Fin 2) ℂ)
    (hX : IsStarNormal (Eᴴ * M⁻¹ * E)) (b : Unit ⊕ Fin 2 → ℂ)
    (U : Matrix (Unit ⊕ Fin 2) (Unit ⊕ Fin 2) ℂ)
    (hU : IsUnitary U) (hb : ∀ j, b j ≠ 0) :
    ∃ (x : Fin 2 → ℂ) (V : Matrix (Fin 2) (Fin 2) ℂ), IsUnitary V ∧
      Eᴴ * M⁻¹ * E = V * diagonal x * Vᴴ ∧
      (M + E * activeCompression b U * Eᴴ).det ∈
        convexHull ℝ (Set.range (fun σ => M.det * effectiveCompressionVertex x b σ)) := by
  obtain ⟨x, V, hV, hx, hv⟩ := det_normal_activeCompression_mem_hull _ hX b U hU hb
  refine ⟨x, V, hV, hx, ?_⟩
  exact hull_of_common_factor (det_effective_update M hM E _) (fun _ => rfl) hv

/-- The coordinate inclusion of the retained two-dimensional active plane. -/
def activePlaneInclusion (κ : Type*) : Matrix (Fin 2 ⊕ κ) (Fin 2) ℂ :=
  Matrix.of fun i j => Sum.elim (fun k => (1 : Matrix (Fin 2) (Fin 2) ℂ) k j) (fun _ => 0) i

private theorem activePlaneInclusion_mul (κ : Type*) (Y : Matrix (Fin 2) (Fin 2) ℂ) :
    activePlaneInclusion κ * Y * (activePlaneInclusion κ)ᴴ =
      fromBlocks Y 0 0 (0 : Matrix κ κ ℂ) := by
  have hleft (i : Fin 2 ⊕ κ) (j : Fin 2) : (activePlaneInclusion κ * Y) i j =
      Sum.elim (fun k => Y k j) (fun _ => 0) i := by
    rcases i with i | i <;>
      simp [activePlaneInclusion, Matrix.mul_apply, Matrix.one_apply, ite_mul]
  ext i j : 1
  rcases i with i | i <;> rcases j with j | j <;>
    simp [Matrix.mul_apply, hleft, activePlaneInclusion, Matrix.conjTranspose_apply,
      Matrix.one_apply, mul_ite, apply_ite, eq_comm]

/-- Normality of the effective plane reduces the degree-three compression to
the matching hulls of the lower-order normal deletions with the outside labels fixed. -/
theorem det_activeCompression_mem_deletion_hull {κ : Type*} [Fintype κ] [DecidableEq κ]
    (hSmall : Conjecture (Fin 2 ⊕ κ)) (a : Fin 2 ⊕ κ → ℂ)
    (Q : Matrix (Fin 2 ⊕ κ) (Fin 2 ⊕ κ) ℂ) (hQ : IsUnitary Q)
    (b : Unit ⊕ Fin 2 → ℂ) (U : Matrix (Unit ⊕ Fin 2) (Unit ⊕ Fin 2) ℂ)
    (hU : IsUnitary U) (hb : ∀ j, b j ≠ 0) (d : κ → ℂ) :
    let A := Q * diagonal a * Qᴴ
    let M := A + fromBlocks (0 : Matrix (Fin 2) (Fin 2) ℂ) 0 0 (diagonal d)
    let E := activePlaneInclusion κ
    M.det ≠ 0 → IsStarNormal (Eᴴ * M⁻¹ * E) →
      (A + fromBlocks (activeCompression b U) 0 0 (diagonal d)).det ∈ convexHull ℝ
        (Set.range (fun p : Equiv.Perm (Unit ⊕ Fin 2) × Equiv.Perm (Fin 2 ⊕ κ) =>
          matchingProduct a (Sum.elim (fun i => b (p.1.symm (Sum.inr i))) d) p.2)) := by
  intro A M E hM hX
  let C := activeCompression b U
  let B₀ := fromBlocks (0 : Matrix (Fin 2) (Fin 2) ℂ) 0 0 (diagonal d)
  have hinsert (Y : Matrix (Fin 2) (Fin 2) ℂ) :
      M + E * Y * Eᴴ = A + fromBlocks Y 0 0 (diagonal d) := by
    change (A + B₀) + activePlaneInclusion κ * Y * (activePlaneInclusion κ)ᴴ = _
    rw [activePlaneInclusion_mul, add_assoc, show B₀ = fromBlocks 0 0 0 (diagonal d) from rfl,
      Matrix.fromBlocks_add]
    simp only [zero_add, add_zero]
  obtain ⟨x, V, hV, hx, hactive⟩ := det_activeCompression_update_mem_hull M hM E hX b U hU hb
  rw [← hinsert C]
  apply convexHull_min ?_ (convex_convexHull ℝ _) hactive
  rintro _ ⟨σ, rfl⟩
  let β : Fin 2 → ℂ := fun i => b (σ.symm (Sum.inr i))
  let Y := V * diagonal β * Vᴴ
  have hXY : (Eᴴ * M⁻¹ * E) * Y = V * diagonal (fun i => x i * β i) * Vᴴ := by
    rw [hx]
    calc
      _ = V * (diagonal x * (Vᴴ * V) * diagonal β) * Vᴴ := by
        simp only [Y, Matrix.mul_assoc]
      _ = _ := by rw [hV.2, Matrix.mul_one, Matrix.diagonal_mul_diagonal]
  have hdet : (M + E * Y * Eᴴ).det = M.det * effectiveCompressionVertex x b σ := by
    rw [det_effective_update M hM E Y, hXY]
    congr 1
    calc
      _ = (V * (1 + diagonal (fun i => x i * β i)) * Vᴴ).det := by
        rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hV.1]
      _ = _ := by
        rw [det_unitary_conjugation V _ hV, ← Matrix.diagonal_one, Matrix.diagonal_add,
          Matrix.det_diagonal]
        rfl
  let R := fromBlocks V 0 0 (1 : Matrix κ κ ℂ)
  have hR : IsUnitary R := unitary_directSum hV (by simp [IsUnitary])
  have hRight : R * diagonal (Sum.elim β d) * Rᴴ = fromBlocks Y 0 0 (diagonal d) := by
    dsimp only [R, Y]
    rw [← Matrix.fromBlocks_diagonal, Matrix.fromBlocks_conjTranspose,
      Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
    simp only [Matrix.conjTranspose_zero, Matrix.conjTranspose_one, Matrix.mul_zero,
      Matrix.zero_mul, Matrix.one_mul, Matrix.mul_one, add_zero, zero_add]
  have hv := hSmall a (Sum.elim β d) (Qᴴ * R) (relative_unitary Q R hQ hR)
  unfold Holds at hv
  rw [← determinantValue_relative a (Sum.elim β d) Q R hQ, hRight] at hv
  change M.det * effectiveCompressionVertex x b σ ∈ _
  rw [← hdet, hinsert]
  apply convexHull_mono ?_ hv
  rintro _ ⟨τ, rfl⟩
  exact ⟨(σ, τ), rfl⟩

end

end MOC
