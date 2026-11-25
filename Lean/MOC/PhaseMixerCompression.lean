import MOC.Core
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-! Determinant compression for a unitary that acts by a given phase matrix
on the range of an isometry and fixes its orthogonal complement. -/

open Matrix

namespace MOC

noncomputable section

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- The unitary acting by `W` on the columns of `Y`. -/
def phaseMixer (Y : Matrix ι κ ℂ) (W : Matrix κ κ ℂ) : Matrix ι ι ℂ :=
  1 + Y * (W - 1) * Yᴴ

private theorem phaseMixer_mul_adjoint (Y : Matrix ι κ ℂ) (W : Matrix κ κ ℂ)
    (hY : Yᴴ * Y = 1) (hW : W * Wᴴ = 1) :
    phaseMixer Y W * (phaseMixer Y W)ᴴ = 1 := by
  let D := W - 1
  have hD : D + Dᴴ + D * Dᴴ = 0 := by
    dsimp only [D]
    simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, Matrix.sub_mul,
      Matrix.mul_sub, Matrix.mul_one, Matrix.one_mul, hW]
    abel
  have hquad : (Y * D * Yᴴ) * (Y * Dᴴ * Yᴴ) = Y * (D * Dᴴ) * Yᴴ := by
    calc
      _ = Y * (D * ((Yᴴ * Y) * Dᴴ)) * Yᴴ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hY, Matrix.one_mul]
  have hstar : (Y * D * Yᴴ)ᴴ = Y * Dᴴ * Yᴴ := by
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  change (1 + Y * D * Yᴴ) * (1 + Y * D * Yᴴ)ᴴ = 1
  simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_one, hstar, Matrix.add_mul,
    Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, hquad]
  have hzero : Y * D * Yᴴ + Y * Dᴴ * Yᴴ + Y * (D * Dᴴ) * Yᴴ = 0 := by
    simpa only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_zero, Matrix.zero_mul] using
      congrArg (fun Q : Matrix κ κ ℂ => Y * Q * Yᴴ) hD
  calc
    _ = 1 + (Y * D * Yᴴ + Y * Dᴴ * Yᴴ + Y * (D * Dᴴ) * Yᴴ) := by abel
    _ = 1 := by rw [hzero, add_zero]

theorem phaseMixer_adjoint (Y : Matrix ι κ ℂ) (W : Matrix κ κ ℂ) :
    (phaseMixer Y W)ᴴ = phaseMixer Y Wᴴ := by
  simp only [phaseMixer, Matrix.conjTranspose_add, Matrix.conjTranspose_sub,
    Matrix.conjTranspose_one, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    Matrix.mul_assoc]

theorem phaseMixer_unitary (Y : Matrix ι κ ℂ) (W : Matrix κ κ ℂ)
    (hY : Yᴴ * Y = 1) (hW : IsUnitary W) : IsUnitary (phaseMixer Y W) := by
  refine ⟨phaseMixer_mul_adjoint Y W hY hW.1, ?_⟩
  have hW' : Wᴴ * (Wᴴ)ᴴ = 1 := by simpa only [Matrix.conjTranspose_conjTranspose] using hW.2
  have h := phaseMixer_mul_adjoint Y Wᴴ hY hW'
  simpa only [← phaseMixer_adjoint, Matrix.conjTranspose_conjTranspose] using h

theorem det_phaseMixer (Y : Matrix ι κ ℂ) (W : Matrix κ κ ℂ)
    (hY : Yᴴ * Y = 1) : (phaseMixer Y W).det = W.det := by
  rw [phaseMixer, Matrix.det_one_add_mul_comm, ← Matrix.mul_assoc, hY, Matrix.one_mul]
  congr 1
  abel

private def joinCols (P Q : Matrix ι κ ℂ) : Matrix ι (κ ⊕ κ) ℂ :=
  fun i => Sum.elim (P i) (Q i)

private def joinRows (P Q : Matrix κ ι ℂ) : Matrix (κ ⊕ κ) ι ℂ :=
  Sum.elim P Q

private theorem joinCols_mul_joinRows (P Q : Matrix ι κ ℂ) (R S : Matrix κ ι ℂ) :
    joinCols P Q * joinRows R S = P * R + Q * S := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.add_apply, Fintype.sum_sum_type, joinCols, joinRows,
    Sum.elim_inl, Sum.elim_inr]

private theorem mul_joinCols (C : Matrix ι ι ℂ) (P Q : Matrix ι κ ℂ) :
    C * joinCols P Q = joinCols (C * P) (C * Q) := by
  ext i j
  cases j <;> simp only [Matrix.mul_apply, joinCols, Sum.elim_inl, Sum.elim_inr]

private theorem joinRows_mul_joinCols (P Q : Matrix κ ι ℂ) (R S : Matrix ι κ ℂ) :
    joinRows P Q * joinCols R S = Matrix.fromBlocks (P * R) (P * S) (Q * R) (Q * S) := by
  ext i j
  cases i <;> cases j <;> simp only [Matrix.mul_apply, joinRows, joinCols, Sum.elim_inl,
    Sum.elim_inr, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
    Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂]

/-- The dependence on the isometry is through the four displayed
compressions of functions of the two summands. -/
theorem det_phaseMixer_orbit (A B : Matrix ι ι ℂ) (Y : Matrix ι κ ℂ)
    (W : Matrix κ κ ℂ) (hY : Yᴴ * Y = 1) (hW : IsUnitary W)
    (hT : IsUnit (A + B).det) :
    let C := (A + B)⁻¹
    let D := W - 1
    let M := Matrix.fromBlocks
      (D * Yᴴ * C * A * Y) (D * Yᴴ * C * Y)
      (D * Yᴴ * B * C * A * Y) (D * Yᴴ * B * C * Y)
    (A + phaseMixer Y W * B * (phaseMixer Y W)ᴴ).det * W.det =
      (A + B).det * (1 + M).det := by
  intro C D M
  let V := phaseMixer Y W
  let L := joinCols (A * Y) Y
  let R := joinRows (D * Yᴴ) (D * Yᴴ * B)
  have hV : IsUnitary V := phaseMixer_unitary Y W hY hW
  have hupdate : (A + V * B * Vᴴ) * V = (A + B) + L * R := by
    rw [Matrix.add_mul, Matrix.mul_assoc (V * B) Vᴴ V, hV.2, Matrix.mul_one]
    change A * (1 + Y * D * Yᴴ) + (1 + Y * D * Yᴴ) * B = (A + B) + L * R
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul,
      show L * R = _ from joinCols_mul_joinRows (A * Y) Y (D * Yᴴ) (D * Yᴴ * B)]
    simp only [Matrix.mul_assoc]
    abel
  have hcore : R * C * L = M := by
    rw [Matrix.mul_assoc R C L, show C * L = _ from mul_joinCols C (A * Y) Y,
      show R * joinCols (C * (A * Y)) (C * Y) = _ from
        joinRows_mul_joinCols (D * Yᴴ) (D * Yᴴ * B) (C * (A * Y)) (C * Y)]
    simp only [M, Matrix.mul_assoc]
  change (A + V * B * Vᴴ).det * W.det = _
  rw [← det_phaseMixer Y W hY, ← Matrix.det_mul, hupdate, Matrix.det_add_mul L R hT, hcore]

/-- Compress a diagonal spectral function to the active subspace. -/
def phaseMoment (Y : Matrix ι κ ℂ) (f : ι → ℂ) : Matrix κ κ ℂ :=
  Yᴴ * diagonal f * Y

/-- Three complex moments, together with the isometry condition, suffice to
preserve the determinant under a change of the active columns. -/
theorem determinantValue_phaseMixer_eq_of_moments (a b : ι → ℂ)
    (Y Z : Matrix ι κ ℂ) (W : Matrix κ κ ℂ) (hY : Yᴴ * Y = 1) (hZ : Zᴴ * Z = 1)
    (hW : IsUnitary W) (hreg : ∀ i, a i + b i ≠ 0)
    (h₀ : phaseMoment Y (fun i => (a i + b i)⁻¹) = phaseMoment Z (fun i => (a i + b i)⁻¹))
    (h₁ : phaseMoment Y (fun i => (a i + b i)⁻¹ * a i) =
      phaseMoment Z (fun i => (a i + b i)⁻¹ * a i))
    (h₂ : phaseMoment Y (fun i => b i * (a i + b i)⁻¹ * a i) =
      phaseMoment Z (fun i => b i * (a i + b i)⁻¹ * a i)) :
    determinantValue a b (phaseMixer Y W) = determinantValue a b (phaseMixer Z W) := by
  let c (i : ι) := (a i + b i)⁻¹
  let A := diagonal a
  let B := diagonal b
  have hT : IsUnit (A + B).det := by
    rw [show A + B = diagonal (fun i => a i + b i) from Matrix.diagonal_add a b,
      Matrix.det_diagonal]
    exact isUnit_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr (fun i _ => hreg i))
  have hC : (A + B)⁻¹ = diagonal c := by
    apply Matrix.inv_eq_right_inv
    rw [show A + B = diagonal (fun i => a i + b i) from Matrix.diagonal_add a b,
      Matrix.diagonal_mul_diagonal]
    have hf : (fun i => (a i + b i) * c i) = fun _ => (1 : ℂ) := by
      funext i
      exact mul_inv_cancel₀ (hreg i)
    rw [hf, Matrix.diagonal_one]
  have hsum : (fun i => b i * c i) = fun i => 1 - c i * a i := by
    funext i
    dsimp only [c]
    field_simp [hreg i] <;> ring
  have h₃ : phaseMoment Y (fun i => b i * c i) = phaseMoment Z (fun i => b i * c i) := by
    rw [hsum]
    have hsplit (X : Matrix ι κ ℂ) :
        phaseMoment X (fun i => 1 - c i * a i) =
          Xᴴ * X - phaseMoment X (fun i => c i * a i) := by
      have hd := Matrix.diagonal_sub (fun _ : ι => (1 : ℂ)) (fun i => c i * a i)
      simp only [Matrix.diagonal_one] at hd
      simp only [phaseMoment, ← hd, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one]
    rw [hsplit Y, hsplit Z, hY, hZ, h₁]
  have hform (X : Matrix ι κ ℂ) (hX : Xᴴ * X = 1) :
      determinantValue a b (phaseMixer X W) * W.det =
        (A + B).det * (1 + Matrix.fromBlocks
          ((W - 1) * phaseMoment X (fun i => c i * a i))
          ((W - 1) * phaseMoment X c)
          ((W - 1) * phaseMoment X (fun i => b i * c i * a i))
          ((W - 1) * phaseMoment X (fun i => b i * c i))).det := by
    have h := det_phaseMixer_orbit A B X W hX hW hT
    dsimp only at h
    rw [hC] at h
    simpa only [determinantValue, A, B, phaseMoment, Matrix.mul_assoc,
      ← Matrix.diagonal_mul_diagonal, mul_assoc] using h
  apply mul_right_cancel₀ (det_ne_zero_of_unitary hW)
  rw [hform Y hY, hform Z hZ, h₀, h₁, h₂, h₃]

end

end MOC
