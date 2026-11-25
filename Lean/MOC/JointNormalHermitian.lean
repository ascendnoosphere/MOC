import MOC.Normal
import Mathlib.Tactic.LinearCombination

/-! Simultaneous diagonalization of a normal matrix and a commuting Hermitian matrix. -/

open Matrix

namespace MOC

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem exists_separating_projection (a : ι → ℂ) :
    ∃ t : ℝ, ∀ i j, (a i).re + t * (a i).im = (a j).re + t * (a j).im → a i = a j := by
  classical
  letI : Infinite ℝ := Infinite.of_injective (fun n : ℕ => (n : ℝ)) Nat.cast_injective
  let slope (p : ι × ι) := ((a p.2).re - (a p.1).re) / ((a p.1).im - (a p.2).im)
  obtain ⟨t, ht⟩ := Infinite.exists_not_mem_finset (Finset.univ.image slope)
  refine ⟨t, fun i j he => ?_⟩
  by_cases hi : (a i).im = (a j).im
  · refine Complex.ext ?_ hi
    exact add_right_cancel (by simpa only [hi] using he)
  · exfalso
    apply ht
    refine Finset.mem_image.mpr ⟨(i, j), Finset.mem_univ _, ?_⟩
    dsimp only [slope]
    apply (div_eq_iff (sub_ne_zero.mpr hi)).mpr
    linear_combination -he

private theorem conjugate_mul (U : Matrix ι ι ℂ) (hU : IsUnitary U) (A B : Matrix ι ι ℂ) :
    (U * A * Uᴴ) * (U * B * Uᴴ) = U * (A * B) * Uᴴ := by
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc Uᴴ U, hU.2, Matrix.one_mul]

/-- A normal matrix and a commuting Hermitian matrix have a common unitary
eigenbasis, including when either spectrum repeats. -/
theorem exists_joint_normal_hermitian_diagonalization (N H : Matrix ι ι ℂ)
    (hN : IsStarNormal N) (hH : H.IsHermitian) (hNH : Commute N H) :
    ∃ (a b : ι → ℂ) (V : Matrix ι ι ℂ), IsUnitary V ∧
      N = V * diagonal a * Vᴴ ∧ H = V * diagonal b * Vᴴ := by
  classical
  obtain ⟨a, U, hU, hNa⟩ := exists_unitary_diagonalization N hN
  obtain ⟨t, ht⟩ := exists_separating_projection a
  let c (i : ι) : ℂ := ((a i).re + t * (a i).im : ℝ)
  let X := Uᴴ * H * U
  let K := U * diagonal c * Uᴴ
  have hX : U * X * Uᴴ = H := by
    calc
      _ = (U * Uᴴ) * H * (U * Uᴴ) := by simp only [X, Matrix.mul_assoc]
      _ = _ := by simp only [hU.1, Matrix.one_mul, Matrix.mul_one]
  have hpull (Y : Matrix ι ι ℂ) : Uᴴ * (U * Y * Uᴴ) * U = Y := by
    calc
      _ = (Uᴴ * U) * Y * (Uᴴ * U) := by simp only [Matrix.mul_assoc]
      _ = _ := by simp only [hU.2, Matrix.one_mul, Matrix.mul_one]
  have hAX : diagonal a * X = X * diagonal a := by
    have he : U * (diagonal a * X) * Uᴴ = U * (X * diagonal a) * Uᴴ := by
      rw [← conjugate_mul U hU (diagonal a) X, ← conjugate_mul U hU X (diagonal a), hX, ← hNa]
      exact hNH.eq
    have hh := congrArg (fun Y : Matrix ι ι ℂ => Uᴴ * Y * U) he
    simpa only [hpull] using hh
  have hCX : diagonal c * X = X * diagonal c := by
    ext i j : 1
    rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
    by_cases he : a i = a j
    · have hc : c i = c j := by simp only [c, he]
      rw [hc, mul_comm]
    · have hh := congrArg (fun Y : Matrix ι ι ℂ => Y i j) hAX
      change (diagonal a * X) i j = (X * diagonal a) i j at hh
      rw [Matrix.diagonal_mul, Matrix.mul_diagonal, mul_comm (X i j)] at hh
      have hz : (a i - a j) * X i j = 0 := by rw [sub_mul, hh, sub_self]
      simp only [(mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr he), mul_zero, zero_mul]
  have hcH : (diagonal c).IsHermitian := by
    apply Matrix.isHermitian_diagonal_iff.mpr
    intro i
    simp [c, isSelfAdjoint_iff, Complex.star_def]
  have hKH : Commute K H := by
    change (U * diagonal c * Uᴴ) * H = H * (U * diagonal c * Uᴴ)
    rw [← hX, conjugate_mul U hU (diagonal c) X, conjugate_mul U hU X (diagonal c), hCX]
  obtain ⟨k, b, V, hV, hK, hHV⟩ := exists_joint_hermitian_diagonalization K H
    (Matrix.isHermitian_mul_mul_conjTranspose U hcH) hH hKH
  let Z := Uᴴ * V
  have hZ : IsUnitary Z := relative_unitary U V hU hV
  have hCK : diagonal c * Z = Z * diagonal k := by
    calc
      _ = Uᴴ * K * V := by
        simp only [Z, K, ← Matrix.mul_assoc, hU.2, Matrix.one_mul]
      _ = _ := by rw [hK]; simp only [Z, Matrix.mul_assoc, hV.2, Matrix.mul_one]
  have hnz (j : ι) : ∃ i, Z i j ≠ 0 := by
    by_cases h : ∃ i, Z i j ≠ 0
    · exact h
    · have hz (i : ι) : Z i j = 0 := Classical.byContradiction (fun hi => h ⟨i, hi⟩)
      have hh := congrArg (fun Y : Matrix ι ι ℂ => Y j j) hZ.2
      have he : (0 : ℂ) = 1 := by
        simpa only [Matrix.mul_apply, Matrix.conjTranspose_apply, hz, mul_zero,
          Finset.sum_const_zero, Matrix.one_apply_eq] using hh
      exact (zero_ne_one he).elim
  let i₀ (j : ι) := Classical.choose (hnz j)
  have hh (i j : ι) (hi : Z i j ≠ 0) : c i = k j := by
    have he := congrArg (fun Y : Matrix ι ι ℂ => Y i j) hCK
    change (diagonal c * Z) i j = (Z * diagonal k) i j at he
    rw [Matrix.diagonal_mul, Matrix.mul_diagonal, mul_comm (Z i j)] at he
    exact mul_right_cancel₀ hi he
  let a' (j : ι) := a (i₀ j)
  have hAZ : diagonal a * Z = Z * diagonal a' := by
    ext i j : 1
    rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
    by_cases hi : Z i j = 0
    · simp only [hi, mul_zero, zero_mul]
    · have he : c i = c (i₀ j) := (hh i j hi).trans
        (hh (i₀ j) j (Classical.choose_spec (hnz j))).symm
      have ha : a i = a' j := ht i (i₀ j) (Complex.ofReal_injective he)
      rw [ha, mul_comm]
  have hNV : N * V = V * diagonal a' := by
    calc
      _ = U * (diagonal a * Z) := by rw [hNa]; simp only [Z, Matrix.mul_assoc]
      _ = U * (Z * diagonal a') := by rw [hAZ]
      _ = _ := by simp only [Z, ← Matrix.mul_assoc, hU.1, Matrix.one_mul]
  refine ⟨a', b, V, hV, ?_, hHV⟩
  rw [← hNV, Matrix.mul_assoc, hV.1, Matrix.mul_one]

end MOC
