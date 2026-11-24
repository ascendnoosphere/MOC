import MOC.Weights
import Mathlib.Data.Complex.Exponential

open BigOperators Matrix

namespace MOC.Reformulations

noncomputable section

/-- The finite order-three regularized determinant on real order-two
matrices, written using its defining trace correction. -/
def finiteDetThree (C : Matrix (Fin 2) (Fin 2) ℝ) : ℝ :=
  (1 + C).det * Real.exp (-C.trace + (C * C).trace / 2)

/-- An individual order-three regularized spectral factor. -/
def canonicalFactorThree (t : ℝ) : ℝ := (1 + t) * Real.exp (-t + t ^ 2 / 2)

/-- Trace and determinant completely determine this order-two comparison. -/
theorem finiteDetThree_eq_trace_det (C : Matrix (Fin 2) (Fin 2) ℝ) :
    finiteDetThree C =
      (1 + C.trace + C.det) * Real.exp (-C.trace + C.trace ^ 2 / 2 - C.det) := by
  have hd : (1 + C).det = 1 + C.trace + C.det := by
    simp [Matrix.det_fin_two, Matrix.add_apply, Matrix.one_apply, Matrix.trace,
      Fin.sum_univ_two]
    ring
  have ht : (C * C).trace = C.trace ^ 2 - 2 * C.det := by
    simp only [Matrix.trace, Matrix.diag_apply, Fin.sum_univ_two, Matrix.mul_apply,
      Matrix.det_fin_two]
    ring
  rw [finiteDetThree, hd, ht]
  congr 2
  ring

/-- At fixed trace the regularized determinant has a strict maximum at
`det C = -trace C`. This follows from the strict exponential tangent bound
and does not require optimization or tabulation of matrix instances. -/
theorem finiteDetThree_strict_max (C : Matrix (Fin 2) (Fin 2) ℝ)
    (h : C.det ≠ -C.trace) :
    finiteDetThree C < Real.exp (C.trace ^ 2 / 2) := by
  let z := C.trace + C.det
  have hz : z ≠ 0 := by
    intro he
    apply h
    change C.trace + C.det = 0 at he
    linarith
  rw [finiteDetThree_eq_trace_det]
  have he : -C.trace + C.trace ^ 2 / 2 - C.det = C.trace ^ 2 / 2 - z := by
    dsimp [z]
    ring
  rw [he]
  have hr : Real.exp (C.trace ^ 2 / 2) = Real.exp z * Real.exp (C.trace ^ 2 / 2 - z) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hr]
  apply mul_lt_mul_of_pos_right _ (Real.exp_pos _)
  simpa [z, add_assoc, add_comm, add_left_comm] using Real.add_one_lt_exp hz

/-- The value at the critical determinant is the sharp upper bound. -/
theorem finiteDetThree_eq_critical (C : Matrix (Fin 2) (Fin 2) ℝ)
    (h : C.det = -C.trace) :
    finiteDetThree C = Real.exp (C.trace ^ 2 / 2) := by
  rw [finiteDetThree_eq_trace_det, h]
  simp only [add_neg_cancel_right, one_mul, sub_neg_eq_add, neg_add_cancel_left]
  congr 1
  ring

private def rotation (c s : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![c, -s; s, c]

private theorem rotation_orthogonal (c s : ℝ) (h : c ^ 2 + s ^ 2 = 1) :
    rotation c s * (rotation c s)ᵀ = 1 := by
  apply Matrix.ext_iff.mp
  simp only [Fin.forall_fin_two, rotation, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.transpose_apply, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.one_apply]
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> simp
  · simpa [pow_two] using h
  · ring
  · ring
  · simpa [pow_two, add_comm] using h

private def equalPair (a b c s : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  diagonal ![a,b] + rotation c s * diagonal ![a,b] * (rotation c s)ᵀ

private theorem equalPair_trace (a b c s : ℝ) (h : c ^ 2 + s ^ 2 = 1) :
    (equalPair a b c s).trace = 2 * (a + b) := by
  simp [equalPair, rotation, Matrix.trace, Matrix.mul_apply, Matrix.add_apply, Matrix.diagonal_apply,
    Fin.sum_univ_two, Matrix.vecMul, dotProduct, Matrix.transpose_apply]
  linear_combination (a + b) * h

private theorem equalPair_det (a b c s : ℝ) (h : c ^ 2 + s ^ 2 = 1) :
    (equalPair a b c s).det = (a + b) ^ 2 - (a - b) ^ 2 * c ^ 2 := by
  simp [equalPair, rotation, Matrix.det_fin_two, Matrix.mul_apply,
    Matrix.add_apply, Matrix.diagonal_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct,
    Matrix.transpose_apply]
  linear_combination (a ^ 2 + b ^ 2 + a * b * (c ^ 2 + s ^ 2 + 1)) * h

private theorem finiteDetThree_diagonal (d : Fin 2 → ℝ) :
    finiteDetThree (diagonal d) = ∏ j, canonicalFactorThree (d j) := by
  simp [finiteDetThree, canonicalFactorThree, Fin.prod_univ_two, Matrix.det_fin_two,
    Matrix.trace, Fin.sum_univ_two, Matrix.one_apply, Matrix.diagonal_mul_diagonal]
  rw [mul_mul_mul_comm, ← Real.exp_add]
  congr 2
  ring

/-- A family of exact native refutations to order-three regularization:
an interior critical determinant with neither commuting orientation critical
lies outside the whole permutation hull. -/
theorem finiteSchattenThreeHull_of_interior (a b c s : ℝ) (h : c ^ 2 + s ^ 2 = 1)
    (hcritical : (a + b) ^ 2 - (a - b) ^ 2 * c ^ 2 = -(2 * (a + b)))
    (halign : 4 * a * b ≠ -(2 * (a + b))) (hswap : (a + b) ^ 2 ≠ -(2 * (a + b))) :
    finiteDetThree (equalPair a b c s) ∉
      convexHull ℝ (Set.range (fun σ : Equiv.Perm (Fin 2) =>
        ∏ j, canonicalFactorThree ((![a,b] : Fin 2 → ℝ) (σ j) + ![a,b] j))) := by
  let d : Fin 2 → ℝ := ![a,b]
  let t := 2 * (a + b)
  have hpoint : finiteDetThree (equalPair a b c s) = Real.exp (t ^ 2 / 2) := by
    have hc : (equalPair a b c s).det = -(equalPair a b c s).trace := by
      rw [equalPair_det a b c s h, equalPair_trace a b c s h]
      exact hcritical
    rw [finiteDetThree_eq_critical _ hc, equalPair_trace a b c s h]
  let v (σ : Equiv.Perm (Fin 2)) := fun j => d (σ j) + d j
  have hvertex (σ : Equiv.Perm (Fin 2)) :
      (diagonal (v σ)).trace = t ∧ (diagonal (v σ)).det ≠ -t := by
    constructor
    · rw [Matrix.trace_diagonal]
      simp_rw [v, Finset.sum_add_distrib, Equiv.sum_comp σ]
      simp [d, t, Fin.sum_univ_two]
      ring
    · have hdiff := σ.injective.ne (show (0 : Fin 2) ≠ 1 by decide)
      by_cases hzero : σ 0 = 0
      · have hone : σ 1 = 1 := by omega
        simpa [Matrix.det_diagonal, Fin.prod_univ_two, v, d, t, hzero, hone,
          show (a + a) * (b + b) = 4 * a * b by ring] using halign
      · have hzero' : σ 0 = 1 := by omega
        have hone : σ 1 = 0 := by omega
        simpa [Matrix.det_diagonal, Fin.prod_univ_two, v, d, t, hzero', hone,
          add_comm b a, pow_two] using hswap
  change finiteDetThree (equalPair a b c s) ∉
    convexHull ℝ (Set.range (fun σ => ∏ j, canonicalFactorThree (v σ j)))
  rw [hpoint]
  intro hc
  have hsub : Set.range (fun σ => ∏ j, canonicalFactorThree (v σ j)) ⊆
      Set.Iio (Real.exp (t ^ 2 / 2)) := by
    rintro _ ⟨σ, rfl⟩
    change (∏ j, canonicalFactorThree (v σ j)) < Real.exp (t ^ 2 / 2)
    rw [← finiteDetThree_diagonal]
    have hh := finiteDetThree_strict_max (diagonal (v σ))
      (by rw [(hvertex σ).1]; exact (hvertex σ).2)
    rwa [(hvertex σ).1] at hh
  exact lt_irrefl (Real.exp (t ^ 2 / 2))
    (convexHull_min hsub (convex_Iio (𝕜 := ℝ) (Real.exp (t ^ 2 / 2))) hc)

/-- Atlas 064 fails at p=3 already for a real orthogonal mixer. -/
theorem finiteSchattenThreeHull_false :
    ∃ (a : Fin 2 → ℝ) (Q : Matrix (Fin 2) (Fin 2) ℝ), Q * Qᵀ = 1 ∧
      finiteDetThree (diagonal a + Q * diagonal a * Qᵀ) ∉
        convexHull ℝ (Set.range (fun σ : Equiv.Perm (Fin 2) =>
          ∏ j, canonicalFactorThree (a (σ j) + a j))) := by
  have hs : (Real.sqrt 5) ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hrot : (Real.sqrt 5 / 3) ^ 2 + (2 / 3 : ℝ) ^ 2 = 1 := by nlinarith only [hs]
  refine ⟨![(-1 / 2), -2], rotation (Real.sqrt 5 / 3) (2 / 3),
    rotation_orthogonal _ _ hrot, ?_⟩
  apply finiteSchattenThreeHull_of_interior _ _ _ _ hrot
  · nlinarith only [hs]
  · norm_num
  · norm_num

end

end MOC.Reformulations
