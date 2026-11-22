import MOC.FiniteMinorLaw
import MOC.FourQuaternionRotation
import MOC.Realification

/-! Quaternion coordinates for the squared entries and two-minors of a real
orthogonal mixer of order four. -/

open BigOperators Matrix

namespace MOC

noncomputable section

/-- The quaternion representation after row signs preserves the squared minors
of sizes one and two used by order-four support certificates. -/
theorem exists_quaternionRotation_same_squaredMinors
    (O : Matrix.orthogonalGroup (Fin 4) ℝ) :
    ∃ p q : Fin 4 → ℝ, (∑ i, p i ^ 2) = 1 ∧ (∑ i, q i ^ 2) = 1 ∧
      let B := quaternionRotation p q
      let m := subsetMinorSq (Complex.ofRealHom.mapMatrix O.val)
      (∀ i j : Fin 4, m {i} {j} = B i j ^ 2) ∧
      ∀ i k j l : Fin 4, i ≠ k → j ≠ l →
        m {i, k} {j, l} = (B i j * B k l - B i l * B k j) ^ 2 := by
  obtain ⟨s, p, q, hs, hp, hq, hrot⟩ := exists_quaternionRotation_after_row_signs O.val
    ((Matrix.mem_orthogonalGroup_iff' _ ℝ).mp O.property)
  let B := quaternionRotation p q
  let U := Complex.ofRealHom.mapMatrix O.val
  have hU : IsUnitary U := isUnitary_ofReal_orthogonal O
  have hentry (i j : Fin 4) : B i j = s i * O.val i j := by
    change quaternionRotation p q i j = _
    rw [← hrot, Matrix.diagonal_mul]
  refine ⟨p, q, hp, hq, ?_, ?_⟩
  · intro i j
    change subsetMinorSq U {i} {j} = B i j ^ 2
    rw [subsetMinorSq_singleton U hU, hentry]
    change Complex.normSq (O.val i j : ℂ) = _
    rw [Complex.normSq_ofReal, mul_pow, hs, one_mul, pow_two]
  · intro i k j l hi hj
    change subsetMinorSq U {i, k} {j, l} = (B i j * B k l - B i l * B k j) ^ 2
    rw [subsetMinorSq_pair U hU hi hj]
    change Complex.normSq (((O.val i j : ℂ) * (O.val k l : ℂ)) -
      ((O.val i l : ℂ) * (O.val k j : ℂ))) = _
    rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_sub, Complex.normSq_ofReal]
    simp only [hentry]
    symm
    calc
      _ = s i ^ 2 * s k ^ 2 * (O.val i j * O.val k l - O.val i l * O.val k j) ^ 2 := by ring
      _ = _ := by simp only [hs, one_mul, pow_two]

end

end MOC
