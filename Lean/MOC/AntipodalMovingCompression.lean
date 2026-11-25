import MOC.AntipodalDeterminantJet
import Mathlib.Tactic.LinearCombination
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Hermitian

/-! Moving the mixer at a two-dimensional antipodal kernel changes the
compressed determinant by a nonpositive squared off-diagonal term.
The proof is algebraic in the skew-Hermitian orbit tangent. -/

open BigOperators Matrix

namespace MOC

noncomputable section

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

private theorem compression_intertwine_left
    (K : Matrix ι ι ℂ) (E : Matrix ι κ ℂ) (D : Matrix κ κ ℂ)
    (hK : K.IsHermitian) (hD : D.IsHermitian) (h : K * E = E * D) :
    Eᴴ * K = D * Eᴴ := by
  simpa only [Matrix.conjTranspose_mul, hK.eq, hD.eq] using
    congrArg Matrix.conjTranspose h

/-- A compressed variation commutes with the induced sign involution
as long as the original variation commutes with its own sign. -/
theorem commute_compression_of_intertwine
    (K V : Matrix ι ι ℂ) (E : Matrix ι κ ℂ) (D : Matrix κ κ ℂ)
    (hK : K.IsHermitian) (hD : D.IsHermitian) (h : K * E = E * D)
    (hv : Commute K V) :
    Commute D (Eᴴ * V * E) := by
  have hL := compression_intertwine_left K E D hK hD h
  change D * (Eᴴ * V * E) = Eᴴ * V * E * D
  calc
    _ = Eᴴ * (K * V) * E := by
      rw [← Matrix.mul_assoc D (Eᴴ * V) E, ← Matrix.mul_assoc D Eᴴ V, ← hL,
        Matrix.mul_assoc Eᴴ K V]
    _ = _ := by
      rw [hv.eq, ← Matrix.mul_assoc Eᴴ V K, Matrix.mul_assoc (Eᴴ * V) K E, h,
        ← Matrix.mul_assoc]

/-- Compression of the orbit commutator is the commutator of the compressed
tangent with the induced sign. No invertibility or unitarity of E is needed. -/
theorem compression_commutator_of_intertwine
    (K X : Matrix ι ι ℂ) (E : Matrix ι κ ℂ) (D : Matrix κ κ ℂ)
    (hK : K.IsHermitian) (hD : D.IsHermitian) (h : K * E = E * D) :
    Eᴴ * (X * K - K * X) * E = (Eᴴ * X * E) * D - D * (Eᴴ * X * E) := by
  have hL := compression_intertwine_left K E D hK hD h
  rw [Matrix.mul_sub, Matrix.sub_mul]
  congr 1
  · rw [← Matrix.mul_assoc Eᴴ X K, Matrix.mul_assoc (Eᴴ * X) K E, h,
      ← Matrix.mul_assoc]
  · rw [← Matrix.mul_assoc Eᴴ K X, hL, Matrix.mul_assoc D Eᴴ X, Matrix.mul_assoc D (Eᴴ * X) E]

/-- The positive and negative signed kernel lines in their natural order. -/
def antipodalSignPlane : Matrix (Fin 2) (Fin 2) ℂ :=
  diagonal ![1, -1]

private theorem signPlane_hermitian : antipodalSignPlane.IsHermitian := by
  rw [Matrix.IsHermitian, antipodalSignPlane, Matrix.diagonal_conjTranspose]
  apply congrArg Matrix.diagonal
  funext i
  fin_cases i <;> simp [Pi.star_apply]

private theorem signPlane_commute_offdiag (A : Matrix (Fin 2) (Fin 2) ℂ)
    (hA : Commute antipodalSignPlane A) : A 0 1 = 0 ∧ A 1 0 = 0 := by
  have h01 := congrFun (congrFun hA.eq 0) 1
  have h10 := congrFun (congrFun hA.eq 1) 0
  simp only [antipodalSignPlane, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, one_mul, mul_one, neg_one_mul,
    mul_neg, mul_one] at h01 h10
  constructor
  · linear_combination (1/2 : ℂ) * h01
  · linear_combination -(1/2 : ℂ) * h10

/-- The skew-Hermitian motion of the mixer adds a Hermitian crossed
off-diagonal. Its determinant cost on a diagonal compressed velocity is
four times the squared modulus of the tangent off-diagonal. -/
theorem det_add_crossed_tangent_fin_two
    (A T : Matrix (Fin 2) (Fin 2) ℂ) (hA : Commute antipodalSignPlane A)
    (hT : Tᴴ = -T) :
    (A + (T * (-antipodalSignPlane) - (-antipodalSignPlane) * T)).det =
      A 0 0 * A 1 1 - 4 * (Complex.normSq (T 0 1) : ℂ) := by
  obtain ⟨h01, h10⟩ := signPlane_commute_offdiag A hA
  have hs : T 1 0 = -star (T 0 1) := by
    have h := congrFun (congrFun hT 1) 0
    simp only [Matrix.conjTranspose_apply, Matrix.neg_apply] at h
    exact (neg_neg _).symm.trans (congrArg Neg.neg h.symm)
  have hC (i j : Fin 2) :
      (T * (-antipodalSignPlane) - (-antipodalSignPlane) * T) i j =
        T i j * (- (![1, -1] : Fin 2 → ℂ) j) -
          (- (![1, -1] : Fin 2 → ℂ) i) * T i j := by
    rw [antipodalSignPlane, Matrix.diagonal_neg]
    simp only [Matrix.sub_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, Pi.neg_apply]
  rw [Matrix.det_fin_two]
  simp only [Matrix.add_apply, hC, h01, h10, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, neg_neg, one_mul, mul_one, neg_one_mul]
  rw [hs, ← Complex.mul_conj]
  simp only [Complex.star_def]
  ring

/-- Exact compressed quadratic term at a signed two-dimensional kernel.
The first kernel vector lies in the positive eigenspace of J and the
negative eigenspace of K, and the second has the opposite signs. -/
theorem det_antipodal_kernel_tangent_compression
    (J K V W X : Matrix ι ι ℂ) (E : Matrix ι (Fin 2) ℂ)
    (hJ : J.IsHermitian) (hK : K.IsHermitian)
    (hJE : J * E = E * antipodalSignPlane) (hKE : K * E = E * (-antipodalSignPlane))
    (hV : Commute J V) (hW : Commute K W) (hX : Xᴴ = -X) :
    let A := Eᴴ * (V+W) * E
    let T := Eᴴ * X * E
    (Eᴴ * (V+W+(X*K-K*X)) * E).det =
      A 0 0 * A 1 1 - 4 * (Complex.normSq (T 0 1) : ℂ) := by
  intro A T
  have hd : antipodalSignPlane.IsHermitian := signPlane_hermitian
  have hv := commute_compression_of_intertwine J V E antipodalSignPlane hJ hd hJE hV
  have hn : (-antipodalSignPlane).IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_neg, hd.eq]
  have hw := commute_compression_of_intertwine K W E (-antipodalSignPlane) hK hn hKE hW
  have hw' : Commute antipodalSignPlane (Eᴴ * W * E) := by
    change antipodalSignPlane * (Eᴴ * W * E) = (Eᴴ * W * E) * antipodalSignPlane
    simpa only [Matrix.neg_mul, Matrix.mul_neg, neg_inj] using hw.eq
  have hA : Commute antipodalSignPlane A := by
    change Commute antipodalSignPlane (Eᴴ * (V+W) * E)
    rw [Matrix.mul_add, Matrix.add_mul]
    exact hv.add_right hw'
  have hT : Tᴴ = -T := by
    simp only [T, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hX,
      Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]
  have hcomp := compression_commutator_of_intertwine K X E (-antipodalSignPlane) hK hn hKE
  rw [Matrix.mul_add, Matrix.add_mul, hcomp]
  exact det_add_crossed_tangent_fin_two A T hA hT

/-- If the support functional is nonnegative on the reduced determinant,
skew-Hermitian mixing cannot increase the tested quadratic coefficient. -/
theorem projected_antipodal_kernel_tangent_le
    (J K V W X : Matrix ι ι ℂ) (E : Matrix ι (Fin 2) ℂ)
    (hJ : J.IsHermitian) (hK : K.IsHermitian)
    (hJE : J * E = E * antipodalSignPlane) (hKE : K * E = E * (-antipodalSignPlane))
    (hV : Commute J V) (hW : Commute K W) (hX : Xᴴ = -X)
    (η d : ℂ) (hd : 0 ≤ (η * d).re) :
    let A := Eᴴ * (V+W) * E
    (η * d * (Eᴴ * (V+W+(X*K-K*X)) * E).det).re ≤
      (η * d * (A 0 0 * A 1 1)).re := by
  intro A
  rw [det_antipodal_kernel_tangent_compression J K V W X E hJ hK hJE hKE hV hW hX]
  let q : ℝ := 4 * Complex.normSq ((Eᴴ * X * E) 0 1)
  have hq : 0 ≤ q := mul_nonneg (by positivity) (Complex.normSq_nonneg _)
  have he : (4 * (Complex.normSq ((Eᴴ * X * E) 0 1) : ℂ)) = (q : ℂ) := by
    simp only [q, Complex.ofReal_mul, Complex.ofReal_ofNat]
  rw [he, mul_sub, Complex.sub_re, Complex.re_mul_ofReal, sub_le_self_iff]
  exact mul_nonneg hd hq


end

end MOC
