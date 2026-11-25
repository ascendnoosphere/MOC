import MOC.AntipodalDeterminantJet
import MOC.Core
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Matrix.Spectrum
import Mathlib.Algebra.Polynomial.Eval.Defs

/-! An exact polynomial determinant reduction at a singular center.
The kernel/range split for a pair of Hermitian involutions is the part of
Halmos's two-subspace geometry used here (DOI: 10.1090/S0002-9947-1969-0251519-5).
The determinant reduction itself is by row factoring, including singular
velocity compressions. -/

open Matrix Polynomial

namespace MOC
noncomputable section

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ]

/-- The polynomial of an affine matrix pencil, with the velocities fixed. -/
def affineDetPoly (S H : Matrix ι ι ℂ) : ℂ[X] :=
  (S.map C + (X : ℂ[X]) • H.map C).det

/-- A zero central block forces a factor of `X` for each row in that block.
The coefficient left at that degree uses only the two diagonal blocks. -/
theorem affineDetPoly_kernel_factor (T A : Matrix ι ι ℂ) (B : Matrix ι κ ℂ)
    (D : Matrix κ ι ℂ) (E : Matrix κ κ ℂ) :
    ∃ q : ℂ[X], affineDetPoly (fromBlocks T 0 0 (0 : Matrix κ κ ℂ))
      (fromBlocks A B D E) = X ^ Fintype.card κ * q ∧
      q.coeff 0 = T.det * E.det := by
  let Q : Matrix (ι ⊕ κ) (ι ⊕ κ) ℂ[X] :=
    fromBlocks (T.map C + (X : ℂ[X]) • A.map C) ((X : ℂ[X]) • B.map C) (D.map C) (E.map C)
  let s : ι ⊕ κ → ℂ[X] := Sum.elim (fun _ => 1) (fun _ => X)
  have hQ : (fromBlocks T 0 0 (0 : Matrix κ κ ℂ)).map C +
      (X : ℂ[X]) • (fromBlocks A B D E).map C = diagonal s * Q := by
    ext (i | i) (j | j) <;>
      simp [Q, s, Matrix.diagonal_mul, Matrix.smul_apply, smul_eq_mul]
  have hdiag : (diagonal s).det = X ^ Fintype.card κ := by
    simp [Matrix.det_diagonal, s, Fintype.prod_sum_type]
  refine ⟨Q.det, ?_, ?_⟩
  · rw [affineDetPoly, hQ, Matrix.det_mul, hdiag]
  · have hmap : Q.map (Polynomial.evalRingHom (0 : ℂ)) = fromBlocks T 0 D E := by
      ext (i | i) (j | j) <;>
        simp [Q, Matrix.smul_apply, smul_eq_mul]
    rw [Polynomial.coeff_zero_eq_eval_zero, ← Polynomial.coe_evalRingHom,
      RingHom.map_det, RingHom.mapMatrix_apply, hmap, Matrix.det_fromBlocks_zero₁₂]

/-- This is an exact coefficient formula, not just a bound on the order of
vanishing. A singular compression can give still higher vanishing. -/
theorem affineDetPoly_kernel_coeff (T A : Matrix ι ι ℂ) (B : Matrix ι κ ℂ)
    (D : Matrix κ ι ℂ) (E : Matrix κ κ ℂ) :
    let p := affineDetPoly (fromBlocks T 0 0 (0 : Matrix κ κ ℂ)) (fromBlocks A B D E)
    (∀ d < Fintype.card κ, p.coeff d = 0) ∧
      p.coeff (Fintype.card κ) = T.det * E.det := by
  intro p
  obtain ⟨q, hq, h0⟩ := affineDetPoly_kernel_factor T A B D E
  change p = _ at hq
  constructor
  · intro d hd
    rw [hq, Polynomial.coeff_X_pow_mul']
    exact if_neg (not_le_of_gt hd)
  · rw [hq, Polynomial.coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self, h0]

private theorem affineDetPoly_reindex (S H : Matrix ι ι ℂ) (e : κ ≃ ι) :
    affineDetPoly (S.submatrix e e) (H.submatrix e e) = affineDetPoly S H := by
  rw [affineDetPoly, affineDetPoly, ← Matrix.det_submatrix_equiv_self e]
  rfl

/-- For a diagonal center, the leading coefficient is the product of its
nonzero entries times the velocity minor on the zero coordinates. -/
theorem affineDetPoly_diagonal_coeff (d : ι → ℂ) (H : Matrix ι ι ℂ) :
    let Z := {i // ¬ d i ≠ 0}
    let p := affineDetPoly (diagonal d) H
    (∀ k < Fintype.card Z, p.coeff k = 0) ∧
      p.coeff (Fintype.card Z) =
        (∏ i : {i // d i ≠ 0}, d i) * (H.submatrix (Subtype.val : Z → ι) Subtype.val).det := by
  classical
  intro Z p
  let NZ := {i // d i ≠ 0}
  let e : NZ ⊕ Z ≃ ι := Equiv.sumCompl (fun i => d i ≠ 0)
  let G := H.submatrix e e
  have hS : (diagonal d).submatrix e e =
      fromBlocks (diagonal fun i : NZ => d i) 0 0 (0 : Matrix Z Z ℂ) := by
    ext (i | i) (j | j)
    · change (diagonal d) (i : ι) (j : ι) = (diagonal (fun a : NZ => d a)) i j
      simp [Matrix.diagonal_apply, Subtype.coe_inj]
    · have hn : (i : ι) ≠ j := fun he => j.2 (he ▸ i.2)
      simp [e, Matrix.diagonal_apply, hn]
    · have hn : (i : ι) ≠ j := fun he => i.2 (he.symm ▸ j.2)
      simp [e, Matrix.diagonal_apply, hn]
    · have hz : d (j : ι) = 0 := not_not.mp j.2
      change (diagonal d) (i : ι) (j : ι) = 0
      simp [Matrix.diagonal_apply, not_not.mp i.2]
  have hp : p = affineDetPoly _ G := (affineDetPoly_reindex (diagonal d) H e).symm
  rw [hp, hS, ← Matrix.fromBlocks_toBlocks G]
  simpa only [G, e, Matrix.det_diagonal] using
    affineDetPoly_kernel_coeff (diagonal fun i : NZ => d i)
      G.toBlocks₁₁ G.toBlocks₁₂ G.toBlocks₂₁ G.toBlocks₂₂

theorem affineDetPoly_unitary_conjugation (U S H : Matrix ι ι ℂ) (hU : IsUnitary U) :
    affineDetPoly (U * S * Uᴴ) (U * H * Uᴴ) = affineDetPoly S H := by
  let f : Matrix ι ι ℂ →+* Matrix ι ι ℂ[X] := (Polynomial.C : ℂ →+* ℂ[X]).mapMatrix
  change (f (U * S * Uᴴ) + (X : ℂ[X]) • f (U * H * Uᴴ)).det = (f S + X • f H).det
  simp only [map_mul]
  rw [← Matrix.smul_mul, ← Matrix.mul_smul, ← Matrix.add_mul, ← Matrix.mul_add,
    Matrix.det_mul, Matrix.det_mul, mul_right_comm]
  have hscaled : f U * f Uᴴ = 1 := by rw [← map_mul, hU.1, map_one]
  rw [← Matrix.det_mul (f U) (f Uᴴ), hscaled, Matrix.det_one, one_mul]

/-- No inverse of the center is needed. In a Hermitian eigenbasis the
first potentially nonzero coefficient is its nonzero spectral product
times the determinant of the full compression to the kernel. -/
theorem affineDetPoly_hermitian_coeff (S H : Matrix ι ι ℂ) (hS : S.IsHermitian) :
    let U : Matrix ι ι ℂ := hS.eigenvectorUnitary
    let d : ι → ℂ := fun i => hS.eigenvalues i
    let Z := {i // ¬ d i ≠ 0}
    let p := affineDetPoly S H
    (∀ k < Fintype.card Z, p.coeff k = 0) ∧
      p.coeff (Fintype.card Z) =
        (∏ i : {i // d i ≠ 0}, d i) *
          ((Uᴴ * H * U).submatrix (Subtype.val : Z → ι) Subtype.val).det := by
  intro U d Z p
  have hU : IsUnitary U :=
    ⟨Matrix.mem_unitaryGroup_iff.mp hS.eigenvectorUnitary.2,
      Matrix.mem_unitaryGroup_iff'.mp hS.eigenvectorUnitary.2⟩
  have hS' : S = U * diagonal d * Uᴴ := hS.spectral_theorem
  have hH' : U * (Uᴴ * H * U) * Uᴴ = H := by
    calc
      _ = (U * Uᴴ) * H * (U * Uᴴ) := by simp only [Matrix.mul_assoc]
      _ = _ := by simp [hU.1]
  have hp : p = affineDetPoly (diagonal d) (Uᴴ * H * U) := by
    rw [← affineDetPoly_unitary_conjugation U _ _ hU, hH', ← hS']
  exact hp ▸ affineDetPoly_diagonal_coeff d (Uᴴ * H * U)

/-- In coordinates diagonalizing the sum of two involutions, the zero
eigenspace reduces both summands. The restriction of the first is again
an involution, opposite to the second, and is traceless in the balanced case. -/
theorem antipodal_diagonal_kernel_restriction (J K : Matrix ι ι ℂ) (d : ι → ℂ)
    (hJ : J * J = 1) (hK : K * K = 1) (hS : J + K = diagonal d)
    (htr : J.trace = K.trace) :
    let Z := {i // ¬ d i ≠ 0}
    let E := J.submatrix (Subtype.val : Z → ι) Subtype.val
    E * E = 1 ∧ E.trace = 0 ∧
      K.submatrix (Subtype.val : Z → ι) Subtype.val = -E := by
  classical
  intro Z E
  let NZ := {i // d i ≠ 0}
  let e : NZ ⊕ Z ≃ ι := Equiv.sumCompl (fun i => d i ≠ 0)
  have hJS : J * diagonal d = diagonal d * K := by
    rw [← hS, Matrix.mul_add, Matrix.add_mul, hJ, hK, add_comm]
  have hSJ : diagonal d * J = K * diagonal d := by
    rw [← hS, Matrix.mul_add, Matrix.add_mul, hJ, hK, add_comm]
  have hentry (i j : ι) : J i j * d j = d i * K i j := by
    simpa [Matrix.mul_diagonal, Matrix.diagonal_mul] using
      congrArg (fun A : Matrix ι ι ℂ => A i j) hJS
  have hentry' (i j : ι) : d i * J i j = K i j * d j := by
    simpa [Matrix.mul_diagonal, Matrix.diagonal_mul] using
      congrArg (fun A : Matrix ι ι ℂ => A i j) hSJ
  have hze (i : Z) : d (i : ι) = 0 := not_not.mp i.2
  have h12 (i : NZ) (j : Z) : J i j = 0 := by
    have hh := hentry' i j
    rw [hze, mul_zero] at hh
    exact (mul_eq_zero.mp hh).resolve_left i.2
  have h21 (i : Z) (j : NZ) : J i j = 0 := by
    have hh := hentry i j
    rw [hze, zero_mul] at hh
    exact (mul_eq_zero.mp hh).resolve_right j.2
  have hblocks : J.submatrix e e = fromBlocks
      (J.submatrix (Subtype.val : NZ → ι) Subtype.val) 0 0 E := by
    ext (i | i) (j | j)
    · rfl
    · exact h12 i j
    · exact h21 i j
    · rfl
  have hsq : J.submatrix e e * J.submatrix e e = 1 := by
    rw [Matrix.submatrix_mul_equiv _ _ _ _ e, hJ, Matrix.submatrix_one_equiv]
  have hE : E * E = 1 := by
    rw [hblocks, Matrix.fromBlocks_multiply] at hsq
    have hh := congrArg Matrix.toBlocks₂₂ hsq
    have hOne : Matrix.toBlocks₂₂ (1 : Matrix (NZ ⊕ Z) (NZ ⊕ Z) ℂ) = 1 := by
      ext i j
      simp [Matrix.toBlocks₂₂, Matrix.one_apply]
    simpa [hOne] using hh
  have hrev : K.submatrix (Subtype.val : Z → ι) Subtype.val = -E := by
    ext i j
    have he := congrArg (fun A : Matrix ι ι ℂ => A i j) hS
    change J i j + K i j = diagonal d i j at he
    have hz : diagonal d i j = 0 := by simp [Matrix.diagonal_apply, hze i]
    rw [hz] at he
    change K i j = -J i j
    exact eq_neg_of_add_eq_zero_right he
  have hmatch (i : NZ) : J i i = K i i := by
    have he := hentry i i
    rw [mul_comm (J i i)] at he
    exact mul_left_cancel₀ i.2 he
  have hsum (A : Matrix ι ι ℂ) : A.trace =
      (∑ i : NZ, A i i) + ∑ i : Z, A i i := by
    change (∑ i, A i i) = _
    rw [← Equiv.sum_comp e (fun i => A i i), Fintype.sum_sum_type]
    rfl
  have ht : E.trace = (-E).trace := by
    rw [hsum J, hsum K] at htr
    simp_rw [hmatch] at htr
    have hh := add_left_cancel htr
    change E.trace = (K.submatrix (Subtype.val : Z → ι) Subtype.val).trace at hh
    rwa [hrev] at hh
  have hzero : E.trace = 0 := by
    rw [Matrix.trace_neg] at ht
    linear_combination ht / 2
  exact ⟨hE, hzero, hrev⟩

private theorem unitary_conj_mul (U A B : Matrix ι ι ℂ) (hU : IsUnitary U) :
    (U * A * Uᴴ) * (U * B * Uᴴ) = U * (A * B) * Uᴴ := by
  calc
    _ = U * A * (Uᴴ * U) * B * Uᴴ := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hU.2, Matrix.mul_one, Matrix.mul_assoc U A B]

private theorem unitary_conj_trace (U A : Matrix ι ι ℂ) (hU : IsUnitary U) :
    (U * A * Uᴴ).trace = A.trace := by
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hU.2, Matrix.one_mul]

private theorem hermitian_involution_even_of_trace_zero (A : Matrix ι ι ℂ)
    (hA : A.IsHermitian) (hSq : A * A = 1) (hTr : A.trace = 0) :
    Even (Fintype.card ι) := by
  classical
  let U : Matrix ι ι ℂ := hA.eigenvectorUnitary
  let d : ι → ℂ := fun i => hA.eigenvalues i
  have hU : IsUnitary U :=
    ⟨Matrix.mem_unitaryGroup_iff.mp hA.eigenvectorUnitary.2,
      Matrix.mem_unitaryGroup_iff'.mp hA.eigenvectorUnitary.2⟩
  have hU' : IsUnitary Uᴴ := ⟨by simpa using hU.2, by simpa using hU.1⟩
  have hd : Uᴴ * A * U = diagonal d := hA.star_mul_self_mul_eq_diagonal
  have hh := unitary_conj_mul Uᴴ A A hU'
  rw [Matrix.conjTranspose_conjTranspose, hd, hSq, Matrix.mul_one, hU.2,
    Matrix.diagonal_mul_diagonal] at hh
  have hs (i : ι) : d i = 1 ∨ d i = -1 := by
    have h := congrArg (fun M : Matrix ι ι ℂ => M i i) hh
    simp only [Matrix.diagonal_apply_eq, Matrix.one_apply_eq] at h
    have hz : (d i - 1) * (d i + 1) = 0 := by linear_combination h
    rcases mul_eq_zero.mp hz with h | h
    · exact Or.inl (sub_eq_zero.mp h)
    · exact Or.inr (eq_neg_of_add_eq_zero_left h)
  have hsum : (∑ i, d i) = 0 := by
    have hh := unitary_conj_trace Uᴴ A hU'
    rw [Matrix.conjTranspose_conjTranspose, hd, hTr, Matrix.trace_diagonal] at hh
    exact hh
  let P := {i // d i = 1}
  let N := {i // d i ≠ 1}
  let e : P ⊕ N ≃ ι := Equiv.sumCompl (fun i => d i = 1)
  have hp (i : P) : d (i : ι) = 1 := i.2
  have hn (i : N) : d (i : ι) = -1 := (hs i).resolve_left i.2
  rw [← Equiv.sum_comp e d, Fintype.sum_sum_type] at hsum
  change (∑ i : P, d (i : ι)) + ∑ i : N, d (i : ι) = 0 at hsum
  simp only [hp, hn, Finset.sum_const, Finset.card_univ, nsmul_one, smul_neg] at hsum
  have hcard : Fintype.card P = Fintype.card N := by
    exact_mod_cast (eq_of_sub_eq_zero hsum : (Fintype.card P : ℂ) = Fintype.card N)
  refine ⟨Fintype.card P, ?_⟩
  rw [← Fintype.card_congr e, Fintype.card_sum, hcard]

/-- Equal traces force an even-dimensional kernel for the sum of Hermitian
involutions, so every singular balanced center loses at least two determinant
orders, for arbitrary velocity. -/
theorem antipodal_hermitian_even_kernel (J K : Matrix ι ι ℂ)
    (hJH : J.IsHermitian) (hKH : K.IsHermitian)
    (hJ : J * J = 1) (hK : K * K = 1) (hTr : J.trace = K.trace) :
    let hS := hJH.add hKH
    Even (Fintype.card {i // ¬ (hS.eigenvalues i : ℂ) ≠ 0}) := by
  classical
  intro hS
  let U : Matrix ι ι ℂ := hS.eigenvectorUnitary
  let J' := Uᴴ * J * U
  let K' := Uᴴ * K * U
  have hU' : IsUnitary Uᴴ := ⟨by
      simpa only [Matrix.conjTranspose_conjTranspose] using
        Matrix.mem_unitaryGroup_iff'.mp hS.eigenvectorUnitary.2, by
      simpa only [Matrix.conjTranspose_conjTranspose] using
        Matrix.mem_unitaryGroup_iff.mp hS.eigenvectorUnitary.2⟩
  have hs (A : Matrix ι ι ℂ) (h : A * A = 1) :
      (Uᴴ * A * U) * (Uᴴ * A * U) = 1 := by
    have hh := unitary_conj_mul Uᴴ A A hU'
    rwa [Matrix.conjTranspose_conjTranspose, h, Matrix.mul_one, show Uᴴ * U = 1 by
      simpa using hU'.1] at hh
  have hd : J' + K' = diagonal (fun i => (hS.eigenvalues i : ℂ)) := by
    change Uᴴ * J * U + Uᴴ * K * U = _
    rw [← Matrix.add_mul, ← Matrix.mul_add]
    exact hS.star_mul_self_mul_eq_diagonal
  have ht (A : Matrix ι ι ℂ) : (Uᴴ * A * U).trace = A.trace := by
    simpa only [Matrix.conjTranspose_conjTranspose] using unitary_conj_trace Uᴴ A hU'
  obtain ⟨he, hzero, _⟩ := antipodal_diagonal_kernel_restriction J' K'
    (fun i => (hS.eigenvalues i : ℂ)) (hs J hJ) (hs K hK) hd
      (by change (Uᴴ * J * U).trace = (Uᴴ * K * U).trace; rw [ht, ht, hTr])
  have hj' : J'.IsHermitian := by
    change (Uᴴ * J * U)ᴴ = Uᴴ * J * U
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, hJH.eq, Matrix.mul_assoc]
  exact hermitian_involution_even_of_trace_zero _ (hj'.submatrix _) he hzero

/-- A basis-free corank test and the corresponding determinant vanishing.
No commutation of the velocity with the involutions is needed. -/
theorem antipodal_even_corank_and_vanishing (J K H : Matrix ι ι ℂ)
    (hJH : J.IsHermitian) (hKH : K.IsHermitian)
    (hJ : J * J = 1) (hK : K * K = 1) (hTr : J.trace = K.trace) :
    let r := Fintype.card ι - (J + K).rank
    Even r ∧ ∀ k < r, (affineDetPoly (J + K) H).coeff k = 0 := by
  classical
  intro r
  let hS := hJH.add hKH
  let d : ι → ℂ := fun i => hS.eigenvalues i
  have he : r = Fintype.card {i // ¬ d i ≠ 0} := by
    have hcard : Fintype.card {i // d i ≠ 0} =
        Fintype.card {i // hS.eigenvalues i ≠ 0} := by
      apply Fintype.card_congr
      exact Equiv.subtypeEquivRight (fun i => by simp [d, Complex.ofReal_eq_zero])
    rw [Fintype.card_subtype_compl (fun i => d i ≠ 0), hcard,
      ← Matrix.IsHermitian.rank_eq_card_non_zero_eigs hS]
  rw [he]
  exact ⟨antipodal_hermitian_even_kernel J K hJH hKH hJ hK hTr,
    (affineDetPoly_hermitian_coeff (J + K) H hS).1⟩

end
end MOC
