import MOC.PhaseMove
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Matrix
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.UniformSpace.Matrix

/-! Jacobi's determinant derivative at a diagonal matrix, including singular diagonal sums. -/

open BigOperators Matrix

namespace MOC

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- At a diagonal matrix only the diagonal entry derivatives contribute to the first variation. -/
theorem hasDerivAt_det_diagonal
    (M : ℝ → Matrix ι ι ℂ) (V : Matrix ι ι ℂ) (t : ℝ) (h : ι → ℂ)
    (hvalue : M t = diagonal h)
    (hderiv : ∀ i j, HasDerivAt (fun s => M s i j) (V i j) t) :
    HasDerivAt (fun s => (M s).det)
      (∑ i, (∏ j ∈ Finset.univ.erase i, h j) * V i i) t := by
  classical
  let f (σ : Equiv.Perm ι) (s : ℝ) := ∏ i, M s (σ i) i
  let df (σ : Equiv.Perm ι) := ∑ i, (∏ j ∈ Finset.univ.erase i, M t (σ j) j) * V (σ i) i
  let c (σ : Equiv.Perm ι) : ℂ := ((Equiv.Perm.sign σ : ℤ) : ℂ)
  have hσ (σ : Equiv.Perm ι) : HasDerivAt (fun s => c σ * f σ s) (c σ * df σ) t := by
    apply HasDerivAt.const_mul
    have hp := HasDerivAt.finset_prod (u := Finset.univ) (f := fun i s => M s (σ i) i)
      (f' := fun i => V (σ i) i) (fun i _ => hderiv (σ i) i)
    simpa only [f, df, Finset.prod_apply, smul_eq_mul] using hp
  have hz (σ : Equiv.Perm ι) (hσ' : σ ≠ 1) : df σ = 0 := by
    have hex : ∃ j, σ j ≠ j := by
      exact not_forall.mp (fun hh => hσ' (Equiv.ext hh))
    obtain ⟨j, hj⟩ := hex
    apply Finset.sum_eq_zero
    intro i _
    have hk : ∃ k, k ≠ i ∧ σ k ≠ k := by
      by_cases hji : j = i
      · exact ⟨σ j, fun hh => hj (hh.trans hji.symm), fun hh => hj (σ.injective hh)⟩
      · exact ⟨j, hji, hj⟩
    obtain ⟨k, hki, hk⟩ := hk
    have hp : (∏ j ∈ Finset.univ.erase i, M t (σ j) j) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hki, Finset.mem_univ k⟩)
      simp [hvalue, Matrix.diagonal_apply_ne _ hk]
    rw [hp, zero_mul]
  have hd := HasDerivAt.sum (u := Finset.univ) (fun σ _ => hσ σ)
  have hsum : (∑ σ, c σ * df σ) = ∑ i, (∏ j ∈ Finset.univ.erase i, h j) * V i i := by
    rw [Finset.sum_eq_single (1 : Equiv.Perm ι)]
    · simp [c, df, hvalue]
    · intro σ _ hc
      rw [hz σ hc, mul_zero]
    · simp
  rw [hsum] at hd
  simpa only [Matrix.det_apply', c, f] using hd

/-- The invertible diagonal formula divides each contribution by the corresponding eigenvalue. -/
theorem hasDerivAt_det_diagonal_of_nonzero
    (M : ℝ → Matrix ι ι ℂ) (V : Matrix ι ι ℂ) (t : ℝ) (h : ι → ℂ)
    (hvalue : M t = diagonal h) (hnz : ∀ i, h i ≠ 0)
    (hderiv : ∀ i j, HasDerivAt (fun s => M s i j) (V i j) t) :
    HasDerivAt (fun s => (M s).det) ((diagonal h).det * ∑ i, V i i / h i) t := by
  convert hasDerivAt_det_diagonal M V t h hvalue hderiv using 1
  rw [Matrix.det_diagonal, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.mul_prod_erase Finset.univ h (Finset.mem_univ i)]
  field_simp [hnz i]
  ring

/-- The support derivative on a diagonal sum, written in the form used by the phase move. -/
theorem hasDerivAt_support_of_commutator
    (M : ℝ → Matrix ι ι ℂ) (B K : Matrix ι ι ℂ) (t : ℝ) (h : ι → ℂ) (η : ℂ)
    (hvalue : M t = diagonal h) (hnz : ∀ i, h i ≠ 0)
    (hderiv : ∀ i j, HasDerivAt (fun s => M s i j) ((K * B - B * K) i j) t) :
    let J := diagonal (fun i => (h i)⁻¹)
    let κ := η * (diagonal h).det
    HasDerivAt (fun s => (η * (M s).det).re) ((κ • (B * J - J * B) * K).trace.re) t := by
  let J := diagonal (fun i => (h i)⁻¹)
  let κ := η * (diagonal h).det
  have htrace : (∑ i, (K * B - B * K) i i / h i) = ((B * J - J * B) * K).trace := by
    have he : (∑ i, (K * B - B * K) i i / h i) = ((K * B - B * K) * J).trace := by
      simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_diagonal, J, div_eq_mul_inv]
    rw [he, Matrix.sub_mul, Matrix.sub_mul, Matrix.trace_sub, Matrix.trace_sub,
      Matrix.trace_mul_cycle K B J, Matrix.trace_mul_cycle B K J,
      Matrix.trace_mul_comm (J * K) B, Matrix.trace_mul_comm (J * B) K]
    simp only [Matrix.mul_assoc]
  have hd := (hasDerivAt_det_diagonal_of_nonzero M (K * B - B * K) t h hvalue hnz
    hderiv).const_mul η
  have hr := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hd
  simpa only [htrace, Function.comp_apply, Complex.reCLM_apply, Matrix.smul_mul,
    Matrix.trace_smul, smul_eq_mul, mul_assoc, κ, J] using hr

omit [DecidableEq ι] in
/-- Skew-Hermitian directions detect exactly the skew-Hermitian part under real trace pairing. -/
theorem conjTranspose_eq_of_real_trace_mul_skew_eq_zero (C : Matrix ι ι ℂ)
    (hc : ∀ K : Matrix ι ι ℂ, Kᴴ = -K → (C * K).trace.re = 0) : Cᴴ = C := by
  let K := C - Cᴴ
  have hK : Kᴴ = -K := by
    simp only [K, Matrix.conjTranspose_sub, Matrix.conjTranspose_conjTranspose, neg_sub]
  have hre := hc K hK
  have hconj : (Cᴴ * K).trace.re = 0 := by
    have he := congrArg Complex.re (Matrix.trace_conjTranspose (C * K))
    rw [Matrix.conjTranspose_mul, hK, Matrix.neg_mul, Matrix.trace_neg, Matrix.trace_mul_comm] at he
    rw [Complex.star_def, Complex.conj_re, hre, Complex.neg_re, neg_eq_zero] at he
    exact he
  have hzero : (K * Kᴴ).trace.re = 0 := by
    rw [hK, Matrix.mul_neg, Matrix.trace_neg, Complex.neg_re, neg_eq_zero]
    change ((C - Cᴴ) * K).trace.re = 0
    rw [Matrix.sub_mul, Matrix.trace_sub, Complex.sub_re, hre, hconj, sub_zero]
  have hsum : (∑ i, ∑ j, Complex.normSq (K i j)) = 0 := by
    have hterm (i j : ι) : Complex.reAddGroupHom (K i j * star (K i j)) =
        Complex.normSq (K i j) := by
      change (K i j * star (K i j)).re = _
      rw [Complex.star_def, Complex.mul_conj, Complex.ofReal_re]
    change Complex.reAddGroupHom (∑ i, ∑ j, K i j * star (K i j)) = 0 at hzero
    simpa only [map_sum, hterm] using hzero
  have hKzero : K = 0 := by
    ext i j
    have hs : (∑ j, Complex.normSq (K i j)) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun k _ =>
        Finset.sum_nonneg (fun l _ => Complex.normSq_nonneg (K k l)))).mp hsum i (Finset.mem_univ i)
    have hij : Complex.normSq (K i j) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => Complex.normSq_nonneg (K i k))).mp
        hs j (Finset.mem_univ j)
    simpa only [Matrix.zero_apply] using Complex.normSq_eq_zero.mp hij
  exact (sub_eq_zero.mp hKzero).symm

/-- A support maximum on the unitary orbit of a diagonal sum forces the Hermitian
commutator appearing in the phase move. -/
theorem stationary_of_unitary_support_max
    (h : ι → ℂ) (B : Matrix ι ι ℂ) (η : ℂ) (hnz : ∀ i, h i ≠ 0)
    (hmax : ∀ R : Matrix ι ι ℂ, IsUnitary R →
      (η * (diagonal h - B + R * B * Rᴴ).det).re ≤ (η * (diagonal h).det).re) :
    let M := diagonal (fun i => (h i)⁻¹)
    let κ := η * (diagonal h).det
    (κ • (B * M - M * B))ᴴ = κ • (B * M - M * B) := by
  letI : NormedRing (Matrix ι ι ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Matrix ι ι ℂ) := Matrix.linftyOpNormedAlgebra
  dsimp only
  apply conjTranspose_eq_of_real_trace_mul_skew_eq_zero
  intro K hK
  let R (s : ℝ) := NormedSpace.exp ℝ (s • K)
  let Q (s : ℝ) := NormedSpace.exp ℝ (s • (-K))
  let S (s : ℝ) := diagonal h - B + R s * B * Q s
  have hR0 : R 0 = 1 := by simp [R, NormedSpace.exp_zero]
  have hQ0 : Q 0 = 1 := by simp [Q, NormedSpace.exp_zero]
  have hstar (s : ℝ) : (R s)ᴴ = Q s := by
    change star (NormedSpace.exp ℝ (s • K)) = _
    rw [NormedSpace.star_exp]
    change NormedSpace.exp ℝ ((s • K)ᴴ) = _
    rw [Matrix.conjTranspose_smul, star_trivial, hK]
  have hRunitary (s : ℝ) : IsUnitary (R s) := by
    have hskew : s • K ∈ skewAdjoint (Matrix ι ι ℂ) := by
      apply skewAdjoint.mem_iff.mpr
      change (s • K)ᴴ = -(s • K)
      rw [Matrix.conjTranspose_smul, star_trivial, hK, smul_neg]
    have hu := unitary.mem_iff.mp (NormedSpace.exp_mem_unitary_of_mem_skewAdjoint ℝ hskew)
    exact ⟨hu.2, hu.1⟩
  have hR : HasDerivAt R K (0 : ℝ) := by
    simpa [R, NormedSpace.exp_zero] using
      hasDerivAt_exp_smul_const (𝕂 := ℝ) K (0 : ℝ)
  have hQ : HasDerivAt Q (-K) (0 : ℝ) := by
    simpa [Q, NormedSpace.exp_zero] using
      hasDerivAt_exp_smul_const (𝕂 := ℝ) (-K) (0 : ℝ)
  have hS0 : S 0 = diagonal h := by simp [S, hR0, hQ0]
  have hS : HasDerivAt S (K * B - B * K) (0 : ℝ) := by
    have hs := (hasDerivAt_const (0 : ℝ) (diagonal h - B)).add ((hR.mul_const B).mul hQ)
    simpa only [S, hR0, hQ0, Matrix.mul_one, Matrix.one_mul, Matrix.mul_neg,
      ← sub_eq_add_neg, zero_add] using hs
  have hpoint (i j : ι) : HasDerivAt (fun s => S s i j) ((K * B - B * K) i j) 0 := by
    let ev : Matrix ι ι ℂ →L[ℝ] ℂ :=
      ⟨Matrix.entryLinearMap ℝ ℂ i j, (continuous_apply j).comp (continuous_apply i)⟩
    exact ev.hasFDerivAt.comp_hasDerivAt 0 hS
  have hderiv := hasDerivAt_support_of_commutator S B K 0 h η hS0 hnz hpoint
  have hlocal : IsLocalMax (fun t => (η * (S t).det).re) 0 := Filter.Eventually.of_forall fun t => by
    simp only [S, ← hstar t, hS0]
    simpa only [hS0, S, hR0, hQ0, Matrix.one_mul, Matrix.mul_one, sub_add_cancel] using
      hmax (R t) (hRunitary t)
  exact hlocal.hasDerivAt_eq_zero hderiv

/-- At a support maximum that also maximizes squared Frobenius norm, a distinguished row
chosen to have no within-eigenspace coupling has zero coupling to every other row. -/
theorem row_zero_of_diagonal_support_frobenius_max
    (h : Unit ⊕ ι → ℂ) (B : Matrix (Unit ⊕ ι) (Unit ⊕ ι) ℂ)
    (η : ℂ) (hnz : ∀ i, h i ≠ 0)
    (hB : B * Bᴴ = Bᴴ * B)
    (hA : (diagonal h - B) * (diagonal h - B)ᴴ = (diagonal h - B)ᴴ * (diagonal h - B))
    (hmax : ∀ R : Matrix (Unit ⊕ ι) (Unit ⊕ ι) ℂ, IsUnitary R →
      (η * (diagonal h - B + R * B * Rᴴ).det).re ≤ (η * (diagonal h).det).re)
    (htie : ∀ R : Matrix (Unit ⊕ ι) (Unit ⊕ ι) ℂ, IsUnitary R →
      let S := diagonal h - B + R * B * Rᴴ
      (η * S.det).re = (η * (diagonal h).det).re →
      (∑ i, ∑ j, Complex.normSq (S i j)) ≤ ∑ i, ∑ j, Complex.normSq (diagonal h i j))
    (hwithin : ∀ i : ι, h (Sum.inl ()) = h (Sum.inr i) →
      B (Sum.inl ()) (Sum.inr i) * B (Sum.inr i) (Sum.inl ()) = 0) :
    ∀ j : ι, B (Sum.inl ()) (Sum.inr j) = 0 := by
  intro j
  by_contra hj
  obtain ⟨R, hR, he, hlt⟩ := stationary_normal_diagonal_exists_phase_move h B η hnz hB hA
    (stationary_of_unitary_support_max h B η hnz hmax) hwithin ⟨j, hj⟩
  exact (not_le_of_lt hlt) (htie R hR he)

<<<<<<< HEAD
private theorem isUnitary_submatrix_equiv {κ : Type*} [Fintype κ] [DecidableEq κ]
    (e : κ ≃ ι) {R : Matrix ι ι ℂ} (hR : IsUnitary R) :
    IsUnitary (R.submatrix e e) := by
  constructor
  · rw [Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, hR.1,
      Matrix.submatrix_one_equiv]
  · rw [Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, hR.2,
      Matrix.submatrix_one_equiv]

omit [DecidableEq ι] in
private theorem normSq_sum_submatrix_equiv {κ : Type*} [Fintype κ]
    (e : κ ≃ ι) (Q : Matrix ι ι ℂ) :
    (∑ i, ∑ j, Complex.normSq ((Q.submatrix e e) i j)) =
      ∑ i, ∑ j, Complex.normSq (Q i j) := by
  simp only [Matrix.submatrix_apply]
  calc
    _ = ∑ i : κ, ∑ j : ι, Complex.normSq (Q (e i) j) :=
      Finset.sum_congr rfl (fun i _ => Equiv.sum_comp e (fun j => Complex.normSq (Q (e i) j)))
    _ = _ := Equiv.sum_comp e (fun i => ∑ j : ι, Complex.normSq (Q i j))

/-- A simultaneous determinant-support and Frobenius maximizer is diagonal once each
compression inside a repeated eigenspace of its sum is diagonal. -/
theorem diagonal_of_support_frobenius_max
    (h : ι → ℂ) (B : Matrix ι ι ℂ)
    (η : ℂ) (hnz : ∀ i, h i ≠ 0)
    (hB : B * Bᴴ = Bᴴ * B)
    (hA : (diagonal h - B) * (diagonal h - B)ᴴ = (diagonal h - B)ᴴ * (diagonal h - B))
    (hmax : ∀ R : Matrix ι ι ℂ, IsUnitary R →
      (η * (diagonal h - B + R * B * Rᴴ).det).re ≤ (η * (diagonal h).det).re)
    (htie : ∀ R : Matrix ι ι ℂ, IsUnitary R →
      let S := diagonal h - B + R * B * Rᴴ
      (η * S.det).re = (η * (diagonal h).det).re →
      (∑ i, ∑ j, Complex.normSq (S i j)) ≤ ∑ i, ∑ j, Complex.normSq (diagonal h i j))
    (hwithin : ∀ i j, h i = h j → i ≠ j → B i j = 0) :
    B = diagonal fun i => B i i := by
  ext i j
  by_cases hij : i = j
  · subst j
    exact (Matrix.diagonal_apply_eq _ i).symm
  rw [Matrix.diagonal_apply_ne _ hij]
  let single : Unit ≃ {k : ι // k = i} :=
    { toFun := fun _ => ⟨i, rfl⟩
      invFun := fun _ => ()
      left_inv := fun _ => Subsingleton.elim _ _
      right_inv := fun k => Subtype.ext k.property.symm }
  let e : (Unit ⊕ {k : ι // k ≠ i}) ≃ ι :=
    (Equiv.sumCongr single (Equiv.refl _)).trans (Equiv.sumCompl (fun k => k = i))
  let h' := h ∘ e
  let B' := B.submatrix e e
  have hD : diagonal h' = (diagonal h).submatrix e e :=
    (Matrix.submatrix_diagonal_equiv h e).symm
  have hB' : B' * B'ᴴ = B'ᴴ * B' := by
    simpa only [B', Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv] using
      congrArg (fun T : Matrix ι ι ℂ => T.submatrix e e) hB
  have hAs : diagonal h' - B' = (diagonal h - B).submatrix e e := by
    rw [hD]
    rfl
  have hA' : (diagonal h' - B') * (diagonal h' - B')ᴴ =
      (diagonal h' - B')ᴴ * (diagonal h' - B') := by
    rw [hAs, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv,
      Matrix.submatrix_mul_equiv, hA]
  let κ := Unit ⊕ {k : ι // k ≠ i}
  let liftR (R : Matrix κ κ ℂ) := R.submatrix e.symm e.symm
  have hlift (R : Matrix κ κ ℂ) : (liftR R).submatrix e e = R := by
    simp only [liftR, Matrix.submatrix_submatrix, Equiv.symm_comp_self, Matrix.submatrix_id_id]
  have hsum (R : Matrix κ κ ℂ) :
      diagonal h' - B' + R * B' * Rᴴ =
        (diagonal h - B + liftR R * B * (liftR R)ᴴ).submatrix e e := by
    change diagonal h' - B' + R * B' * Rᴴ =
      (diagonal h - B).submatrix e e + (liftR R * B * (liftR R)ᴴ).submatrix e e
    rw [← hAs, ← Matrix.submatrix_mul_equiv (liftR R * B) (liftR R)ᴴ e e e,
      ← Matrix.submatrix_mul_equiv (liftR R) B e e e,
      ← Matrix.conjTranspose_submatrix, hlift]
  have hmax' (R : Matrix κ κ ℂ) (hR : IsUnitary R) :
      (η * (diagonal h' - B' + R * B' * Rᴴ).det).re ≤ (η * (diagonal h').det).re := by
    rw [hsum, hD, Matrix.det_submatrix_equiv_self, Matrix.det_submatrix_equiv_self]
    exact hmax (liftR R) (isUnitary_submatrix_equiv e.symm hR)
  have htie' (R : Matrix κ κ ℂ) (hR : IsUnitary R) :
      let S := diagonal h' - B' + R * B' * Rᴴ
      (η * S.det).re = (η * (diagonal h').det).re →
      (∑ i, ∑ j, Complex.normSq (S i j)) ≤ ∑ i, ∑ j, Complex.normSq (diagonal h' i j) := by
    dsimp only
    rw [hsum, hD, Matrix.det_submatrix_equiv_self, Matrix.det_submatrix_equiv_self,
      normSq_sum_submatrix_equiv, normSq_sum_submatrix_equiv]
    exact htie (liftR R) (isUnitary_submatrix_equiv e.symm hR)
  have hwithin' (k : {k : ι // k ≠ i}) (hk : h' (Sum.inl ()) = h' (Sum.inr k)) :
      B' (Sum.inl ()) (Sum.inr k) * B' (Sum.inr k) (Sum.inl ()) = 0 := by
    change h i = h k at hk
    change B i k * B k i = 0
    rw [hwithin i k hk (Ne.symm k.property), zero_mul]
  exact row_zero_of_diagonal_support_frobenius_max h' B' η (fun k => hnz (e k)) hB' hA'
    hmax' htie' hwithin' ⟨j, Ne.symm hij⟩

=======
>>>>>>> origin/main
end MOC
