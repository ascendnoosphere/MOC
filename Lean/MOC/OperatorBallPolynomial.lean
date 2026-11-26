import MOC.Variational
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Data.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.LinearAlgebra.Matrix.PosDef

/-! Operator norm and holomorphic estimates for complex matrices. -/

open BigOperators Filter Matrix Metric
open scoped Kronecker Matrix.L2OpNorm Polynomial Topology

namespace MOC

noncomputable section

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

private theorem l2_opNorm_starAlgHom (f : Matrix ι ι ℂ →⋆ₐ[ℂ] Matrix κ κ ℂ)
    (hf : Function.Injective f) (A : Matrix ι ι ℂ) : ‖f A‖ = ‖A‖ := by
  let F := Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)
  let G := Matrix.toEuclideanCLM (n := κ) (𝕜 := ℂ)
  let ψ := (G : _ →⋆ₐ[ℂ] _).comp (f.comp (F.symm : _ →⋆ₐ[ℂ] _))
  have hψ : Function.Injective ψ := G.injective.comp (hf.comp F.symm.injective)
  have h := NonUnitalStarAlgHom.norm_map ψ.toNonUnitalStarAlgHom hψ (F A)
  change ‖G (f (F.symm (F A)))‖ = ‖F A‖ at h
  rw [StarAlgEquiv.symm_apply_apply] at h
  exact h

private def kroneckerIdentityHom :
    Matrix ι ι ℂ →⋆ₐ[ℂ] Matrix (ι × κ) (ι × κ) ℂ where
  toFun A := A ⊗ₖ (1 : Matrix κ κ ℂ)
  map_one' := Matrix.one_kronecker_one
  map_zero' := Matrix.zero_kronecker _
  map_add' A B := Matrix.add_kronecker A B _
  map_mul' A B := by rw [← Matrix.mul_kronecker_mul, Matrix.mul_one]
  commutes' z := by
    simp only [Algebra.algebraMap_eq_smul_one, Matrix.smul_kronecker, Matrix.one_kronecker_one]
  map_star' A := by
    apply Matrix.ext
    rintro ⟨i, k⟩ ⟨j, l⟩
    by_cases h : k = l
    · subst l
      simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply,
        Matrix.kronecker_apply, Matrix.one_apply_eq, mul_one]
    · simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply,
        Matrix.kronecker_apply, Matrix.one_apply_ne h, Matrix.one_apply_ne h.symm,
        mul_zero, star_zero]

/-- Amplification by a nonempty identity matrix preserves the operator norm. -/
theorem l2_opNorm_kronecker_one [Nonempty κ] (A : Matrix ι ι ℂ) :
    ‖A ⊗ₖ (1 : Matrix κ κ ℂ)‖ = ‖A‖ := by
  refine l2_opNorm_starAlgHom kroneckerIdentityHom ?_ A
  intro B C h
  obtain ⟨k⟩ := ‹Nonempty κ›
  apply Matrix.ext
  intro i j
  have hk := congrArg (fun M : Matrix (ι × κ) (ι × κ) ℂ => M (i, k) (j, k)) h
  change (B ⊗ₖ (1 : Matrix κ κ ℂ)) (i, k) (j, k) =
    (C ⊗ₖ (1 : Matrix κ κ ℂ)) (i, k) (j, k) at hk
  simpa only [Matrix.kronecker_apply, Matrix.one_apply_eq, mul_one] using hk

private theorem l2_opNorm_reindex (e : ι ≃ κ) (A : Matrix ι ι ℂ) :
    ‖Matrix.reindex e e A‖ = ‖A‖ := by
  let f : Matrix ι ι ℂ →⋆ₐ[ℂ] Matrix κ κ ℂ :=
    { (Matrix.reindexAlgEquiv ℂ ℂ e).toAlgHom with map_star' := fun _ => rfl }
  exact l2_opNorm_starAlgHom f (Matrix.reindexAlgEquiv ℂ ℂ e).injective A

/-- The same identity holds when the identity matrix is the first factor. -/
theorem l2_opNorm_one_kronecker [Nonempty κ] (A : Matrix ι ι ℂ) :
    ‖(1 : Matrix κ κ ℂ) ⊗ₖ A‖ = ‖A‖ := by
  let e := Equiv.prodComm ι κ
  have he : Matrix.reindex e e (A ⊗ₖ (1 : Matrix κ κ ℂ)) =
      (1 : Matrix κ κ ℂ) ⊗ₖ A := by
    apply Matrix.ext
    rintro ⟨k, i⟩ ⟨l, j⟩
    exact mul_comm _ _
  rw [← he, l2_opNorm_reindex, l2_opNorm_kronecker_one]

private theorem exists_torus_norm_ge (f : (ι → ℂ) → ℂ)
    (hf : ∀ x i, Differentiable ℂ (fun z => f (Function.update x i z)))
    (x : ι → ℂ) (hx : ∀ i, ‖x i‖ ≤ 1) :
    ∃ y : ι → ℂ, (∀ i, ‖y i‖ = 1) ∧ ‖f x‖ ≤ ‖f y‖ := by
  have h (s : Finset ι) : ∃ y : ι → ℂ,
      (∀ i, ‖y i‖ ≤ 1) ∧ (∀ i ∈ s, ‖y i‖ = 1) ∧ ‖f x‖ ≤ ‖f y‖ := by
    induction s using Finset.induction_on with
    | empty => exact ⟨x, hx, fun i hi => (Finset.not_mem_empty i hi).elim, le_rfl⟩
    | insert i s hi ih =>
      obtain ⟨y, hy, hys, hxy⟩ := ih
      obtain ⟨z, hz, hzmax⟩ := Complex.exists_mem_frontier_isMaxOn_norm
        (U := Metric.ball (0 : ℂ) 1) Metric.isBounded_ball
        ⟨0, Metric.mem_ball_self zero_lt_one⟩ (hf y i).diffContOnCl
      rw [frontier_ball 0 one_ne_zero] at hz
      have hzn : ‖z‖ = 1 := mem_sphere_zero_iff_norm.mp hz
      have hiy : y i ∈ closure (Metric.ball (0 : ℂ) 1) := by
        rw [closure_ball 0 one_ne_zero]
        exact mem_closedBall_zero_iff.mpr (hy i)
      have hvalue : ‖f y‖ ≤ ‖f (Function.update y i z)‖ := by
        simpa only [Function.comp_apply, Function.update_eq_self] using
          isMaxOn_iff.mp hzmax (y i) hiy
      refine ⟨Function.update y i z, ?_, ?_, hxy.trans hvalue⟩
      · intro j
        by_cases hj : j = i
        · subst j
          simpa only [Function.update_self] using hzn.le
        · simpa only [Function.update_of_ne hj] using hy j
      · intro j hj
        rcases Finset.mem_insert.mp hj with rfl | hjs
        · simpa only [Function.update_self] using hzn
        · have hji : j ≠ i := fun hji => hi (hji ▸ hjs)
          simpa only [Function.update_of_ne hji] using hys j hjs
  obtain ⟨y, _, hunit, hge⟩ := h Finset.univ
  exact ⟨y, fun i => hunit i (Finset.mem_univ i), hge⟩

private theorem norm_entry_le_diagonal_norm (d : ι → ℂ) (i : ι) :
    ‖d i‖ ≤ ‖diagonal d‖ := by
  have h := (diagonal d).l2_opNorm_mulVec (EuclideanSpace.single i (1 : ℂ))
  have he : (EuclideanSpace.equiv ι ℂ).symm
      (diagonal d *ᵥ EuclideanSpace.single i (1 : ℂ)) = EuclideanSpace.single i (d i) := by
    apply congrArg (EuclideanSpace.equiv ι ℂ).symm
    change diagonal d *ᵥ Pi.single i 1 = Pi.single i (d i)
    rw [Matrix.mulVec_single_one]
    funext j
    by_cases hj : j = i
    · subst j
      simp only [Matrix.diagonal_apply_eq, Pi.single_eq_same]
    · simp only [Matrix.diagonal_apply_ne _ hj, Pi.single_apply, if_neg hj]
  simpa only [he, EuclideanSpace.norm_single, norm_one, mul_one] using h

private theorem unitary_diagonal_of_norm_one (d : ι → ℂ) (hd : ∀ i, ‖d i‖ = 1) :
    IsUnitary (diagonal d) := by
  have hm (i : ι) : d i * star (d i) = 1 := by
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, hd i, one_pow,
      Complex.ofReal_one]
  have hn (i : ι) : star (d i) * d i = 1 := (mul_comm _ _).trans (hm i)
  constructor
  · rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
    simp only [Pi.star_apply, hm, Matrix.diagonal_one]
  · rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
    simp only [Pi.star_apply, hn, Matrix.diagonal_one]

private theorem polar_diagonal_of_invertible_contraction (Z : Matrix ι ι ℂ)
    (hZ : ‖Z‖ ≤ 1) (hzdet : IsUnit Z.det) :
    ∃ L R : Matrix ι ι ℂ, IsUnitary L ∧ IsUnitary R ∧
      ∃ d : ι → ℂ, (∀ i, ‖d i‖ ≤ 1) ∧ Z = L * diagonal d * Rᴴ := by
  let hGram := Matrix.posSemidef_conjTranspose_mul_self Z
  let S := hGram.sqrt
  have hSpos : S.PosSemidef := hGram.posSemidef_sqrt
  have hSadj : Sᴴ = S := hSpos.1.eq
  have hSsq : S * S = Zᴴ * Z := hGram.sqrt_mul_self
  have hSdet : IsUnit S.det := isUnit_iff_ne_zero.mpr (by
    intro hz
    have h := congrArg Matrix.det hSsq
    rw [Matrix.det_mul, Matrix.det_mul, hz, zero_mul, Matrix.det_conjTranspose] at h
    exact (mul_ne_zero (star_ne_zero.mpr hzdet.ne_zero) hzdet.ne_zero) h.symm)
  let U := Z * S⁻¹
  have hUadj : Uᴴ * U = 1 := by
    have hInvAdj : (S⁻¹)ᴴ * S = 1 := by
      have he := congrArg Matrix.conjTranspose (S.mul_nonsing_inv hSdet)
      simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_one, hSadj] using he
    calc
      Uᴴ * U = (S⁻¹)ᴴ * (Zᴴ * Z) * S⁻¹ := by
        rw [U, Matrix.conjTranspose_mul]
        simp only [mul_assoc]
      _ = (S⁻¹)ᴴ * S * (S * S⁻¹) := by rw [← hSsq]; simp only [mul_assoc]
      _ = 1 := by rw [S.mul_nonsing_inv hSdet, mul_one, hInvAdj]
  have hU : U ∈ Matrix.unitaryGroup ι ℂ := Matrix.mem_unitaryGroup_iff'.mpr hUadj
  have hZS : Z = U * S := by
    rw [U, mul_assoc, S.nonsing_inv_mul hSdet, mul_one]
  have hSn : ‖S‖ ≤ 1 := by rw [← CStarRing.norm_mem_unitary_mul S hU, ← hZS]; exact hZ
  let R : Matrix ι ι ℂ := hSpos.1.eigenvectorUnitary
  have hR : R ∈ Matrix.unitaryGroup ι ℂ := hSpos.1.eigenvectorUnitary.property
  let d (i : ι) : ℂ := hSpos.1.eigenvalues i
  have hSdiag : S = R * diagonal d * Rᴴ := hSpos.1.spectral_theorem
  have hdn : ‖diagonal d‖ ≤ 1 := by
    have he : ‖S‖ = ‖diagonal d‖ := by
      rw [hSdiag, CStarRing.norm_mul_mem_unitary _ (unitary.star_mem hR),
        CStarRing.norm_mem_unitary_mul _ hR]
    rw [← he]
    exact hSn
  have hL : U * R ∈ Matrix.unitaryGroup ι ℂ := (Matrix.unitaryGroup ι ℂ).mul_mem hU hR
  refine ⟨U * R, R, ⟨Matrix.mem_unitaryGroup_iff.mp hL, Matrix.mem_unitaryGroup_iff'.mp hL⟩,
    ⟨Matrix.mem_unitaryGroup_iff.mp hR, Matrix.mem_unitaryGroup_iff'.mp hR⟩, d,
    fun i => (norm_entry_le_diagonal_norm d i).trans hdn, ?_⟩
  rw [hZS, hSdiag]
  simp only [mul_assoc]

private theorem norm_eval_le_of_unitary_bound_invertible (f : Matrix ι ι ℂ → ℂ)
    (hf : Differentiable ℂ f) (B : ℝ) (hB : ∀ U, IsUnitary U → ‖f U‖ ≤ B)
    (Z : Matrix ι ι ℂ) (hZ : ‖Z‖ ≤ 1) (hzdet : IsUnit Z.det) : ‖f Z‖ ≤ B := by
  obtain ⟨L, R, hL, hR, d, hd, hzd⟩ := polar_diagonal_of_invertible_contraction Z hZ hzdet
  let g (x : ι → ℂ) := f (L * diagonal x * Rᴴ)
  have hg (x : ι → ℂ) (i : ι) : Differentiable ℂ fun z => g (Function.update x i z) := by
    have hup (z : ℂ) : diagonal (Function.update x i z) =
        diagonal (Function.update x i 0) + z • diagonal (Pi.single i 1) := by
      rw [← Matrix.diagonal_smul, Matrix.diagonal_add]
      apply congrArg Matrix.diagonal
      funext j
      by_cases hj : j = i
      · subst j
        simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      · simp [Pi.add_apply, Pi.smul_apply, Function.update_of_ne hj, Pi.single_apply, hj]
    simp only [g, hup]
    exact hf.comp (by fun_prop)
  obtain ⟨w, hw, hge⟩ := exists_torus_norm_ge g hg d hd
  have hLm : L ∈ Matrix.unitaryGroup ι ℂ := Matrix.mem_unitaryGroup_iff.mpr hL.1
  have hRm : R ∈ Matrix.unitaryGroup ι ℂ := Matrix.mem_unitaryGroup_iff.mpr hR.1
  have hDm : diagonal w ∈ Matrix.unitaryGroup ι ℂ :=
    Matrix.mem_unitaryGroup_iff.mpr (unitary_diagonal_of_norm_one w hw).1
  have hW : L * diagonal w * Rᴴ ∈ Matrix.unitaryGroup ι ℂ :=
    (Matrix.unitaryGroup ι ℂ).mul_mem ((Matrix.unitaryGroup ι ℂ).mul_mem hLm hDm)
      (unitary.star_mem hRm)
  rw [hzd]
  exact hge.trans (hB _ ⟨Matrix.mem_unitaryGroup_iff.mp hW, Matrix.mem_unitaryGroup_iff'.mp hW⟩)

private theorem eventually_invertible_contraction_path [Nonempty ι]
    (Z : Matrix ι ι ℂ) (hZ : ‖Z‖ ≤ 1) :
    ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ),
      let A := (1 - (t : ℂ)) • Z + ((t : ℂ) * (1 / 2)) • (1 : Matrix ι ι ℂ)
      ‖A‖ ≤ 1 ∧ IsUnit A.det := by
  let W : Matrix ι ι ℂ[X] :=
    (1 - Polynomial.X) • Z.map Polynomial.C +
      (Polynomial.X * Polynomial.C (1 / 2)) • (1 : Matrix ι ι ℂ[X])
  let q := W.det
  have hqeval (t : ℂ) : q.eval t =
      ((1 - t) • Z + (t * (1 / 2)) • (1 : Matrix ι ι ℂ)).det := by
    change Polynomial.eval t W.det = _
    rw [← Polynomial.coe_evalRingHom, RingHom.map_det]
    apply congrArg Matrix.det
    apply Matrix.ext
    intro i j
    by_cases hij : i = j <;>
      simp [W, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply,
        Matrix.one_apply, smul_eq_mul, hij]
  have hq : q ≠ 0 := by
    intro hz
    have he := hqeval 1
    rw [hz, Polynomial.eval_zero, sub_self, zero_smul, zero_add, one_mul,
      Matrix.det_smul, Matrix.det_one, mul_one] at he
    exact (pow_ne_zero _ (by norm_num : (1 / 2 : ℂ) ≠ 0)) he.symm
  let roots : Set ℝ := Complex.ofReal ⁻¹' {t : ℂ | q.IsRoot t} \ {0}
  have hroots : roots.Finite :=
    ((Polynomial.finite_setOf_isRoot hq).preimage Complex.ofReal_injective.injOn).subset
      Set.diff_subset
  have hnotroot : ∀ᶠ t : ℝ in 𝓝 (0 : ℝ), t ∉ roots :=
    hroots.isClosed.isOpen_compl.mem_nhds (by simp [roots])
  filter_upwards [hnotroot.filter_mono nhdsWithin_le_nhds,
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with t htq ht₁ ht₀
  change 0 < t at ht₀
  constructor
  · have hfirst : (1 - (t : ℂ)) = (↑(1 - t) : ℂ) := by simp
    have hsecond : (t : ℂ) * (1 / 2) = (↑(t * (1 / 2)) : ℂ) := by
      norm_cast
    calc
      _ ≤ ‖(1 - (t : ℂ)) • Z‖ + ‖((t : ℂ) * (1 / 2)) • (1 : Matrix ι ι ℂ)‖ :=
        norm_add_le _ _
      _ = (1 - t) * ‖Z‖ + t * (1 / 2) := by
        rw [hfirst, hsecond, norm_smul, norm_smul, Complex.norm_real, Complex.norm_real,
          Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr ht₁.le),
          abs_of_nonneg (mul_nonneg ht₀.le (by norm_num)), norm_one, mul_one]
      _ ≤ (1 - t) * 1 + t * (1 / 2) := by
        exact add_le_add_right (mul_le_mul_of_nonneg_left hZ (sub_nonneg.mpr ht₁.le)) _
      _ ≤ 1 := by linarith only [ht₀]
  · apply isUnit_iff_ne_zero.mpr
    intro hz
    apply htq
    exact ⟨(hqeval (t : ℂ)).trans hz, by simpa using ht₀.ne'⟩

private theorem norm_eval_le_of_unitary_bound [Nonempty ι] (f : Matrix ι ι ℂ → ℂ)
    (hf : Differentiable ℂ f) (B : ℝ) (hB : ∀ U, IsUnitary U → ‖f U‖ ≤ B)
    (Z : Matrix ι ι ℂ) (hZ : ‖Z‖ ≤ 1) : ‖f Z‖ ≤ B := by
  let A (t : ℝ) : Matrix ι ι ℂ :=
    (1 - (t : ℂ)) • Z + ((t : ℂ) * (1 / 2)) • 1
  have hcont : Continuous (fun t : ℝ => ‖f (A t)‖) :=
    (hf.continuous.comp (by unfold A; fun_prop)).norm
  have hlim : Tendsto (fun t => ‖f (A t)‖) (𝓝[>] (0 : ℝ)) (𝓝 ‖f Z‖) := by
    have h := hcont.continuousAt.tendsto.mono_left
      (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 (0 : ℝ))
    simpa only [A, Complex.ofReal_zero, sub_zero, one_smul, zero_mul, zero_smul, add_zero] using h
  apply le_of_tendsto hlim
  exact (eventually_invertible_contraction_path Z hZ).mono fun t ht =>
    norm_eval_le_of_unitary_bound_invertible f hf B hB (A t) ht.1 ht.2

private theorem differentiable_mvPolynomial_matrix_eval (p : MvPolynomial (ι × ι) ℂ) :
    Differentiable ℂ (fun Z : Matrix ι ι ℂ => MvPolynomial.eval (fun ij => Z ij.1 ij.2) p) := by
  induction p using MvPolynomial.induction_on with
  | C c => simpa only [MvPolynomial.eval_C] using (differentiable_const (c := c))
  | add p q hp hq => simpa only [map_add] using hp.add hq
  | mul_X p ij hp =>
    have he : Differentiable ℂ (fun Z : Matrix ι ι ℂ => Z ij.1 ij.2) :=
      (Matrix.entryLinearMap ℂ ℂ ij.1 ij.2).toContinuousLinearMap.differentiable
    simpa only [map_mul, MvPolynomial.eval_X] using hp.mul he

/-- A bound on a matrix polynomial over the unitary group holds on the whole
operator norm unit ball. -/
theorem norm_mvPolynomial_matrix_eval_le_of_unitary_bound [Nonempty ι]
    (p : MvPolynomial (ι × ι) ℂ) (B : ℝ)
    (hB : ∀ U : Matrix ι ι ℂ, IsUnitary U →
      ‖MvPolynomial.eval (fun ij => U ij.1 ij.2) p‖ ≤ B)
    (Z : Matrix ι ι ℂ) (hZ : ‖Z‖ ≤ 1) :
    ‖MvPolynomial.eval (fun ij => Z ij.1 ij.2) p‖ ≤ B :=
  norm_eval_le_of_unitary_bound _ (differentiable_mvPolynomial_matrix_eval p) B hB Z hZ

/-- A complex matrix polynomial attains its maximum modulus on the operator
norm unit ball at a unitary matrix. -/
theorem exists_unitary_maximum_mvPolynomial_matrix_eval [Nonempty ι]
    (p : MvPolynomial (ι × ι) ℂ) :
    ∃ U : Matrix ι ι ℂ, IsUnitary U ∧ ‖U‖ ≤ 1 ∧
      ∀ Z : Matrix ι ι ℂ, ‖Z‖ ≤ 1 →
        ‖MvPolynomial.eval (fun ij => Z ij.1 ij.2) p‖ ≤
          ‖MvPolynomial.eval (fun ij => U ij.1 ij.2) p‖ := by
  let f (Z : Matrix ι ι ℂ) := MvPolynomial.eval (fun ij => Z ij.1 ij.2) p
  have hf : Differentiable ℂ f := differentiable_mvPolynomial_matrix_eval p
  have hne : {U : Matrix ι ι ℂ | IsUnitary U}.Nonempty := ⟨1, isUnitary_one⟩
  obtain ⟨U, hU, hmax⟩ :=
    isCompact_setOf_isUnitary.exists_isMaxOn hne hf.continuous.norm.continuousOn
  have hU' : U ∈ Matrix.unitaryGroup ι ℂ := Matrix.mem_unitaryGroup_iff.mpr hU.1
  exact ⟨U, hU, (CStarRing.norm_of_mem_unitary hU').le,
    norm_eval_le_of_unitary_bound f hf _ (fun V hV => isMaxOn_iff.mp hmax V hV)⟩

end

end MOC
