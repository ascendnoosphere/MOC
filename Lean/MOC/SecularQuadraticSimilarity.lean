import MOC.SecularChamberGeometry

/-! On the positive-residue domain the column model is similar to the
quadratic spectral image of the symmetric rank-one trial matrix. -/

open BigOperators Finset Filter Matrix
open scoped Topology

namespace MOC

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem secularColumnMatrix_polynomial (d r : ι → ℝ) (c e : ℂ)
    (a : ι → ℂ) :
    let Y := diagonal (fun i => (d i : ℂ)) + vecMulVec (fun _ => (1 : ℂ)) (fun i => (r i : ℂ))
    secularQuadraticColumnMatrix d r c e a = Y*Y + c • Y + e • 1 + diagonal a := by
  intro Y
  let D := diagonal (fun i => (d i : ℂ))
  let R := vecMulVec (fun _ : ι => (1 : ℂ)) (fun i => (r i : ℂ))
  let q : ℂ := ∑ i, (r i : ℂ)
  have hR : R*R = q • R := by
    ext i j : 1
    simp only [R, Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.smul_apply, smul_eq_mul,
      one_mul, q, Finset.sum_mul]
  change _ = (D+R)*(D+R) + c • (D+R) + e • 1 + diagonal a
  rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, hR, smul_add]
  rw [show D*D = diagonal (fun i => (d i : ℂ)*(d i : ℂ)) from Matrix.diagonal_mul_diagonal _ _]
  ext i j : 1
  simp only [secularQuadraticColumnMatrix, Matrix.add_apply, Matrix.of_apply, Matrix.diagonal_mul,
    Matrix.mul_diagonal, Matrix.smul_apply, smul_eq_mul, Matrix.vecMulVec_apply, R, D,
    one_mul, q, Complex.ofReal_sum]
  by_cases h : i = j
  · subst j
    simp only [Matrix.diagonal_apply_eq, Matrix.one_apply_eq, mul_one]
    ring
  · simp only [Matrix.diagonal_apply_ne _ h, Matrix.one_apply_ne h, mul_zero, zero_add, add_zero]
    ring

private theorem det_secularColumnMatrix_eq_physical_quadratic_of_nonzero
    (d x : ι → ℝ) (hx : ∀ i, x i ≠ 0) (t u : ℝ) (a : ι → ℂ) :
    let H := diagonal d + vecMulVec x x
    let Q := (H - t • 1)*(H - u • 1)
    (secularQuadraticColumnMatrix d (fun i => x i*x i) (-(t : ℂ)-(u : ℂ)) (t*u : ℂ) a).det =
      (Q.map Complex.ofRealHom + diagonal a).det := by
  intro H Q
  let r (i : ι) := x i*x i
  let v (i : ι) : ℂ := x i
  let D := diagonal (fun i => (d i : ℂ))
  let A := H.map Complex.ofRealHom
  let X := D + vecMulVec (fun _ => (1 : ℂ)) (fun i => (r i : ℂ))
  let P := diagonal v
  let B := diagonal a
  have hv (i : ι) : v i * v i = (r i : ℂ) := by
    exact (Complex.ofReal_mul _ _).symm
  have hA : A = D + vecMulVec v v := by
    change (diagonal d + vecMulVec x x).map Complex.ofRealHom = _
    ext i j : 1
    by_cases hij : i = j
    · subst j
      simp only [Matrix.map_apply, Matrix.add_apply, Matrix.diagonal_apply_eq,
        Matrix.vecMulVec_apply, map_add, map_mul, D, v]
      rfl
    · simp only [Matrix.map_apply, Matrix.add_apply, Matrix.diagonal_apply_ne _ hij, zero_add,
        Matrix.vecMulVec_apply, map_mul, D, v]
      rfl
  have hAP : A*P = P*X := by
    rw [hA]
    ext i j : 1
    simp only [X, P, D, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.add_apply,
      Matrix.vecMulVec_apply, one_mul, hv]
    by_cases hij : i = j
    · subst j
      simp only [Matrix.diagonal_apply_eq]
      rw [hv i]
      ring
    · simp only [Matrix.diagonal_apply_ne _ hij, zero_add]
      rw [mul_assoc, hv]
  have hshift (z : ℂ) : (A-z • 1)*P = P*(X-z • 1) := by
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul,
      one_mul, mul_one, hAP]
  have hQ : Q.map Complex.ofRealHom = (A-(t : ℂ) • 1)*(A-(u : ℂ) • 1) := by
    change (((H - t • 1)*(H-u • 1)).map Complex.ofRealHom) = _
    simp only [Matrix.map_mul, Matrix.map_sub _ (map_sub _),
      Matrix.map_smul' _ _ _ (map_mul _), Matrix.map_one _ (map_zero _) (map_one _),
      A]
    rfl
  have hP : P.det ≠ 0 := by
    rw [Matrix.det_diagonal]
    exact prod_ne_zero_iff.mpr fun i _ => Complex.ofReal_ne_zero.mpr (hx i)
  have hB : B*P = P*B := by
    change diagonal a * diagonal v = diagonal v * diagonal a
    rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    apply congrArg Matrix.diagonal
    funext i
    ring
  have hpoly : secularQuadraticColumnMatrix d r (-(t : ℂ)-(u : ℂ)) (t*u : ℂ) a =
      (X-(t : ℂ) • 1)*(X-(u : ℂ) • 1) + B := by
    rw [secularColumnMatrix_polynomial]
    change X*X + (-(t : ℂ)-(u : ℂ)) • X + (t*u : ℂ) • 1 + B = _
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.smul_mul, Matrix.smul_mul,
      Matrix.mul_smul, Matrix.mul_smul, mul_one, one_mul, one_mul, smul_smul,
      sub_smul, neg_smul]
    abel
  have Hmul : (Q.map Complex.ofRealHom + diagonal a)*P =
      P * secularQuadraticColumnMatrix d r (-(t : ℂ)-(u : ℂ)) (t*u : ℂ) a := by
    rw [hQ, hpoly, Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc _ _ P, hshift (u : ℂ),
      ← Matrix.mul_assoc _ P _, hshift (t : ℂ), Matrix.mul_assoc, show diagonal a = B from rfl, hB]
  have he := congrArg Matrix.det Hmul
  rw [Matrix.det_mul, Matrix.det_mul, mul_comm _ P.det] at he
  exact (mul_left_cancel₀ hP he).symm

/-- The column model computes the quadratic determinant of a real
Hermitian rank-one perturbation, including when vector entries vanish. -/
theorem det_secularColumnMatrix_eq_rank_one_quadratic (d x : ι → ℝ)
    (t u : ℝ) (a : ι → ℂ) :
    let H := diagonal d + vecMulVec x x
    let Q := (H - t • 1)*(H - u • 1)
    (secularQuadraticColumnMatrix d (fun i => x i*x i) (-(t : ℂ)-(u : ℂ)) (t*u : ℂ) a).det =
      (Q.map Complex.ofRealHom + diagonal a).det := by
  intro H Q
  let v (s : ℝ) (i : ι) := x i+s
  let r (s : ℝ) (i : ι) := v s i * v s i
  let F (s : ℝ) := (secularQuadraticColumnMatrix d (r s) (-(t : ℂ)-(u : ℂ)) (t*u : ℂ) a).det
  let A (s : ℝ) := diagonal d + vecMulVec (v s) (v s)
  let N (s : ℝ) := (A s-t • 1)*(A s-u • 1)
  let G (s : ℝ) := ((N s).map Complex.ofRealHom + diagonal a).det
  have hF : Continuous F := by
    have hMat : Continuous (fun s : ℝ =>
        secularQuadraticColumnMatrix d (r s) (-(t : ℂ)-(u : ℂ)) (t*u : ℂ) a) := by
      apply continuous_matrix
      intro i j
      simp only [secularQuadraticColumnMatrix, Matrix.add_apply, Matrix.diagonal_apply,
        Matrix.of_apply, r, v]
      split_ifs <;> fun_prop
    exact hMat.matrix_det
  have hG : Continuous G := by
    have ha : Continuous A := by
      apply continuous_matrix
      intro i j
      simp only [A, Matrix.add_apply, Matrix.vecMulVec_apply, v]
      fun_prop
    have hn : Continuous N := by unfold N; fun_prop
    have hm : Continuous (fun s : ℝ => (N s).map Complex.ofRealHom) :=
      continuous_matrix fun i j => Complex.continuous_ofReal.comp (hn.matrix_elem i j)
    exact (hm.add continuous_const).matrix_det
  have hreg : ∀ᶠ s in 𝓝[≠] (0 : ℝ), ∀ i, v s i ≠ 0 := by
    apply Filter.eventually_all.mpr
    intro i
    by_cases hi : x i = 0
    · filter_upwards [self_mem_nhdsWithin (s := ({0} : Set ℝ)ᶜ)] with s hs
      have hn : s ≠ 0 := hs
      simpa only [v, hi, zero_add] using hn
    · have hc : ContinuousAt (fun s : ℝ => v s i) 0 := by unfold v; fun_prop
      have h0 : v 0 i ≠ 0 := by simpa only [v, add_zero] using hi
      exact (hc.eventually_ne h0).filter_mono nhdsWithin_le_nhds
  have he : F =ᶠ[𝓝[≠] (0 : ℝ)] G := by
    filter_upwards [hreg] with s hs
    exact det_secularColumnMatrix_eq_physical_quadratic_of_nonzero d (v s) hs t u a
  have hF0 : ContinuousAt F 0 := hF.continuousAt
  have hG0 : ContinuousAt G 0 := hG.continuousAt
  have eq0 : F 0 = G 0 := tendsto_nhds_unique_of_eventuallyEq
    (hF0.tendsto.mono_left nhdsWithin_le_nhds) (hG0.tendsto.mono_left nhdsWithin_le_nhds) he
  simpa only [F, G, r, N, A, v, add_zero, H, Q] using eq0

/-- The determinant of the column model agrees with the corresponding
quadratic image of the real symmetric matrix throughout the chamber. -/
theorem det_secularColumnMatrix_eq_physical_quadratic (h d : ι → ℝ)
    (hd : d ∈ secularChamber h) (t u : ℝ) (a : ι → ℂ) :
    let H := secularChamberMatrix h d
    let Q := (H - t • 1)*(H - u • 1)
    (secularQuadraticColumnMatrix d (secularResidue h d) (-(t : ℂ)-(u : ℂ)) (t*u : ℂ) a).det =
      (Q.map Complex.ofRealHom + diagonal a).det := by
  have he : (fun i => Real.sqrt (secularResidue h d i) * Real.sqrt (secularResidue h d i)) =
      secularResidue h d := by
    funext i
    exact Real.mul_self_sqrt (hd.2 i).le
  simpa only [secularChamberMatrix, he] using
    det_secularColumnMatrix_eq_rank_one_quadratic d (fun i => Real.sqrt (secularResidue h d i)) t u a

end

end MOC
