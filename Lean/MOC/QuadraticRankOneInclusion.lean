import MOC.SecularQuadraticCommonWeights
import Mathlib.LinearAlgebra.Matrix.Polynomial
import Mathlib.Algebra.Polynomial.Eval.SMul
import Mathlib.LinearAlgebra.Lagrange

/-! Bivariate interpolation of one common quadratic determinant law. -/

open BigOperators Finset Matrix Polynomial

namespace MOC

noncomputable section

private theorem affine_det_polynomial {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι ℂ) :
    ∃ p : ℂ[X], p.natDegree ≤ Fintype.card ι ∧ ∀ z : ℂ, p.eval z = (z • A+B).det := by
  refine ⟨(X • A.map C + B.map C).det, natDegree_det_X_add_C_le A B, ?_⟩
  intro z
  change (Polynomial.evalRingHom z) ((X • A.map C+B.map C).det) = _
  rw [RingHom.map_det, RingHom.mapMatrix_apply]
  congr 1
  ext i j : 1
  simp [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  ring

private def secularRootDet {n : ℕ} (d r : Fin n → ℝ) (a : Fin n → ℂ)
    (z w : ℂ) : ℂ := (secularQuadraticColumnMatrix d r (-z-w) (z*w) a).det

private def secularRootVertex {n : ℕ} (h : Fin n → ℝ) (a : Fin n → ℂ)
    (σ : Equiv.Perm (Fin n)) (z w : ℂ) : ℂ :=
  matchingProduct (secularQuadraticLabels h (-z-w) (z*w)) a σ

private theorem secularRootDet_symm {n : ℕ} (d r : Fin n → ℝ) (a : Fin n → ℂ) (z w : ℂ) :
    secularRootDet d r a z w = secularRootDet d r a w z := by
  unfold secularRootDet
  rw [sub_eq_add_neg, sub_eq_add_neg, add_comm (-z), mul_comm z w]

private theorem secularRootVertex_symm {n : ℕ} (h : Fin n → ℝ) (a : Fin n → ℂ)
    (σ : Equiv.Perm (Fin n)) (z w : ℂ) :
    secularRootVertex h a σ z w = secularRootVertex h a σ w z := by
  unfold secularRootVertex
  rw [sub_eq_add_neg, sub_eq_add_neg, add_comm (-z), mul_comm z w]

private theorem secularRootDet_polynomial {n : ℕ} (d r : Fin n → ℝ) (a : Fin n → ℂ) (w : ℂ) :
    ∃ p : ℂ[X], p.natDegree ≤ n ∧ ∀ z, p.eval z = secularRootDet d r a z w := by
  let A : Matrix (Fin n) (Fin n) ℂ :=
    diagonal (fun i => w-d i) - Matrix.of (fun _ j => (r j : ℂ))
  let B := secularQuadraticColumnMatrix d r (-w) 0 a
  obtain ⟨p,hp,he⟩ := affine_det_polynomial A B
  refine ⟨p, by simpa only [Fintype.card_fin] using hp, fun z => ?_⟩
  rw [he]
  apply congrArg Matrix.det
  ext i j : 1
  simp only [A, B, secularQuadraticColumnMatrix, Matrix.add_apply, Matrix.sub_apply,
    Matrix.smul_apply, smul_eq_mul, Matrix.of_apply]
  by_cases h : i = j
  · subst j
    simp only [Matrix.diagonal_apply_eq, add_zero]
    ring
  · simp only [Matrix.diagonal_apply_ne _ h, zero_sub, zero_add]
    ring

private theorem secularRootVertex_polynomial {n : ℕ} (h : Fin n → ℝ) (a : Fin n → ℂ)
    (σ : Equiv.Perm (Fin n)) (w : ℂ) :
    ∃ p : ℂ[X], p.natDegree ≤ n ∧ ∀ z, p.eval z = secularRootVertex h a σ z w := by
  let A := diagonal fun i => w-h (σ i)
  let B := diagonal fun i => (h (σ i) : ℂ)^2 - w*h (σ i)+a i
  obtain ⟨p,hp,he⟩ := affine_det_polynomial A B
  refine ⟨p, by simpa only [Fintype.card_fin] using hp, fun z => ?_⟩
  have hMatrix : z • A + B =
      diagonal (fun i => secularQuadraticLabels h (-z-w) (z*w) (σ i)+a i) := by
    ext i j : 1
    by_cases h : i = j
    · subst j
      simp only [A, B, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.diagonal_apply_eq,
        secularQuadraticLabels]
      ring
    · simp only [A, B, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
        Matrix.diagonal_apply_ne _ h, mul_zero, add_zero]
  rw [he, hMatrix, Matrix.det_diagonal]
  rfl

private def nodeEvaluator {n : ℕ} (t : Fin (n+1) → ℂ) (x : ℂ) :
    (Fin (n+1) → ℂ) →ₗ[ℂ] ℂ :=
  (Polynomial.leval x).comp (Lagrange.interpolate univ t)

private theorem nodeEvaluator_eval {n : ℕ} (t : Fin (n+1) → ℂ) (ht : Function.Injective t)
    (x : ℂ) (p : ℂ[X]) (hp : p.natDegree ≤ n) :
    nodeEvaluator t x (fun i => p.eval (t i)) = p.eval x := by
  have hd : p.degree < ((univ : Finset (Fin (n+1))).card : WithBot ℕ) := by
    rw [card_univ, Fintype.card_fin]
    exact degree_le_natDegree.trans_lt (WithBot.coe_lt_coe.mpr (Nat.lt_succ_of_le hp))
  change (Lagrange.interpolate univ t (fun i => p.eval (t i))).eval x = p.eval x
  exact congrArg (Polynomial.eval x) (Lagrange.eq_interpolate (s := univ) ht.injOn hd).symm

private def gridEvaluator {n : ℕ} (t u : Fin (n+1) → ℂ) (x y : ℂ) :
    (Fin (n+1) × Fin (n+1) → ℂ) →ₗ[ℝ] ℂ :=
  ({ toFun := fun f => nodeEvaluator t x (fun i => nodeEvaluator u y (fun j => f (i,j)))
     map_add' := fun f g => by
       have he : (fun i => nodeEvaluator u y (fun j => (f+g) (i,j))) =
           (fun i => nodeEvaluator u y (fun j => f (i,j))) +
             (fun i => nodeEvaluator u y (fun j => g (i,j))) := by
         funext i
         exact map_add (nodeEvaluator u y) _ _
       rw [he, map_add]
     map_smul' := fun c f => by
       have he : (fun i => nodeEvaluator u y (fun j => (c • f) (i,j))) =
           c • (fun i => nodeEvaluator u y (fun j => f (i,j))) := by
         funext i
         exact map_smul (nodeEvaluator u y) c _
       rw [he, map_smul, RingHom.id_apply] } :
    (Fin (n+1) × Fin (n+1) → ℂ) →ₗ[ℂ] ℂ).restrictScalars ℝ

private theorem gridEvaluator_eq {n : ℕ} (t u : Fin (n+1) → ℂ) (ht : Function.Injective t)
    (hu : Function.Injective u) (x y : ℂ) (F : ℂ → ℂ → ℂ)
    (hf : ∀ w, ∃ p : ℂ[X], p.natDegree ≤ n ∧ ∀ z, p.eval z = F z w)
    (hs : ∀ z w, F z w = F w z) :
    gridEvaluator t u x y (fun ij => F (t ij.1) (u ij.2)) = F x y := by
  have hin (i : Fin (n+1)) :
      nodeEvaluator u y (fun j => F (t i) (u j)) = F (t i) y := by
    obtain ⟨p,hp,he⟩ := hf (t i)
    have hh : (fun j => F (t i) (u j)) = (fun j => p.eval (u j)) := by
      funext j
      rw [he, hs]
    rw [hh, nodeEvaluator_eval u hu y p hp, he, hs]
  change nodeEvaluator t x (fun i => nodeEvaluator u y (fun j => F (t i) (u j))) = F x y
  rw [show (fun i => nodeEvaluator u y (fun j => F (t i) (u j))) =
    (fun i => F (t i) y) from funext hin]
  obtain ⟨p,hp,he⟩ := hf y
  rw [show (fun i => F (t i) y) = (fun i => p.eval (t i)) from funext fun i => (he (t i)).symm,
    nodeEvaluator_eval t ht x p hp, he]

private theorem exists_complex_quadratic_roots (c e : ℂ) :
    ∃ x y : ℂ, -x-y = c ∧ x*y = e := by
  obtain ⟨Δ,hΔ⟩ := IsAlgClosed.exists_pow_nat_eq (c^2-4*e) (n := 2) (by decide)
  refine ⟨(-c+Δ)/2, (-c-Δ)/2, ?_, ?_⟩
  · ring
  · linear_combination -hΔ/4

/-- In every finite order the shifted secular determinant for an
arbitrary complex quadratic lies in its permutation hull. -/
theorem secularColumnMatrix_mem_hull_of_quadratic {n : ℕ} (d r h : Fin n → ℝ)
    (hr : ∀ i, 0 ≤ r i) (hp : secularCharacteristic d r = ∏ i, (X-C (h i)))
    (c e : ℂ) (a : Fin n → ℂ) :
    (secularQuadraticColumnMatrix d r c e a).det ∈
      convexHull ℝ (Set.range (matchingProduct (secularQuadraticLabels h c e) a)) := by
  let U := 1+ ∑ i, |h i|
  let t (i : Fin (n+1)) : ℝ := U+(i.val : ℝ)
  let u (j : Fin (n+1)) : ℝ := U+(n+1 : ℕ)+(j.val : ℝ)
  have he (i : Fin n) : h i < U := by
    dsimp only [U]
    have hle : |h i| ≤ ∑ j, |h j| := single_le_sum (fun j _ => abs_nonneg (h j)) (mem_univ i)
    linarith only [hle, le_abs_self (h i)]
  have ht (i : Fin (n+1)) (k : Fin n) : h k < t i :=
    (he k).trans_le (le_add_of_nonneg_right (Nat.cast_nonneg _))
  have hu (i : Fin (n+1)) (k : Fin n) : h k < u i :=
    (he k).trans_le ((le_add_of_nonneg_right (Nat.cast_nonneg (n+1))).trans
      (le_add_of_nonneg_right (Nat.cast_nonneg _)))
  have htU (i j : Fin (n+1)) : t i < u j := by
    dsimp only [t,u]
    have hi : (i.val : ℝ) < (n+1 : ℕ) := by exact_mod_cast i.isLt
    linarith only [hi, Nat.cast_nonneg (α := ℝ) j.val]
  let T (i : Fin (n+1) × Fin (n+1)) := t i.1
  let V (i : Fin (n+1) × Fin (n+1)) := u i.2
  have hHull := secularQuadraticProfile_mem_hull T V (fun ij => (htU ij.1 ij.2).ne)
    n d r h hr hp (fun ij => ht ij.1) (fun ij => hu ij.2) a
  let T' (i : Fin (n+1)) : ℂ := t i
  let U' (i : Fin (n+1)) : ℂ := u i
  have ht' : Function.Injective T' := by
    intro i j hij
    have he : t i = t j := Complex.ofReal_injective hij
    apply Fin.ext
    exact_mod_cast add_left_cancel he
  have hu' : Function.Injective U' := by
    intro i j hij
    have he : u i = u j := Complex.ofReal_injective hij
    apply Fin.ext
    exact_mod_cast add_left_cancel he
  obtain ⟨x,y,hxy₁,hxy₂⟩ := exists_complex_quadratic_roots c e
  let L := gridEvaluator T' U' x y
  have hD : L (secularQuadraticProfile d r T V a) = (secularQuadraticColumnMatrix d r c e a).det := by
    have hE := gridEvaluator_eq T' U' ht' hu' x y (secularRootDet d r a)
      (secularRootDet_polynomial d r a) (secularRootDet_symm d r a)
    change L (secularQuadraticProfile d r T V a) = secularRootDet d r a x y at hE
    rw [hE, secularRootDet, hxy₁, hxy₂]
  have hP (σ : Equiv.Perm (Fin n)) :
      L (secularQuadraticProfileMatching h T V a σ) =
        matchingProduct (secularQuadraticLabels h c e) a σ := by
    have hE := gridEvaluator_eq T' U' ht' hu' x y (secularRootVertex h a σ)
      (secularRootVertex_polynomial h a σ) (secularRootVertex_symm h a σ)
    change L (secularQuadraticProfileMatching h T V a σ) = secularRootVertex h a σ x y at hE
    rw [hE, secularRootVertex, hxy₁, hxy₂]
  rw [← hD]
  have hMem : L (secularQuadraticProfile d r T V a) ∈
      convexHull ℝ (L '' Set.range (secularQuadraticProfileMatching h T V a)) := by
    rw [← LinearMap.image_convexHull]
    exact ⟨_,hHull,rfl⟩
  apply convexHull_mono _ hMem
  rintro _ ⟨_,⟨σ,rfl⟩,rfl⟩
  exact ⟨σ,(hP σ).symm⟩

private theorem matrix_quadratic_factored {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (x y : ℂ) :
    (H-x • 1)*(H-y • 1) = H*H + (-x-y) • H + (x*y) • 1 := by
  rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.smul_mul, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.mul_smul, mul_one, one_mul, one_mul, smul_smul, sub_smul, neg_smul]
  abel

private def physicalRootDet {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (a : Fin n → ℂ)
    (x y : ℂ) : ℂ := ((H-x • 1)*(H-y • 1)+diagonal a).det

private theorem physicalRootDet_symm {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ)
    (a : Fin n → ℂ) (x y : ℂ) : physicalRootDet H a x y = physicalRootDet H a y x := by
  unfold physicalRootDet
  rw [matrix_quadratic_factored, matrix_quadratic_factored]
  simp only [sub_eq_add_neg, add_comm (-x), mul_comm x y]

private theorem physicalRootDet_polynomial {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ)
    (a : Fin n → ℂ) (y : ℂ) :
    ∃ p : ℂ[X], p.natDegree ≤ n ∧ ∀ x, p.eval x = physicalRootDet H a x y := by
  let A := -(H-y • 1)
  let B := H*(H-y • 1)+diagonal a
  obtain ⟨p,hp,he⟩ := affine_det_polynomial A B
  refine ⟨p, by simpa only [Fintype.card_fin] using hp, fun x => ?_⟩
  rw [he]
  apply congrArg Matrix.det
  dsimp only [A,B]
  rw [Matrix.sub_mul, Matrix.smul_mul, one_mul, smul_neg]
  abel

private theorem physicalRootDet_real_factor {n : ℕ}
    (H : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℂ) (x y : ℝ) :
    physicalRootDet (H.map Complex.ofRealHom) a x y =
      ((((H-x • 1)*(H-y • 1)).map Complex.ofRealHom)+diagonal a).det := by
  unfold physicalRootDet
  simp only [Matrix.map_mul, Matrix.map_sub _ (map_sub _),
      Matrix.map_smul' _ _ _ (map_mul _), Matrix.map_one _ (map_zero _) (map_one _)]
  rfl

/-- The physical quadratic matrix and the secular column model have the
same shifted determinant for every complex quadratic coefficient. -/
theorem det_secularColumnMatrix_eq_rank_one_polynomial {n : ℕ} (d v : Fin n → ℝ)
    (c e : ℂ) (a : Fin n → ℂ) :
    let H := (diagonal d + vecMulVec v v).map Complex.ofRealHom
    (secularQuadraticColumnMatrix d (fun i => v i*v i) c e a).det =
      (H*H+c • H+e • 1+diagonal a).det := by
  intro H
  let A : Matrix (Fin n) (Fin n) ℝ := diagonal d + vecMulVec v v
  let r (i : Fin n) := v i*v i
  let t (i : Fin (n+1)) : ℝ := i.val
  let T (i : Fin (n+1)) : ℂ := t i
  have hT : Function.Injective T := by
    intro i j hij
    have he := Complex.ofReal_injective hij
    change (i.val : ℝ) = (j.val : ℝ) at he
    apply Fin.ext
    exact_mod_cast he
  have hgrid : (fun ij : Fin (n+1) × Fin (n+1) => secularRootDet d r a (T ij.1) (T ij.2)) =
      (fun ij => physicalRootDet H a (T ij.1) (T ij.2)) := by
    funext ij
    change secularRootDet d r a (t ij.1) (t ij.2) =
      physicalRootDet (A.map Complex.ofRealHom) a (t ij.1) (t ij.2)
    rw [physicalRootDet_real_factor]
    exact det_secularColumnMatrix_eq_rank_one_quadratic d v _ _ a
  obtain ⟨x,y,hxy₁,hxy₂⟩ := exists_complex_quadratic_roots c e
  have hLeft := gridEvaluator_eq T T hT hT x y (secularRootDet d r a)
    (secularRootDet_polynomial d r a) (secularRootDet_symm d r a)
  have hRight := gridEvaluator_eq T T hT hT x y (physicalRootDet H a)
    (physicalRootDet_polynomial H a) (physicalRootDet_symm H a)
  rw [hgrid, hRight] at hLeft
  rw [secularRootDet, physicalRootDet, matrix_quadratic_factored, hxy₁, hxy₂] at hLeft
  exact hLeft.symm

/-- A quadratic polynomial of a real Hermitian diagonal-plus-rank-one
matrix satisfies determinant inclusion with every complex diagonal
partner. The polynomial coefficients are arbitrary complex numbers. -/
theorem det_quadratic_rank_one_hermitian_mem_hull
    {n : ℕ} (d v h : Fin n → ℝ)
    (hh : (diagonal d + vecMulVec v v).charpoly = ∏ i, (X - C (h i)))
    (c e : ℂ) (a : Fin n → ℂ) :
    let H := (diagonal d + vecMulVec v v).map Complex.ofRealHom
    (H*H+c • H+e • 1+diagonal a).det ∈
      convexHull ℝ (Set.range (matchingProduct (secularQuadraticLabels h c e) a)) := by
  intro H
  have hspec := charpoly_diagonal_add_outer d v v
  rw [hh] at hspec
  have h := secularColumnMatrix_mem_hull_of_quadratic d (fun i => v i*v i) h
    (fun i => mul_self_nonneg (v i)) hspec.symm c e a
  rw [det_secularColumnMatrix_eq_rank_one_polynomial d v c e a] at h
  exact h

end

end MOC
