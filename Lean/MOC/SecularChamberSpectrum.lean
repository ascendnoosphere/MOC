import MOC.SecularBoundaryResidueTransfer
import MOC.SecularQuadraticPrincipalMinor
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic

/-! The spectrum of the secular trial matrices. -/

open BigOperators Finset Filter Matrix Polynomial
open scoped Topology

namespace MOC

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem det_diagonal_add_outer {K : Type*} [Field K]
    (w x y : ι → K) (hw : ∀ i, w i ≠ 0) :
    (diagonal w + vecMulVec x y).det =
      (∏ i, w i) * (1 + ∑ i, y i * ((w i)⁻¹ * x i)) := by
  let v (i : ι) := (w i)⁻¹ * x i
  have hfactor : diagonal w + vecMulVec x y = diagonal w * (1 + vecMulVec v y) := by
    rw [Matrix.mul_add, mul_one]
    ext i j : 1
    simp only [Matrix.add_apply, Matrix.diagonal_mul, Matrix.vecMulVec_apply, v]
    rw [← mul_assoc (w i) ((w i)⁻¹ * x i) (y j), ← mul_assoc (w i) (w i)⁻¹ (x i)]
    rw [mul_inv_cancel₀ (hw i), one_mul]
  have houter : vecMulVec v y = replicateCol Unit v * replicateRow Unit y := by
    ext i j : 1
    simp [Matrix.vecMulVec_apply, Matrix.mul_apply]
  rw [hfactor, Matrix.det_mul, Matrix.det_diagonal, houter,
    Matrix.det_one_add_replicateCol_mul_replicateRow]
  rfl

private theorem eval_charpoly_sec (A : Matrix ι ι ℝ) (z : ℝ) :
    A.charpoly.eval z = (z • (1 : Matrix ι ι ℝ) - A).det := by
  change (Polynomial.evalRingHom z) A.charmatrix.det = _
  rw [RingHom.map_det, RingHom.mapMatrix_apply]
  congr 1
  ext i j : 1
  by_cases hij : i = j
  · subst j
    simp [Matrix.smul_apply, smul_eq_mul]
  · simp [Matrix.charmatrix_apply_ne _ _ _ hij, Matrix.one_apply_ne hij,
      Matrix.smul_apply, smul_eq_mul]

/-- The polynomial expression for the secular trial data is the
characteristic polynomial of the diagonal plus the outer product. -/
theorem charpoly_diagonal_add_outer (d x y : ι → ℝ) :
    (diagonal d + vecMulVec x y).charpoly =
      secularCharacteristic d (fun i => x i * y i) := by
  apply Polynomial.eq_of_infinite_eval_eq
  refine (Set.finite_range d).infinite_compl.mono ?_
  intro z hz
  have hd (i : ι) : z ≠ d i := fun he => hz ⟨i, he.symm⟩
  let w (i : ι) := z-d i
  have hreg (i : ι) : w i ≠ 0 := sub_ne_zero.mpr (hd i)
  have hM : z • (1 : Matrix ι ι ℝ) - (diagonal d + vecMulVec x y) =
      diagonal w + vecMulVec (fun i => -x i) y := by
    ext i j : 1
    by_cases hij : i = j
    · subst j
      simp only [w, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
        Matrix.one_apply_eq, Matrix.diagonal_apply_eq, mul_one, Matrix.vecMulVec_apply]
      ring
    · simp only [w, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
        Matrix.one_apply_ne hij, Matrix.diagonal_apply_ne _ hij, mul_zero, zero_add,
        zero_sub, Matrix.vecMulVec_apply, neg_mul]
  change (diagonal d + vecMulVec x y).charpoly.eval z =
    (secularCharacteristic d (fun i => x i * y i)).eval z
  rw [eval_charpoly_sec, hM, det_diagonal_add_outer w _ y hreg]
  unfold secularCharacteristic
  simp only [eval_sub, eval_prod, eval_X, eval_C, eval_finset_sum, eval_mul]
  change (∏ j, w j) * (1 + ∑ i, y i * ((w i)⁻¹ * -x i)) =
    (∏ j, w j) - ∑ i, (x i * y i) * ∏ j ∈ univ.erase i, w j
  rw [mul_add, mul_one, mul_sum, sub_eq_add_neg, ← sum_neg_distrib]
  congr 1
  apply sum_congr rfl
  intro i _
  rw [← Finset.prod_erase_mul univ w (mem_univ i)]
  field_simp [hreg i]
  ring

/-- On the positive-residue domain the trial matrix has the prescribed
characteristic polynomial. -/
theorem charpoly_secularChamberMatrix (h d : ι → ℝ) (hd : Function.Injective d)
    (hr : ∀ i, 0 ≤ secularResidue h d i) :
    (secularChamberMatrix h d).charpoly = ∏ i, (X - C (h i)) := by
  rw [secularChamberMatrix, charpoly_diagonal_add_outer]
  have he : (fun i => Real.sqrt (secularResidue h d i) * Real.sqrt (secularResidue h d i)) =
      secularResidue h d := by
    funext i
    exact Real.mul_self_sqrt (hr i)
  rw [he, secularCharacteristic, ← secular_polynomial_identity h d hd]
  abel

/-- Evaluating at a node leaves just its own residue term, including
when another node has the same value. -/
theorem eval_secularCharacteristic_at_node (d r : ι → ℝ) (i : ι) :
    (secularCharacteristic d r).eval (d i) =
      -(r i * ∏ j ∈ univ.erase i, (d i-d j)) := by
  unfold secularCharacteristic
  simp only [eval_sub, eval_prod, eval_X, eval_C, eval_finset_sum, eval_mul]
  rw [prod_eq_zero (mem_univ i) (sub_self (d i)), zero_sub, sum_eq_single i]
  · intro j _ hij
    rw [prod_eq_zero (mem_erase.mpr ⟨Ne.symm hij, mem_univ i⟩) (sub_self (d i)), mul_zero]
  · exact fun h => (h (mem_univ i)).elim

/-- Any strict upper bound on the fixed spectrum strictly bounds every
secular node with a nonnegative residue vector. -/
theorem secular_nodes_lt_spectral_upper_bound (d r h : ι → ℝ)
    (hr : ∀ i, 0 ≤ r i) (hp : secularCharacteristic d r = ∏ i, (X - C (h i)))
    (M : ℝ) (hM : ∀ i, h i < M) (i : ι) :
    d i < M := by
  classical
  obtain ⟨k, _, hk⟩ := Finset.exists_max_image univ d ⟨i, mem_univ i⟩
  by_contra! hi
  have hMk : M ≤ d k := hi.trans (hk i (mem_univ _))
  have hpos : 0 < ∏ j, (d k-h j) :=
    Finset.prod_pos fun j _ => sub_pos.mpr ((hM j).trans_le hMk)
  have hneg : -(r k * ∏ j ∈ univ.erase k, (d k-d j)) ≤ 0 :=
    neg_nonpos.mpr (mul_nonneg (hr k)
      (Finset.prod_nonneg fun j _ => sub_nonneg.mpr (hk j (mem_univ _))))
  have he := congrArg (Polynomial.eval (d k)) hp
  simp only [eval_secularCharacteristic_at_node d r k, eval_prod, eval_sub, eval_X, eval_C] at he
  exact (not_lt_of_ge (he ▸ hneg)) hpos

/-- Above the spectrum, the positive residues divided by their node
distances have sum strictly less than one. -/
theorem secular_residue_ratios_sum_lt_one (d r h : ι → ℝ)
    (hr : ∀ i, 0 ≤ r i) (hp : secularCharacteristic d r = ∏ i, (X - C (h i)))
    (M : ℝ) (hM : ∀ i, h i < M) :
    (∑ i, r i / (M - d i)) < 1 := by
  let w (i : ι) := M-d i
  have hw (i : ι) : 0 < w i := sub_pos.mpr (secular_nodes_lt_spectral_upper_bound d r h hr hp M hM i)
  have hprod : 0 < ∏ i, w i := Finset.prod_pos fun i _ => hw i
  have ht : 0 < ∏ i, (M-h i) := Finset.prod_pos fun i _ => sub_pos.mpr (hM i)
  have hsum : (∏ j, w j) * (∑ i, r i / w i) =
      ∑ i, r i * ∏ j ∈ univ.erase i, w j := by
    rw [mul_sum]
    apply sum_congr rfl
    intro i _
    rw [← prod_erase_mul univ w (mem_univ i)]
    field_simp [(hw i).ne']
    ring
  have he := congrArg (Polynomial.eval M) hp
  unfold secularCharacteristic at he
  simp only [eval_sub, eval_prod, eval_X, eval_C, eval_finset_sum, eval_mul] at he
  change (∏ j, w j) - (∑ i, r i * ∏ j ∈ univ.erase i, w j) = _ at he
  rw [← hsum, ← mul_one_sub] at he
  have hpositive := he.symm ▸ ht
  exact sub_pos.mp ((mul_pos_iff_of_pos_left hprod).mp hpositive)

/-- The fixed spectrum bounds all chamber matrix entries, including
when the diagonal nodes themselves are unbounded below. -/
theorem abs_secularChamberMatrix_entry_le (h d : ι → ℝ)
    (hd : Function.Injective d) (hr : ∀ i, 0 ≤ secularResidue h d i)
    (M : ℝ) (hM : ∀ i, h i < M) (i j : ι) :
    |secularChamberMatrix h d i j| ≤
      |M| + (∑ k, (M - h k)) := by
  let r := secularResidue h d
  let w (k : ι) := M-d k
  let x (k : ι) := r k / w k
  let v (k : ι) := M-d k-r k
  let B := ∑ k, (M-h k)
  have hp : secularCharacteristic d r = ∏ k, (X - C (h k)) := by
    unfold secularCharacteristic
    rw [← secular_polynomial_identity h d hd]
    abel
  have hw (k : ι) : 0 < w k :=
    sub_pos.mpr (secular_nodes_lt_spectral_upper_bound d r h hr hp M hM k)
  have hx (k : ι) : 0 ≤ x k := div_nonneg (hr k) (hw k).le
  have hs : (∑ k, x k) < 1 := secular_residue_ratios_sum_lt_one d r h hr hp M hM
  have hB : 0 ≤ B := sum_nonneg fun k _ => sub_nonneg.mpr (hM k).le
  have hv (k : ι) : 0 ≤ v k := by
    have hxi : x k ≤ ∑ l, x l := single_le_sum (fun l _ => hx l) (mem_univ k)
    have hri : r k < w k := (div_lt_one (hw k)).mp (hxi.trans_lt hs)
    exact sub_nonneg.mpr hri.le
  have hvs : ∑ k, v k = B := by
    simp only [v, B, sum_sub_distrib]
    rw [sum_secularResidue h d hd]
    ring
  have hvB (k : ι) : v k ≤ B :=
    (single_le_sum (fun l _ => hv l) (mem_univ k)).trans hvs.le
  by_cases hij : i = j
  · subst j
    have he : secularChamberMatrix h d i i = M - v i := by
      simp only [secularChamberMatrix, Matrix.add_apply, Matrix.diagonal_apply_eq,
        Matrix.vecMulVec_apply, Real.mul_self_sqrt (hr i), v, r]
      ring
    rw [he]
    exact (abs_sub _ _).trans (add_le_add_left (by rw [abs_of_nonneg (hv i)]; exact hvB i) _)
  · have hpairs : x i + x j ≤ ∑ k, x k := by
      simpa only [sum_pair hij] using
        (sum_le_sum_of_subset_of_nonneg (f := x) (subset_univ ({i,j} : Finset ι))
          (fun k _ _ => hx k))
    have hxij : x i + x j ≤ 1 := hpairs.trans hs.le
    have hi : x i * w i = r i := div_mul_cancel₀ _ (hw i).ne'
    have hj : x j * w j = r j := div_mul_cancel₀ _ (hw j).ne'
    have he : (1-x i-x j)*(w i*w j) = v i*v j-r i*r j := by
      dsimp only [w, v] at hi hj ⊢
      linear_combination -(M-d j) * hi - (M-d i) * hj
    have hnon : 0 ≤ (1-x i-x j)*(w i*w j) :=
      mul_nonneg (by linarith only [hxij]) (mul_nonneg (hw i).le (hw j).le)
    have hrB : r i*r j ≤ B*B :=
      (sub_nonneg.mp (he ▸ hnon)).trans (mul_le_mul (hvB i) (hvB j) (hv j) hB)
    have hsq : Real.sqrt (r i) * Real.sqrt (r j) * (Real.sqrt (r i) * Real.sqrt (r j)) =
        r i*r j := by
      rw [show Real.sqrt (r i) * Real.sqrt (r j) * (Real.sqrt (r i) * Real.sqrt (r j)) =
        (Real.sqrt (r i) * Real.sqrt (r i)) * (Real.sqrt (r j) * Real.sqrt (r j)) by ring]
      rw [Real.mul_self_sqrt (hr i), Real.mul_self_sqrt (hr j)]
    have hn := mul_nonneg (Real.sqrt_nonneg (r i)) (Real.sqrt_nonneg (r j))
    have hbnd : Real.sqrt (r i) * Real.sqrt (r j) ≤ B := by
      nlinarith only [hrB, hsq, hn, hB]
    simp only [secularChamberMatrix, Matrix.add_apply, Matrix.diagonal_apply_ne _ hij,
      Matrix.vecMulVec_apply, zero_add]
    change |Real.sqrt (r i) * Real.sqrt (r j)| ≤ |M| + B
    rw [abs_of_nonneg hn]
    exact hbnd.trans (le_add_of_nonneg_left (abs_nonneg M))

end

end MOC
