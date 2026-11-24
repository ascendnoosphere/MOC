import MOC.Reformulations.FirstMatrix
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.Algebra.Module.Projective
import Mathlib.RingTheory.Norm.Defs
import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly
import Mathlib.Analysis.Complex.Polynomial.Basic

/-! Native polynomial quotient norms and projective base change. -/

open BigOperators Matrix TensorProduct Polynomial

namespace MOC.Reformulations

noncomputable section

private def evalProduct {n : ℕ} (r : Fin n → ℂ) : ℂ[X] →* ℂ where
  toFun q := ∏ i, q.eval (r i)
  map_one' := by simp
  map_mul' f g := by simp [Polynomial.eval_mul, Finset.prod_mul_distrib]

private theorem quotientNorm_linear {n : ℕ} (p : ℂ[X]) (hp : p.Monic)
    (hd : p.natDegree = n) (r : Fin n → ℂ) (hr : p.roots = Finset.univ.val.map r)
    (a : ℂ) :
    Algebra.norm ℂ (AdjoinRoot.mk p (X - C a)) = evalProduct r (X - C a) := by
  classical
  let pb := AdjoinRoot.powerBasis hp.ne_zero
  let A := Algebra.leftMulMatrix pb.basis pb.gen
  have hdim : pb.dim = n := hd
  have hchar : A.charpoly = p :=
    (charpoly_leftMulMatrix pb).trans (AdjoinRoot.minpoly_powerBasis_gen_of_monic hp)
  have heval : p.eval a = (Matrix.scalar (Fin pb.dim) a - A).det := by
    calc
      p.eval a = A.charpoly.eval a := congrArg (Polynomial.eval a) hchar.symm
      _ = _ := by
        unfold Matrix.charpoly
        rw [Matrix.eval_det, Matrix.matPolyEquiv_charmatrix, Polynomial.eval_sub,
          Polynomial.eval_X, Polynomial.eval_C]
  have hmul :
      Algebra.leftMulMatrix pb.basis (AdjoinRoot.mk p (X - C a)) =
        A - Matrix.scalar (Fin pb.dim) a := by
    rw [map_sub, AdjoinRoot.mk_X, AdjoinRoot.mk_C, ← AdjoinRoot.algebraMap_eq,
      map_sub, AlgHom.commutes, ← AdjoinRoot.powerBasis_gen hp.ne_zero]
    congr 1
  have hfac : p = ∏ i, (X - C (r i)) := by
    rw [p.eq_prod_roots_of_monic_of_splits_id hp (IsAlgClosed.splits p), hr, Multiset.map_map]
    rfl
  have hp_eval : p.eval a = ∏ i, (a - r i) := by
    rw [hfac, Polynomial.eval_prod]
    simp
  calc
    Algebra.norm ℂ (AdjoinRoot.mk p (X - C a)) =
        (-(Matrix.scalar (Fin pb.dim) a - A)).det := by
      rw [Algebra.norm_eq_matrix_det pb.basis, hmul, neg_sub]
    _ = (-1 : ℂ) ^ n * p.eval a := by
      rw [Matrix.det_neg, Fintype.card_fin, ← heval, hdim]
    _ = evalProduct r (X - C a) := by
      rw [hp_eval]
      change _ = ∏ i, (X - C a).eval (r i)
      simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
      have hpow : (-1 : ℂ) ^ n = ∏ _ : Fin n, (-1 : ℂ) := by simp
      rw [hpow, ← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro i _
      ring


/-- The norm of multiplication in a monic polynomial quotient is the
product of evaluations at the roots, retaining their multiplicities. -/
theorem polynomialQuotientNorm_eq_prod_eval {n : ℕ} (p q : ℂ[X]) (hp : p.Monic)
    (r : Fin n → ℂ) (hr : p.roots = Finset.univ.val.map r) :
    LinearMap.det (Algebra.lmul ℂ (AdjoinRoot p) (AdjoinRoot.mk p q)) =
      ∏ i, q.eval (r i) := by
  classical
  have hd : p.natDegree = n := by
    rw [Polynomial.natDegree_eq_card_roots (IsAlgClosed.splits p), Polynomial.map_id,
      hr, Multiset.card_map]
    simp
  let F : ℂ[X] →* ℂ := (Algebra.norm ℂ).comp (AdjoinRoot.mk p).toMonoidHom
  let G := evalProduct r
  change F q = G q
  have hC (a : ℂ) : F (C a) = G (C a) := by
    change Algebra.norm ℂ (AdjoinRoot.mk p (C a)) = ∏ i, (C a).eval (r i)
    rw [AdjoinRoot.mk_C, ← AdjoinRoot.algebraMap_eq, Algebra.norm_algebraMap_of_basis
      (AdjoinRoot.powerBasis hp.ne_zero).basis, Fintype.card_fin]
    change a ^ p.natDegree = _
    simp [hd]
  have hprod (s : Multiset ℂ) :
      F (s.map (fun a => X - C a)).prod = G (s.map (fun a => X - C a)).prod := by
    simp only [map_multiset_prod, Multiset.map_map]
    congr 1
    apply Multiset.map_congr rfl
    intro a _
    exact quotientNorm_linear p hp hd r hr a
  rw [q.eq_prod_roots_of_splits_id (IsAlgClosed.splits q), map_mul, map_mul, hC, hprod]

/-- In the actual polynomial quotient, the norm of multiplication by a sum
equals the identity matching of the two evaluation lists. -/
theorem polynomialQuotientNorm_mem_hull {n : ℕ} (p f g : ℂ[X]) (hp : p.Monic)
    (r : Fin n → ℂ) (hr : p.roots = Finset.univ.val.map r) :
    LinearMap.det (Algebra.lmul ℂ (AdjoinRoot p) (AdjoinRoot.mk p (f + g))) ∈
      convexHull ℝ (Set.range (matchingProduct (fun i => f.eval (r i))
        (fun i => g.eval (r i)))) := by
  rw [polynomialQuotientNorm_eq_prod_eval p (f + g) hp r hr]
  apply subset_convexHull ℝ _
  refine ⟨1, ?_⟩
  simp [matchingProduct, Polynomial.eval_add]

/-- The actual fiber map of an endomorphism after scalar extension. The given
basis fixes the coordinates of the finite-dimensional Hermitian fiber. -/
def fiberEndomorphismMatrix {R E : Type*} [CommRing R] [Algebra R ℂ]
    [AddCommGroup E] [Module R E] {n : ℕ} (e : Basis (Fin n) ℂ (ℂ ⊗[R] E))
    (A : E →ₗ[R] E) : Matrix (Fin n) (Fin n) ℂ :=
  LinearMap.toMatrix e e (A.baseChange ℂ)

/-- Atlas 036 at a chosen scalar fiber. Projectivity is source data, not
an additional hypothesis on the MOC implication. -/
theorem nativeProjectiveFiberHull_of_moc (h : MOCIsTrue)
    {R E : Type} [CommRing R] [Algebra R ℂ] [AddCommGroup E] [Module R E]
    [Module.Projective R E] {n : ℕ}
    (e : Basis (Fin n) ℂ (ℂ ⊗[R] E)) (A B : E →ₗ[R] E)
    (U : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n → ℂ)
    (hX : IsStarNormal (fiberEndomorphismMatrix e A))
    (hY : IsStarNormal (fiberEndomorphismMatrix e B)) (hU : IsUnitary U)
    (ha : (fiberEndomorphismMatrix e A).charpoly.roots = Finset.univ.val.map a)
    (hb : (fiberEndomorphismMatrix e B).charpoly.roots = Finset.univ.val.map b) :
    (fiberEndomorphismMatrix e A + U * fiberEndomorphismMatrix e B * Uᴴ).det ∈
      convexHull ℝ (Set.range (matchingProduct a b)) :=
  moc_iff_complexMatrices.mp h n _ _ U a b hX hY hU ha hb

end
end MOC.Reformulations
