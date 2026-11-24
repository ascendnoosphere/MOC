import MOC.Reformulations.FirstMatrix
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.Algebra.Module.Projective

/-! Actual polynomial quotient multiplication and projective base change.
The quotient norm's local multiplicity law is not derived in this module. -/

open BigOperators Matrix TensorProduct Polynomial

namespace MOC.Reformulations
noncomputable section

/-- Atlas 035, the ordinary determinant of multiplication by the actual
sum in the monic polynomial quotient. This is the native target, with
no asserted theorem about repeated-root or local factors. -/
def nativePolynomialQuotientNormHull : Prop :=
  ∀ (n : ℕ) (p f g : ℂ[X]), p.Monic → p.natDegree = n →
    ∀ (r : Fin n → ℂ), p.roots = Finset.univ.val.map r →
      LinearMap.det (Algebra.lmul ℂ (AdjoinRoot p) (AdjoinRoot.mk p (f + g))) ∈
        convexHull ℝ (Set.range (matchingProduct (fun i => f.eval (r i))
          (fun i => g.eval (r i))))

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
