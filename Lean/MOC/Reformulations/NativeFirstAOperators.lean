import MOC.Reformulations.FirstMatrix
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Projection
import Mathlib.Analysis.Normed.Operator.Compact

/-! Actual finite invariant restrictions and actual orthogonal compressions. -/

open BigOperators Matrix

namespace MOC.Reformulations
noncomputable section

/-- Matrix of the restriction of a bounded operator to an invariant subspace.
The chosen basis fixes the Hilbert inner product on the invariant subspace. -/
def invariantRestrictionMatrix {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    {n : ℕ} (E : Submodule ℂ X) (e : Basis (Fin n) ℂ E) (A : X →L[ℂ] X)
    (hA : ∀ x : E, A x ∈ E) : Matrix (Fin n) (Fin n) ℂ :=
  LinearMap.toMatrix e e (LinearMap.codRestrict E (A.toLinearMap.domRestrict E) hA)

/-- Restrict two bounded operators on a Banach space to a common finite
invariant subspace. Normality and rotation use its chosen inner product. -/
theorem nativeInvariantBanachHull_of_moc (h : MOCIsTrue) {X : Type}
    [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X] {n : ℕ}
    (E : Submodule ℂ X) (e : Basis (Fin n) ℂ E) (A B : X →L[ℂ] X)
    (hA : ∀ x : E, A x ∈ E) (hB : ∀ x : E, B x ∈ E)
    (U : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n → ℂ)
    (hAn : IsStarNormal (invariantRestrictionMatrix E e A hA))
    (hBn : IsStarNormal (invariantRestrictionMatrix E e B hB)) (hU : IsUnitary U)
    (ha : (invariantRestrictionMatrix E e A hA).charpoly.roots = Finset.univ.val.map a)
    (hb : (invariantRestrictionMatrix E e B hB).charpoly.roots = Finset.univ.val.map b) :
    (invariantRestrictionMatrix E e A hA + U * invariantRestrictionMatrix E e B hB * Uᴴ).det ∈
      convexHull ℝ (Set.range (matchingProduct a b)) :=
  moc_iff_complexMatrices.mp h n _ _ U a b hAn hBn hU ha hb

/-- Matrix of the actual orthogonal compression of a bounded operator. -/
def orthogonalCompressionMatrix {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {n : ℕ} (E : Submodule ℂ H) [E.HasOrthogonalProjection]
    (e : OrthonormalBasis (Fin n) ℂ E) (A : H →L[ℂ] H) : Matrix (Fin n) (Fin n) ℂ :=
  LinearMap.toMatrix e.toBasis e.toBasis
    (E.orthogonalProjection.toLinearMap.comp (A.toLinearMap.domRestrict E))

/-- MOC implies the normal finite compression comparison for
compact operators. The implication actually only uses normality
after compression, so the hypotheses may be relaxed to bounded inputs. -/
theorem nativeCompactCompression_of_moc (h : MOCIsTrue) {H : Type}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {n : ℕ}
    (E : Submodule ℂ H) [E.HasOrthogonalProjection]
    (e : OrthonormalBasis (Fin n) ℂ E) (A B : H →L[ℂ] H)
    (_hAc : IsCompactOperator A) (_hBc : IsCompactOperator B)
    (_hAn : IsStarNormal A) (_hBn : IsStarNormal B)
    (U : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n → ℂ)
    (hX : IsStarNormal (orthogonalCompressionMatrix E e A))
    (hY : IsStarNormal (orthogonalCompressionMatrix E e B)) (hU : IsUnitary U)
    (ha : (orthogonalCompressionMatrix E e A).charpoly.roots = Finset.univ.val.map a)
    (hb : (orthogonalCompressionMatrix E e B).charpoly.roots = Finset.univ.val.map b) :
    (orthogonalCompressionMatrix E e A + U * orthogonalCompressionMatrix E e B * Uᴴ).det ∈
      convexHull ℝ (Set.range (matchingProduct a b)) :=
  moc_iff_complexMatrices.mp h n _ _ U a b hX hY hU ha hb

end
end MOC.Reformulations
