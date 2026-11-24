import MOC.Reformulations.NativeFirstBHomology
import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.LinearAlgebra.Quotient.Basic

/-! Exact restricted native pieces of group homology, sheaf cohomology,
and spectral sequences. An actual quotient, sheaf section map, or chain
component is constructed; higher functorial identifications are not assumed. -/

open CategoryTheory Matrix

namespace MOC.Reformulations.NativeFirstB

noncomputable section

/-- The relation span for group coinvariants, i.e. degree-zero homology. -/
def coinvariantRelations {G : Type} [Group G] (W : Rep ℂ G) : Submodule ℂ W :=
  Submodule.span ℂ {v | ∃ g : G, ∃ x : W, v = W.ρ g x - x}

def coinvariantAction {G : Type} [Group G] {W : Rep ℂ G} (f : W ⟶ W) :
    (W ⧸ coinvariantRelations W) →ₗ[ℂ] (W ⧸ coinvariantRelations W) :=
  (coinvariantRelations W).mapQ (coinvariantRelations W) f.hom.hom (by
    apply Submodule.span_le.mpr
    rintro _ ⟨g, x, rfl⟩
    change f.hom.hom (W.ρ g x - x) ∈ coinvariantRelations W
    rw [map_sub]
    have he := Rep.hom_comm_apply f g x
    change f.hom.hom (W.ρ g x) = W.ρ g (f.hom.hom x) at he
    rw [he]
    exact Submodule.subset_span ⟨g, f.hom.hom x, rfl⟩)

/-- 082 in degree zero: a genuine equivariant endomorphism acts on the
coinvariant quotient. No assertion in a higher degree is made here. -/
theorem groupCoinvariantHull (h : MOCIsTrue) {G : Type} [Group G] {W : Rep ℂ G}
    (f g : W ⟶ W) {n : ℕ} (e : Basis (Fin n) ℂ (W ⧸ coinvariantRelations W))
    (U : Mat n) (a b : Fin n → ℂ)
    (hA : IsStarNormal (LinearMap.toMatrix e e (coinvariantAction f)))
    (hB : IsStarNormal (LinearMap.toMatrix e e (coinvariantAction g))) (hU : IsUnitary U)
    (ha : HasRoots (LinearMap.toMatrix e e (coinvariantAction f)) a)
    (hb : HasRoots (LinearMap.toMatrix e e (coinvariantAction g)) b) :
    OperatorHull (LinearMap.toMatrix e e (coinvariantAction f))
      (LinearMap.toMatrix e e (coinvariantAction g)) U a b :=
  operatorHull_of_moc h _ _ _ _ _ hA hB hU ha hb

/-- 084 in degree zero on a site with terminal object (X): the actual
global-section map of two sheaf endomorphisms. Restriction to another
site object is the same section calculation, without calling it global. -/
theorem sheafSectionHull (h : MOCIsTrue) {C : Type*} [Category C]
    {J : GrothendieckTopology C} (F : Sheaf J (ModuleCat ℂ)) (f g : F ⟶ F)
    (X : C) {n : ℕ} (e : Basis (Fin n) ℂ (F.val.obj (Opposite.op X)))
    (U : Mat n) (a b : Fin n → ℂ)
    (hA : IsStarNormal (moduleOperator e (f.val.app (Opposite.op X))))
    (hB : IsStarNormal (moduleOperator e (g.val.app (Opposite.op X))))
    (hU : IsUnitary U)
    (ha : HasRoots (moduleOperator e (f.val.app (Opposite.op X))) a)
    (hb : HasRoots (moduleOperator e (g.val.app (Opposite.op X))) b) :
    OperatorHull (moduleOperator e (f.val.app (Opposite.op X)))
      (moduleOperator e (g.val.app (Opposite.op X))) U a b :=
  operatorHull_of_moc h _ _ _ _ _ hA hB hU ha hb

/-- 092: the actual component maps on one page of a spectral sequence,
viewed as the specified bigraded complex with its page differential.
The selected maps must be chain morphisms for that differential. No
shared weights across pages or convergence data are asserted. -/
theorem spectralPageHull (h : MOCIsTrue) {c : ComplexShape (ℤ × ℤ)}
    (E : HomologicalComplex (ModuleCat ℂ) c) (f g : E ⟶ E) (pq : ℤ × ℤ)
    {n : ℕ} (e : Basis (Fin n) ℂ (E.X pq)) (U : Mat n) (a b : Fin n → ℂ)
    (hA : IsStarNormal (moduleOperator e (f.f pq)))
    (hB : IsStarNormal (moduleOperator e (g.f pq))) (hU : IsUnitary U)
    (ha : HasRoots (moduleOperator e (f.f pq)) a)
    (hb : HasRoots (moduleOperator e (g.f pq)) b) :
    OperatorHull (moduleOperator e (f.f pq)) (moduleOperator e (g.f pq)) U a b :=
  operatorHull_of_moc h _ _ _ _ _ hA hB hU ha hb

end

end MOC.Reformulations.NativeFirstB
