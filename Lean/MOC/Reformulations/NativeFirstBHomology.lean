import MOC.Reformulations.NativeFirstB
import Mathlib.Algebra.Homology.Single
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.RepresentationTheory.GroupCohomology.Basic

/-! Chain and cohomology endomorphisms. The actual chain map or homology
functor determines the operator before its roots are listed. Choice of
basis specifies the finite Hermitian coordinates. -/

open CategoryTheory Matrix

namespace MOC.Reformulations.NativeFirstB

noncomputable section

def moduleOperator {X : ModuleCat ℂ} {n : ℕ} (e : Basis (Fin n) ℂ X)
    (f : X ⟶ X) : Mat n := LinearMap.toMatrix e e f.hom

/-- 073: determinant comparison for the degree component of actual chain
endomorphisms. The relative unitary need not extend to a chain
automorphism. -/
def ChainTermForm : Prop :=
  ∀ (C : ChainComplex (ModuleCat.{0} ℂ) ℕ) (f g : C ⟶ C) (k n : ℕ)
    (e : Basis (Fin n) ℂ (C.X k)) (U : Mat n) (a b : Fin n → ℂ),
    let A := moduleOperator e (f.f k)
    let B := moduleOperator e (g.f k)
    IsStarNormal A → IsStarNormal B → IsUnitary U →
    HasRoots A a → HasRoots B b → OperatorHull A B U a b

theorem chainTermForm_iff : ChainTermForm ↔ MOCIsTrue := by
  constructor
  · intro h n
    apply conjecture_iff_normalConjecture.mpr
    intro A B a b hA hB ha hb
    let X := ModuleCat.of ℂ (Fin n → ℂ)
    let C := (ChainComplex.single₀ (ModuleCat ℂ)).obj X
    let f : X ⟶ X := ModuleCat.ofHom A.toLin'
    let g : X ⟶ X := ModuleCat.ofHom B.toLin'
    let F := (ChainComplex.single₀ (ModuleCat ℂ)).map f
    let G := (ChainComplex.single₀ (ModuleCat ℂ)).map g
    have hf : moduleOperator (Pi.basisFun ℂ (Fin n)) (F.f 0) = A := by
      change moduleOperator (Pi.basisFun ℂ (Fin n))
        (((ChainComplex.single₀ (ModuleCat ℂ)).map f).f 0) = A
      rw [ChainComplex.single₀_map_f_zero]
      exact LinearMap.toMatrix'_toLin' A
    have hg : moduleOperator (Pi.basisFun ℂ (Fin n)) (G.f 0) = B := by
      change moduleOperator (Pi.basisFun ℂ (Fin n))
        (((ChainComplex.single₀ (ModuleCat ℂ)).map g).f 0) = B
      rw [ChainComplex.single₀_map_f_zero]
      exact LinearMap.toMatrix'_toLin' B
    have hh := h C F G 0 n (Pi.basisFun ℂ (Fin n)) 1 a b
    dsimp only at hh
    rw [hf, hg] at hh
    simpa [OperatorHull] using hh hA hB isUnitary_one ha hb
  · intro h C f g k n e U a b
    dsimp only
    intro hA hB hU ha hb
    exact operatorHull_of_moc h _ _ _ _ _ hA hB hU ha hb

/-- The actual induced homology maps, rather than the degree component maps.
This lemma can be specialized to any complex whose homology is defined in
the library; it neither equates chain dimension and homology dimension nor
assumes that a geometric endomorphism can realize arbitrary operators. -/
theorem inducedHomologyHull (h : MOCIsTrue) {ι : Type*} {c : ComplexShape ι}
    (C : HomologicalComplex (ModuleCat ℂ) c) (f g : C ⟶ C) (k : ι) {n : ℕ}
    (e : Basis (Fin n) ℂ (C.homology k)) (U : Mat n) (a b : Fin n → ℂ)
    (hA : IsStarNormal (moduleOperator e (HomologicalComplex.homologyMap f k)))
    (hB : IsStarNormal (moduleOperator e (HomologicalComplex.homologyMap g k)))
    (hU : IsUnitary U)
    (ha : HasRoots (moduleOperator e (HomologicalComplex.homologyMap f k)) a)
    (hb : HasRoots (moduleOperator e (HomologicalComplex.homologyMap g k)) b) :
    OperatorHull (moduleOperator e (HomologicalComplex.homologyMap f k))
      (moduleOperator e (HomologicalComplex.homologyMap g k)) U a b :=
  operatorHull_of_moc h _ _ _ _ _ hA hB hU ha hb

/-- Singular homology over the coefficient field, not a sampled spectrum. -/
abbrev singularComplexHomology (k : ℕ) : TopCat ⥤ ModuleCat ℂ :=
  (AlgebraicTopology.singularHomologyFunctor (ModuleCat ℂ) k).obj (ModuleCat.of ℂ ℂ)

/-- 074 and the degreewise determinant of 098: the functorial action of
continuous self-maps on actual singular homology. -/
theorem singularHomologyHull (h : MOCIsTrue) (X : TopCat) (f g : X ⟶ X) (k : ℕ)
    {n : ℕ} (e : Basis (Fin n) ℂ ((singularComplexHomology k).obj X))
    (U : Mat n) (a b : Fin n → ℂ)
    (hA : IsStarNormal (moduleOperator e ((singularComplexHomology k).map f)))
    (hB : IsStarNormal (moduleOperator e ((singularComplexHomology k).map g)))
    (hU : IsUnitary U)
    (ha : HasRoots (moduleOperator e ((singularComplexHomology k).map f)) a)
    (hb : HasRoots (moduleOperator e ((singularComplexHomology k).map g)) b) :
    OperatorHull (moduleOperator e ((singularComplexHomology k).map f))
      (moduleOperator e ((singularComplexHomology k).map g)) U a b :=
  operatorHull_of_moc h _ _ _ _ _ hA hB hU ha hb

/-- 075: contravariant pullback in the linear dual model of field-coefficient
singular cohomology. This constructs the dual operator itself; the
comparison with an independently constructed cochain complex is separate. -/
def singularDualAction {X : TopCat} (f : X ⟶ X) (k : ℕ) :
    Module.Dual ℂ ((singularComplexHomology k).obj X) →ₗ[ℂ]
      Module.Dual ℂ ((singularComplexHomology k).obj X) :=
  LinearMap.dualMap ((singularComplexHomology k).map f).hom

theorem singularDualHull (h : MOCIsTrue) (X : TopCat) (f g : X ⟶ X) (k : ℕ)
    {n : ℕ} (e : Basis (Fin n) ℂ (Module.Dual ℂ ((singularComplexHomology k).obj X)))
    (U : Mat n) (a b : Fin n → ℂ)
    (hA : IsStarNormal (LinearMap.toMatrix e e (singularDualAction f k)))
    (hB : IsStarNormal (LinearMap.toMatrix e e (singularDualAction g k)))
    (hU : IsUnitary U)
    (ha : HasRoots (LinearMap.toMatrix e e (singularDualAction f k)) a)
    (hb : HasRoots (LinearMap.toMatrix e e (singularDualAction g k)) b) :
    OperatorHull (LinearMap.toMatrix e e (singularDualAction f k))
      (LinearMap.toMatrix e e (singularDualAction g k)) U a b :=
  operatorHull_of_moc h _ _ _ _ _ hA hB hU ha hb

/-- 083: an equivariant coefficient endomorphism acts on standard-resolution
cochains by postcomposition. The square commutes by associativity. -/
def coefficientCochainMap {G : Type} [Group G] {A : Rep ℂ G} (f : A ⟶ A) :
    groupCohomology.linearYonedaObjResolution A ⟶ groupCohomology.linearYonedaObjResolution A where
  f i := ModuleCat.ofHom (CategoryTheory.Linear.rightComp ℂ
    ((groupCohomology.resolution ℂ G).X i) f)
  comm' i j _ := by
    apply ModuleCat.hom_ext
    ext x
    change (groupCohomology.linearYonedaObjResolution A).d i j (x ≫ f) =
      ((groupCohomology.linearYonedaObjResolution A).d i j x) ≫ f
    rw [groupCohomology.linearYonedaObjResolution_d_apply,
      groupCohomology.linearYonedaObjResolution_d_apply, Category.assoc]

/-- The same coefficient action in the inhomogeneous cochain model used
by mathlib's `groupCohomology`. -/
def groupCoefficientAction {G : Type} [Group G] {A : Rep ℂ G} (f : A ⟶ A) (k : ℕ) :
    groupCohomology A k ⟶ groupCohomology A k :=
  HomologicalComplex.homologyMap ((groupCohomology.inhomogeneousCochainsIso A).hom ≫
    coefficientCochainMap f ≫ (groupCohomology.inhomogeneousCochainsIso A).inv) k

theorem groupCohomologyCoefficientHull (h : MOCIsTrue)
    {G : Type} [Group G] {A : Rep ℂ G} (f g : A ⟶ A) (k : ℕ) {n : ℕ}
    (e : Basis (Fin n) ℂ (groupCohomology A k)) (U : Mat n) (a b : Fin n → ℂ)
    (hA : IsStarNormal (moduleOperator e (groupCoefficientAction f k)))
    (hB : IsStarNormal (moduleOperator e (groupCoefficientAction g k))) (hU : IsUnitary U)
    (ha : HasRoots (moduleOperator e (groupCoefficientAction f k)) a)
    (hb : HasRoots (moduleOperator e (groupCoefficientAction g k)) b) :
    OperatorHull (moduleOperator e (groupCoefficientAction f k))
      (moduleOperator e (groupCoefficientAction g k)) U a b :=
  operatorHull_of_moc h _ _ _ _ _ hA hB hU ha hb

/-!
077: the theorem for actual chain components applies after a cellular
chain complex and its cellular maps have been constructed. It does not
construct the CW cellular functor.

078–079, 081–082, 084, 086–088, 092 and 121: the determinant of a specified
finite induced normal map follows from the operator theorem. This file
does not supply the de Rham, Dolbeault, intersection, group homology, sheaf,
Hochschild, cyclic, spectral sequence or Floer functorial constructions.
Those are not interchangeable with arbitrary sampled eigenvalue lists.
-/

end

end MOC.Reformulations.NativeFirstB
