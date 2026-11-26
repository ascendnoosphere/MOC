import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.AlgebraicTopology.SingularHomology.Basic

open CategoryTheory

namespace MOC

noncomputable section

/-- Singular homology with integral coefficients. -/
abbrev integralSingularHomology (k : ℕ) : TopCat.{0} ⥤ ModuleCat ℤ :=
  (AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) k).obj (ModuleCat.of ℤ ℤ)

abbrev puncturePreimage {X Y : TopCat.{0}} (f : X ⟶ Y) (z : Y) : TopCat.{0} :=
  TopCat.of {x : X // f x ≠ z}

abbrev puncturedSpace (Y : TopCat.{0}) (z : Y) : TopCat.{0} :=
  TopCat.of {y : Y // y ≠ z}

def puncturePreimageInclusion {X Y : TopCat.{0}} (f : X ⟶ Y) (z : Y) :
    puncturePreimage f z ⟶ X :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

def punctureRestriction {X Y : TopCat.{0}} (f : X ⟶ Y) (z : Y) :
    puncturePreimage f z ⟶ puncturedSpace Y z :=
  TopCat.ofHom ⟨fun x => ⟨f x, x.property⟩, (f.hom.continuous.comp continuous_subtype_val).subtype_mk _⟩

/-- If a homology class becomes zero in the full source but its image in
the punctured target is nonzero, the full image contains the puncture. -/
theorem mem_range_of_nonzero_punctured_homology {X Y : TopCat.{0}}
    (f : X ⟶ Y) (z : Y) (k : ℕ)
    (c : (integralSingularHomology k).obj (puncturePreimage f z))
    (hzero : ((integralSingularHomology k).map (puncturePreimageInclusion f z)) c = 0)
    (hlink : ((integralSingularHomology k).map (punctureRestriction f z)) c ≠ 0) :
    z ∈ Set.range f := by
  by_contra hz
  have hne (x : X) : f x ≠ z := fun hx => hz ⟨x, hx⟩
  let g : X ⟶ puncturedSpace Y z :=
    TopCat.ofHom ⟨fun x => ⟨f x, hne x⟩, f.hom.continuous.subtype_mk _⟩
  have hcomp : puncturePreimageInclusion f z ≫ g = punctureRestriction f z := by
    ext x
    rfl
  apply hlink
  rw [← hcomp, Functor.map_comp]
  change ((integralSingularHomology k).map g)
    (((integralSingularHomology k).map (puncturePreimageInclusion f z)) c) = 0
  rw [hzero, map_zero]

/-- Vanishing homology in the full source discharges the bounding-class premise. -/
theorem mem_range_of_nonzero_punctured_homology_of_subsingleton {X Y : TopCat.{0}}
    (f : X ⟶ Y) (z : Y) (k : ℕ)
    (hX : Subsingleton ((integralSingularHomology k).obj X))
    (c : (integralSingularHomology k).obj (puncturePreimage f z))
    (hlink : ((integralSingularHomology k).map (punctureRestriction f z)) c ≠ 0) :
    z ∈ Set.range f :=
  mem_range_of_nonzero_punctured_homology f z k c (hX.elim _ _) hlink

end

end MOC
