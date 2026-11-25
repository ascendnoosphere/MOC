import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.Ideal.GoingDown
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.Invariant

/-! Going down for a finite extension of domains with normal base in characteristic zero. -/

open scoped Pointwise

namespace MOC

private theorem goingDown_of_invariant_extension
    (A B C G : Type*) [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] [Algebra B C] [IsScalarTower A B C] [FaithfulSMul A B]
    [Algebra.IsIntegral B C] [Group G] [Finite G] [MulSemiringAction G C]
    [SMulCommClass G A C] [Algebra.IsInvariant A C G]
    (hBC : Function.Injective (algebraMap B C)) : Algebra.HasGoingDown A B := by
  letI : Algebra.IsIntegral A C := Algebra.IsInvariant.isIntegral A C G
  have hAC : Function.Injective (algebraMap A C) := by
    rw [IsScalarTower.algebraMap_eq A B C]
    exact hBC.comp (FaithfulSMul.algebraMap_injective _ _)
  constructor
  intro p hp Q hQ hpQ
  have hkerBC : Ideal.comap (algebraMap B C) (⊥ : Ideal C) = ⊥ :=
    (RingHom.injective_iff_ker_eq_bot _).mp hBC
  have hkerAC : Ideal.comap (algebraMap A C) (⊥ : Ideal C) = ⊥ :=
    (RingHom.injective_iff_ker_eq_bot _).mp hAC
  obtain ⟨Q', _, hQ', hQ'Q⟩ := Ideal.exists_ideal_over_prime_of_isIntegral Q (⊥ : Ideal C)
    (by rw [hkerBC]; exact bot_le)
  obtain ⟨P', _, hP', hP'p⟩ := Ideal.exists_ideal_over_prime_of_isIntegral p (⊥ : Ideal C)
    (by rw [hkerAC]; exact bot_le)
  have hQ'base : Q'.under A = Q.under A := by
    rw [← Ideal.under_under Q' (A := A) (B := B)]
    change (Ideal.comap (algebraMap B C) Q').under A = Q.under A
    rw [hQ'Q]
  obtain ⟨R', hP'R', hR', hR'base⟩ :=
    Ideal.exists_ideal_over_prime_of_isIntegral_of_isPrime (Q.under A) P'
      (by rw [hP'p]; exact hpQ.le)
  obtain ⟨g, hg⟩ := Algebra.IsInvariant.exists_smul_of_under_eq A C G R' Q'
    (hR'base.trans hQ'base.symm)
  have hsmul : (g • P' : Ideal C) ≤ Q' := by
    rw [hg]
    exact smul_mono_right g hP'R'
  have hlower : (g • P' : Ideal C).under A = p := (P'.under_smul A g).trans hP'p
  haveI : (g • P' : Ideal C).IsPrime := hP'.smul g
  refine ⟨(g • P' : Ideal C).under B, ?_, inferInstance, ⟨?_⟩⟩
  · rw [← hQ'Q]
    exact Ideal.comap_mono hsmul
  · rw [Ideal.under_under, hlower]

private theorem finite_fraction_extension
    (A B F E : Type*) [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [Field F] [Field E] [Algebra A B] [Algebra A F] [Algebra B E] [Algebra A E]
    [Algebra F E] [IsScalarTower A B E] [IsScalarTower A F E]
    [IsFractionRing A F] [IsFractionRing B E] [Module.Finite A B] :
    FiniteDimensional F E := by
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := A) (M := B)
  have hinj : Function.Injective (algebraMap A E) := by
    rw [IsScalarTower.algebraMap_eq A F E]
    exact (algebraMap F E).injective.comp (IsFractionRing.injective A F)
  have hs' : (Ideal.span ({1} : Set B) : Set B) ⊆ Submodule.span A (↑s : Set B) := by
    rw [hs]
    exact Set.subset_univ _
  have h := IsFractionRing.ideal_span_singleton_map_subset A
    (K := F) (L := E) hinj hs'
  rw [map_one, Ideal.span_singleton_one] at h
  refine ⟨?_⟩
  have heq : Submodule.span F (algebraMap B E '' (↑s : Set B)) = ⊤ :=
    top_unique fun _ _ => h (by simp)
  rw [← heq]
  exact Submodule.fg_span (s.finite_toSet.image (algebraMap B E))

/-- A finite domain extension of an integrally closed domain satisfies going
down when the fraction field has characteristic zero. -/
theorem finite_domain_goingDown_of_normal_base
    (A B : Type*) [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [Algebra A B] [FaithfulSMul A B] [Module.Finite A B] [IsIntegrallyClosed A]
    [CharZero (FractionRing A)] : Algebra.HasGoingDown A B := by
  let F := FractionRing A
  let E := FractionRing B
  letI : Algebra F E := FractionRing.liftAlgebra A E
  letI : IsScalarTower A F E := FractionRing.isScalarTower_liftAlgebra A E
  letI : FiniteDimensional F E := finite_fraction_extension A B F E
  let L₀ := AlgebraicClosure F
  let j : E →ₐ[F] L₀ := IsAlgClosed.lift
  letI : Algebra E L₀ := j.toRingHom.toAlgebra
  letI : IsScalarTower F E L₀ := IsScalarTower.of_algebraMap_eq fun x => (j.commutes x).symm
  let L := IntermediateField.normalClosure F E L₀
  letI : Algebra A L := ((algebraMap F L).comp (algebraMap A F)).toAlgebra
  letI : IsScalarTower A F L := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower A E L := IsScalarTower.of_algebraMap_eq' <| by
    rw [IsScalarTower.algebraMap_eq A F E, ← RingHom.comp_assoc,
      ← IsScalarTower.algebraMap_eq F E L, ← IsScalarTower.algebraMap_eq A F L]
  letI : Algebra B L := ((algebraMap E L).comp (algebraMap B E)).toAlgebra
  letI : IsScalarTower B E L := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower A B L := IsScalarTower.of_algebraMap_eq' <| by
    rw [IsScalarTower.algebraMap_eq B E L, RingHom.comp_assoc,
      ← IsScalarTower.algebraMap_eq A B E, ← IsScalarTower.algebraMap_eq A E L]
  let C := integralClosure A L
  letI : IsFractionRing C L := integralClosure.isFractionRing_of_finite_extension F L
  let i : B →ₐ[A] C := IsIntegralClosure.lift A C L
  letI : Algebra B C := i.toRingHom.toAlgebra
  letI : IsScalarTower A B C := IsScalarTower.of_algebraMap_eq fun a => (i.commutes a).symm
  letI : IsScalarTower B C L := IsScalarTower.of_algebraMap_eq fun b =>
    (IsIntegralClosure.algebraMap_lift A C L b).symm
  have hi : Function.Injective (algebraMap B C) := by
    have hbL : Function.Injective (algebraMap B L) := by
      rw [IsScalarTower.algebraMap_eq B E L]
      exact (algebraMap E L).injective.comp (IsFractionRing.injective B E)
    rw [IsScalarTower.algebraMap_eq B C L] at hbL
    change Function.Injective (algebraMap C L ∘ algebraMap B C) at hbL
    exact Function.Injective.of_comp hbL
  letI : Algebra.IsIntegral B C :=
    ⟨fun c => (IsIntegralClosure.isIntegral A L c).tower_top⟩
  letI : Algebra.IsInvariant A C (C ≃ₐ[A] C) := Algebra.isInvariant_of_isGalois' A F L C
  letI : Finite (C ≃ₐ[A] C) := Finite.of_equiv (L ≃ₐ[F] L) (galRestrict A F L C).toEquiv
  exact goingDown_of_invariant_extension A B C (C ≃ₐ[A] C) hi

end MOC
