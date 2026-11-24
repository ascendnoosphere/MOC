import Mathlib.RingTheory.Invariant
import Mathlib.RingTheory.Ideal.GoingDown
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.Normal.Closure
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.RingTheory.Localization.Integral

/-! Going down for finite normal-base domain extensions in characteristic
zero. In a finite Galois normal closure, conjugacy of primes lets a
going-up chain end at the prescribed prime. See the Stacks Project
going-down theorem (tag 00HW) for the general commutative algebra result. -/

open scoped Pointwise

namespace MOC

section

variable (A B : Type*) [CommRing A] [IsDomain A] [CharZero A] [IsIntegrallyClosed A]
  [CommRing B] [IsDomain B] [Algebra A B] [FaithfulSMul A B] [Module.Finite A B]

set_option maxHeartbeats 2000000 in
/-- An injective finite extension of domains of characteristic zero has
going down when the base is integrally closed. -/
theorem hasGoingDown_of_finite_normal_base : Algebra.HasGoingDown A B := by
  classical
  let K := FractionRing A
  let L := FractionRing B
  letI : Algebra K L := FractionRing.liftAlgebra A L
  letI : IsScalarTower A K L := FractionRing.isScalarTower_liftAlgebra A L
  have hBL := IsFractionRing.injective B L
  have hAL := FaithfulSMul.algebraMap_injective A L
  have hrepr (x : L) : ∃ b : B, ∃ a : A, a ≠ 0 ∧
      algebraMap B L b = algebraMap A L a * x := by
    obtain ⟨b, c, hc, hbc⟩ := IsFractionRing.div_surjective (A := B) x
    let I : Ideal B := Ideal.span {c}
    have hI := Ideal.comap_ne_bot_of_algebraic_mem (mem_nonZeroDivisors_iff_ne_zero.mp hc)
      (show c ∈ I from Ideal.mem_span_singleton_self _) (Algebra.IsAlgebraic.isAlgebraic (R := A) c)
    obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
    obtain ⟨q, hq⟩ := Ideal.mem_span_singleton.mp (show algebraMap A B a ∈ I from ha)
    refine ⟨q * b, a, ha0, ?_⟩
    have hcn : algebraMap B L c ≠ 0 := by
      simpa only [map_zero] using hBL.ne (mem_nonZeroDivisors_iff_ne_zero.mp hc)
    have hq' : algebraMap A L a = algebraMap B L c * algebraMap B L q := by
      rw [IsScalarTower.algebraMap_apply A B L, hq, map_mul]
    rw [map_mul, hq', ← hbc]
    field_simp
    ring
  letI : Module.Finite K L := by
    obtain ⟨s, hs⟩ := (inferInstance : Module.Finite A B)
    let j : B →ₗ[A] L := (IsScalarTower.toAlgHom A B L).toLinearMap
    refine ⟨s.image (algebraMap B L), eq_top_iff.mpr (fun x _ => ?_)⟩
    set V := Submodule.span K (↑(s.image (algebraMap B L)) : Set L)
    have hspan : Submodule.span A (↑s : Set B) ≤ (V.restrictScalars A).comap j := by
      apply Submodule.span_le.mpr
      intro y hy
      exact Submodule.subset_span (Finset.mem_image.mpr ⟨y, hy, rfl⟩)
    obtain ⟨b, a, ha, hab⟩ := hrepr x
    have hb : algebraMap B L b ∈ V := hspan (hs ▸ Submodule.mem_top)
    have hsmul := V.smul_mem (algebraMap A K a)⁻¹ hb
    have hn : algebraMap A L a ≠ 0 := by simpa only [map_zero] using hAL.ne ha
    simpa only [hab, Algebra.smul_def, map_inv₀, ← IsScalarTower.algebraMap_apply,
      ← mul_assoc, inv_mul_cancel₀ hn, one_mul] using hsmul
  letI : CharZero K := inferInstanceAs (CharZero (FractionRing A))
  let T := AlgebraicClosure K
  let i : L →ₐ[K] T := IsAlgClosed.lift
  letI : Algebra L T := i.toRingHom.toAlgebra
  letI : IsScalarTower K L T := IsScalarTower.of_algebraMap_eq fun k => (i.commutes k).symm
  let E := ↥(IntermediateField.normalClosure K L T)
  letI : Algebra A E := ((algebraMap K E).comp (algebraMap A K)).toAlgebra
  letI : IsScalarTower A K E := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  letI : IsScalarTower A L E := IsScalarTower.of_algebraMap_eq fun a => by
    rw [IsScalarTower.algebraMap_apply A K E, IsScalarTower.algebraMap_apply A K L,
      ← IsScalarTower.algebraMap_apply K L E]
  let I := integralClosure A E
  let j : B →ₐ[A] E :=
    (IsScalarTower.toAlgHom A L E).comp (IsScalarTower.toAlgHom A B L)
  let g : B →ₐ[A] I := j.codRestrict I (fun b => (Algebra.IsIntegral.isIntegral (R := A) b).map j)
  have hj : Function.Injective j :=
    (algebraMap L E).injective.comp (IsFractionRing.injective B L)
  have hg : Function.Injective g := fun x y h => hj (congrArg Subtype.val h)
  letI : Algebra B I := g.toRingHom.toAlgebra
  letI : IsScalarTower A B I := IsScalarTower.of_algebraMap_eq fun a => (g.commutes a).symm
  letI : Algebra.IsIntegral B I := Algebra.IsIntegral.tower_top A
  letI : IsFractionRing I E := IsIntegralClosure.isFractionRing_of_finite_extension A K E I
  let G := E ≃ₐ[K] E
  letI : MulSemiringAction G I := IsIntegralClosure.MulSemiringAction A K E I
  letI : Algebra.IsInvariant A I G := Algebra.isInvariant_of_isGalois A K E I
  letI : SMulCommClass G A I := ⟨fun s a z => by
    change galRestrict A K E I s (a • z) = a • galRestrict A K E I s z
    exact map_smul _ _ _⟩
  constructor
  intro p hp Q hQ hpQ
  have hker : RingHom.ker (algebraMap B I) ≤ Q := by
    have hgb : Function.Injective (algebraMap B I) := hg
    rw [(RingHom.injective_iff_ker_eq_bot (algebraMap B I)).mp hgb]
    exact bot_le
  obtain ⟨Q₀, hQ₀, hQ₀B⟩ := Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain Q hker
  letI : Q₀.IsPrime := hQ₀
  have hAE : Function.Injective (algebraMap A E) :=
    (algebraMap K E).injective.comp (IsFractionRing.injective A K)
  have hIA : Function.Injective (algebraMap A I) := by
    intro a b h
    apply hAE
    simpa only [← IsScalarTower.algebraMap_apply A I E] using congrArg (algebraMap I E) h
  have hkerA : RingHom.ker (algebraMap A I) ≤ p := by
    rw [(RingHom.injective_iff_ker_eq_bot (algebraMap A I)).mp hIA]
    exact bot_le
  obtain ⟨P₁, hP₁, hP₁A⟩ := Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain p hkerA
  have hP₁le : P₁.comap (algebraMap A I) ≤ Q.under A := hP₁A ▸ hpQ.le
  obtain ⟨Q₁, hPQ₁, hQ₁, hQ₁A⟩ :=
    Ideal.exists_ideal_over_prime_of_isIntegral (Q.under A) P₁ hP₁le
  letI : Q₁.IsPrime := hQ₁
  have hQ₀A : Q₀.under A = Q.under A := by
    rw [← Ideal.under_under (B := B), show Q₀.under B = Q from hQ₀B]
  obtain ⟨s, hs⟩ := Algebra.IsInvariant.exists_smul_of_under_eq
    (A := A) (B := I) (G := G) Q₁ Q₀ (hQ₁A.trans hQ₀A.symm)
  let P₂ := s • P₁
  have hP₂Q : P₂ ≤ Q₀ := hs.symm ▸ smul_mono_right s hPQ₁
  have hP₂ : P₂.IsPrime := hP₁.smul s
  refine ⟨P₂.under B, (Ideal.comap_mono hP₂Q).trans_eq hQ₀B, hP₂.comap _, ⟨?_⟩⟩
  change p = (P₂.under B).under A
  calc
    p = P₁.under A := hP₁A.symm
    _ = P₂.under A := (P₁.under_smul A s).symm
    _ = (P₂.under B).under A := (Ideal.under_under P₂).symm

end

end MOC
