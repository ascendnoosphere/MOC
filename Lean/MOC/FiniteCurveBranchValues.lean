import MOC.FiniteCurveConnected
import MOC.FiniteCurveExceptions
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Polynomial.GaussLemma

/-! The exceptional fibers of an irreducible monic plane polynomial are finite. -/

open Polynomial

namespace MOC

/-- A monic irreducible plane polynomial admits a simple-root cover
after removing finitely many base values. The proof lifts a nonzero
element of the derivative ideal in the quotient back to a Bézout
identity over the one-variable coefficient ring. -/
theorem finite_nonseparable_specializations_of_irreducible
    (P : ℂ[X][X]) (hP : P.Monic) (hirr : Irreducible P) :
    Set.Finite {z : ℂ | ¬ (P.map (evalRingHom z)).Separable} := by
  classical
  let A := ℂ[X]
  let B := AdjoinRoot P
  letI : IsDomain B := AdjoinRoot.isDomain_of_prime (irreducible_iff_prime.mp hirr)
  letI : Module.Finite A B := hP.finite_adjoinRoot
  have hdeg : 0 < P.natDegree := Nat.pos_of_ne_zero fun he => by
    have h := hP.natDegree_eq_zero_iff_eq_one.mp he
    exact hirr.not_isUnit (h ▸ isUnit_one)
  have hd : P.derivative ≠ 0 := fun hz =>
    (Nat.ne_of_gt hdeg) (natDegree_eq_zero_of_derivative_eq_zero hz)
  let r : B := AdjoinRoot.mk P P.derivative
  have hr : r ≠ 0 :=
    AdjoinRoot.mk_ne_zero_of_natDegree_lt hP hd (natDegree_derivative_lt (Nat.ne_of_gt hdeg))
  let I : Ideal B := Ideal.span {r}
  have hrI : r ∈ I := Ideal.subset_span (Set.mem_singleton r)
  have hI := Ideal.comap_ne_bot_of_algebraic_mem hr hrI
    (Algebra.IsAlgebraic.isAlgebraic (R := A) r)
  obtain ⟨p, hp, hp0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  have hp' : AdjoinRoot.mk P (C p) ∈ I := hp
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp hp'
  obtain ⟨Q, rfl⟩ := Ideal.Quotient.mk_surjective b
  have he : AdjoinRoot.mk P (C p) = AdjoinRoot.mk P (P.derivative * Q) := by
    simpa only [r, RingHom.map_mul] using hb
  obtain ⟨T, hT⟩ := (AdjoinRoot.mk_eq_mk.mp he)
  have hbez : C p = P * T + P.derivative * Q := sub_eq_iff_eq_add.mp hT
  apply (Polynomial.finite_setOf_isRoot hp0).subset
  intro z hz
  change ¬ (P.map (evalRingHom z)).Separable at hz
  change p.eval z = 0
  apply Classical.byContradiction
  intro hn'
  let f := evalRingHom z
  let U := P.map f
  let T' := T.map f
  let Q' := Q.map f
  have heval : (C (p.eval z) : ℂ[X]) = U * T' + U.derivative * Q' := by
    have hh := congrArg (Polynomial.map f) hbez
    rw [Polynomial.map_C] at hh
    simpa only [Polynomial.map_C, Polynomial.map_add, Polynomial.map_mul, ← derivative_map, coe_evalRingHom] using hh
  apply hz
  apply (separable_def' _).mpr
  refine ⟨T' * C ((p.eval z)⁻¹), Q' * C ((p.eval z)⁻¹), ?_⟩
  change (T' * C ((p.eval z)⁻¹)) * U + (Q' * C ((p.eval z)⁻¹)) * U.derivative = 1
  calc
    _ = (U * T' + U.derivative * Q') * C ((p.eval z)⁻¹) := by ring
    _ = 1 := by rw [← heval, ← C_mul, mul_inv_cancel₀ hn', C_1]

/-- Removing exactly the finitely many nonseparable fibers leaves a
nonempty connected finite plane root cover. -/
theorem isConnected_regular_root_cover_of_monic_irreducible
    (P : ℂ[X][X]) (hP : P.Monic) (hirr : Irreducible P) :
    IsConnected {p : ℂ × ℂ | (P.map (evalRingHom p.1)).Separable ∧
      (P.map (evalRingHom p.1)).IsRoot p.2} := by
  let S : Set ℂ := {z | ¬ (P.map (evalRingHom z)).Separable}
  have hS : S.Finite := finite_nonseparable_specializations_of_irreducible P hP hirr
  have hs : ∀ z ∈ Sᶜ, (P.map (evalRingHom z)).Separable := fun _ hz => not_not.mp hz
  simpa only [S, Set.mem_compl_iff, Set.mem_setOf_eq, not_not] using
    isConnected_simple_root_cover_of_irreducible P hP hirr hS hs

end MOC
