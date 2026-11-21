import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-! Polynomial specialization on the conjugation graph used to partition
the eigenvalues of a two-root Hermitian pencil. -/

open Polynomial
open scoped Polynomial

namespace MOC

noncomputable section

private theorem eval_pair_eq_zero_of_real_line (p : MvPolynomial (Fin 2) ℂ)
    (a b c d : ℂ)
    (h : ∀ x : ℝ, MvPolynomial.eval ![a * (x : ℂ) + b, c * (x : ℂ) + d] p = 0)
    (x : ℂ) : MvPolynomial.eval ![a * x + b, c * x + d] p = 0 := by
  let q := MvPolynomial.eval₂ (Polynomial.C : ℂ →+* ℂ[X])
    ![Polynomial.C a * X + Polynomial.C b, Polynomial.C c * X + Polynomial.C d] p
  have heval (x : ℂ) : q.eval x = MvPolynomial.eval ![a * x + b, c * x + d] p := by
    have hcomp : (Polynomial.evalRingHom x).comp (Polynomial.C : ℂ →+* ℂ[X]) =
        RingHom.id ℂ := by ext y; simp
    dsimp only [q]
    rw [MvPolynomial.polynomial_eval_eval₂, hcomp, MvPolynomial.eval₂_id]
    have hvec : (fun i : Fin 2 =>
        Polynomial.eval x ![Polynomial.C a * X + Polynomial.C b,
          Polynomial.C c * X + Polynomial.C d] i) = ![a * x + b, c * x + d] := by
      funext i
      fin_cases i <;> simp
    rw [hvec]
  have hq : q = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    apply (Set.infinite_range_of_injective Complex.ofReal_injective).mono
    rintro _ ⟨y, rfl⟩
    exact (heval (y : ℂ)).trans (h y)
  rw [← heval, hq, Polynomial.eval_zero]

/-- A complex polynomial in two variables vanishing on the graph of
conjugation is identically zero. -/
theorem mvPolynomial_eq_zero_of_eval_conj (p : MvPolynomial (Fin 2) ℂ)
    (h : ∀ z : ℂ, MvPolynomial.eval ![z, star z] p = 0) : p = 0 := by
  have hreal (x y : ℝ) :
      MvPolynomial.eval ![(x : ℂ) + (y : ℂ) * Complex.I,
        (x : ℂ) - (y : ℂ) * Complex.I] p = 0 := by
    have he : star ((x : ℂ) + (y : ℂ) * Complex.I) =
        (x : ℂ) - (y : ℂ) * Complex.I := by simp [Complex.star_def, sub_eq_add_neg]
    simpa only [he] using h ((x : ℂ) + (y : ℂ) * Complex.I)
  have hrealY (y : ℝ) (x : ℂ) :
      MvPolynomial.eval ![x + (y : ℂ) * Complex.I, x - (y : ℂ) * Complex.I] p = 0 := by
    have he (t : ℝ) : MvPolynomial.eval ![(1 : ℂ) * (t : ℂ) + (y : ℂ) * Complex.I,
        (1 : ℂ) * (t : ℂ) + -((y : ℂ) * Complex.I)] p = 0 := by
      simpa only [one_mul, ← sub_eq_add_neg] using hreal t y
    simpa only [one_mul, ← sub_eq_add_neg] using
      eval_pair_eq_zero_of_real_line p 1 ((y : ℂ) * Complex.I) 1 (-((y : ℂ) * Complex.I)) he x
  have hall (x y : ℂ) : MvPolynomial.eval ![x + y * Complex.I, x - y * Complex.I] p = 0 := by
    have he₁ (t : ℂ) : Complex.I * t + x = x + t * Complex.I := by ring
    have he₂ (t : ℂ) : -Complex.I * t + x = x - t * Complex.I := by ring
    have he (t : ℝ) : MvPolynomial.eval ![Complex.I * (t : ℂ) + x,
        -Complex.I * (t : ℂ) + x] p = 0 := by
      rw [he₁, he₂]
      exact hrealY t x
    simpa only [he₁, he₂] using eval_pair_eq_zero_of_real_line p Complex.I x (-Complex.I) x he y
  apply MvPolynomial.funext
  intro f
  change MvPolynomial.eval f p = MvPolynomial.eval f 0
  let x := (f 0 + f 1) / 2
  let y := (f 0 - f 1) / (2 * Complex.I)
  have hy : y * Complex.I = (f 0 - f 1) / 2 := by
    dsimp only [y]
    field_simp [Complex.I_ne_zero]
  have hf : ![x + y * Complex.I, x - y * Complex.I] = f := by
    funext i
    fin_cases i <;> simp [x, hy] <;> ring
  rw [← hf, map_zero]
  exact hall x y

private theorem mvPolynomial_eq_zero_of_eval_conj_nonzero (p : MvPolynomial (Fin 2) ℂ)
    (h : ∀ z : ℂ, z ≠ 0 → MvPolynomial.eval ![z, star z] p = 0) : p = 0 := by
  have he : MvPolynomial.X (0 : Fin 2) * p = 0 := by
    apply mvPolynomial_eq_zero_of_eval_conj
    intro z
    by_cases hz : z = 0
    · simp [hz]
    · rw [map_mul, h z hz, mul_zero]
  exact (mul_eq_zero.mp he).resolve_left (MvPolynomial.X_ne_zero _)

/-- Divisibility by a monic polynomial transfers from every nonzero conjugate
parameter pair to arbitrary complex values of the two parameters. -/
theorem polynomial_dvd_of_conjugate_specializations
    (p q : Polynomial (MvPolynomial (Fin 2) ℂ)) (hp : p.Monic)
    (h : ∀ z : ℂ, z ≠ 0 →
      p.map (MvPolynomial.eval ![z, star z]) ∣ q.map (MvPolynomial.eval ![z, star z])) : p ∣ q := by
  apply (Polynomial.modByMonic_eq_zero_iff_dvd hp).mp
  ext k
  rw [Polynomial.coeff_zero]
  apply mvPolynomial_eq_zero_of_eval_conj_nonzero
  intro z hz
  let e := MvPolynomial.eval ![z, star z]
  have he : q.map e %ₘ p.map e = 0 :=
    (Polynomial.modByMonic_eq_zero_iff_dvd (hp.map e)).mpr (h z hz)
  rw [← Polynomial.map_modByMonic e hp] at he
  simpa only [Polynomial.coeff_map, Polynomial.coeff_zero] using
    congrArg (fun r : ℂ[X] => r.coeff k) he

end

end MOC
