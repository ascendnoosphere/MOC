import MOC.Reformulations.SecondReal
import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-! Atlas 186. Constant generators are a native subclass of periodic systems.
Their diagonal fundamental solution at time one realizes every nonzero
complex spectral list. The existing invertible-representative reduction
removes the restriction without using any heuristic spectral sampling. -/

open Matrix
namespace MOC.Reformulations

noncomputable section

/-- The period-one spectral comparison for genuinely constant diagonal
generators, whose flow at time `t` acts by `exp (t * a i)`. -/
def ConstantMonodromyForm : Prop :=
  ∀ (n : ℕ) (a b : Fin n → ℂ) (U : Matrix (Fin n) (Fin n) ℂ),
    IsUnitary U → Holds (fun i => Complex.exp (a i)) (fun j => Complex.exp (b j)) U

theorem constantMonodromyForm_iff : ConstantMonodromyForm ↔ MOCIsTrue := by
  constructor
  · intro h
    apply invertibleRepresentativeForm_iff.mp
    intro n a b U hU ha hb _
    have hv := h n (fun i => Complex.log (a i)) (fun j => Complex.log (b j)) U hU
    have he : (fun i => Complex.exp (Complex.log (a i))) = a := by
      funext i
      exact Complex.exp_log (ha i)
    have hf : (fun i => Complex.exp (Complex.log (b i))) = b := by
      funext i
      exact Complex.exp_log (hb i)
    rwa [he, hf] at hv
  · intro h n a b U hU
    exact h n _ _ U hU

theorem not_constantMonodromyForm_iff : ¬ ConstantMonodromyForm ↔ ¬ MOCIsTrue :=
  not_congr constantMonodromyForm_iff

/-- Explicit multiplication law for the fundamental solution of the constant
system. Normal matrices are obtained on the standard coordinate space. -/
theorem diagonalConstantFlow_add {n : ℕ} (a : Fin n → ℂ) (s t : ℝ) :
    diagonal (fun i => Complex.exp (((s+t : ℝ) : ℂ) * a i)) =
      diagonal (fun i => Complex.exp ((s : ℂ) * a i)) *
      diagonal (fun i => Complex.exp ((t : ℂ) * a i)) := by
  rw [diagonal_mul_diagonal]
  congr 1
  funext i
  simp [Complex.ofReal_add, add_mul, Complex.exp_add]

end
end MOC.Reformulations
