import MOC.SpectralKKT
import Mathlib.Analysis.Calculus.Deriv.Add

/-! Exact trace/variance identity for the isospectral double-bracket flow.
Brockett's sorting flow: DOI 10.1016/0024-3795(91)90021-N. This
derivative does not assert the adjacent-assignment threshold bound. -/

open Matrix BigOperators

namespace MOC

variable {ι : Type*} [Fintype ι]

/-- Squared Frobenius norm of the spectral commutator. -/
noncomputable def commutatorFrobeniusSq (X H : Matrix ι ι ℂ) : ℝ :=
  ∑ i, ∑ j, Complex.normSq ((X * H - H * X) i j)

theorem trace_mul_doubleBracket_eq_commutator_gram (X H : Matrix ι ι ℂ)
    (hX : X.IsHermitian) (hH : H.IsHermitian) :
    (X * (H * (H * X - X * H) - (H * X - X * H) * H)).trace =
      (((X * H - H * X)ᴴ) * (X * H - H * X)).trace := by
  let D := H * X - X * H
  have hskew : (X * H - H * X)ᴴ = D := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      hX.eq, hH.eq]
  rw [hskew]
  change (X * (H * D - D * H)).trace = (D * (X * H - H * X)).trace
  calc
    _ = (X * (H * D)).trace - (X * (D * H)).trace := by rw [Matrix.mul_sub, Matrix.trace_sub]
    _ = (D * (X * H)).trace - (D * (H * X)).trace := by
      rw [Matrix.trace_mul_cycle' X H D, Matrix.trace_mul_cycle' X D H, Matrix.trace_mul_cycle' H X D]
    _ = _ := by rw [Matrix.mul_sub, Matrix.trace_sub]

/-- The directional score derivative of the double-bracket velocity
equals the summed squared moduli of the commutator entries. -/
theorem doubleBracket_score_directional_coefficient (X H : Matrix ι ι ℂ)
    (hX : X.IsHermitian) (hH : H.IsHermitian) :
    (X * (H * (H * X - X * H) - (H * X - X * H) * H)).trace.re =
      commutatorFrobeniusSq X H := by
  rw [trace_mul_doubleBracket_eq_commutator_gram X H hX hH]
  let D := X * H - H * X
  change (Dᴴ * D).trace.re = ∑ i, ∑ j, Complex.normSq (D i j)
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, dotProduct, Matrix.conjTranspose_apply,
    Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.re_sum, Complex.ofReal_re]
  exact Finset.sum_comm


/-- Along an actual differentiable trajectory with the double-bracket
velocity, the score `Re tr(X H)` has this exact derivative. -/
theorem doubleBracket_score_derivative (X : Matrix ι ι ℂ) (H : ℝ → Matrix ι ι ℂ)
    (t : ℝ) (hX : X.IsHermitian) (hH : (H t).IsHermitian)
    (hvel : ∀ i j, HasDerivAt (fun s => H s i j)
      ((H t * (H t * X - X * H t) - (H t * X - X * H t) * H t) i j) t) :
    HasDerivAt (fun s => (X * H s).trace.re) (commutatorFrobeniusSq X (H t)) t := by
  rw [← doubleBracket_score_directional_coefficient X (H t) hX hH]
  have hc : HasDerivAt (fun s => (X * H s).trace)
      (X * (H t * (H t * X - X * H t) - (H t * X - X * H t) * H t)).trace t := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, dotProduct]
    exact HasDerivAt.sum (fun i _ => HasDerivAt.sum
      (fun j _ => (hvel j i).const_mul (X i j)))
  exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hc

end MOC
