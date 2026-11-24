import MOC.Reformulations.Common
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

/-!
C★ 11: simultaneous characteristic-polynomial hull in finite spectral
coordinates. Permutation vertices are the characteristic polynomials of the
matched commuting sums, with eigenvalues listed by column. This formulation
does not construct the universal C★ free product. The implication from the
simultaneous hull to MOC is proved; no converse is asserted.
-/

open BigOperators Matrix

namespace MOC.Reformulations.CStar

noncomputable section

/-- The full coefficient vector, represented as a polynomial. Taking a real
convex hull here uses one set of weights for all coefficients, rather than
one family of weights for each scalar evaluation. -/
def SimultaneousCharacteristicForm : Prop :=
  ∀ (n : ℕ) (a b : Fin n → ℂ) (U : Matrix (Fin n) (Fin n) ℂ), IsUnitary U →
    (diagonal a + U * diagonal b * Uᴴ).charpoly ∈
      convexHull ℝ (Set.range fun σ : Equiv.Perm (Fin n) =>
        (diagonal (fun j => a (σ j) + b j)).charpoly)

/-- Real-linear signed coefficient extraction, also used for the individual
elementary coefficients. -/
def signedCoefficient (c : ℂ) (k : ℕ) : Polynomial ℂ →ₗ[ℝ] ℂ where
  toFun p := c * p.coeff k
  map_add' p q := by simp [Polynomial.coeff_add, mul_add]
  map_smul' r p := by simp [Polynomial.coeff_smul, Complex.real_smul]; ring

theorem coefficient_hull_of_simultaneous (h : SimultaneousCharacteristicForm)
    {n : ℕ} (a b : Fin n → ℂ) (U : Matrix (Fin n) (Fin n) ℂ) (hU : IsUnitary U)
    (c : ℂ) (k : ℕ) :
    c * (diagonal a + U * diagonal b * Uᴴ).charpoly.coeff k ∈
      convexHull ℝ (Set.range fun σ : Equiv.Perm (Fin n) =>
        c * (diagonal (fun j => a (σ j) + b j)).charpoly.coeff k) := by
  let S := Set.range fun σ : Equiv.Perm (Fin n) =>
    (diagonal (fun j => a (σ j) + b j)).charpoly
  have he : signedCoefficient c k ((diagonal a + U * diagonal b * Uᴴ).charpoly) ∈
      signedCoefficient c k '' convexHull ℝ S :=
    ⟨_, h n a b U hU, rfl⟩
  rw [LinearMap.image_convexHull, ← Set.range_comp] at he
  exact he

/-- The simultaneous characteristic-polynomial form implies MOC by
projecting onto its constant term, with the determinant sign accounted for. -/
theorem moc_of_simultaneousCharacteristicForm (h : SimultaneousCharacteristicForm) :
    MOCIsTrue := by
  intro n a b U hU
  let c : ℂ := (-1) ^ Fintype.card (Fin n)
  have hh := coefficient_hull_of_simultaneous h a b U hU c 0
  have hs (M : Matrix (Fin n) (Fin n) ℂ) : c * M.charpoly.coeff 0 = M.det :=
    M.det_eq_sign_charpoly_coeff.symm
  simp only [hs, Matrix.det_diagonal] at hh
  exact hh

end

end MOC.Reformulations.CStar
