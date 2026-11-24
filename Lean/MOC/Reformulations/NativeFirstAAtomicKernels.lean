import MOC.Reformulations.NativeFirstAFredholm
import Mathlib.Data.Real.Sqrt

/-! Atlas 065 on finite atomic measure spaces with positive atom masses. -/

open BigOperators Matrix

namespace MOC.Reformulations
noncomputable section

/-- The matrix of the finite integral operator in the normalized
point-mass basis. The two square roots encode the Hilbert metric. -/
def normalizedAtomicKernel {n : ℕ} (mass : Fin n → ℝ)
    (kernel : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j => (Real.sqrt (mass i) : ℂ) * kernel i j * (Real.sqrt (mass j) : ℂ)

private theorem normalizedCountingKernel {n : ℕ}
    (kernel : Matrix (Fin n) (Fin n) ℂ) :
    normalizedAtomicKernel (fun _ => 1) kernel = kernel := by
  ext i j
  simp [normalizedAtomicKernel]

private theorem atomicDiagonalNormal {n : ℕ} (a : Fin n → ℂ) :
    IsStarNormal (diagonal a) := by
  constructor
  change Commute (diagonal a)ᴴ (diagonal a)
  rw [Matrix.diagonal_conjTranspose, Commute, SemiconjBy, Matrix.diagonal_mul_diagonal,
    Matrix.diagonal_mul_diagonal]
  exact congrArg Matrix.diagonal (funext fun i => mul_comm _ _)

private theorem atomicDiagonalRoots {n : ℕ} (a : Fin n → ℂ) :
    (diagonal a).charpoly.roots = (Finset.univ : Finset (Fin n)).val.map a := by
  have hOne : IsUnitary (1 : Matrix (Fin n) (Fin n) ℂ) := by simp [IsUnitary]
  simpa using roots_unitary_diagonalization a hOne

/-- The finite atomic integral-operator Fredholm comparison in the two
normal eigenbases. The spectra here are actual roots of the two normalized
kernel matrices. This does not assert the infinite trace-class limit. -/
def nativeFiniteAtomicKernelHull : Prop :=
  ∀ (n : ℕ) (mass : Fin n → ℝ), (∀ i, 0 < mass i) →
    ∀ (K L : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n → ℂ)
      (U : Matrix (Fin n) (Fin n) ℂ),
      IsStarNormal (normalizedAtomicKernel mass K) →
      IsStarNormal (normalizedAtomicKernel mass L) →
      IsUnitary U →
      (normalizedAtomicKernel mass K).charpoly.roots = Finset.univ.val.map a →
      (normalizedAtomicKernel mass L).charpoly.roots = Finset.univ.val.map b →
      finiteFredholmValue a b U ∈ convexHull ℝ (Set.range (finiteFredholmVertex a b))

theorem moc_iff_nativeFiniteAtomicKernelHull :
    MOCIsTrue ↔ nativeFiniteAtomicKernelHull := by
  rw [moc_iff_nativeFiniteFredholmHull]
  constructor
  · intro h n mass hm K L a b U hK hL hU ha hb
    exact h n a b U hU
  · intro h n a b U hU
    have hx := normalizedCountingKernel (diagonal a)
    have hy := normalizedCountingKernel (diagonal b)
    exact h n (fun _ => 1) (fun _ => one_pos) (diagonal a) (diagonal b) a b U
      (hx.symm ▸ atomicDiagonalNormal a) (hy.symm ▸ atomicDiagonalNormal b) hU
      (hx.symm ▸ atomicDiagonalRoots a) (hy.symm ▸ atomicDiagonalRoots b)

end
end MOC.Reformulations
