import MOC.Reformulations.FirstMatrix
import Mathlib.RingTheory.TensorProduct.Basic

/-! Native finite representations. The sufficient matrix hypotheses concern the
images of the actual algebra operations, not arbitrary assigned spectral labels. -/

open BigOperators Matrix TensorProduct

namespace MOC.Reformulations
noncomputable section

/-- The pure algebraic, slightly stronger form of Atlas 051: continuity and
completeness of the source do not enter the finite determinant argument. -/
def nativeComplexAlgebraRepresentation : Prop :=
  ∀ (n : ℕ) (A : Type) [Ring A] [Algebra ℂ A]
    (ρ : A →ₐ[ℂ] Matrix (Fin n) (Fin n) ℂ) (x y : A)
    (U : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n → ℂ),
    IsStarNormal (ρ x) → IsStarNormal (ρ y) → IsUnitary U →
    (ρ x).charpoly.roots = Finset.univ.val.map a →
    (ρ y).charpoly.roots = Finset.univ.val.map b →
    (ρ x + U * ρ y * Uᴴ).det ∈ convexHull ℝ (Set.range (matchingProduct a b))

theorem moc_iff_nativeComplexAlgebraRepresentation :
    MOCIsTrue ↔ nativeComplexAlgebraRepresentation := by
  rw [moc_iff_complexMatrices]
  constructor
  · intro h n A _ _ ρ x y U a b hx hy hU ha hb
    exact h n (ρ x) (ρ y) U a b hx hy hU ha hb
  · intro h n X Y U a b hX hY hU ha hb
    exact h n (Matrix (Fin n) (Fin n) ℂ) (AlgHom.id ℂ _) X Y U a b hX hY hU ha hb

/-- The algebraic strengthening of Atlas 053: the source need only be a
complex star algebra. A source unitary and its adjoint are represented by
the same star homomorphism. -/
def nativeStarAlgebraRepresentation : Prop :=
  ∀ (n : ℕ) (A : Type) [Ring A] [Algebra ℂ A] [StarRing A]
    (ρ : A →⋆ₐ[ℂ] Matrix (Fin n) (Fin n) ℂ) (x y : A)
    (u : unitary A) (a b : Fin n → ℂ),
    IsStarNormal x → IsStarNormal y →
    (ρ x).charpoly.roots = Finset.univ.val.map a →
    (ρ y).charpoly.roots = Finset.univ.val.map b →
    (ρ (x + (u : A) * y * star (u : A))).det ∈
      convexHull ℝ (Set.range (matchingProduct a b))

theorem moc_iff_nativeStarAlgebraRepresentation :
    MOCIsTrue ↔ nativeStarAlgebraRepresentation := by
  rw [moc_iff_complexMatrices]
  constructor
  · intro h n A _ _ _ ρ x y u a b hx hy ha hb
    obtain ⟨h₁, h₂⟩ := unitary.mem_iff.mp u.property
    have hU : IsUnitary (ρ u) := by
      constructor
      · change ρ (u : A) * star (ρ (u : A)) = 1
        rw [← map_star, ← map_mul, h₂, map_one]
      · change star (ρ (u : A)) * ρ (u : A) = 1
        rw [← map_star, ← map_mul, h₁, map_one]
    change _ ∈ _
    rw [map_add, map_mul, map_mul, map_star]
    exact h n (ρ x) (ρ y) (ρ u) a b (hx.map ρ) (hy.map ρ) hU ha hb
  · intro h n X Y U a b hX hY hU ha hb
    let u : unitary (Matrix (Fin n) (Fin n) ℂ) :=
      ⟨U, unitary.mem_iff.mpr ⟨hU.2, hU.1⟩⟩
    exact h n (Matrix (Fin n) (Fin n) ℂ) (StarAlgHom.id ℂ _) X Y u a b hX hY ha hb

/-- Atlas 027: actual scalar extension and a chosen algebra splitting. No
extra structural property of the original algebra is used after the splitting. -/
def nativeSplitScalarExtension : Prop :=
  ∀ (F : Type) [Field F] [Algebra F ℂ] (A : Type) [Ring A] [Algebra F A]
    (n : ℕ) (ρ : (ℂ ⊗[F] A) ≃ₐ[ℂ] Matrix (Fin n) (Fin n) ℂ)
    (x y : A) (U : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n → ℂ),
    let X := ρ ((1 : ℂ) ⊗ₜ[F] x)
    let Y := ρ ((1 : ℂ) ⊗ₜ[F] y)
    IsStarNormal X → IsStarNormal Y → IsUnitary U →
    X.charpoly.roots = Finset.univ.val.map a → Y.charpoly.roots = Finset.univ.val.map b →
    (X + U * Y * Uᴴ).det ∈ convexHull ℝ (Set.range (matchingProduct a b))

theorem moc_iff_nativeSplitScalarExtension : MOCIsTrue ↔ nativeSplitScalarExtension := by
  rw [moc_iff_complexMatrices]
  constructor
  · intro h F _ _ A _ _ n ρ x y U a b
    dsimp only
    exact h n (ρ ((1 : ℂ) ⊗ₜ[F] x)) (ρ ((1 : ℂ) ⊗ₜ[F] y)) U a b
  · intro h n X Y U a b hX hY hU ha hb
    let ρ := Algebra.TensorProduct.lid ℂ (Matrix (Fin n) (Fin n) ℂ)
    have hr := h ℂ (Matrix (Fin n) (Fin n) ℂ) n ρ X Y U a b
    simpa [ρ, Algebra.TensorProduct.lid_tmul] using hr
      (by simpa [ρ, Algebra.TensorProduct.lid_tmul] using hX)
      (by simpa [ρ, Algebra.TensorProduct.lid_tmul] using hY) hU
      (by simpa [ρ, Algebra.TensorProduct.lid_tmul] using ha)
      (by simpa [ρ, Algebra.TensorProduct.lid_tmul] using hb)

/-- The entrywise extension of a division-ring representation to complex
block matrices, in the stated enumeration of row and column pairs. -/
def divisionBlockMatrix {D : Type} [DivisionRing D] {n r s : ℕ}
    (ρ : D →+* Matrix (Fin s) (Fin s) ℂ) (e : Fin n ≃ Fin r × Fin s)
    (X : Matrix (Fin r) (Fin r) D) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j => ρ (X (e i).1 (e j).1) (e i).2 (e j).2

/-- Atlas 030, with actual block representation; the cardinality of the
target is enforced by the enumeration equivalence. -/
def nativeDivisionBlockHull : Prop :=
  ∀ (D : Type) [DivisionRing D] (n r s : ℕ)
    (ρ : D →+* Matrix (Fin s) (Fin s) ℂ), Function.Injective ρ →
    ∀ (e : Fin n ≃ Fin r × Fin s) (X Y : Matrix (Fin r) (Fin r) D)
    (U : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n → ℂ),
    IsStarNormal (divisionBlockMatrix ρ e X) → IsStarNormal (divisionBlockMatrix ρ e Y) →
    IsUnitary U →
    (divisionBlockMatrix ρ e X).charpoly.roots = Finset.univ.val.map a →
    (divisionBlockMatrix ρ e Y).charpoly.roots = Finset.univ.val.map b →
    (divisionBlockMatrix ρ e X + U * divisionBlockMatrix ρ e Y * Uᴴ).det ∈
      convexHull ℝ (Set.range (matchingProduct a b))

private def enumerateScalarBlocks (n : ℕ) : Fin n ≃ Fin n × Fin 1 where
  toFun i := (i, 0)
  invFun := Prod.fst
  left_inv _ := rfl
  right_inv _ := Prod.ext rfl (Subsingleton.elim _ _)

private theorem scalarBlocks_eq {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) :
    divisionBlockMatrix (Matrix.scalar (Fin 1)) (enumerateScalarBlocks n) X = X := by
  ext i j
  simp [divisionBlockMatrix, enumerateScalarBlocks, Matrix.scalar_apply]

theorem moc_iff_nativeDivisionBlockHull : MOCIsTrue ↔ nativeDivisionBlockHull := by
  rw [moc_iff_complexMatrices]
  constructor
  · intro h D _ n r s ρ _ e X Y U a b hX hY hU ha hb
    exact h n _ _ U a b hX hY hU ha hb
  · intro h n X Y U a b hX hY hU ha hb
    have hinj : Function.Injective (Matrix.scalar (Fin 1) : ℂ →+* Matrix (Fin 1) (Fin 1) ℂ) := by
      intro a b hEq
      have h00 := congrArg (fun K : Matrix (Fin 1) (Fin 1) ℂ => K 0 0) hEq
      simpa [Matrix.scalar_apply] using h00
    exact scalarBlocks_eq X ▸ scalarBlocks_eq Y ▸
      h ℂ n n 1 (Matrix.scalar (Fin 1)) hinj (enumerateScalarBlocks n) X Y U a b
        ((scalarBlocks_eq X).symm ▸ hX) ((scalarBlocks_eq Y).symm ▸ hY) hU
        ((scalarBlocks_eq X).symm ▸ ha) ((scalarBlocks_eq Y).symm ▸ hb)


end
end MOC.Reformulations
