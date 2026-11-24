import MOC.Reformulations.NativeFirstB
import MOC.Realification
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Calculus.FDeriv.Basic

/-! Native local geometric operators (099–111, 125–126, 128, 132–133).
The comparison uses the actual endomorphisms in the chosen tangent or fiber
frame, not arbitrary functions of their spectra. A local matrix construction
does not prove global geometric realizability. -/

open BigOperators Matrix
open scoped ComplexOrder

namespace MOC.Reformulations.NativeFirstB

noncomputable section

abbrev RMat (n : ℕ) := Matrix (Fin n) (Fin n) ℝ

def complexify {n : ℕ} (A : RMat n) : Mat n := Complex.ofRealHom.mapMatrix A

theorem complexify_hermitian {n : ℕ} {A : RMat n} (hA : Aᵀ = A) :
    (complexify A).IsHermitian := by
  ext i j
  change star ((A j i : ℝ) : ℂ) = ((A i j : ℝ) : ℂ)
  simp only [Complex.star_def, Complex.conj_ofReal]
  exact congrArg (fun B : RMat n => (B i j : ℂ)) hA

/-- The matrix of the positive stretch of a specified linear derivative:
the positive-semidefinite square root of its Gram matrix. -/
def IsStretch {n : ℕ} (F P : RMat n) : Prop := P.PosSemidef ∧ P * P = Fᵀ * F

/-- 099, and 111 on the specified approximate tangent space: the finite
hull of combined positive stretches, not the Jacobian of the sum of maps. -/
theorem stretchHull {n : ℕ} (F G P R : RMat n) (Q : Matrix.orthogonalGroup (Fin n) ℝ)
    (hP : IsStretch F P) (hR : IsStretch G R) (a b : Fin n → ℝ)
    (ha : HasRoots (complexify P) (fun j => a j))
    (hb : HasRoots (complexify R) (fun j => b j)) :
    OperatorHull (complexify P) (complexify R) (complexify Q.val)
      (fun j => a j) (fun j => b j) :=
  diracBlockHull _ _ _ _ _ (complexify_hermitian hP.1.isHermitian.eq)
    (complexify_hermitian hR.1.isHermitian.eq) (isUnitary_ofReal_orthogonal Q) ha hb

/-- 100: the assertion for actual affine maps, with unrestricted translations
and the determinant of their linear parts in the standard frame. -/
def AffineDerivativeForm : Prop :=
  ∀ (n : ℕ) (f g : (Fin n → ℂ) →ᵃ[ℂ] (Fin n → ℂ)) (U : Mat n) (a b : Fin n → ℂ),
    let A := LinearMap.toMatrix' f.linear
    let B := LinearMap.toMatrix' g.linear
    IsStarNormal A → IsStarNormal B → IsUnitary U → HasRoots A a → HasRoots B b →
    OperatorHull A B U a b

theorem affineDerivativeForm_iff : AffineDerivativeForm ↔ MOCIsTrue := by
  constructor
  · intro h n
    apply conjecture_iff_normalConjecture.mpr
    intro A B a b hA hB ha hb
    let f := A.toLin'.toAffineMap
    let g := B.toLin'.toAffineMap
    have h₁ : LinearMap.toMatrix' f.linear = A := LinearMap.toMatrix'_toLin' A
    have h₂ : LinearMap.toMatrix' g.linear = B := LinearMap.toMatrix'_toLin' B
    have hh := h n f g 1 a b
    dsimp only at hh
    rw [h₁, h₂] at hh
    simpa [OperatorHull] using hh hA hB (by simp [IsUnitary]) ha hb
  · intro h n f g U a b
    dsimp only
    intro hA hB hU ha hb
    exact operatorHull_of_moc h _ _ _ _ _ hA hB hU ha hb

/-- 103 and 109 in a frame orthonormal for the reference form. The two
positive Gram matrices are the relative metric endomorphisms in this frame.
For Finsler geometry they are evaluated on the same nonzero direction. -/
theorem positiveMetricHull {n : ℕ} (P R : RMat n) (Q : Matrix.orthogonalGroup (Fin n) ℝ)
    (hP : P.PosDef) (hR : R.PosDef) (a b : Fin n → ℝ)
    (ha : HasRoots (complexify P) (fun j => a j))
    (hb : HasRoots (complexify R) (fun j => b j)) :
    OperatorHull (complexify P) (complexify R) (complexify Q.val)
      (fun j => a j) (fun j => b j) :=
  diracBlockHull _ _ _ _ _ (complexify_hermitian hP.isHermitian.eq)
    (complexify_hermitian hR.isHermitian.eq) (isUnitary_ofReal_orthogonal Q) ha hb

/-- 104: two relative endomorphisms of indefinite forms, with a mixing map
preserving both the specified positive structure and the complex bilinear
reference metric. The normality hypotheses are not dropped. -/
theorem indefiniteRelativeFormHull (h : MOCIsTrue) {n : ℕ}
    (G₀ G₁ G₂ U : Mat n) (a b : Fin n → ℂ)
    (_hG : G₀.det ≠ 0) (_hIso : Uᵀ * G₀ * U = G₀)
    (hA : IsStarNormal (G₀⁻¹ * G₁)) (hB : IsStarNormal (G₀⁻¹ * G₂))
    (hU : IsUnitary U) (ha : HasRoots (G₀⁻¹ * G₁) a) (hb : HasRoots (G₀⁻¹ * G₂) b) :
    OperatorHull (G₀⁻¹ * G₁) (G₀⁻¹ * G₂) U a b :=
  operatorHull_of_moc h _ _ _ _ _ hA hB hU ha hb

/-- 105–107 and 132: actual real symmetric shape, relative Ricci,
curvature or intersection operators in orthonormal coordinates. The
curvature case uses the basis of the second exterior power, not the rank
of the tangent space. -/
theorem realSymmetricGeometricHull {n : ℕ} (A B : RMat n)
    (Q : Matrix.orthogonalGroup (Fin n) ℝ) (hA : Aᵀ = A) (hB : Bᵀ = B)
    (a b : Fin n → ℝ) (ha : HasRoots (complexify A) (fun j => a j))
    (hb : HasRoots (complexify B) (fun j => b j)) :
    OperatorHull (complexify A) (complexify B) (complexify Q.val)
      (fun j => a j) (fun j => b j) :=
  diracBlockHull _ _ _ _ _ (complexify_hermitian hA) (complexify_hermitian hB)
    (isUnitary_ofReal_orthogonal Q) ha hb

/-- 108: positive complex metric matrices in a reference-unitary frame. -/
theorem kahlerMetricHull {n : ℕ} (A B U : Mat n) (hA : A.PosDef) (hB : B.PosDef)
    (hU : IsUnitary U) (a b : Fin n → ℝ) (ha : HasRoots A (fun j => a j))
    (hb : HasRoots B (fun j => b j)) : OperatorHull A B U (fun j => a j) (fun j => b j) :=
  diracBlockHull A B U a b hA.isHermitian hB.isHermitian hU ha hb

/-- The second Fréchet derivative in the standard coordinate frame. -/
def hessianMatrix {n : ℕ} (u : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : RMat n :=
  Matrix.of fun i j => (fderiv ℝ (fderiv ℝ u) x (Pi.single j 1)) (Pi.single i 1)

/-- 110: Hessian determinant, with symmetry stated for the actual Hessians.
For a `C²` chart this is the usual mixed-derivative symmetry condition. -/
theorem hessianHull {n : ℕ} (f g : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ)
    (Q : Matrix.orthogonalGroup (Fin n) ℝ)
    (hf : (hessianMatrix f x)ᵀ = hessianMatrix f x)
    (hg : (hessianMatrix g x)ᵀ = hessianMatrix g x)
    (a b : Fin n → ℝ) (ha : HasRoots (complexify (hessianMatrix f x)) (fun j => a j))
    (hb : HasRoots (complexify (hessianMatrix g x)) (fun j => b j)) :
    OperatorHull (complexify (hessianMatrix f x)) (complexify (hessianMatrix g x))
      (complexify Q.val) (fun j => a j) (fun j => b j) :=
  realSymmetricGeometricHull _ _ Q hf hg a b ha hb

/-- 125 in complex tangent coordinates: the actual normal derivatives at a
common fixed point. It applies in local holomorphic coordinates on a smooth
complex variety; no global algebraic geometry is assumed from the matrix. -/
theorem complexFixedPointDerivativeHull (h : MOCIsTrue) {n : ℕ}
    (f g : (Fin n → ℂ) → (Fin n → ℂ)) (x : Fin n → ℂ) (_hf : f x = x) (_hg : g x = x)
    (U : Mat n) (a b : Fin n → ℂ)
    (hA : IsStarNormal (LinearMap.toMatrix' (fderiv ℂ f x).toLinearMap))
    (hB : IsStarNormal (LinearMap.toMatrix' (fderiv ℂ g x).toLinearMap))
    (hU : IsUnitary U)
    (ha : HasRoots (LinearMap.toMatrix' (fderiv ℂ f x).toLinearMap) a)
    (hb : HasRoots (LinearMap.toMatrix' (fderiv ℂ g x).toLinearMap) b) :
    OperatorHull (LinearMap.toMatrix' (fderiv ℂ f x).toLinearMap)
      (LinearMap.toMatrix' (fderiv ℂ g x).toLinearMap) U a b :=
  operatorHull_of_moc h _ _ _ _ _ hA hB hU ha hb

/-- 126: pointwise normal bundle endomorphisms in chosen fiber frames.
Neither the frames nor the hull weights are asserted to vary continuously. -/
theorem pointwiseFiberHull (h : MOCIsTrue) {X : Type*} {n : ℕ}
    (A B U : X → Mat n) (a b : X → Fin n → ℂ) (x : X)
    (hA : IsStarNormal (A x)) (hB : IsStarNormal (B x)) (hU : IsUnitary (U x))
    (ha : HasRoots (A x) (a x)) (hb : HasRoots (B x) (b x)) :
    OperatorHull (A x) (B x) (U x) (a x) (b x) :=
  operatorHull_of_moc h _ _ _ _ _ hA hB hU ha hb

/-- 127: on one complex line the unitary conjugation fixes the scalar. -/
theorem lineFiberDet {A B U : Mat 1} (hU : IsUnitary U) :
    (A + U * B * Uᴴ).det = A 0 0 + B 0 0 := by
  rw [Matrix.det_fin_one]
  have hB : B = diagonal (fun _ => B 0 0) := by
    ext i j
    have hi : i = 0 := Subsingleton.elim _ _
    have hj : j = 0 := Subsingleton.elim _ _
    subst i; subst j; simp
  have hS : diagonal (fun _ : Fin 1 => B 0 0) = B 0 0 • (1 : Mat 1) := by
    ext i j
    have hi : i = 0 := Subsingleton.elim _ _
    have hj : j = 0 := Subsingleton.elim _ _
    subst i; subst j; simp
  conv_lhs => rw [hB, hS, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hU.1]
  simp

/-- 128: in a specified nonzero canonical-line trivialization, the scalar
Higgs fields are the divided endomorphisms, with their actual roots. -/
theorem higgsTrivializationHull (h : MOCIsTrue) {n : ℕ}
    (Φ Ψ U : Mat n) (ω : ℂ) (_hω : ω ≠ 0) (a b : Fin n → ℂ)
    (hΦ : IsStarNormal (ω⁻¹ • Φ)) (hΨ : IsStarNormal (ω⁻¹ • Ψ)) (hU : IsUnitary U)
    (ha : HasRoots (ω⁻¹ • Φ) a) (hb : HasRoots (ω⁻¹ • Ψ) b) :
    ω⁻¹ ^ n * (Φ + U * Ψ * Uᴴ).det ∈
      convexHull ℝ (Set.range (matchingProduct a b)) := by
  have hh := operatorHull_of_moc h _ _ _ _ _ hΦ hΨ hU ha hb
  unfold OperatorHull at hh
  rw [Matrix.mul_smul, Matrix.smul_mul, ← smul_add, Matrix.det_smul, Fintype.card_fin] at hh
  exact hh

/-- 133: the actual contraction of the skew-Hermitian curvature form,
scaled by the Chern–Weil scalar. This is not a top Chern form. -/
theorem curvatureContractionHull {n : ℕ} (F G U : Mat n)
    (hF : Fᴴ = -F) (hG : Gᴴ = -G) (hU : IsUnitary U) (a b : Fin n → ℝ)
    (ha : HasRoots ((Complex.I / (2 * Real.pi)) • F) (fun j => a j))
    (hb : HasRoots ((Complex.I / (2 * Real.pi)) • G) (fun j => b j)) :
    OperatorHull ((Complex.I / (2 * Real.pi)) • F) ((Complex.I / (2 * Real.pi)) • G)
      U (fun j => a j) (fun j => b j) := by
  have hs (X : Mat n) (hX : Xᴴ = -X) :
      ((Complex.I / (2 * Real.pi)) • X).IsHermitian := by
    change (((Complex.I / (2 * Real.pi)) • X)ᴴ) = _
    rw [Matrix.conjTranspose_smul, hX]
    simp [Complex.star_def, Complex.conj_I, neg_div]
  exact diracBlockHull _ _ _ a b (hs F hF) (hs G hG) hU ha hb

end

end MOC.Reformulations.NativeFirstB
