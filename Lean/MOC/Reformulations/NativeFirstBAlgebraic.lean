import MOC.Reformulations.NativeFirstBGeometry
import Mathlib.LinearAlgebra.SymplecticGroup
import Mathlib.RingTheory.Norm.Defs

/-! Symplectic and algebraic finite operators (112–120, 124, 129–131).
Normality and restrictions on changes of frame are imposed before taking
spectra. The geometric construction of the input, e.g. a periodic orbit
or moment polytope, is not inferred from the determinant conclusion. -/

open BigOperators Matrix

namespace MOC.Reformulations.NativeFirstB

noncomputable section

/-- The standard skew form in the ordered coordinates of a doubled space. -/
def symplecticJ (r : ℕ) : RMat (r + r) :=
  (Matrix.J (Fin r) ℝ).submatrix finSumFinEquiv.symm finSumFinEquiv.symm

def IsSymplectic {r : ℕ} (A : RMat (r + r)) : Prop :=
  Aᵀ * symplecticJ r * A = symplecticJ r

/-- 112, and the supplied normal return/leaf maps of 118 and 120:
the exact finite comparison in compatible real symplectic coordinates. -/
theorem symplecticNormalHull (h : MOCIsTrue) {r : ℕ}
    (A B : RMat (r + r)) (Q : Matrix.orthogonalGroup (Fin (r + r)) ℝ)
    (_hSA : IsSymplectic A) (_hSB : IsSymplectic B) (_hSQ : IsSymplectic Q.val)
    (a b : Fin (r + r) → ℂ)
    (hA : IsStarNormal (complexify A)) (hB : IsStarNormal (complexify B))
    (ha : HasRoots (complexify A) a) (hb : HasRoots (complexify B) b) :
    OperatorHull (complexify A) (complexify B) (complexify Q.val) a b :=
  operatorHull_of_moc h _ _ _ _ _ hA hB (isUnitary_ofReal_orthogonal Q) ha hb

/-- 114 also covers the infinitesimal Hamiltonian case (J H), which is
not itself required to be symplectic as a group element. -/
theorem hamiltonianLinearizationHull (h : MOCIsTrue) {r : ℕ}
    (H K : RMat (r + r)) (Q : Matrix.orthogonalGroup (Fin (r + r)) ℝ)
    (_hH : Hᵀ = H) (_hK : Kᵀ = K) (_hQ : IsSymplectic Q.val)
    (a b : Fin (r + r) → ℂ)
    (hA : IsStarNormal (complexify (symplecticJ r * H)))
    (hB : IsStarNormal (complexify (symplecticJ r * K)))
    (ha : HasRoots (complexify (symplecticJ r * H)) a)
    (hb : HasRoots (complexify (symplecticJ r * K)) b) :
    OperatorHull (complexify (symplecticJ r * H)) (complexify (symplecticJ r * K))
      (complexify Q.val) a b :=
  operatorHull_of_moc h _ _ _ _ _ hA hB (isUnitary_ofReal_orthogonal Q) ha hb

def doubledList {r : ℕ} (a : Fin r → ℝ) : Fin (r + r) → ℝ :=
  fun j => Sum.elim a a (finSumFinEquiv.symm j)

/-- 113: actual Williamson representatives with their repeated positive
symplectic eigenvalues. There is no assertion of invariance under general
symplectic congruence of either input. -/
theorem williamsonRepHull {r : ℕ} (ν η : Fin r → ℝ)
    (_hν : ∀ j, 0 < ν j) (_hη : ∀ j, 0 < η j)
    (Q : Matrix.orthogonalGroup (Fin (r + r)) ℝ) (_hQ : IsSymplectic Q.val) :
    Holds (fun j => doubledList ν j) (fun j => doubledList η j) (complexify Q.val) :=
  holds_of_real_spectra (doubledList ν) (doubledList η) _ (isUnitary_ofReal_orthogonal Q)

/-- 115–116: the moment-vector theorem uses one common real-linear
functional, not unrelated complex values on the labelled fixed points
or vertices. The input lists are the selected actual moment images. -/
theorem momentVectorHull (h : MOCIsTrue) {n : ℕ} {V : Type*}
    [AddCommGroup V] [Module ℝ V] (L : V →ₗ[ℝ] ℂ)
    (μ ν : Fin n → V) (U : Mat n) (hU : IsUnitary U) :
    Holds (fun j => L (μ j)) (fun j => L (ν j)) U :=
  h n _ _ U hU

/-- 117: the one-parameter torus acts by its actual integral powers. -/
def OneParameterWeightForm : Prop :=
  ∀ (n : ℕ) (a b : Fin n → ℤ) (z : ℂˣ) (U : Mat n), IsUnitary U →
    Holds (fun j => ((z ^ a j : ℂˣ) : ℂ)) (fun j => ((z ^ b j : ℂˣ) : ℂ)) U

theorem oneParameterWeightForm_of_moc (h : MOCIsTrue) : OneParameterWeightForm :=
  fun n _ _ _ U hU => h n _ _ U hU

/-- 119 in a supplied finite quantization representation. The operators
are the images of observables, not arbitrary functions of their labels. -/
theorem quantizedObservableHull (h : MOCIsTrue) {R : Type*} [Ring R] [Algebra ℂ R]
    {n : ℕ} (quantize : R →ₐ[ℂ] Mat n) (f g : R) (U : Mat n) (a b : Fin n → ℂ)
    (hA : IsStarNormal (quantize f)) (hB : IsStarNormal (quantize g)) (hU : IsUnitary U)
    (ha : HasRoots (quantize f) a) (hb : HasRoots (quantize g) b) :
    OperatorHull (quantize f) (quantize g) U a b :=
  operatorHull_of_moc h _ _ _ _ _ hA hB hU ha hb

/-- 124: a common triangular basis for the two multiplication maps in a
finite commutative fiber already gives a single matching vertex. The
hypothesis is satisfied by the common local-factor triangular model
with each residue character repeated by local length. The theorem
does not supply that model for a scheme from its prime ideals. -/
theorem triangularMultiplicationNorm {R : Type*} [CommRing R] [Algebra ℂ R]
    {n : ℕ} (e : Basis (Fin n) ℂ R) (x y : R)
    (hx : (Algebra.leftMulMatrix e x).BlockTriangular id)
    (hy : (Algebra.leftMulMatrix e y).BlockTriangular id) :
    Algebra.norm ℂ (x + y) = matchingProduct
      (Algebra.leftMulMatrix e x).diag (Algebra.leftMulMatrix e y).diag
      (Equiv.refl (Fin n)) := by
  rw [Algebra.norm_eq_matrix_det e, map_add, Matrix.det_of_upperTriangular (hx.add hy)]
  rfl

/-- 129: the positive operator on an orthogonal split slope filtration
has its actual exponential slope spectrum. The statement takes a real
log only after checking positivity of the determinant's real value. -/
theorem slopeFiltrationLogHull {n : ℕ} (s t : Fin n → ℝ)
    (U : Mat n) (hU : IsUnitary U) :
    let d := (determinantValue (fun j => (Real.exp (s j) : ℂ))
      (fun j => (Real.exp (t j) : ℂ)) U).re
    0 < d ∧ ∃ lo hi : Equiv.Perm (Fin n),
      (∑ j, Real.log (Real.exp (s (lo j)) + Real.exp (t j))) ≤ Real.log d ∧
      Real.log d ≤ ∑ j, Real.log (Real.exp (s (hi j)) + Real.exp (t j)) :=
  exponentialSpectra_log_bounds s t U hU

/-- 130: the character of an actual integer lattice weight at a torus point. -/
def torusCharacter {r : ℕ} (z : Fin r → ℂˣ) (w : Fin r → ℤ) : ℂ :=
  ∏ i, ((z i ^ w i : ℂˣ) : ℂ)

theorem toricCharacterHull (h : MOCIsTrue) {n r : ℕ}
    (a b : Fin n → Fin r → ℤ) (z : Fin r → ℂˣ) (U : Mat n) (hU : IsUnitary U) :
    Holds (fun j => torusCharacter z (a j)) (fun j => torusCharacter z (b j)) U :=
  h n _ _ U hU

/-- 131: fixed-degree normalized integer valuation vectors evaluated by
one real-linear scalar map, rather than arbitrary evaluations of a
Newton–Okounkov body or its volume. -/
theorem valuationVectorHull (h : MOCIsTrue) {n r : ℕ} (m : ℕ) (_hm : 0 < m)
    (a b : Fin n → Fin r → ℤ) (L : (Fin r → ℝ) →ₗ[ℝ] ℂ) (U : Mat n) (hU : IsUnitary U) :
    Holds (fun j => L (fun i => (a j i : ℝ) / m))
      (fun j => L (fun i => (b j i : ℝ) / m)) U :=
  h n _ _ U hU

end

end MOC.Reformulations.NativeFirstB
