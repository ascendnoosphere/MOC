import MOC.Reformulations.Commutant
import Mathlib.Algebra.Star.StarAlgHom

/-!
C★ 8, finite representation interface: two function algebras have genuine
unital star algebra representations in one matrix algebra. The comparison
representations have the same labelled multiplicities and commuting ranges.

We supply the spectral realizations, and use real convex hulls of their actual
determinants. We do not construct or assume the universal completion of an
algebraic free product. In particular, the theorem is for representations of
the two factors, with explicit finite spectral data.
-/

open Matrix

namespace MOC.Reformulations.CStar

noncomputable section

private def pullbackFunctions {X Y : Type} (x : Y → X) : (X → ℂ) →ₐ[ℂ] (Y → ℂ) where
  toFun f := f ∘ x
  map_one' := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  commutes' _ := rfl

/-- Evaluation at the specified labels, followed by diagonal inclusion. -/
def diagonalFunctionRep {X : Type} {n : ℕ} (x : Fin n → X) :
    (X → ℂ) →⋆ₐ[ℂ] Matrix (Fin n) (Fin n) ℂ where
  toAlgHom := (Matrix.diagonalAlgHom (n := Fin n) ℂ).comp (pullbackFunctions x)
  map_star' f := by
    change diagonal (fun i => star (f (x i))) = (diagonal (f ∘ x))ᴴ
    rw [Matrix.diagonal_conjTranspose]
    rfl

private def conjugationRep {n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ) (hU : IsUnitary U) :
    Matrix (Fin n) (Fin n) ℂ →⋆ₐ[ℂ] Matrix (Fin n) (Fin n) ℂ where
  toFun M := U * M * Uᴴ
  map_one' := by rw [Matrix.mul_one, hU.1]
  map_zero' := by simp
  map_add' M N := by rw [Matrix.mul_add, Matrix.add_mul]
  map_mul' M N := by
    calc
      _ = U * M * (Uᴴ * U) * N * Uᴴ := by simp only [hU.2, Matrix.mul_one, Matrix.mul_assoc]
      _ = _ := by simp only [Matrix.mul_assoc]
  commutes' r := by
    simp only [Algebra.algebraMap_eq_smul_one, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_one, hU.1]
  map_star' M := by
    simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]

/-- The representation has the multiplicities encoded by the list (x), as
witnessed by a single unitary spectral basis for all functions. -/
def HasLabelledSpectrum {X : Type} {n : ℕ}
    (ρ : (X → ℂ) →⋆ₐ[ℂ] Matrix (Fin n) (Fin n) ℂ) (x : Fin n → X) : Prop :=
  ∃ V : Matrix (Fin n) (Fin n) ℂ, IsUnitary V ∧
    ∀ f, ρ f = V * diagonal (f ∘ x) * Vᴴ

private theorem diagonalFunctionRep_hasSpectrum {X : Type} {n : ℕ}
    (x : Fin n → X) (σ : Equiv.Perm (Fin n)) :
    HasLabelledSpectrum (diagonalFunctionRep (x ∘ σ)) x := by
  refine ⟨Equiv.Perm.permMatrix ℂ σ, isUnitary_permMatrix σ, fun f => ?_⟩
  change diagonal (f ∘ x ∘ σ) = _
  rw [permMatrix_conjugates, Matrix.submatrix_diagonal_equiv]
  rfl

/-- Scalar comparison values of the pairs of factor representations whose
ranges commute. Thus both factor representations, and not only the two
specific evaluated elements, commute. -/
def commutingPairDeterminants {X Y : Type} {n : ℕ}
    (x : Fin n → X) (y : Fin n → Y) (f : X → ℂ) (g : Y → ℂ) : Set ℂ :=
  {z | ∃ (ρ : (X → ℂ) →⋆ₐ[ℂ] Matrix (Fin n) (Fin n) ℂ)
      (η : (Y → ℂ) →⋆ₐ[ℂ] Matrix (Fin n) (Fin n) ℂ),
      HasLabelledSpectrum ρ x ∧ HasLabelledSpectrum η y ∧
      (∀ p q, Commute (ρ p) (η q)) ∧ z = (ρ f + η g).det}

/-- Finite C★ two-factor determinant comparison for star representations.
The finite index lists supply the multiplicities, including repetitions. -/
def PairedStarRepresentationForm : Prop :=
  ∀ (X Y : Type) [Fintype X] [Fintype Y] (n : ℕ)
    (x : Fin n → X) (y : Fin n → Y) (f : X → ℂ) (g : Y → ℂ)
    (ρ : (X → ℂ) →⋆ₐ[ℂ] Matrix (Fin n) (Fin n) ℂ)
    (η : (Y → ℂ) →⋆ₐ[ℂ] Matrix (Fin n) (Fin n) ℂ),
    HasLabelledSpectrum ρ x → HasLabelledSpectrum η y →
    (ρ f + η g).det ∈ convexHull ℝ (commutingPairDeterminants x y f g)

private theorem matchingProduct_subset_commutingPair {X Y : Type} {n : ℕ}
    (x : Fin n → X) (y : Fin n → Y) (f : X → ℂ) (g : Y → ℂ) :
    Set.range (matchingProduct (f ∘ x) (g ∘ y)) ⊆ commutingPairDeterminants x y f g := by
  rintro _ ⟨σ, rfl⟩
  refine ⟨diagonalFunctionRep (x ∘ σ), diagonalFunctionRep y,
    diagonalFunctionRep_hasSpectrum x σ, ?_, ?_, ?_⟩
  · exact ⟨1, isUnitary_one, fun q => by simp [diagonalFunctionRep, pullbackFunctions]⟩
  · intro p q
    change Commute (diagonal (p ∘ x ∘ σ)) (diagonal (q ∘ y))
    unfold Commute SemiconjBy
    rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    exact congrArg Matrix.diagonal (funext fun j => mul_comm (p (x (σ j))) (q (y j)))
  · change matchingProduct (f ∘ x) (g ∘ y) σ =
      (diagonal (f ∘ x ∘ σ) + diagonal (g ∘ y)).det
    rw [Matrix.diagonal_add, Matrix.det_diagonal]
    rfl

private theorem commutingPair_subset_commutant {n : ℕ} (a b : Fin n → ℂ) :
    commutingPairDeterminants id id a b ⊆ commutantDeterminants a b := by
  rintro _ ⟨ρ, η, hρ, hη, hComm, rfl⟩
  obtain ⟨V, hV, hv⟩ := hρ
  obtain ⟨W, hW, hw⟩ := hη
  have hAdjV : IsUnitary Vᴴ := ⟨by simpa using hV.2, by simpa using hV.1⟩
  refine ⟨Vᴴ * W, relative_unitary V W hV hW, ?_, ?_⟩
  · have hc := (hComm a b).map (conjugationRep Vᴴ hAdjV).toAlgHom
    change Commute (Vᴴ * ρ a * (Vᴴ)ᴴ) (Vᴴ * η b * (Vᴴ)ᴴ) at hc
    rw [hv a, hw b, Matrix.conjTranspose_conjTranspose] at hc
    change Commute (Vᴴ * (V * diagonal a * Vᴴ) * V)
      (Vᴴ * (W * diagonal b * Wᴴ) * V) at hc
    have ha : Vᴴ * (V * diagonal a * Vᴴ) * V = diagonal a := by
      calc
        _ = (Vᴴ * V) * diagonal a * (Vᴴ * V) := by simp only [Matrix.mul_assoc]
        _ = _ := by simp [hV.2]
    rw [ha] at hc
    simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
      using hc
  · rw [hv a, hw b]
    exact determinantValue_relative a b V W hV

theorem pairedStarRepresentationForm_iff : PairedStarRepresentationForm ↔ MOCIsTrue := by
  constructor
  · intro h
    apply commutantForm_iff.mp
    intro n a b U hU
    let ρ := diagonalFunctionRep (id : Fin n → Fin n)
    let η := (conjugationRep U hU).comp ρ
    have ha : HasLabelledSpectrum ρ id :=
      ⟨1, isUnitary_one, fun _ => by simp [ρ, diagonalFunctionRep, pullbackFunctions]⟩
    have hb : HasLabelledSpectrum η id := ⟨U, hU, fun _ => rfl⟩
    have he := h (Fin n) (Fin n) n id id a b ρ η ha hb
    exact convexHull_mono (commutingPair_subset_commutant a b) he
  · intro h X Y _ _ n x y f g ρ η hρ hη
    obtain ⟨V, hV, hv⟩ := hρ
    obtain ⟨W, hW, hw⟩ := hη
    rw [hv f, hw g, determinantValue_relative _ _ V W hV]
    exact convexHull_mono (matchingProduct_subset_commutingPair x y f g)
      (h n (f ∘ x) (g ∘ y) (Vᴴ * W) (relative_unitary V W hV hW))

end

end MOC.Reformulations.CStar
