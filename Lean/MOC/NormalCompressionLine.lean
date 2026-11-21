import MOC.PoleCompression
import MOC.SpectralSupportLine

/-! Normality of a codimension-one compression gives equal centered spectral
outer products on the support of the deleted row. -/

open BigOperators Matrix

namespace MOC

noncomputable section

variable {n : ℕ}

private def centeredColumn (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (p : Fin (n + 1)) : Matrix (Fin (n + 1)) Unit ℂ :=
  fun i _ => M i p - if i = p then M p p else 0

private theorem outerColumn_apply {ι : Type*} (X : Matrix ι Unit ℂ) (i j : ι) :
    (X * Xᴴ) i j = X i () * star (X j ()) := by
  simp [Matrix.mul_apply, Matrix.conjTranspose_apply]

private theorem transformed_centeredColumn (β : Fin (n + 1) → ℂ)
    (U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (hU : IsUnitary U) (p j : Fin (n + 1)) :
    let M := U * diagonal β * Uᴴ
    (Uᴴ * centeredColumn M p) j () = (β j - M p p) * star (U p j) := by
  intro M
  have hmul : Uᴴ * M = diagonal β * Uᴴ := by
    change Uᴴ * (U * diagonal β * Uᴴ) = _
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hU.2, Matrix.one_mul]
  have hcenter : (Uᴴ * centeredColumn M p) j () = (Uᴴ * M) j p - Uᴴ j p * M p p := by
    simp only [Matrix.mul_apply, centeredColumn, mul_sub, Finset.sum_sub_distrib, mul_ite,
      mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [hcenter, hmul, Matrix.diagonal_mul, Matrix.conjTranspose_apply, sub_mul,
    mul_comm (star (U p j)) (M p p)]

private theorem adjoint_diagonal_conjugation (β : Fin (n + 1) → ℂ)
    (U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    (U * diagonal β * Uᴴ)ᴴ = U * diagonal (fun k => star (β k)) * Uᴴ := by
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    Matrix.diagonal_conjTranspose, Matrix.mul_assoc, Pi.star_def β]

private theorem transformed_centeredAdjointColumn (β : Fin (n + 1) → ℂ)
    (U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (hU : IsUnitary U) (p j : Fin (n + 1)) :
    let M := U * diagonal β * Uᴴ
    (Uᴴ * centeredColumn Mᴴ p) j () = star (β j - M p p) * star (U p j) := by
  intro M
  calc
    _ = (star (β j) - Mᴴ p p) * star (U p j) := by
      rw [show Mᴴ = _ from adjoint_diagonal_conjugation β U]
      exact transformed_centeredColumn (fun k => star (β k)) U hU p j
    _ = _ := by rw [Matrix.conjTranspose_apply, star_sub]

private theorem diagonal_conjugation_commutes_adjoint (β : Fin (n + 1) → ℂ)
    (U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (hU : IsUnitary U) :
    let M := U * diagonal β * Uᴴ
    M * Mᴴ = Mᴴ * M := by
  have hprod (a b : Fin (n + 1) → ℂ) :
      (U * diagonal a * Uᴴ) * (U * diagonal b * Uᴴ) = U * (diagonal a * diagonal b) * Uᴴ := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Uᴴ U, hU.2, Matrix.one_mul]
  have hcomm : diagonal β * diagonal (fun k => star (β k)) =
      diagonal (fun k => star (β k)) * diagonal β := by
    rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    exact congrArg diagonal (funext fun k => mul_comm (β k) (star (β k)))
  dsimp only
  rw [adjoint_diagonal_conjugation, hprod β (fun k => star (β k)),
    hprod (fun k => star (β k)) β, hcomm]

/-- In spectral coordinates the zero-padded compression self-commutator
has entries given by the deleted row and the centered spectral cross products. -/
theorem principalCompression_selfCommutator_spectral_lift (β : Fin (n + 1) → ℂ)
    (U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (hU : IsUnitary U) (p : Fin (n + 1)) :
    let M := U * diagonal β * Uᴴ
    let C := M.submatrix p.succAbove p.succAbove
    let δ (i : Fin (n + 1)) := β i - M p p
    let E : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ := fun i j =>
      star (U p i) * U p j * (star (δ i) * δ j - δ i * star (δ j))
    let T := U * E * Uᴴ
    T.submatrix p.succAbove p.succAbove = C * Cᴴ - Cᴴ * C ∧
      (∀ i, T p i = 0) ∧ (∀ i, T i p = 0) := by
  intro M C δ E T
  let X := centeredColumn M p
  let Y := centeredColumn Mᴴ p
  have hE : (Uᴴ * Y) * (Uᴴ * Y)ᴴ - (Uᴴ * X) * (Uᴴ * X)ᴴ = E := by
    ext i j : 1
    have hx (k : Fin (n + 1)) : (Uᴴ * X) k () = δ k * star (U p k) :=
      transformed_centeredColumn β U hU p k
    have hy (k : Fin (n + 1)) : (Uᴴ * Y) k () = star (δ k) * star (U p k) :=
      transformed_centeredAdjointColumn β U hU p k
    have hYij : ((Uᴴ * Y) * (Uᴴ * Y)ᴴ) i j =
        (star (δ i) * star (U p i)) * star (star (δ j) * star (U p j)) := by
      rw [outerColumn_apply, hy i, hy j]
    have hXij : ((Uᴴ * X) * (Uᴴ * X)ᴴ) i j =
        (δ i * star (U p i)) * star (δ j * star (U p j)) := by
      rw [outerColumn_apply, hx i, hx j]
    rw [Matrix.sub_apply, hYij, hXij]
    simp only [star_mul', star_star]
    ring
  have hcancel (A : Matrix (Fin (n + 1)) Unit ℂ) :
      U * ((Uᴴ * A) * (Uᴴ * A)ᴴ) * Uᴴ = A * Aᴴ := by
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.mul_assoc, hU.1, Matrix.mul_one]
    rw [← Matrix.mul_assoc U Uᴴ, hU.1, Matrix.one_mul]
  have hT : T = Y * Yᴴ - X * Xᴴ := by
    change U * E * Uᴴ = _
    rw [← hE, Matrix.mul_sub, Matrix.sub_mul, hcancel, hcancel]
  refine ⟨?_, ?_, ?_⟩
  · rw [hT, principalCompression_self_commutator M p (diagonal_conjugation_commutes_adjoint β U hU)]
    ext i j : 1
    simp only [Matrix.submatrix_apply, Matrix.sub_apply, outerColumn_apply, X, Y, centeredColumn,
      Matrix.conjTranspose_apply, Fin.succAbove_ne, if_false, sub_zero, star_star,
      Matrix.add_apply, Matrix.vecMulVec_apply, neg_mul]
    ring
  · intro i
    rw [hT, Matrix.sub_apply, outerColumn_apply, outerColumn_apply]
    simp [X, Y, centeredColumn]
  · intro i
    rw [hT, Matrix.sub_apply, outerColumn_apply, outerColumn_apply]
    simp [X, Y, centeredColumn]

/-- In a normal principal compression, the two centered spectral columns
have equal outer products. -/
theorem normalCompression_centered_spectral_outer_eq (β : Fin (n + 1) → ℂ)
    (U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (hU : IsUnitary U) (p : Fin (n + 1))
    (hC : IsStarNormal ((U * diagonal β * Uᴴ).submatrix p.succAbove p.succAbove)) :
    let μ := (U * diagonal β * Uᴴ) p p
    let x (j : Fin (n + 1)) := (β j - μ) * star (U p j)
    let y (j : Fin (n + 1)) := star (β j - μ) * star (U p j)
    ∀ i j, x i * star (x j) = y i * star (y j) := by
  intro μ x y i j
  let M := U * diagonal β * Uᴴ
  let C := M.submatrix p.succAbove p.succAbove
  let X := centeredColumn M p
  let Y := centeredColumn Mᴴ p
  have hM : M * Mᴴ = Mᴴ * M := diagonal_conjugation_commutes_adjoint β U hU
  have hsmall (a b : Fin n) :
      M (p.succAbove a) p * star (M (p.succAbove b) p) =
        star (M p (p.succAbove a)) * M p (p.succAbove b) := by
    have h := principalCompression_self_commutator M p hM
    change C * Cᴴ - Cᴴ * C = _ at h
    rw [show C * Cᴴ = Cᴴ * C from hC.star_comm_self.eq.symm, sub_self] at h
    have he := congrArg (fun W : Matrix (Fin n) (Fin n) ℂ => W a b) h
    simp only [Matrix.zero_apply, Matrix.add_apply, Matrix.vecMulVec_apply, neg_mul] at he
    linear_combination he
  have houter : X * Xᴴ = Y * Yᴴ := by
    ext a b : 1
    rw [outerColumn_apply, outerColumn_apply]
    by_cases ha : a = p
    · subst a
      simp [X, Y, centeredColumn]
    by_cases hb : b = p
    · subst b
      simp [X, Y, centeredColumn]
    obtain ⟨a, rfl⟩ := Fin.exists_succAbove_eq ha
    obtain ⟨b, rfl⟩ := Fin.exists_succAbove_eq hb
    simpa only [X, Y, centeredColumn, Matrix.conjTranspose_apply, Fin.succAbove_ne,
      if_false, sub_zero, star_star] using hsmall a b
  have htransport : (Uᴴ * X) * (Uᴴ * X)ᴴ = (Uᴴ * Y) * (Uᴴ * Y)ᴴ := by
    simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
      using congrArg (fun W => Uᴴ * W * U) houter
  have hx (k : Fin (n + 1)) : (Uᴴ * X) k () = x k :=
    transformed_centeredColumn β U hU p k
  have hy (k : Fin (n + 1)) : (Uᴴ * Y) k () = y k :=
    transformed_centeredAdjointColumn β U hU p k
  have he := congrArg (fun W : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ => W i j) htransport
  simpa only [outerColumn_apply, hx, hy] using he

/-- The spectrum on the support of a deleted row lies on an affine line
whenever the remaining principal compression is normal. -/
theorem exists_spectral_line_of_normalCompression (β : Fin (n + 1) → ℂ)
    (U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (hU : IsUnitary U) (p : Fin (n + 1))
    (hC : IsStarNormal ((U * diagonal β * Uᴴ).submatrix p.succAbove p.succAbove)) :
    let μ := (U * diagonal β * Uᴴ) p p
    ∃ d : ℂ, d ≠ 0 ∧ ∀ j, U p j ≠ 0 → ∃ t : ℝ, β j = μ + d * (t : ℂ) := by
  intro μ
  have h := normalCompression_centered_spectral_outer_eq β U hU p hC
  obtain ⟨d, hd, hline⟩ := exists_spectral_line_of_centered_outer_eq
    β (fun j => star (U p j)) μ (by simpa only [Complex.star_def] using h)
  exact ⟨d, hd, fun j hj => hline j (star_ne_zero.mpr hj)⟩

/-- Affine-line support of the deleted row is sufficient for normality of
the remaining principal compression, even with repeated spectral values. -/
theorem normalCompression_of_spectral_line_on_support (β : Fin (n + 1) → ℂ)
    (U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (hU : IsUnitary U) (p : Fin (n + 1))
    (c d : ℂ) (knots : Fin (n + 1) → ℝ) (hline : ∀ j, U p j ≠ 0 → β j = c + d * (knots j : ℂ)) :
    IsStarNormal ((U * diagonal β * Uᴴ).submatrix p.succAbove p.succAbove) := by
  let M := U * diagonal β * Uᴴ
  let H := U * diagonal (fun k => (knots k : ℂ)) * Uᴴ
  let C := M.submatrix p.succAbove p.succAbove
  have hH : Hᴴ = H := by
    dsimp only [H]
    rw [adjoint_diagonal_conjugation]
    simp only [Pi.star_def, Complex.star_def, Complex.conj_ofReal]
  have hHerm (i j : Fin (n + 1)) : star (H j i) = H i j :=
    congrArg (fun W : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ => W i j) hH
  have hvalue (γ : Fin (n + 1) → ℂ) (i j : Fin (n + 1)) :
      (U * diagonal γ * Uᴴ) i j = ∑ k, U i k * γ k * star (U j k) := by
    calc
      (U * diagonal γ * Uᴴ) i j
          = ∑ k, (U * diagonal γ) i k * Uᴴ k j := by
            simp [Matrix.mul_apply]
        _ = ∑ k, U i k * γ k * star (U j k) := by
            simp [Matrix.mul_diagonal, Matrix.conjTranspose_apply, mul_assoc]
  have hentry (i j : Fin (n + 1)) (hij : i = p ∨ j = p) :
      M i j = c * (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) i j + d * H i j := by
    have h1 : (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) i j =
        ∑ k, U i k * star (U j k) := by
      have h := congrArg (fun W : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ => W i j) hU.1
      simpa [Matrix.mul_apply, Matrix.one_apply, Matrix.conjTranspose_apply, eq_comm] using h
    dsimp only [M, H]
    rw [hvalue β i j, hvalue (fun k => (knots k : ℂ)) i j, h1, Finset.mul_sum,
      Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases hk : U p k = 0
    · rcases hij with hi | hj
      · subst i; simp [hk]
      · subst j; simp [hk]
    · rw [hline k hk]
      ring
  have hcol (i : Fin n) : M (p.succAbove i) p = d * H (p.succAbove i) p := by
    simpa only [Matrix.one_apply_ne (Fin.succAbove_ne p i), mul_zero, zero_add] using
      hentry (p.succAbove i) p (Or.inr rfl)
  have hrow (i : Fin n) : M p (p.succAbove i) = d * H p (p.succAbove i) := by
    simpa only [Matrix.one_apply_ne (Fin.succAbove_ne p i).symm, mul_zero, zero_add] using
      hentry p (p.succAbove i) (Or.inl rfl)
  constructor
  change Cᴴ * C = C * Cᴴ
  symm
  apply sub_eq_zero.mp
  rw [principalCompression_self_commutator M p (diagonal_conjugation_commutes_adjoint β U hU)]
  ext i j : 1
  simp only [Matrix.zero_apply, Matrix.add_apply, Matrix.vecMulVec_apply, neg_mul, hcol, hrow]
  rw [star_mul', star_mul']
  simp only [hHerm]
  ring

end

end MOC
