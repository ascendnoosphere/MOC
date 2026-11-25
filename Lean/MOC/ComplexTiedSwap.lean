import MOC.TripleOrbit
import MOC.Small
import MOC.StrongSupport

/-!
# Complex tied-swap obstruction, including singular sums

The pair-plane criterion in PairRayleigh (numerical-range background:
Lakos, DOI: 10.1007/s00013-023-01957-9) gives complex cofactor stationarity.
No inverse of the stationary sum or flattened comparison is required.
For determinant covariance under common fractional-linear changes, see
Drury, DOI: 10.13001/1081-3810.1239. The inverse-entry identity is proved directly.
-/

open BigOperators Matrix

namespace MOC

noncomputable section

private theorem adjugate_cross_eq_of_eq_off_pair_entry
    {ι : Type*} [Fintype ι] [DecidableEq ι] (A B : Matrix ι ι ℂ) (i j : ι)
    (he : ∀ x y, x ≠ i ∨ y ≠ i → A x y = B x y) :
    A.adjugate i j = B.adjugate i j ∧ A.adjugate j i = B.adjugate j i := by
  have hr (A B : Matrix ι ι ℂ)
      (h : ∀ x y, x ≠ i ∨ y ≠ i → A x y = B x y) :
      A.adjugate j i = B.adjugate j i := by
    rw [Matrix.adjugate_apply, Matrix.adjugate_apply]
    congr 1
    ext x y
    by_cases hx : x = i
    · simp [Matrix.updateRow_apply, hx]
    · rw [Matrix.updateRow_ne hx, Matrix.updateRow_ne hx]
      exact h x y (Or.inl hx)
  refine ⟨?_, hr A B he⟩
  have ht : ∀ x y, x ≠ i ∨ y ≠ i → Aᵀ x y = Bᵀ x y := fun x y h => he y x h.symm
  simpa only [← Matrix.adjugate_transpose, Matrix.transpose_apply] using hr Aᵀ Bᵀ ht

private theorem pairPlane_cross_adjugate
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (a : Fin 2 ⊕ κ → ℂ) (B : Matrix (Fin 2 ⊕ κ) (Fin 2 ⊕ κ) ℂ) (η : ℂ)
    (hmax : ∀ V : Matrix (Fin 2 ⊕ κ) (Fin 2 ⊕ κ) ℂ, IsUnitary V →
      (η * (V * diagonal a * Vᴴ + B).det).re ≤ (η * (diagonal a + B).det).re) :
    let i : Fin 2 ⊕ κ := .inl 0
    let j : Fin 2 ⊕ κ := .inl 1
    let Z := (η * (a i - a j)) • (diagonal a + B).adjugate
    Z i j + star (Z j i) = 0 := by
  intro i j Z
  let C := diagonal (pairPlaneFlatten a) + B
  let M := diagonal a + B
  have hC : ∀ x y, x ≠ i ∨ y ≠ i → C x y = M x y := by
    intro x y h
    by_cases hxy : x = y
    · subst y
      have hx : x ≠ i := h.elim id id
      cases x with
      | inl r =>
        have hr : r ≠ 0 := fun hr => hx (by simp [i, hr])
        have hr' : r = 1 := Fin.eq_one_of_ne_zero r hr
        simp [C, M, pairPlaneFlatten, hr']
      | inr r => simp [C, M, pairPlaneFlatten]
    · simp [C, M, Matrix.diagonal_apply_ne _ hxy]
  have hsame := adjugate_cross_eq_of_eq_off_pair_entry C M i j hC
  have h := ((unitary_pairPlane_identity_max_iff a B η).mp fun V hV =>
    hmax _ (unitary_directSum hV (by simp [IsUnitary]))).2
  change (η * (a i - a j)) * C.adjugate i j +
    star ((η * (a i - a j)) * C.adjugate j i) = 0 at h
  change (η * (a i - a j)) * M.adjugate i j +
    star ((η * (a i - a j)) * M.adjugate j i) = 0
  simpa only [hsame.1, hsame.2] using h

/-- At any global support maximum of a complex diagonal orbit, the
determinant-weighted cofactor equation holds across each distinct pair.
The stationary sum is allowed to be singular. -/
theorem adjugate_cross_of_complex_diagonal_support_max
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ℂ) (B : Matrix ι ι ℂ) (η : ℂ) {i j : ι} (hij : i ≠ j)
    (hmax : ∀ V : Matrix ι ι ℂ, IsUnitary V →
      (η * (V * diagonal a * Vᴴ + B).det).re ≤ (η * (diagonal a + B).det).re) :
    let Z := (η * (a i - a j)) • (diagonal a + B).adjugate
    Z i j + star (Z j i) = 0 := by
  classical
  let f : Fin 2 → ι := ![i, j]
  have hf : Function.Injective f := by
    intro x y he
    fin_cases x <;> fin_cases y <;> simp_all [f]
  let κ := {x : ι // x ∉ Set.range f}
  let e : Fin 2 ⊕ κ ≃ ι :=
    (Equiv.sumCongr (Equiv.ofInjective f hf) (Equiv.refl κ)).trans
      (Equiv.sumCompl (fun x => x ∈ Set.range f))
  have ei : e (.inl 0) = i := rfl
  have ej : e (.inl 1) = j := rfl
  let a' : Fin 2 ⊕ κ → ℂ := a ∘ e
  let B' : Matrix (Fin 2 ⊕ κ) (Fin 2 ⊕ κ) ℂ := B.submatrix e e
  have hd : diagonal a' = (diagonal a).submatrix e e :=
    (Matrix.submatrix_diagonal_equiv a e).symm
  have h' (V : Matrix (Fin 2 ⊕ κ) (Fin 2 ⊕ κ) ℂ) (hV : IsUnitary V) :
      (η * (V * diagonal a' * Vᴴ + B').det).re ≤ (η * (diagonal a' + B').det).re := by
    let W := V.submatrix e.symm e.symm
    have hw : IsUnitary W := unitary_reindex e.symm e.symm hV
    have hw' : W.submatrix e e = V := by ext x y; simp [W]
    have hu : (W * diagonal a * Wᴴ + B).submatrix e e =
        V * diagonal a' * Vᴴ + B' := by
      rw [Matrix.submatrix_add, Pi.add_apply, Pi.add_apply]
      rw [← Matrix.submatrix_mul_equiv _ _ e e e, ← Matrix.submatrix_mul_equiv _ _ e e e,
        ← Matrix.conjTranspose_submatrix, hw', ← hd]
    have hb : (diagonal a + B).submatrix e e = diagonal a' + B' := by
      rw [Matrix.submatrix_add, Pi.add_apply, Pi.add_apply, ← hd]
    rw [← hu, ← hb, Matrix.det_submatrix_equiv_self, Matrix.det_submatrix_equiv_self]
    exact hmax W hw
  have h := pairPlane_cross_adjugate a' B' η h'
  have hm : diagonal a' + B' = (diagonal a + B).submatrix e e := by
    rw [Matrix.submatrix_add, hd]
    rfl
  intro Z
  change (η * (a' (.inl 0) - a' (.inl 1))) * (diagonal a' + B').adjugate (.inl 0) (.inl 1)
      + star ((η * (a' (.inl 0) - a' (.inl 1))) *
        (diagonal a' + B').adjugate (.inl 1) (.inl 0)) = 0 at h
  simpa only [hm, Matrix.adjugate_submatrix_equiv_self, Matrix.submatrix_apply,
    a', Function.comp_apply, ei, ej, Z, Matrix.smul_apply, smul_eq_mul] using h

private theorem triple_swap_support_max (a : Fin 3 → ℂ)
    (B : Matrix (Fin 3) (Fin 3) ℂ) (η : ℂ) (σ : Equiv.Perm (Fin 3))
    (hmax : ∀ V : Matrix (Fin 3) (Fin 3) ℂ, IsUnitary V →
      (η * (V * diagonal a * Vᴴ + B).det).re ≤ (η * (diagonal a + B).det).re)
    (htie : (η * (diagonal (a ∘ σ) + B).det).re = (η * (diagonal a + B).det).re) :
    ∀ V : Matrix (Fin 3) (Fin 3) ℂ, IsUnitary V →
      (η * (V * diagonal (a ∘ σ) * Vᴴ + B).det).re ≤
        (η * (diagonal (a ∘ σ) + B).det).re := by
  intro V hV
  let P := σ.permMatrix ℂ
  have hP : IsUnitary P := isUnitary_permMatrix σ
  have hV' : IsUnitary Vᴴ := ⟨by simpa using hV.2, by simpa using hV.1⟩
  have hU : IsUnitary (V * P) := by
    simpa only [Matrix.conjTranspose_conjTranspose] using relative_unitary Vᴴ P hV' hP
  have hD : P * diagonal a * Pᴴ = diagonal (a ∘ σ) := by
    rw [permMatrix_conjugates, Matrix.submatrix_diagonal_equiv]
  rw [htie, ← hD]
  simpa only [Matrix.conjTranspose_mul, Matrix.mul_assoc] using hmax _ hU

private theorem triple_cofactor_pencil_vector
    (a₀ a₁ : Fin 3 → ℂ) (B : Matrix (Fin 3) (Fin 3) ℂ) (η : ℂ) (d b : ℂ)
    (h₀ : let Z := (η * d) • (diagonal a₀ + B).adjugate
      Z 0 2 + star (Z 2 0) = 0)
    (h₁ : let Z := (η * d) • (diagonal a₁ + B).adjugate
      Z 1 2 + star (Z 2 1) = 0)
    (ha : a₀ 1 = b) (hb : a₁ 0 = b) :
    let T := (B.submatrix Fin.castSucc Fin.castSucc).adjugate
    let Y := T + b • (1 : Matrix (Fin 2) (Fin 2) ℂ)
    let u : Fin 2 → ℂ := fun p => η * B p.castSucc 2
    let v : Fin 2 → ℂ := fun p => star (η * B 2 p.castSucc)
    (d • Y) *ᵥ u + (star d • Yᴴ) *ᵥ v = 0 := by
  intro T Y u v
  simp [Matrix.adjugate_fin_three, Matrix.add_apply, Matrix.diagonal_apply, Matrix.smul_apply,
    smul_eq_mul, Complex.star_def, ha, hb] at h₀ h₁
  funext p
  fin_cases p <;> simp [T, Y, u, v, Matrix.adjugate_fin_two, Matrix.submatrix_apply,
    Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct,
    Matrix.conjTranspose_apply, Fin.sum_univ_two, Matrix.one_apply, Complex.star_def]
  · linear_combination -h₀
  · linear_combination -h₁

/-- The skew-Hermitian matrix obtained by evaluating the generalized
circle through the negatives of the three spectral slots on the
internal pair cofactor. -/
def pairCircleObstruction (T : Matrix (Fin 2) (Fin 2) ℂ) (a b s : ℂ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  let X := T + a • (1 : Matrix (Fin 2) (Fin 2) ℂ)
  let Y := T + b • (1 : Matrix (Fin 2) (Fin 2) ℂ)
  let c := star (a - s) * (b - s)
  c • (Yᴴ * X) - star c • (Xᴴ * Y)

/-- At a complex three-slot maximum, a tied swap of the first two
distinct slots forces either reduction of their plane or singularity of
their explicit circle obstruction. Both stationary sums may be singular.
There is no normality assumption on the three-slot partner. -/
theorem triple_complex_flat_swap_circle_obstruction
    (a : Fin 3 → ℂ) (B : Matrix (Fin 3) (Fin 3) ℂ) (η : ℂ) (hη : η ≠ 0)
    (h01 : a 0 ≠ a 1) (h02 : a 0 ≠ a 2) (h12 : a 1 ≠ a 2)
    (hmax : ∀ V : Matrix (Fin 3) (Fin 3) ℂ, IsUnitary V →
      (η * (V * diagonal a * Vᴴ + B).det).re ≤ (η * (diagonal a + B).det).re)
    (htie : (η * (diagonal (a ∘ Equiv.swap 0 1) + B).det).re =
      (η * (diagonal a + B).det).re) :
    let T := (B.submatrix Fin.castSucc Fin.castSucc).adjugate
    (pairCircleObstruction T (a 0) (a 1) (a 2)).det = 0 ∨
      ∀ p : Fin 2, B p.castSucc 2 = 0 ∧ B 2 p.castSucc = 0 := by
  intro T
  let σ := Equiv.swap (0 : Fin 3) 1
  let a' := a ∘ σ
  have hσ0 : a' 0 = a 1 := by simp [a', σ]
  have hσ1 : a' 1 = a 0 := by simp [a', σ]
  have hσ2 : a' 2 = a 2 := by
    have h := Equiv.swap_apply_of_ne_of_ne (by decide : (2 : Fin 3) ≠ 0)
      (by decide : (2 : Fin 3) ≠ 1)
    exact congrArg a h
  have hmax' := triple_swap_support_max a B η σ hmax htie
  have hs0 := adjugate_cross_of_complex_diagonal_support_max a B η
    (i := 0) (j := 2) (by decide) hmax
  have hs1 := adjugate_cross_of_complex_diagonal_support_max a B η
    (i := 1) (j := 2) (by decide) hmax
  have ht0 := adjugate_cross_of_complex_diagonal_support_max a' B η
    (i := 0) (j := 2) (by decide) hmax'
  have ht1 := adjugate_cross_of_complex_diagonal_support_max a' B η
    (i := 1) (j := 2) (by decide) hmax'
  dsimp only at ht0 ht1
  rw [hσ0, hσ2] at ht0
  rw [hσ1, hσ2] at ht1
  have hu := triple_cofactor_pencil_vector a a' B η (a 0 - a 2) (a 1) hs0 ht1 rfl hσ0
  have hv := triple_cofactor_pencil_vector a' a B η (a 1 - a 2) (a 0) ht0 hs1 hσ1 rfl
  rcases eq_or_ne (pairCircleObstruction T (a 0) (a 1) (a 2)).det 0 with hz | hz
  · exact Or.inl hz
  · apply Or.inr
    obtain ⟨hU, hV⟩ := flat_pair_cross_zero_of_circle_test T h01
      (sub_ne_zero.mpr h02) (sub_ne_zero.mpr h12) _ _ hu hv (isUnit_iff_ne_zero.mpr hz)
    intro p
    have hp := congrFun hU p
    have hq := congrFun hV p
    change η * B p.castSucc 2 = 0 at hp
    change star (η * B 2 p.castSucc) = 0 at hq
    rw [star_eq_zero] at hq
    exact ⟨(mul_eq_zero.mp hp).resolve_left hη, (mul_eq_zero.mp hq).resolve_left hη⟩

/-- For noncollinear slots, the circle test is exactly a shifted Gram
matrix minus a scalar square radius. Thus its singularity tests for a
singular value of the shifted internal cofactor, not an eigenvalue
of that cofactor (unless it is normal). -/
theorem pairCircleObstruction_centered_gram
    (T : Matrix (Fin 2) (Fin 2) ℂ) (a b s : ℂ)
    (hc : star (a - s) * (b - s) - star (star (a - s) * (b - s)) ≠ 0) :
    let c := star (a - s) * (b - s)
    let g := c - star c
    let w := -(star c * (b - a)) / g
    let K := T + (a + w) • (1 : Matrix (Fin 2) (Fin 2) ℂ)
    pairCircleObstruction T a b s =
      g • (Kᴴ * K - (Complex.normSq w : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) := by
  intro c g w K
  let X := T + a • (1 : Matrix (Fin 2) (Fin 2) ℂ)
  let Y := T + b • (1 : Matrix (Fin 2) (Fin 2) ℂ)
  let d := b-a
  have hy : Y = X + d • 1 := by
    simp only [X, Y, d, sub_smul]
    abel
  have hk : K = X + w • 1 := by
    simp only [K, X, add_smul, add_assoc]
  have hg : star g = -g := by simp [g]
  have hw : g * w = -(star c * d) := by
    change g * (-(star c * d) / g) = _
    rw [mul_div_left_comm, div_self (show g ≠ 0 from hc), mul_one]
  have hsw : g * star w = c * star d := by
    have h := congrArg (star : ℂ → ℂ) hw
    simp only [StarMul.star_mul, star_neg, star_star, hg, mul_neg, neg_inj] at h
    simpa only [mul_comm] using h
  have hnr : star w * w = (Complex.normSq w : ℂ) := by
    exact (Complex.normSq_eq_conj_mul_self (z := w)).symm
  change c • (Yᴴ * X) - star c • (Xᴴ * Y) =
    g • (Kᴴ * K - (Complex.normSq w : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ))
  rw [hy, hk, ← hnr]
  simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, Matrix.conjTranspose_one,
    Matrix.mul_add, Matrix.add_mul, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
    Matrix.mul_one, smul_add, smul_sub, smul_smul]
  rw [hsw, hw, mul_comm w (star w)]
  simp only [g, sub_smul, neg_smul]
  abel

/-- For collinear slots the circle test instead reduces to the
linear skew part in the direction joining the first two slots. -/
theorem pairCircleObstruction_collinear
    (T : Matrix (Fin 2) (Fin 2) ℂ) (a b s : ℂ)
    (hc : star (a - s) * (b - s) = star (star (a - s) * (b - s))) :
    let c := star (a - s) * (b - s)
    let X := T + a • (1 : Matrix (Fin 2) (Fin 2) ℂ)
    pairCircleObstruction T a b s =
      c • (star (b - a) • X - (b - a) • Xᴴ) := by
  intro c X
  let Y := T + b • (1 : Matrix (Fin 2) (Fin 2) ℂ)
  have he : star c = c := hc.symm
  have hy : Y = X + (b-a) • 1 := by
    simp only [X, Y, sub_smul]
    abel
  change c • (Yᴴ * X) - star c • (Xᴴ * Y) = _
  rw [hy, he, ← smul_sub]
  congr 1
  simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, Matrix.conjTranspose_one,
    Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]
  abel

/-- The tied-swap obstruction applies to an active triple in every order
when the inactive principal block is invertible. The two full sums need
not be invertible. The reduction conclusion concerns the active Schur
complement; reconstructing an ambient block requires more information. -/
theorem blocked_triple_complex_flat_swap_circle_obstruction
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (a : Fin 3 → ℂ) (A : Matrix (Fin 3) (Fin 3) ℂ)
    (B : Matrix (Fin 3) κ ℂ) (C : Matrix κ (Fin 3) ℂ)
    (D : Matrix κ κ ℂ) [Invertible D]
    (η : ℂ) (hη : η ≠ 0)
    (h01 : a 0 ≠ a 1) (h02 : a 0 ≠ a 2) (h12 : a 1 ≠ a 2)
    (hmax : ∀ V : Matrix (Fin 3) (Fin 3) ℂ, IsUnitary V →
      (η * (fromBlocks (V * diagonal a * Vᴴ + A) B C D).det).re ≤
        (η * (fromBlocks (diagonal a + A) B C D).det).re)
    (htie : (η * (fromBlocks (diagonal (a ∘ Equiv.swap 0 1) + A) B C D).det).re =
      (η * (fromBlocks (diagonal a + A) B C D).det).re) :
    let S := A - B * ⅟ D * C
    let T := (S.submatrix Fin.castSucc Fin.castSucc).adjugate
    (pairCircleObstruction T (a 0) (a 1) (a 2)).det = 0 ∨
      ∀ p : Fin 2, S p.castSucc 2 = 0 ∧ S 2 p.castSucc = 0 := by
  intro S T
  have hdet (H : Matrix (Fin 3) (Fin 3) ℂ) :
      (fromBlocks (H + A) B C D).det = D.det * (H + S).det := by
    rw [Matrix.det_fromBlocks₂₂, add_sub_assoc]
  have hD : D.det ≠ 0 := isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det D).mp
    (isUnit_of_invertible D))
  have hmax' (V : Matrix (Fin 3) (Fin 3) ℂ) (hV : IsUnitary V) :
      (η * D.det * (V * diagonal a * Vᴴ + S).det).re ≤
        (η * D.det * (diagonal a + S).det).re := by
    simpa only [hdet, mul_assoc] using hmax V hV
  have htie' : (η * D.det * (diagonal (a ∘ Equiv.swap 0 1) + S).det).re =
      (η * D.det * (diagonal a + S).det).re := by
    simpa only [hdet, mul_assoc] using htie
  exact triple_complex_flat_swap_circle_obstruction a S (η * D.det) (mul_ne_zero hη hD)
    h01 h02 h12 hmax' htie'

/-- The fractional-linear inverse preserves every off-diagonal zero in
the first eigenbasis. This lets different regular fractional-linear
charts be used for different spectator triples. For determinant transport
in MOC, see Drury, DOI: 10.13001/1081-3810.1239. -/
theorem inverse_fractional_diagonal_offdiag_zero_iff
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C : Matrix ι ι ℂ) (d : ι → ℂ) (t : ℂ) (hd : ∀ i, d i ≠ 0)
    (hC : IsUnit C.det) (hX : IsUnit (diagonal d + t • C).det)
    {i j : ι} (hij : i ≠ j) :
    let Y := diagonal d
    let X := Y + t • C
    ((Y⁻¹ * C * X⁻¹)⁻¹) i j = 0 ↔ C⁻¹ i j = 0 := by
  intro Y X
  have hY : IsUnit Y.det := by
    change IsUnit (diagonal d).det
    rw [Matrix.det_diagonal, isUnit_iff_ne_zero]
    exact Finset.prod_ne_zero_iff.mpr (fun k _ => hd k)
  have h₁ : (Y⁻¹ * C * X⁻¹)⁻¹ = X * C⁻¹ * Y := by
    rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv X hX,
      Matrix.nonsing_inv_nonsing_inv Y hY, Matrix.mul_assoc]
  have h₂ : X * C⁻¹ * Y = Y * C⁻¹ * Y + t • Y := by
    change (Y + t • C) * C⁻¹ * Y = _
    rw [Matrix.add_mul, Matrix.smul_mul, Matrix.mul_nonsing_inv _ hC, Matrix.add_mul,
      Matrix.smul_mul, Matrix.one_mul]
  rw [h₁, h₂]
  change (diagonal d * C⁻¹ * diagonal d + t • diagonal d) i j = 0 ↔ _
  simp only [Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.smul_apply,
    smul_eq_mul, Matrix.diagonal_apply_ne _ hij, mul_zero, add_zero]
  simp only [mul_eq_zero, hd, false_or, or_false]

end

end MOC
