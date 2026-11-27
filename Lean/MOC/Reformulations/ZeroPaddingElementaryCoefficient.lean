import MOC.Reformulations.SecondCoefficient

/-! Zero padding for a fourth-coefficient counterexample with a bound on
partial matchings. Each unmatched original row or column contributes its own
linear factor. -/

open BigOperators Finset Matrix Polynomial

namespace MOC.Reformulations.CStar

noncomputable section

private theorem padded_matching_polynomial {m : ℕ} (a b : Fin m → ℂ) {k : ℕ}
    (σ : Equiv.Perm (Fin m ⊕ Fin k)) :
    ∃ d : Fin m → Option (Fin m),
      (∀ j l i, d j = some i → d l = some i → j = l) ∧
      (∏ j, (1 + C (Sum.elim a (fun _ : Fin k => 0) (σ j) +
          Sum.elim b (fun _ : Fin k => 0) j) * X)) =
        (∏ j, (1 + C ((d j).elim 0 a + b j) * X)) *
          ∏ i ∈ univ.filter (fun i => ∀ j, d j ≠ some i), (1 + C (a i) * X) := by
  classical
  let d (j : Fin m) : Option (Fin m) := Sum.elim some (fun _ => none) (σ (.inl j))
  have hmatch (j i : Fin m) : d j = some i ↔ σ (.inl j) = .inl i := by
    cases h : σ (.inl j) <;> simp [d, h]
  refine ⟨d, ?_, ?_⟩
  · intro j l i hj hl
    exact Sum.inl.inj (σ.injective (((hmatch j i).mp hj).trans ((hmatch l i).mp hl).symm))
  let isPadding : Fin m ⊕ Fin k → Prop := Sum.elim (fun _ => False) (fun _ => True)
  let f (x : Fin m ⊕ Fin k) : ℂ[X] :=
    if isPadding (σ.symm x) then 1 + C (Sum.elim a (fun _ : Fin k => 0) x) * X else 1
  have hunmatched (i : Fin m) : isPadding (σ.symm (.inl i)) ↔ ∀ j, d j ≠ some i := by
    constructor
    · intro hi j hj
      have hσ := (hmatch j i).mp hj
      have hpre : σ.symm (.inl i) = .inl j := by rw [← hσ, Equiv.symm_apply_apply]
      simpa only [hpre, isPadding, Sum.elim_inl] using hi
    · intro hi
      cases hpre : σ.symm (.inl i) with
      | inl j =>
        have hσ : σ (.inl j) = .inl i := by rw [← hpre, Equiv.apply_symm_apply]
        exact (hi j ((hmatch j i).mpr hσ)).elim
      | inr j => simp only [hpre, isPadding, Sum.elim_inr]
  have hright :
      (∏ j : Fin k, (1 + C (Sum.elim a (fun _ : Fin k => 0) (σ (.inr j))) * X)) =
        ∏ i ∈ univ.filter (fun i => ∀ j, d j ≠ some i), (1 + C (a i) * X) := by
    calc
      _ = ∏ x, f (σ x) := by
        rw [Fintype.prod_sum_type]
        simp only [f, Equiv.symm_apply_apply, isPadding, Sum.elim_inl, Sum.elim_inr,
          if_false, if_true, Finset.prod_const_one, one_mul]
      _ = ∏ x, f x := Equiv.prod_comp σ f
      _ = _ := by
        rw [Fintype.prod_sum_type, Finset.prod_filter]
        have hf (j : Fin k) : f (.inr j) = 1 := by
          simp only [f, Sum.elim_inr, map_zero, zero_mul, add_zero, ite_self]
        simp only [hf, Finset.prod_const_one, mul_one]
        apply Finset.prod_congr rfl
        intro i _
        change (if isPadding (σ.symm (.inl i)) then 1 + C (a i) * X else 1) = _
        by_cases hi : ∀ j, d j ≠ some i
        · rw [if_pos hi, if_pos ((hunmatched i).mpr hi)]
        · rw [if_neg hi, if_neg (fun h => hi ((hunmatched i).mp h))]
  rw [Fintype.prod_sum_type]
  simp only [Sum.elim_inr, add_zero, hright]
  congr 1
  apply Finset.prod_congr rfl
  intro j _
  have ha : Sum.elim a (fun _ : Fin k => 0) (σ (.inl j)) = (d j).elim 0 a := by
    cases h : σ (.inl j) <;> simp [d, h]
  rw [ha, Sum.elim_inl]

private theorem padding_charpolyRev_neg_diagonal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ℂ) : (-(diagonal a)).charpolyRev = ∏ j, (1 + C (a j) * X) := by
  unfold Matrix.charpolyRev
  have h : 1 - (X : ℂ[X]) • (-(diagonal a)).map C =
      diagonal (fun j => 1 + C (a j) * X) := by
    ext i j : 1
    by_cases hij : i = j
    · subst j
      simp only [Matrix.sub_apply, Matrix.one_apply_eq, Matrix.diagonal_apply_eq,
        Matrix.map_apply, Matrix.neg_apply, Matrix.smul_apply, smul_eq_mul, map_neg,
        mul_neg, neg_mul, sub_neg_eq_add, mul_comm X]
    · simp only [Matrix.sub_apply, Matrix.one_apply_ne hij, Matrix.diagonal_apply_ne _ hij,
        Matrix.map_apply, Matrix.neg_apply, Matrix.smul_apply, smul_eq_mul, neg_zero,
        map_zero, mul_zero, sub_zero]
  rw [h, Matrix.det_diagonal]

private theorem padding_charpolyRev_submatrix {ι κ : Type*}
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (M : Matrix ι ι ℂ) (e : κ ≃ ι) : (M.submatrix e e).charpolyRev = M.charpolyRev := by
  simp only [← Matrix.reverse_charpoly]
  apply congrArg Polynomial.reverse
  simpa only [Matrix.reindex_apply, Equiv.symm_symm] using Matrix.charpoly_reindex e.symm M

private theorem padding_charpolyRev_neg_block {m : ℕ} (M : Matrix (Fin m) (Fin m) ℂ) (k : ℕ) :
    (-(fromBlocks M 0 0 (0 : Matrix (Fin k) (Fin k) ℂ))).charpolyRev =
      (-M).charpolyRev := by
  simp only [Matrix.charpolyRev, Matrix.fromBlocks_neg, neg_zero, Matrix.fromBlocks_map,
    Matrix.map_zero _ Polynomial.C_0, Matrix.fromBlocks_smul, smul_zero]
  rw [← Matrix.fromBlocks_one (l := Fin m) (m := Fin k)]
  simp only [sub_eq_add_neg, Matrix.fromBlocks_neg, neg_zero, Matrix.fromBlocks_add,
    add_zero, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, mul_one]

/-- A strict fourth-coefficient separation against all partial matchings in
order m persists when both spectra are extended by zeros. -/
theorem fourthElementaryCoefficient_not_mem_after_zero_padding {m : ℕ}
    (a b : Fin m → ℂ) (U : Matrix (Fin m) (Fin m) ℂ) (hU : IsUnitary U)
    (η : ℂ) (bound : ℝ)
    (hactual : bound < (η * elementaryCoefficient (diagonal a + U * diagonal b * Uᴴ) 4).re)
    (hpartial : ∀ d : Fin m → Option (Fin m),
      (∀ j l i, d j = some i → d l = some i → j = l) →
      (η * ((∏ j, (1 + C ((d j).elim 0 a + b j) * X)) *
        ∏ i ∈ univ.filter (fun i => ∀ j, d j ≠ some i), (1 + C (a i) * X)).coeff 4).re ≤ bound)
    {n : ℕ} (hn : m ≤ n) :
    ∃ (a' b' : Fin n → ℂ) (V' : Matrix (Fin n) (Fin n) ℂ), IsUnitary V' ∧
      elementaryCoefficient (diagonal a' + V' * diagonal b' * V'ᴴ) 4 ∉
        convexHull ℝ (Set.range fun σ : Equiv.Perm (Fin n) =>
          elementaryCoefficient (diagonal fun j => a' (σ j) + b' j) 4) := by
  let k := n - m
  let e : Fin n ≃ Fin m ⊕ Fin k :=
    (finCongr (show n = m + k by dsimp only [k]; omega)).trans finSumFinEquiv.symm
  let a₀ : Fin m ⊕ Fin k → ℂ := Sum.elim a (fun _ => 0)
  let b₀ : Fin m ⊕ Fin k → ℂ := Sum.elim b (fun _ => 0)
  let V : Matrix (Fin m ⊕ Fin k) (Fin m ⊕ Fin k) ℂ := fromBlocks U 0 0 (1 : Matrix (Fin k) (Fin k) ℂ)
  let a' := a₀ ∘ e
  let b' := b₀ ∘ e
  let V' := V.submatrix e e
  refine ⟨a', b', V', unitary_reindex e e (unitary_directSum hU isUnitary_one), ?_⟩
  have hsum : diagonal a' + V' * diagonal b' * V'ᴴ =
      (diagonal a₀ + V * diagonal b₀ * Vᴴ).submatrix e e := by
    have hadd : (diagonal a₀ + V * diagonal b₀ * Vᴴ).submatrix e e =
        (diagonal a₀).submatrix e e + (V * diagonal b₀ * Vᴴ).submatrix e e := rfl
    dsimp only [a', b', V']
    rw [hadd, ← Matrix.submatrix_mul_equiv _ _ e e e,
      ← Matrix.submatrix_mul_equiv _ _ e e e, ← Matrix.conjTranspose_submatrix,
      Matrix.submatrix_diagonal_equiv, Matrix.submatrix_diagonal_equiv]
  have hblock : diagonal a₀ + V * diagonal b₀ * Vᴴ =
      fromBlocks (diagonal a + U * diagonal b * Uᴴ) 0 0 (0 : Matrix (Fin k) (Fin k) ℂ) := by
    dsimp only [a₀, b₀, V]
    rw [← Matrix.fromBlocks_diagonal, ← Matrix.fromBlocks_diagonal, Matrix.fromBlocks_conjTranspose]
    simp only [Matrix.diagonal_zero, Matrix.fromBlocks_multiply, Matrix.fromBlocks_add,
      Matrix.conjTranspose_zero, Matrix.conjTranspose_one, Matrix.zero_mul, Matrix.mul_zero,
      add_zero, zero_add]
  have hactual' : elementaryCoefficient (diagonal a' + V' * diagonal b' * V'ᴴ) 4 =
      elementaryCoefficient (diagonal a + U * diagonal b * Uᴴ) 4 := by
    have hneg : -((diagonal a₀ + V * diagonal b₀ * Vᴴ).submatrix e e) =
        (-(diagonal a₀ + V * diagonal b₀ * Vᴴ)).submatrix e e := rfl
    unfold elementaryCoefficient
    rw [hsum, hneg, padding_charpolyRev_submatrix, hblock, padding_charpolyRev_neg_block]
  have hvertices (σ : Equiv.Perm (Fin n)) :
      (η * elementaryCoefficient (diagonal fun j => a' (σ j) + b' j) 4).re ≤ bound := by
    let τ : Equiv.Perm (Fin m ⊕ Fin k) := (e.symm.trans σ).trans e
    have hproduct :
        (∏ j : Fin n, (1 + C (a' (σ j) + b' j) * X)) =
          ∏ j : Fin m ⊕ Fin k, (1 + C (a₀ (τ j) + b₀ j) * X) := by
      symm
      apply Fintype.prod_equiv e.symm
      intro j
      simp only [τ, a', b', Equiv.trans_apply, Function.comp_apply, Equiv.apply_symm_apply]
    obtain ⟨d, hd, heq⟩ := padded_matching_polynomial a b τ
    rw [elementaryCoefficient, padding_charpolyRev_neg_diagonal, hproduct, heq]
    exact hpartial d hd
  let f : ℂ →ₗ[ℝ] ℝ := Complex.reLm.comp (LinearMap.mulLeft ℝ η)
  intro h
  have hf : f (elementaryCoefficient (diagonal a' + V' * diagonal b' * V'ᴴ) 4) ≤ bound := by
    apply convexHull_min ?_ (convex_halfSpace_le f.isLinear _) h
    rintro _ ⟨σ, rfl⟩
    exact hvertices σ
  change (η * elementaryCoefficient (diagonal a' + V' * diagonal b' * V'ᴴ) 4).re ≤ bound at hf
  rw [hactual'] at hf
  exact (not_lt_of_ge hf) hactual

end

end MOC.Reformulations.CStar
