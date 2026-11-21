import MOC.Source

/-! Recovery of the normalized rank-one chart from its matching products. -/

open BigOperators

namespace MOC

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A matching coordinate in the anchored rank-one chart, with its common scale. -/
def anchoredMatchingCoordinate (c : ℂ) (x y : ι → ℂ) (σ : Equiv.Perm ι) : ℂ :=
  c * ∏ j, (1 - x (σ j) * y j)

private theorem anchored_edge_eq_one_sub_ratio (c : ℂ) (x y : ι → ℂ)
    (σ : Equiv.Perm ι) (j₀ j : ι) (hx : x (σ j₀) = 0) (hy : y j₀ = 0)
    (hnz : anchoredMatchingCoordinate c x y ((Equiv.swap j₀ j).trans σ) ≠ 0) :
    x (σ j) * y j = 1 - anchoredMatchingCoordinate c x y σ /
      anchoredMatchingCoordinate c x y ((Equiv.swap j₀ j).trans σ) := by
  unfold anchoredMatchingCoordinate at hnz ⊢
  rw [mul_div_mul_left _ _ (left_ne_zero_of_mul hnz)]
  apply anchored_entry_of_swap x y σ j₀ j hx hy
  simpa only [Equiv.trans_apply] using right_ne_zero_of_mul hnz

/-- The anchored matching coordinates determine every entry of the rank-one
outer product whenever all matching coordinates are nonzero. -/
theorem anchored_outerProduct_eq_of_matchingCoordinates_eq (c c' : ℂ) (x y x' y' : ι → ℂ)
    (i₀ j₀ : ι) (hx : x i₀ = 0) (hy : y j₀ = 0) (hx' : x' i₀ = 0) (hy' : y' j₀ = 0)
    (hnz : ∀ σ, anchoredMatchingCoordinate c x y σ ≠ 0)
    (he : ∀ σ, anchoredMatchingCoordinate c x y σ = anchoredMatchingCoordinate c' x' y' σ) :
    ∀ i j, x i * y j = x' i * y' j := by
  intro i j
  by_cases hi : i = i₀
  · subst i
    simp only [hx, hx', zero_mul]
  by_cases hj : j = j₀
  · subst j
    simp only [hy, hy', mul_zero]
  let p := Equiv.swap j₀ i₀
  let σ := p.trans (Equiv.swap (p j) i)
  have hp₀ : p j₀ = i₀ := Equiv.swap_apply_left _ _
  have hσ₀ : σ j₀ = i₀ := by
    change Equiv.swap (p j) i (p j₀) = i₀
    rw [hp₀]
    exact Equiv.swap_apply_of_ne_of_ne (fun h => hj (p.injective (h.symm.trans hp₀.symm))) hi.symm
  have hσj : σ j = i := Equiv.swap_apply_left _ _
  let τ := (Equiv.swap j₀ j).trans σ
  have hnz' : anchoredMatchingCoordinate c' x' y' τ ≠ 0 :=
    fun h => hnz τ ((he τ).trans h)
  have hl := anchored_edge_eq_one_sub_ratio c x y σ j₀ j (by rw [hσ₀, hx]) hy (hnz τ)
  have hr := anchored_edge_eq_one_sub_ratio c' x' y' σ j₀ j (by rw [hσ₀, hx']) hy' hnz'
  calc
    x i * y j = 1 - anchoredMatchingCoordinate c x y σ /
        anchoredMatchingCoordinate c x y τ := by simpa only [hσj] using hl
    _ = 1 - anchoredMatchingCoordinate c' x' y' σ /
        anchoredMatchingCoordinate c' x' y' τ := by rw [he σ, he τ]
    _ = x' i * y' j := by simpa only [hσj] using hr.symm

/-- Fixing one entry of the first factor to one gives unique chart coordinates
and common scale on the open set where the second factor has a nonzero entry. -/
theorem anchored_chart_eq_of_matchingCoordinates_eq (c c' : ℂ) (x y x' y' : ι → ℂ)
    (i₀ j₀ i₁ j₁ : ι) (hx : x i₀ = 0) (hy : y j₀ = 0) (hx' : x' i₀ = 0) (hy' : y' j₀ = 0)
    (hunit : x i₁ = 1) (hunit' : x' i₁ = 1) (hpivot : y j₁ ≠ 0)
    (hnz : ∀ σ, anchoredMatchingCoordinate c x y σ ≠ 0)
    (he : ∀ σ, anchoredMatchingCoordinate c x y σ = anchoredMatchingCoordinate c' x' y' σ) :
    c = c' ∧ x = x' ∧ y = y' := by
  have hprod := anchored_outerProduct_eq_of_matchingCoordinates_eq c c' x y x' y'
    i₀ j₀ hx hy hx' hy' hnz he
  have hyeq : y = y' := by
    funext j
    simpa only [hunit, hunit', one_mul] using hprod i₁ j
  have hxeq : x = x' := by
    funext i
    apply mul_right_cancel₀ hpivot
    simpa only [← hyeq] using hprod i j₁
  let e : Equiv.Perm ι := Equiv.refl ι
  have hval : c * (∏ j, (1 - x (e j) * y j)) ≠ 0 := hnz e
  refine ⟨mul_right_cancel₀ (right_ne_zero_of_mul hval) ?_, hxeq, hyeq⟩
  simpa only [anchoredMatchingCoordinate, ← hxeq, ← hyeq] using he e

/-- Every chart point in positive order is realized by finite spectra, with
the common scale absorbed into the two spectra. -/
theorem exists_spectra_of_anchoredMatchingCoordinate [Nonempty ι] (c : ℂ) (x y : ι → ℂ) :
    ∃ a b : ι → ℂ, ∀ σ, matchingProduct a b σ = anchoredMatchingCoordinate c x y σ := by
  classical
  obtain ⟨t, ht⟩ := (((Set.finite_singleton (0 : ℂ)).union (Set.finite_range x)).union
    (Set.finite_range (fun j => (y j)⁻¹))).exists_not_mem
  have ht₀ : t ≠ 0 := fun h => ht (Or.inl (Or.inl h))
  let X (i : ι) := x i / t
  let Y (j : ι) := t * y j
  have hX (i : ι) : 1 - X i ≠ 0 := by
    intro hi
    have he : x i / t = 1 := (sub_eq_zero.mp hi).symm
    exact ht (Or.inl (Or.inr ⟨i, by simpa using (div_eq_iff ht₀).mp he⟩))
  have hY (j : ι) : 1 - Y j ≠ 0 := by
    intro hj
    have he : t * y j = 1 := (sub_eq_zero.mp hj).symm
    have hy₀ : y j ≠ 0 := by
      intro h
      simp [h] at he
    exact ht (Or.inr ⟨j, by simpa using ((eq_div_iff hy₀).mpr he).symm⟩)
  let a (i : ι) := X i / (1 - X i)
  let b (j : ι) := 1 / (1 - Y j)
  have hXY (i j : ι) : X i * Y j = x i * y j := by
    dsimp only [X, Y]
    field_simp [ht₀] <;> ring
  have hadd (i j : ι) : a i + b j = (1 - x i * y j) / ((1 - X i) * (1 - Y j)) := by
    dsimp only [a, b]
    rw [← hXY i j]
    field_simp [hX i, hY j] <;> ring
  let D : ℂ := (∏ i, (1 - X i)) * ∏ j, (1 - Y j)
  have hD : D ≠ 0 :=
    mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun i _ => hX i)
      (Finset.prod_ne_zero_iff.mpr fun j _ => hY j)
  have hmatch (σ : Equiv.Perm ι) :
      matchingProduct a b σ = (∏ j, (1 - x (σ j) * y j)) / D := by
    unfold matchingProduct D
    simp_rw [hadd]
    rw [Finset.prod_div_distrib, Finset.prod_mul_distrib, Equiv.prod_comp σ (fun i => 1 - X i)]
  let s : ℂ := (c * D) ^ ((Fintype.card ι : ℂ)⁻¹)
  have hs : s ^ Fintype.card ι = c * D := Complex.cpow_nat_inv_pow _ Fintype.card_ne_zero
  refine ⟨fun i => s * a i, fun j => s * b j, ?_⟩
  intro σ
  rw [matchingProduct_scale, hs, hmatch, anchoredMatchingCoordinate]
  field_simp [hD] <;> ring

/-- Nonopposite spectra with distinct pivot and anchor eigenvalues lie in the
normalized open chart. -/
theorem exists_anchored_chart_of_nonopposite_spectra
    (a b : ι → ℂ) (i₀ j₀ i₁ j₁ : ι) (hsum : ∀ i j, a i + b j ≠ 0)
    (ha : a i₁ ≠ a i₀) (hb : b j₁ ≠ b j₀) :
    ∃ (c : ℂ) (x y : ι → ℂ), x i₀ = 0 ∧ y j₀ = 0 ∧ x i₁ = 1 ∧ y j₁ ≠ 0 ∧
      (∀ σ, anchoredMatchingCoordinate c x y σ ≠ 0) ∧
      ∀ σ, matchingProduct a b σ = anchoredMatchingCoordinate c x y σ := by
  let X (i : ι) := (a i - a i₀) / (a i + b j₀)
  let Y (j : ι) := (b j - b j₀) / (a i₀ + b j)
  have hp : X i₁ ≠ 0 := div_ne_zero (sub_ne_zero.mpr ha) (hsum i₁ j₀)
  let x (i : ι) := X i / X i₁
  let y (j : ι) := X i₁ * Y j
  let c : ℂ := ((∏ i, (a i + b j₀)) * ∏ j, (a i₀ + b j)) /
    (a i₀ + b j₀) ^ Fintype.card ι
  have hXY (i j : ι) : x i * y j = X i * Y j := by
    dsimp only [x, y]
    field_simp [hp] <;> ring
  have hentry (i j : ι) :
      a i + b j = ((a i + b j₀) * (a i₀ + b j)) / (a i₀ + b j₀) * (1 - x i * y j) := by
    rw [hXY i j]
    dsimp only [X, Y]
    field_simp [hsum i j₀, hsum i₀ j, hsum i₀ j₀] <;> ring
  have hmatch (σ : Equiv.Perm ι) :
      matchingProduct a b σ = anchoredMatchingCoordinate c x y σ := by
    unfold matchingProduct anchoredMatchingCoordinate
    calc
      (∏ j, (a (σ j) + b j)) =
          ∏ j, (((a (σ j) + b j₀) * (a i₀ + b j)) / (a i₀ + b j₀) * (1 - x (σ j) * y j)) :=
        Finset.prod_congr rfl (fun j _ => hentry (σ j) j)
      _ = _ := by
        rw [Finset.prod_mul_distrib, Finset.prod_div_distrib, Finset.prod_mul_distrib,
          Equiv.prod_comp σ (fun i => a i + b j₀), Finset.prod_const, Finset.card_univ]
  refine ⟨c, x, y, by simp [x, X], by simp [y, Y], div_self hp, ?_, ?_, hmatch⟩
  · exact mul_ne_zero hp (div_ne_zero (sub_ne_zero.mpr hb) (hsum i₀ j₁))
  · intro σ
    rw [← hmatch]
    exact Finset.prod_ne_zero_iff.mpr fun j _ => hsum (σ j) j

end

end MOC
