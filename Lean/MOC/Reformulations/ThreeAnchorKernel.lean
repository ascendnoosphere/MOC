import MOC.Source
import MOC.Reformulations.Anchored

/-! Normalize the rank-one matching kernel by setting two row coordinates
and one column coordinate. The argument is algebraic and uniform in order. -/

open BigOperators Matrix

namespace MOC.Reformulations

theorem conjecture_iff_three_anchor_kernel {n : ℕ} (i₀ i₁ j₀ : Fin n) (hi : i₀ ≠ i₁) :
    Conjecture (Fin n) ↔
      ∀ (U : Matrix (Fin n) (Fin n) ℂ), IsUnitary U → (∀ i j, U i j ≠ 0) →
        ∀ (x y : Fin n → ℂ), x i₀ = 0 → x i₁ = 1 → y j₀ = 0 →
          (U - diagonal x * U * diagonal y).det / U.det ∈
            convexHull ℝ
              (Set.range (fun σ : Equiv.Perm (Fin n) => ∏ j, (1 - x (σ j) * y j))) := by
  constructor
  · intro h U hU _ x y hx _ hy
    exact anchored_of_conjecture h U hU i₀ j₀ x y hx hy
  · intro h
    apply conjecture_iff_regular_spectra_full_support.mpr
    intro a b U hU hsum hmatch hfull
    have hne : a i₁ ≠ a i₀ := by
      intro he
      have ha (i : Fin n) : a (Equiv.swap i₀ i₁ i) = a i := by
        by_cases hi0 : i = i₀
        · subst i
          simpa using he
        by_cases hi1 : i = i₁
        · subst i
          simpa using he.symm
        rw [Equiv.swap_apply_of_ne_of_ne hi0 hi1]
      have hs : Equiv.swap i₀ i₁ = Equiv.refl (Fin n) := hmatch (by
        unfold matchingProduct
        simp only [ha, Equiv.refl_apply])
      apply hi.symm
      simpa using DFunLike.congr_fun hs i₀
    let X : Fin n → ℂ := fun i => (a i - a i₀) / (a i + b j₀)
    let Y : Fin n → ℂ := fun j => (b j - b j₀) / (a i₀ + b j)
    let c : ℂ := X i₁
    have hc : c ≠ 0 := div_ne_zero (sub_ne_zero.mpr hne) (hsum i₁ j₀)
    let x : Fin n → ℂ := fun i => X i / c
    let y : Fin n → ℂ := fun j => c * Y j
    have hxy (i j : Fin n) : x i * y j = X i * Y j := by
      dsimp [x, y]
      rw [← mul_assoc, div_mul_cancel₀ _ hc]
    have hUxy : diagonal x * U * diagonal y = diagonal X * U * diagonal Y := by
      ext i j
      simp only [Matrix.mul_diagonal, Matrix.diagonal_mul]
      rw [mul_right_comm (x i), hxy, mul_right_comm (X i)]
    apply (holds_iff_anchored a b U hU i₀ j₀ (fun i => hsum i j₀) (hsum i₀)).mpr
    change (U - diagonal X * U * diagonal Y).det / U.det ∈
      convexHull ℝ (Set.range (fun σ : Equiv.Perm (Fin n) => ∏ j, (1 - X (σ j) * Y j)))
    have hh := h U hU hfull x y (by simp [x, X]) (div_self hc) (by simp [y, Y])
    simp only [hUxy, hxy] at hh
    exact hh

/-- An equivalent form of unrestricted MOC in `2n-3` free complex spectral
coordinates. It concerns actual relative unitaries, not a permutation table. -/
theorem moc_iff_three_anchor_kernel :
    MOCIsTrue ↔ ∀ (n : ℕ) (hn : 4 ≤ n),
      let i₀ : Fin n := ⟨0, by omega⟩
      let i₁ : Fin n := ⟨1, by omega⟩
      ∀ (U : Matrix (Fin n) (Fin n) ℂ), IsUnitary U → (∀ i j, U i j ≠ 0) →
        ∀ (x y : Fin n → ℂ), x i₀ = 0 → x i₁ = 1 → y i₀ = 0 →
          (U - diagonal x * U * diagonal y).det / U.det ∈
            convexHull ℝ
              (Set.range (fun σ : Equiv.Perm (Fin n) => ∏ j, (1 - x (σ j) * y j))) := by
  rw [mocIsTrue_iff_from_four]
  refine forall_congr' fun n => forall_congr' fun hn => ?_
  apply conjecture_iff_three_anchor_kernel
  exact fun h => Nat.zero_ne_one (congrArg Fin.val h)

end MOC.Reformulations
