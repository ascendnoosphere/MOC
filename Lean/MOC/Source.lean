import MOC.Geometry
import MOC.Support
import Mathlib.Algebra.CharZero.Infinite

/-! Anchored matching coordinates for the spectral source.
See Howard–Millson–Snowden–Vakil, *The equations for the moduli space of n
points on the line*, Lemma 4.3, for the configuration-space chart. -/

open BigOperators Matrix

namespace MOC

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Normalize the anchor row and column to ones in the matrix of spectral sums.
The first component of the new coordinate pair vanishes at the anchor row,
and the second vanishes at the anchor column. -/
private theorem anchored_entry (a b c d : ℂ) (ha : a + d ≠ 0) (hb : c + b ≠ 0) :
    1 - (a - c) / (a + d) * ((b - d) / (c + b)) =
      ((a + b) * (c + d)) / ((a + d) * (c + b)) := by
  field_simp
  ring

/-- In the anchored chart, each permutation vertex and the corresponding determinant
have the same nonzero spectral factor removed. Only the anchor row and column
of the spectral sum matrix are required to have nonzero entries. -/
theorem holds_iff_anchored (a b : ι → ℂ) (U : Matrix ι ι ℂ) (hU : IsUnitary U)
    (i₀ j₀ : ι) (ha : ∀ i, a i + b j₀ ≠ 0) (hb : ∀ j, a i₀ + b j ≠ 0) :
    let x : ι → ℂ := fun i => (a i - a i₀) / (a i + b j₀)
    let y : ι → ℂ := fun j => (b j - b j₀) / (a i₀ + b j)
    Holds a b U ↔ (U - diagonal x * U * diagonal y).det / U.det ∈
      convexHull ℝ (Set.range (fun σ : Equiv.Perm ι => ∏ j, (1 - x (σ j) * y j))) := by
  intro x y
  let k : ℂ := (a i₀ + b j₀) ^ Fintype.card ι /
    ((∏ i, (a i + b j₀)) * ∏ j, (a i₀ + b j))
  have hk : k ≠ 0 :=
    div_ne_zero (pow_ne_zero _ (ha i₀))
      (mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun i _ => ha i)
        (Finset.prod_ne_zero_iff.mpr fun j _ => hb j))
  have hp (σ : Equiv.Perm ι) :
      (∏ j, (1 - x (σ j) * y j)) = k * matchingProduct a b σ := by
    have he (j : ι) : 1 - x (σ j) * y j =
        ((a (σ j) + b j) * (a i₀ + b j₀)) / ((a (σ j) + b j₀) * (a i₀ + b j)) :=
      anchored_entry _ _ _ _ (ha (σ j)) (hb j)
    simp_rw [he, Finset.prod_div_distrib, Finset.prod_mul_distrib]
    rw [Equiv.prod_comp σ (fun i => a i + b j₀), Finset.prod_const, Finset.card_univ]
    unfold k matchingProduct
    ring
  have hd :
      (U - diagonal x * U * diagonal y).det / U.det =
        ∑ σ, signedWeight U σ * (∏ j, (1 - x (σ j) * y j)) := by
    have he (i j : ι) :
        (U - diagonal x * U * diagonal y) i j = U i j * (1 - x i * y j) := by
      simp only [Matrix.sub_apply, Matrix.mul_diagonal, Matrix.diagonal_mul]
      ring
    rw [Matrix.det_apply', Finset.sum_div]
    apply Finset.sum_congr rfl
    intro σ _
    simp_rw [he, Finset.prod_mul_distrib, signedWeight, leibnizTerm]
    ring
  unfold Holds
  symm
  apply hull_common_factor_iff hk _ hp
  rw [hd, ← signed_determinant a b U hU, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  rw [hp]
  ring

/-- The anchored variables can be arbitrary, including when some entries
of their outer product equal one. A scaling avoids the finitely many poles. -/
theorem anchored_of_conjecture (h : Conjecture ι) (U : Matrix ι ι ℂ) (hU : IsUnitary U)
    (i₀ j₀ : ι) (x y : ι → ℂ) (hx : x i₀ = 0) (hy : y j₀ = 0) :
    (U - diagonal x * U * diagonal y).det / U.det ∈
      convexHull ℝ (Set.range (fun σ : Equiv.Perm ι => ∏ j, (1 - x (σ j) * y j))) := by
  classical
  obtain ⟨t, ht⟩ := (((Set.finite_singleton (0 : ℂ)).union (Set.finite_range x)).union
    (Set.finite_range (fun j => (y j)⁻¹))).exists_not_mem
  have ht₀ : t ≠ 0 := fun h0 => ht (Or.inl (Or.inl h0))
  let X : ι → ℂ := fun i => x i / t
  let Y : ι → ℂ := fun j => t * y j
  have hX (i : ι) : 1 - X i ≠ 0 := by
    intro hi
    have he : x i / t = 1 := (sub_eq_zero.mp hi).symm
    exact ht (Or.inl (Or.inr ⟨i, by simpa using (div_eq_iff ht₀).mp he⟩))
  have hY (j : ι) : 1 - Y j ≠ 0 := by
    intro hj
    have he : t * y j = 1 := (sub_eq_zero.mp hj).symm
    have hy₀ : y j ≠ 0 := by
      intro hj₀
      simp [hj₀] at he
    exact ht (Or.inr ⟨j, by simpa using ((eq_div_iff hy₀).mpr he).symm⟩)
  let a : ι → ℂ := fun i => X i / (1 - X i)
  let b : ι → ℂ := fun j => 1 / (1 - Y j)
  have ha₀ : a i₀ = 0 := by simp [a, X, hx]
  have hb₀ : b j₀ = 1 := by simp [b, Y, hy]
  have hax (i : ι) : a i + b j₀ = 1 / (1 - X i) := by
    rw [hb₀]
    dsimp only [a]
    field_simp [hX i]
  have hby (j : ι) : a i₀ + b j = 1 / (1 - Y j) := by simp [ha₀, b]
  have hr : (fun i => (a i - a i₀) / (a i + b j₀)) = X := by
    funext i
    rw [ha₀, sub_zero, hax, div_div_div_cancel_right₀ (hX i), div_one]
  have hc : (fun j => (b j - b j₀) / (a i₀ + b j)) = Y := by
    funext j
    rw [hb₀, hby]
    dsimp only [b]
    field_simp [hY j]
  have hP (i j : ι) : X i * Y j = x i * y j := by
    dsimp [X, Y]
    field_simp
    ring
  have hM : diagonal X * U * diagonal Y = diagonal x * U * diagonal y := by
    ext i j
    simp only [Matrix.mul_diagonal, Matrix.diagonal_mul]
    rw [mul_right_comm (X i), hP, mul_right_comm (x i)]
  have hheld := (holds_iff_anchored a b U hU i₀ j₀
    (fun i => by rw [hax]; exact one_div_ne_zero (hX i))
    (fun j => by rw [hby]; exact one_div_ne_zero (hY j))).mp (h a b U hU)
  change (U - diagonal (fun i => (a i - a i₀) / (a i + b j₀)) * U *
    diagonal (fun j => (b j - b j₀) / (a i₀ + b j))).det / U.det ∈
    convexHull ℝ (Set.range (fun σ : Equiv.Perm ι =>
      ∏ j, (1 - ((a (σ j) - a i₀) / (a (σ j) + b j₀)) *
        ((b j - b j₀) / (a i₀ + b j))))) at hheld
  rw [hr, hc, hM] at hheld
  have he (i j : ι) :
      (a i - a i₀) / (a i + b j₀) * ((b j - b j₀) / (a i₀ + b j)) = x i * y j := by
    rw [congrFun hr i, congrFun hc j]
    exact hP i j
  simpa only [he] using hheld

/-- The rank-one chart is equivalent to the full conjecture for fixed anchors.
The nonopposite-spectra reduction handles spectra outside the forward chart. -/
theorem conjecture_iff_anchored (i₀ j₀ : ι) :
    Conjecture ι ↔ ∀ (U : Matrix ι ι ℂ), IsUnitary U → ∀ (x y : ι → ℂ),
      x i₀ = 0 → y j₀ = 0 →
        (U - diagonal x * U * diagonal y).det / U.det ∈
          convexHull ℝ (Set.range (fun σ : Equiv.Perm ι => ∏ j, (1 - x (σ j) * y j))) := by
  constructor
  · intro h U hU x y hx hy
    exact anchored_of_conjecture h U hU i₀ j₀ x y hx hy
  · intro h
    apply conjecture_iff_nonopposite.mpr
    intro a b U hU hsum
    exact (holds_iff_anchored a b U hU i₀ j₀ (fun i => hsum i j₀) (hsum i₀)).mpr
      (h U hU (fun i => (a i - a i₀) / (a i + b j₀)) (fun j => (b j - b j₀) / (a i₀ + b j))
        (by simp) (by simp))

<<<<<<< HEAD
/-- Switching the anchor edge with a second edge removes one factor
from the corresponding matching in the normalized chart. -/
theorem anchored_product_swap (x y : ι → ℂ) (σ : Equiv.Perm ι) (j₀ j : ι)
    (hx : x (σ j₀) = 0) (hy : y j₀ = 0) :
    (∏ k, (1 - x (σ k) * y k)) = (1 - x (σ j) * y j) *
      ∏ k, (1 - x (σ (Equiv.swap j₀ j k)) * y k) := by
  let f : ι → ℂ := fun k => 1 - x (σ k) * y k
  let g : ι → ℂ := fun k => 1 - x (σ (Equiv.swap j₀ j k)) * y k
  change (∏ k, f k) = f j * ∏ k, g k
  have hgj : g j = 1 := by simp [g, hx]
  have heq : ∏ k ∈ (Finset.univ : Finset ι).erase j, f k =
      ∏ k ∈ (Finset.univ : Finset ι).erase j, g k := by
    apply Finset.prod_congr rfl
    intro k hk
    by_cases hk₀ : k = j₀
    · subst k
      simp [f, g, hy]
    · have hkj : k ≠ j := (Finset.mem_erase.mp hk).1
      simp [f, g, Equiv.swap_apply_of_ne_of_ne hk₀ hkj]
  calc
    (∏ k, f k) = f j * ∏ k ∈ (Finset.univ : Finset ι).erase j, f k :=
      (Finset.mul_prod_erase Finset.univ f (Finset.mem_univ j)).symm
    _ = f j * ∏ k, g k := by
      rw [heq, ← Finset.mul_prod_erase Finset.univ g (Finset.mem_univ j), hgj, one_mul]

/-- Recover one rank-one entry from the ratios of two matching coordinates. -/
theorem anchored_entry_of_swap (x y : ι → ℂ) (σ : Equiv.Perm ι) (j₀ j : ι)
    (hx : x (σ j₀) = 0) (hy : y j₀ = 0)
    (hnz : (∏ k, (1 - x (σ (Equiv.swap j₀ j k)) * y k)) ≠ 0) :
    x (σ j) * y j = 1 -
      (∏ k, (1 - x (σ k) * y k)) / ∏ k, (1 - x (σ (Equiv.swap j₀ j k)) * y k) := by
  rw [anchored_product_swap x y σ j₀ j hx hy, mul_div_cancel_right₀ _ hnz, sub_sub_cancel]

=======
>>>>>>> origin/main
end

end MOC
