import MOC.BilinearPencil
import MOC.Hermitian
import MOC.MatchingQuartet

/-! A regular collinear matching hull has real additive spectral coordinates. -/

open BigOperators Matrix

namespace MOC

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem matchingProduct_swap_ratio (a b : ι → ℂ) (σ : Equiv.Perm ι) (i j : ι)
    (hij : i ≠ j) (hnz : ∀ r s, a r + b s ≠ 0) :
    matchingProduct a b σ / matchingProduct a b (σ * Equiv.swap i j) =
      ((a (σ i) + b i) * (a (σ j) + b j)) / ((a (σ j) + b i) * (a (σ i) + b j)) := by
  let S : Finset ι := {i, j}
  let R := ∏ k ∈ Sᶜ, (a (σ k) + b k)
  have hR : R ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => hnz (σ k) k
  have hfactor (τ : Equiv.Perm ι) (hτ : ∀ k ∈ Sᶜ, τ k = σ k) :
      matchingProduct a b τ = R * ((a (τ i) + b i) * (a (τ j) + b j)) := by
    let f (k : ι) := a (τ k) + b k
    have hfixed : (∏ k ∈ Sᶜ, f k) = R := Finset.prod_congr rfl fun k hk => by
      simp only [f, hτ k hk]
    change (∏ k, f k) = R * (f i * f j)
    rw [← Finset.prod_compl_mul_prod S f, hfixed]
    change R * (∏ k ∈ ({i, j} : Finset ι), f k) = _
    rw [Finset.prod_pair hij]
  rw [hfactor σ (fun _ _ => rfl), hfactor (σ * Equiv.swap i j) (fun k hk => by
    have h : k ≠ i ∧ k ≠ j := by simpa [S, not_or] using Finset.mem_compl.mp hk
    simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne h.1 h.2])]
  simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_left, Equiv.swap_apply_right]
  exact mul_div_mul_left _ _ hR

private theorem real_normalized_sum_kernel (a b : ι → ℂ) (p : ι) {η : ℂ}
    (hη : η ≠ 0) (hnz : ∀ i j, a i + b j ≠ 0)
    (hline : ∀ σ, (η * matchingProduct a b σ).re = 0) (i j : ι) :
    (((a i + b j) * (a p + b p)) / ((a i + b p) * (a p + b j))).im = 0 := by
  by_cases hi : i = p
  · subst i
    rw [mul_comm (a p + b j), div_self (mul_ne_zero (hnz p p) (hnz p j)), Complex.one_im]
  by_cases hj : j = p
  · subst j
    rw [div_self (mul_ne_zero (hnz i p) (hnz p p)), Complex.one_im]
  let σ := Equiv.swap i j
  have hσ : σ p = p := Equiv.swap_apply_of_ne_of_ne (Ne.symm hi) (Ne.symm hj)
  have hσ' : σ j = i := Equiv.swap_apply_right i j
  have hratio := matchingProduct_swap_ratio a b σ p j (Ne.symm hj) hnz
  rw [hσ, hσ', mul_comm (a p + b p)] at hratio
  rw [← hratio, ← mul_div_mul_left _ _ hη]
  simp only [Complex.div_im, hline, mul_zero, zero_mul, zero_div, sub_self]

private theorem normalized_sum_kernel_real_factors (a b : ι → ℂ) (p q : ι)
    (hpq : p ≠ q) (ha : Function.Injective a) (hb : Function.Injective b)
    (hnz : ∀ i j, a i + b j ≠ 0)
    (hr : ∀ i j, (((a i + b j) * (a p + b p)) / ((a i + b p) * (a p + b j))).im = 0) :
    ∃ x y : ι → ℝ, ∀ i j,
      (a i + b j) * (a p + b p) =
        (a i + b p) * (a p + b j) * (1 - (x i : ℂ) * (y j : ℂ)) := by
  let u (i : ι) := (a i - a p) / (a i + b p)
  let v (j : ι) := (b j - b p) / (a p + b j)
  have huv (i j : ι) :
      (a i + b p) * (a p + b j) * (1 - u i * v j) = (a i + b j) * (a p + b p) := by
    dsimp only [u, v]
    field_simp [hnz i p, hnz p j] <;> ring
  have hre (i j : ι) : (u i * v j).im = 0 := by
    have he := hr i j
    rw [← huv, mul_div_cancel_left₀ _ (mul_ne_zero (hnz i p) (hnz p j)),
      Complex.sub_im, Complex.one_im, zero_sub, neg_eq_zero] at he
    exact he
  have hv : v q ≠ 0 := div_ne_zero (sub_ne_zero.mpr (hb.ne (Ne.symm hpq))) (hnz p q)
  have hu : u q ≠ 0 := div_ne_zero (sub_ne_zero.mpr (ha.ne (Ne.symm hpq))) (hnz q p)
  let z (i : ι) := u i * v q
  let w (j : ι) := v j / v q
  have hz (i : ι) : (z i).im = 0 := hre i q
  have hzw (i j : ι) : z i * w j = u i * v j := by
    dsimp only [z, w]
    field_simp [hv] <;> ring
  have hw (j : ι) : (w j).im = 0 := by
    have he := hre q j
    rw [← hzw, Complex.mul_im, hz, zero_mul, add_zero] at he
    exact (mul_eq_zero.mp he).resolve_left (fun h => (mul_ne_zero hu hv) (Complex.ext h (hz q)))
  refine ⟨fun i => (z i).re, fun j => (w j).re, fun i j => ?_⟩
  have hz' : (((z i).re : ℝ) : ℂ) = z i := Complex.ext rfl (by simp [hz])
  have hw' : (((w j).re : ℝ) : ℂ) = w j := Complex.ext rfl (by simp [hw])
  rw [hz', hw', hzw, huv]

private theorem exists_regular_real_additive_factors (a b : ι → ℂ) (p : ι)
    (hnz : ∀ i j, a i + b j ≠ 0) (x y : ι → ℝ)
    (hxy : ∀ i j, (a i + b j) * (a p + b p) =
      (a i + b p) * (a p + b j) * (1 - (x i : ℂ) * (y j : ℂ))) :
    ∃ (l r : ι → ℂ) (e f : ι → ℝ), ∀ i j, a i + b j = l i * r j * ((e i : ℂ) + (f j : ℂ)) := by
  classical
  letI : Infinite ℝ := Infinite.of_injective (fun n : ℕ => (n : ℝ)) Nat.cast_injective
  obtain ⟨t, ht⟩ := Infinite.exists_not_mem_finset
    (Finset.univ.image x ∪ Finset.univ.image fun j => (y j)⁻¹)
  have hl (i : ι) : x i - t ≠ 0 := fun h =>
    ht (Finset.mem_union.mpr (Or.inl (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, sub_eq_zero.mp h⟩)))
  have hs (j : ι) : 1 - t * y j ≠ 0 := by
    intro h
    have hy : y j ≠ 0 := fun hy => by simp [hy] at h
    have he : t = (y j)⁻¹ := by
      rw [inv_eq_one_div]
      exact (eq_div_iff hy).mpr (sub_eq_zero.mp h).symm
    exact ht (Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr ⟨j, Finset.mem_univ j, he.symm⟩)))
  let l (i : ι) : ℂ := (a i + b p) * ((x i - t : ℝ) : ℂ)
  let r (j : ι) : ℂ := ((a p + b j) / (a p + b p)) * ((1 - t * y j : ℝ) : ℂ)
  let e (i : ι) := (x i - t)⁻¹
  let f (j : ι) := -y j / (1 - t * y j)
  refine ⟨l, r, e, f, fun i j => ?_⟩
  have he : (x i - t) * (1 - t * y j) * (e i + f j) = 1 - x i * y j := by
    dsimp only [e, f]
    field_simp [hl i, hs j] <;> ring
  have he' := congrArg Complex.ofReal he
  push_cast at he'
  apply mul_right_cancel₀ (hnz p p)
  rw [hxy]
  calc
    _ = (a i + b p) * (a p + b j) *
        (((x i - t : ℝ) : ℂ) * ((1 - t * y j : ℝ) : ℂ) * ((e i : ℂ) + (f j : ℂ))) := by
      push_cast
      rw [he']
    _ = (l i * r j * ((e i : ℂ) + (f j : ℂ))) * (a p + b p) := by
      dsimp only [l, r]
      field_simp [hnz p p] <;> ring

/-- For simple spectra with no opposite pair, collinearity of the matching
products guarantees inclusion for every unitary eigenbasis. -/
theorem holds_of_collinear_matching_products {n : ℕ} (a b : Fin n → ℂ)
    (ha : Function.Injective a) (hb : Function.Injective b) (hnz : ∀ i j, a i + b j ≠ 0)
    (η : ℂ) (hη : η ≠ 0) (H : ℝ) (hline : ∀ σ, (η * matchingProduct a b σ).re = H)
    (U : Matrix (Fin n) (Fin n) ℂ) (hU : IsUnitary U) : Holds a b U := by
  by_cases hn : n ≤ 3
  · exact conjecture_le_three hn a b U hU
  let p : Fin n := ⟨0, by omega⟩
  let q : Fin n := ⟨1, by omega⟩
  let s : Fin n := ⟨2, by omega⟩
  let t : Fin n := ⟨3, by omega⟩
  have hH : H = 0 := matchingProduct_disjoint_swaps_common_height_eq_zero a b 1 p q s t
    (by simp [p, q]) (by simp [p, s]) (by simp [p, t]) (by simp [q, s]) (by simp [q, t])
    (by simp [s, t]) ha hb hnz hη (hline _) (hline _) (hline _) (hline _)
  have hline' σ : (η * matchingProduct a b σ).re = 0 := (hline σ).trans hH
  obtain ⟨x, y, hxy⟩ := normalized_sum_kernel_real_factors a b p q (by simp [p, q]) ha hb hnz
    (real_normalized_sum_kernel a b p hη hnz hline')
  obtain ⟨l, r, e, f, h⟩ := exists_regular_real_additive_factors a b p hnz x y hxy
  let k := (∏ i, l i) * ∏ j, r j
  have hs : bilinearPencil a b U 0 1 1 0 = diagonal a + U * diagonal b * Uᴴ := by
    simp [bilinearPencil]
  have hd := bilinearPencil_factorization a b U hU 0 1 1 0 l r
    (fun i => (e i : ℂ)) (fun j => (f j : ℂ)) (fun i j => by simpa [bilinearKernel] using h i j)
  rw [hs] at hd
  have hdet : determinantValue a b U = k * determinantValue (fun i => (e i : ℂ)) (fun j => (f j : ℂ)) U := by
    unfold determinantValue
    rw [hd, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal,
      det_unitary_conjugation _ _ hU, Matrix.det_diagonal]
    dsimp only [k]
    ring
  have hp : ∀ σ, matchingProduct a b σ = k * matchingProduct (fun i => (e i : ℂ)) (fun j => (f j : ℂ)) σ := by
    intro σ
    simp only [matchingProduct, h, k, Finset.prod_mul_distrib, Equiv.prod_comp σ l]
  exact hull_of_common_factor hdet hp (holds_of_real_spectra e f U hU)

end MOC
