import MOC.FourCoincidence
import MOC.Geometry

/-! A bilinear kernel in the two spectra transports to an ordinary sum by
independent fractional-linear changes and a common determinant factor. -/

open BigOperators Matrix Finset

namespace MOC

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def bilinearKernel (α β γ δ x y : ℂ) : ℂ := α * x * y + β * x + γ * y + δ

theorem bilinear_kernel_rectangle (α β γ δ x₁ x₂ y₁ y₂ : ℂ) :
    bilinearKernel α β γ δ x₁ y₁ * bilinearKernel α β γ δ x₂ y₂ -
      bilinearKernel α β γ δ x₁ y₂ * bilinearKernel α β γ δ x₂ y₁ =
      (α * δ - β * γ) * (x₁ - x₂) * (y₁ - y₂) := by
  unfold bilinearKernel
  ring

/-- The two matchings that agree on the anchor row and column differ by a
fixed product of spectral differences times the squared coefficient determinant. -/
theorem bilinear_anchor_swap_gap (α β γ δ x₀ x₁ x₂ x₃ y₀ y₁ y₂ y₃ : ℂ)
    (hzero : bilinearKernel α β γ δ x₀ y₀ = 0) :
    bilinearKernel α β γ δ x₁ y₀ * bilinearKernel α β γ δ x₀ y₁ *
      (bilinearKernel α β γ δ x₂ y₂ * bilinearKernel α β γ δ x₃ y₃ -
        bilinearKernel α β γ δ x₂ y₃ * bilinearKernel α β γ δ x₃ y₂) =
      -(α * δ - β * γ) ^ 2 * (x₁ - x₀) * (y₁ - y₀) * (x₂ - x₃) * (y₂ - y₃) := by
  have h := bilinear_kernel_rectangle α β γ δ x₀ x₁ y₀ y₁
  rw [hzero, zero_mul, zero_sub] at h
  rw [bilinear_kernel_rectangle]
  linear_combination -((α * δ - β * γ) * (x₂ - x₃) * (y₂ - y₃)) * h

def bilinearPencil (a b : ι → ℂ) (U : Matrix ι ι ℂ) (α β γ δ : ℂ) : Matrix ι ι ℂ :=
  let A := diagonal a
  let B := U * diagonal b * Uᴴ
  α • (A * B) + β • A + γ • B + δ • 1

def bilinearMatchingProduct (a b : ι → ℂ) (α β γ δ : ℂ) (σ : Equiv.Perm ι) : ℂ :=
  ∏ j, bilinearKernel α β γ δ (a (σ j)) (b j)

theorem bilinearPencil_mul_unitary (a b : ι → ℂ) (U : Matrix ι ι ℂ) (hU : IsUnitary U)
    (α β γ δ : ℂ) : bilinearPencil a b U α β γ δ * U =
      Matrix.of (fun i j => bilinearKernel α β γ δ (a i) (b j) * U i j) := by
  let A := diagonal a
  let B := U * diagonal b * Uᴴ
  have hBU : B * U = U * diagonal b := by
    simp only [B, Matrix.mul_assoc, hU.2, Matrix.mul_one]
  change (α • (A * B) + β • A + γ • B + δ • (1 : Matrix ι ι ℂ)) * U = _
  simp only [Matrix.add_mul, Matrix.smul_mul, Matrix.mul_assoc A B U, hBU, Matrix.one_mul]
  ext i j
  simp only [A, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.add_apply, Matrix.smul_apply,
    smul_eq_mul, Matrix.of_apply, bilinearKernel]
  ring

/-- The same signed permutation law represents every bilinear kernel. -/
theorem bilinear_signed_determinant (a b : ι → ℂ) (U : Matrix ι ι ℂ) (hU : IsUnitary U)
    (α β γ δ : ℂ) :
    (∑ σ, signedWeight U σ * bilinearMatchingProduct a b α β γ δ σ) =
      (bilinearPencil a b U α β γ δ).det := by
  have hd : (bilinearPencil a b U α β γ δ).det * U.det =
      ∑ σ, leibnizTerm U σ * bilinearMatchingProduct a b α β γ δ σ := by
    rw [← Matrix.det_mul, bilinearPencil_mul_unitary a b U hU, Matrix.det_apply']
    apply Finset.sum_congr rfl
    intro σ _
    simp only [leibnizTerm, bilinearMatchingProduct, Matrix.of_apply, Finset.prod_mul_distrib]
    ring
  rw [(eq_div_iff (det_ne_zero_of_unitary hU)).mpr hd, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro σ _
  unfold signedWeight
  ring

/-- An entrywise factorization gives the corresponding left and right matrix
factors before taking the determinant. -/
theorem bilinearPencil_factorization (a b : ι → ℂ) (U : Matrix ι ι ℂ) (hU : IsUnitary U)
    (α β γ δ : ℂ) (l r a' b' : ι → ℂ)
    (h : ∀ i j, bilinearKernel α β γ δ (a i) (b j) = l i * r j * (a' i + b' j)) :
    bilinearPencil a b U α β γ δ =
      diagonal l * (diagonal a' + U * diagonal b' * Uᴴ) * (U * diagonal r * Uᴴ) := by
  let P := bilinearPencil a b U α β γ δ
  let S := diagonal a' + U * diagonal b' * Uᴴ
  let T := U * diagonal r * Uᴴ
  have hT : T * U = U * diagonal r := by
    simp only [T, Matrix.mul_assoc, hU.2, Matrix.mul_one]
  have hS : S * U = Matrix.of (fun i j => (a' i + b' j) * U i j) := by
    simpa only [bilinearPencil, zero_smul, one_smul, zero_add, add_zero, bilinearKernel,
      zero_mul, one_mul] using bilinearPencil_mul_unitary a' b' U hU 0 1 1 0
  have hprod : (diagonal l * S * T) * U = diagonal l * (S * U) * diagonal r := by
    rw [Matrix.mul_assoc (diagonal l * S) T U, hT]
    simp only [Matrix.mul_assoc]
  have heq : P * U = (diagonal l * S * T) * U := by
    change bilinearPencil a b U α β γ δ * U = _
    rw [bilinearPencil_mul_unitary a b U hU, hprod, hS]
    ext i j
    simp only [Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.of_apply, h]
    ring
  change P = diagonal l * S * T
  calc
    _ = (P * U) * Uᴴ := by rw [Matrix.mul_assoc, hU.1, Matrix.mul_one]
    _ = ((diagonal l * S * T) * U) * Uᴴ := by rw [heq]
    _ = _ := by rw [Matrix.mul_assoc, hU.1, Matrix.mul_one]

private theorem bilinear_determinant_and_products_of_factorization
    (a b : ι → ℂ) (U : Matrix ι ι ℂ) (hU : IsUnitary U) (α β γ δ : ℂ)
    (l r a' b' : ι → ℂ)
    (h : ∀ i j, bilinearKernel α β γ δ (a i) (b j) = l i * r j * (a' i + b' j)) :
    let k := (∏ i, l i) * ∏ j, r j
    (bilinearPencil a b U α β γ δ).det = k * determinantValue a' b' U ∧
      ∀ σ, bilinearMatchingProduct a b α β γ δ σ = k * matchingProduct a' b' σ := by
  dsimp only
  constructor
  · rw [bilinearPencil_factorization a b U hU α β γ δ l r a' b' h,
      Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, det_unitary_conjugation _ _ hU,
      Matrix.det_diagonal, determinantValue]
    ring
  · intro σ
    simp only [bilinearMatchingProduct, matchingProduct, h, Finset.prod_mul_distrib,
      Equiv.prod_comp σ l]

private theorem exists_bilinear_regular_factorization (a b : ι → ℂ)
    (α β γ δ : ℂ) (hH : α * δ - β * γ ≠ 0) :
    ∃ l r a' b' : ι → ℂ, (∀ i, l i ≠ 0) ∧ (∀ j, r j ≠ 0) ∧
      ∀ i j, bilinearKernel α β γ δ (a i) (b j) = l i * r j * (a' i + b' j) := by
  classical
  letI : Infinite ℂ := Infinite.of_injective (fun n : ℕ => (n : ℂ)) Nat.cast_injective
  let m (j : ι) := α * b j + β
  let n (j : ι) := γ * b j + δ
  obtain ⟨p, hp⟩ := Infinite.exists_not_mem_finset
    (Finset.univ.image a ∪ Finset.univ.image fun j => -n j / m j)
  let l (i : ι) := a i - p
  let r (j : ι) := p * m j + n j
  have hl (i : ι) : l i ≠ 0 := sub_ne_zero.mpr (fun hi =>
    hp (Finset.mem_union.mpr (Or.inl (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, hi⟩))))
  have hr (j : ι) : r j ≠ 0 := by
    intro hz
    by_cases hm : m j = 0
    · have hn : n j = 0 := by simpa only [r, hm, mul_zero, zero_add] using hz
      apply hH
      dsimp only [m, n] at hm hn
      linear_combination α * hn - γ * hm
    · have hroot : p = -n j / m j := (eq_div_iff hm).mpr (by
        dsimp only [r] at hz
        linear_combination hz)
      exact hp (Finset.mem_union.mpr (Or.inr
        (Finset.mem_image.mpr ⟨j, Finset.mem_univ j, hroot.symm⟩)))
  let a' (i : ι) := (l i)⁻¹
  let b' (j : ι) := m j / r j
  have h (i j : ι) : bilinearKernel α β γ δ (a i) (b j) = l i * r j * (a' i + b' j) := by
    dsimp only [a', b']
    field_simp [hl i, hr j]
    simp only [bilinearKernel, l, r, m, n]
    ring
  exact ⟨l, r, a', b', hl, hr, h⟩

/-- A nonsingular coefficient matrix admits fractional-linear coordinates
with no poles on either finite spectrum. -/
theorem bilinear_pencil_regular_spectra (a b : ι → ℂ) (U : Matrix ι ι ℂ) (hU : IsUnitary U)
    (α β γ δ : ℂ) (hH : α * δ - β * γ ≠ 0) :
    ∃ (a' b' : ι → ℂ) (k : ℂ), k ≠ 0 ∧
      (bilinearPencil a b U α β γ δ).det = k * determinantValue a' b' U ∧
      ∀ σ, bilinearMatchingProduct a b α β γ δ σ = k * matchingProduct a' b' σ := by
  obtain ⟨l, r, a', b', hl, hr, h⟩ := exists_bilinear_regular_factorization a b α β γ δ hH
  have hk : (∏ i, l i) * (∏ j, r j) ≠ 0 :=
    mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun i _ => hl i) (Finset.prod_ne_zero_iff.mpr fun j _ => hr j)
  exact ⟨a', b', _, hk, bilinear_determinant_and_products_of_factorization a b U hU α β γ δ l r a' b' h⟩

private theorem bilinear_determinant_eq_matching_of_det_zero (a b : ι → ℂ) (U : Matrix ι ι ℂ)
    (hU : IsUnitary U) (α β γ δ : ℂ) (hH : α * δ - β * γ = 0) (σ : Equiv.Perm ι) :
    (bilinearPencil a b U α β γ δ).det = bilinearMatchingProduct a b α β γ δ σ := by
  have hcross := sub_eq_zero.mp hH
  have hfac : ∃ l r : ι → ℂ, ∀ i j, bilinearKernel α β γ δ (a i) (b j) = l i * r j := by
    by_cases hα : α = 0
    · have hβγ : β * γ = 0 := by simpa only [hα, zero_mul] using hcross.symm
      rcases mul_eq_zero.mp hβγ with hβ | hγ
      · exact ⟨fun _ => 1, fun j => γ * b j + δ, fun i j => by
          simp [bilinearKernel, hα, hβ]⟩
      · exact ⟨fun i => β * a i + δ, fun _ => 1, fun i j => by
          simp [bilinearKernel, hα, hγ]⟩
    · refine ⟨fun i => α * a i + γ, fun j => b j + β / α, fun i j => ?_⟩
      unfold bilinearKernel
      field_simp [hα]
      linear_combination hcross
  obtain ⟨l, r, h⟩ := hfac
  let a' (_ : ι) : ℂ := 1
  let b' (_ : ι) : ℂ := 0
  obtain ⟨hd, hp⟩ := bilinear_determinant_and_products_of_factorization a b U hU α β γ δ l r a' b'
    (fun i j => by simpa [a', b'] using h i j)
  rw [hd, hp σ]
  simp [determinantValue, matchingProduct, a', b']

private theorem bilinear_holds_of_det_zero (a b : ι → ℂ) (U : Matrix ι ι ℂ) (hU : IsUnitary U)
    (α β γ δ : ℂ) (hH : α * δ - β * γ = 0) :
    (bilinearPencil a b U α β γ δ).det ∈
      convexHull ℝ (Set.range (bilinearMatchingProduct a b α β γ δ)) :=
  subset_convexHull ℝ _ ⟨1, (bilinear_determinant_eq_matching_of_det_zero a b U hU α β γ δ hH 1).symm⟩

/-- The unrestricted conjecture is equivalent to the determinant inclusion
for every bilinear kernel in the two spectra. -/
theorem conjecture_iff_bilinear_pencil : Conjecture ι ↔
    ∀ (a b : ι → ℂ) (U : Matrix ι ι ℂ), IsUnitary U → ∀ α β γ δ : ℂ,
      (bilinearPencil a b U α β γ δ).det ∈
        convexHull ℝ (Set.range (bilinearMatchingProduct a b α β γ δ)) := by
  constructor
  · intro h a b U hU α β γ δ
    by_cases hH : α * δ - β * γ = 0
    · exact bilinear_holds_of_det_zero a b U hU α β γ δ hH
    · obtain ⟨a', b', _, _, hd, hp⟩ := bilinear_pencil_regular_spectra a b U hU α β γ δ hH
      exact hull_of_common_factor hd hp (h a' b' U hU)
  · intro h a b U hU
    have hp : bilinearMatchingProduct a b 0 1 1 0 = matchingProduct a b := by
      funext σ
      simp [bilinearMatchingProduct, matchingProduct, bilinearKernel]
    simpa [Holds, determinantValue, bilinearPencil, hp] using h a b U hU 0 1 1 0

/-- At order four the same weights work on the whole bilinear zero-edge
hyperplane and remain independent of the two spectra. -/
theorem exists_four_bilinear_anchor_weights (U : Matrix (Fin 4) (Fin 4) ℂ) (hU : IsUnitary U) :
    ∃ w : Equiv.Perm (Fin 4) → ℝ, (∀ σ, 0 ≤ w σ) ∧ (∑ σ, w σ) = 1 ∧
      ∀ (a b : Fin 4 → ℂ) (α β γ δ : ℂ), bilinearKernel α β γ δ (a 0) (b 0) = 0 →
        (∑ σ, (w σ : ℂ) * bilinearMatchingProduct a b α β γ δ σ) =
          (bilinearPencil a b U α β γ δ).det := by
  obtain ⟨w, hw, hs, _, hbase⟩ := exists_four_opposite_pair_weights U hU
  refine ⟨w, hw, hs, fun a b α β γ δ hz => ?_⟩
  by_cases hH : α * δ - β * γ = 0
  · simp only [← bilinear_determinant_eq_matching_of_det_zero a b U hU α β γ δ hH,
      ← Finset.sum_mul, ← Complex.ofReal_sum, hs, Complex.ofReal_one, one_mul]
  · obtain ⟨l, r, a', b', hl, hr, he⟩ := exists_bilinear_regular_factorization a b α β γ δ hH
    have hzero : a' 0 + b' 0 = 0 := by
      rw [he 0 0] at hz
      exact (mul_eq_zero.mp hz).resolve_left (mul_ne_zero (hl _) (hr _))
    obtain ⟨hd, hp⟩ := bilinear_determinant_and_products_of_factorization a b U hU α β γ δ l r a' b' he
    rw [hd, ← hbase a' b' hzero, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro σ _
    rw [hp σ]
    ring

/-- A single zero edge proves the order-four bilinear inclusion, with no
regularity requirement on the other edges. -/
theorem holds_four_bilinear_of_zero_edge (a b : Fin 4 → ℂ) (U : Matrix (Fin 4) (Fin 4) ℂ)
    (hU : IsUnitary U) (α β γ δ : ℂ) {i j : Fin 4}
    (hzero : bilinearKernel α β γ δ (a i) (b j) = 0) :
    (bilinearPencil a b U α β γ δ).det ∈
      convexHull ℝ (Set.range (bilinearMatchingProduct a b α β γ δ)) := by
  by_cases hH : α * δ - β * γ = 0
  · exact bilinear_holds_of_det_zero a b U hU α β γ δ hH
  · obtain ⟨a', b', k, hk, hd, hp⟩ := bilinear_pencil_regular_spectra a b U hU α β γ δ hH
    let σ := Equiv.swap j i
    have hz : bilinearMatchingProduct a b α β γ δ σ = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ j) (by simpa [σ] using hzero)
    have hprod : matchingProduct a' b' σ = 0 := by
      rw [hp σ] at hz
      exact (mul_eq_zero.mp hz).resolve_left hk
    exact hull_of_common_factor hd hp (holds_four_of_zero_matchingProduct a' b' U hU hprod)

end

end MOC
