import MOC.Core

/-! Two disjoint swaps constrain translations in the contact reduction. -/

open BigOperators

namespace MOC

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem matchingProduct_disjoint_swap_factors
    (a b : ι → ℂ) (σ : Equiv.Perm ι) (i j k l : ι)
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    let R := ∏ m ∈ ({i, j, k, l} : Finset ι)ᶜ, (a (σ m) + b m)
    let x₀ := (a (σ i) + b i) * (a (σ j) + b j)
    let x₁ := (a (σ j) + b i) * (a (σ i) + b j)
    let y₀ := (a (σ k) + b k) * (a (σ l) + b l)
    let y₁ := (a (σ l) + b k) * (a (σ k) + b l)
    matchingProduct a b σ = R * x₀ * y₀ ∧
      matchingProduct a b (σ * Equiv.swap i j) = R * x₁ * y₀ ∧
      matchingProduct a b (σ * Equiv.swap k l) = R * x₀ * y₁ ∧
      matchingProduct a b (σ * Equiv.swap i j * Equiv.swap k l) = R * x₁ * y₁ := by
  dsimp only
  let S : Finset ι := {i, j, k, l}
  let R := ∏ m ∈ Sᶜ, (a (σ m) + b m)
  have hprod (f : ι → ℂ) :
      (∏ m ∈ S, f m) = (f i * f j) * (f k * f l) := by
    change (∏ m ∈ ({i, j, k, l} : Finset ι), f m) = _
    rw [Finset.prod_insert (show i ∉ ({j, k, l} : Finset ι) by simp [hij, hik, hil]),
      Finset.prod_insert (show j ∉ ({k, l} : Finset ι) by simp [hjk, hjl]),
      Finset.prod_insert (show k ∉ ({l} : Finset ι) by simp [hkl]),
      Finset.prod_singleton, mul_assoc]
  have hfactor (τ : Equiv.Perm ι) (hτ : ∀ m ∈ Sᶜ, τ m = σ m) :
      matchingProduct a b τ = R * ((a (τ i) + b i) * (a (τ j) + b j)) *
        ((a (τ k) + b k) * (a (τ l) + b l)) := by
    let f (m : ι) := a (τ m) + b m
    have hfixed : (∏ m ∈ Sᶜ, f m) = R := by
      apply Finset.prod_congr rfl
      intro m hm
      change a (τ m) + b m = a (σ m) + b m
      rw [hτ m hm]
    change (∏ m, f m) = R * (f i * f j) * (f k * f l)
    rw [← Finset.prod_compl_mul_prod S f, hfixed, hprod, ← mul_assoc]
  have houtside (m : ι) (hm : m ∈ Sᶜ) : m ≠ i ∧ m ≠ j ∧ m ≠ k ∧ m ≠ l := by
    simpa [S, not_or] using (Finset.mem_compl.mp hm)
  have hs (m : ι) (hm : m ∈ Sᶜ) : Equiv.swap i j m = m :=
    Equiv.swap_apply_of_ne_of_ne (houtside m hm).1 (houtside m hm).2.1
  have ht (m : ι) (hm : m ∈ Sᶜ) : Equiv.swap k l m = m :=
    Equiv.swap_apply_of_ne_of_ne (houtside m hm).2.2.1 (houtside m hm).2.2.2
  refine ⟨hfactor σ (fun _ _ => rfl), ?_, ?_, ?_⟩
  · have h := hfactor (σ * Equiv.swap i j) (fun m hm => by
      simp only [Equiv.Perm.mul_apply, hs m hm])
    simpa only [Equiv.Perm.mul_apply, Equiv.swap_apply_left, Equiv.swap_apply_right,
      Equiv.swap_apply_of_ne_of_ne hik.symm hjk.symm,
      Equiv.swap_apply_of_ne_of_ne hil.symm hjl.symm] using h
  · have h := hfactor (σ * Equiv.swap k l) (fun m hm => by
      simp only [Equiv.Perm.mul_apply, ht m hm])
    simpa only [Equiv.Perm.mul_apply, Equiv.swap_apply_left, Equiv.swap_apply_right,
      Equiv.swap_apply_of_ne_of_ne hik hil, Equiv.swap_apply_of_ne_of_ne hjk hjl] using h
  · have h := hfactor (σ * Equiv.swap i j * Equiv.swap k l) (fun m hm => by
      simp only [Equiv.Perm.mul_apply, ht m hm, hs m hm])
    simpa only [Equiv.Perm.mul_apply, Equiv.swap_apply_left, Equiv.swap_apply_right,
      Equiv.swap_apply_of_ne_of_ne hik hil, Equiv.swap_apply_of_ne_of_ne hjk hjl,
      Equiv.swap_apply_of_ne_of_ne hik.symm hjk.symm,
      Equiv.swap_apply_of_ne_of_ne hil.symm hjl.symm] using h

/-- The two diagonal products of the four matchings formed by disjoint swaps agree. -/
theorem matchingProduct_disjoint_swaps_identity
    (a b : ι → ℂ) (σ : Equiv.Perm ι) (i j k l : ι)
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    matchingProduct a b σ * matchingProduct a b (σ * Equiv.swap i j * Equiv.swap k l) =
      matchingProduct a b (σ * Equiv.swap i j) * matchingProduct a b (σ * Equiv.swap k l) := by
  obtain ⟨h₀₀, h₁₀, h₀₁, h₁₁⟩ :=
    matchingProduct_disjoint_swap_factors a b σ i j k l hij hik hil hjk hjl hkl
  rw [h₀₀, h₁₁, h₁₀, h₀₁]
  ring

/-- The alternating sum factors into spectral differences and the columns fixed by both swaps. -/
theorem matchingProduct_disjoint_swaps_alternating_sum
    (a b : ι → ℂ) (σ : Equiv.Perm ι) (i j k l : ι)
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    matchingProduct a b σ + matchingProduct a b (σ * Equiv.swap i j * Equiv.swap k l) -
        matchingProduct a b (σ * Equiv.swap i j) - matchingProduct a b (σ * Equiv.swap k l) =
      (∏ m ∈ ({i, j, k, l} : Finset ι)ᶜ, (a (σ m) + b m)) *
        ((a (σ i) - a (σ j)) * (b j - b i)) * ((a (σ k) - a (σ l)) * (b l - b k)) := by
  obtain ⟨h₀₀, h₁₀, h₀₁, h₁₁⟩ :=
    matchingProduct_disjoint_swap_factors a b σ i j k l hij hik hil hjk hjl hkl
  rw [h₀₀, h₁₁, h₁₀, h₀₁]
  ring

private theorem matchingProduct_disjoint_swaps_alternating_sum_ne_zero_of_unequal_pairs
    (a b : ι → ℂ) (σ : Equiv.Perm ι) (i j k l : ι)
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l)
    (haij : a (σ i) ≠ a (σ j)) (hakl : a (σ k) ≠ a (σ l))
    (hbij : b i ≠ b j) (hbkl : b k ≠ b l) (hnz : ∀ r s, a r + b s ≠ 0) :
    matchingProduct a b σ + matchingProduct a b (σ * Equiv.swap i j * Equiv.swap k l) -
        matchingProduct a b (σ * Equiv.swap i j) - matchingProduct a b (σ * Equiv.swap k l) ≠ 0 := by
  rw [matchingProduct_disjoint_swaps_alternating_sum a b σ i j k l hij hik hil hjk hjl hkl]
  exact mul_ne_zero
    (mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun m _ => hnz (σ m) m)
      (mul_ne_zero (sub_ne_zero.mpr haij) (sub_ne_zero.mpr hbij.symm)))
    (mul_ne_zero (sub_ne_zero.mpr hakl) (sub_ne_zero.mpr hbkl.symm))

/-- Simple spectra with no opposite pairs give a nonzero alternating sum. -/
theorem matchingProduct_disjoint_swaps_alternating_sum_ne_zero
    (a b : ι → ℂ) (σ : Equiv.Perm ι) (i j k l : ι)
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l)
    (ha : Function.Injective a) (hb : Function.Injective b) (hnz : ∀ r s, a r + b s ≠ 0) :
    matchingProduct a b σ + matchingProduct a b (σ * Equiv.swap i j * Equiv.swap k l) -
        matchingProduct a b (σ * Equiv.swap i j) - matchingProduct a b (σ * Equiv.swap k l) ≠ 0 :=
  matchingProduct_disjoint_swaps_alternating_sum_ne_zero_of_unequal_pairs
    a b σ i j k l hij hik hil hjk hjl hkl
    (ha.ne (σ.injective.ne hij)) (ha.ne (σ.injective.ne hkl)) (hb.ne hij) (hb.ne hkl) hnz

/-- A quartet with nonzero alternating sum has only one common translate satisfying
its multiplicative identity. -/
theorem eq_zero_of_matching_quartet_translation
    {z₀₀ z₀₁ z₁₀ z₁₁ c : ℂ}
    (h : z₀₀ * z₁₁ = z₀₁ * z₁₀) (hΓ : z₀₀ + z₁₁ - z₀₁ - z₁₀ ≠ 0)
    (h' : (z₀₀ + c) * (z₁₁ + c) = (z₀₁ + c) * (z₁₀ + c)) : c = 0 := by
  have hc : c * (z₀₀ + z₁₁ - z₀₁ - z₁₀) = 0 := calc
    _ = ((z₀₀ + c) * (z₁₁ + c) - (z₀₁ + c) * (z₁₀ + c)) -
        (z₀₀ * z₁₁ - z₀₁ * z₁₀) := by ring
    _ = 0 := by rw [h', h, sub_self, sub_self, sub_zero]
  exact (mul_eq_zero.mp hc).resolve_right hΓ

private theorem quartet_common_height_eq_zero {z₀₀ z₀₁ z₁₀ z₁₁ : ℂ} {H : ℝ}
    (hdiag : z₀₀ * z₁₁ = z₀₁ * z₁₀) (hΓ : z₀₀ + z₁₁ - z₀₁ - z₁₀ ≠ 0)
    (h₀₀ : z₀₀.re = H) (h₀₁ : z₀₁.re = H) (h₁₀ : z₁₀.re = H) (h₁₁ : z₁₁.re = H) :
    H = 0 := by
  have he := congrArg Complex.im hdiag
  simp only [Complex.mul_im, h₀₀, h₀₁, h₁₀, h₁₁] at he
  have him : H * (z₀₀.im + z₁₁.im - z₀₁.im - z₁₀.im) = 0 := calc
    _ = (H * z₁₁.im + z₀₀.im * H) - (H * z₁₀.im + z₀₁.im * H) := by ring
    _ = 0 := sub_eq_zero.mpr he
  rcases mul_eq_zero.mp him with hH | him₀
  · exact hH
  · exfalso
    apply hΓ
    apply Complex.ext
    · simp only [Complex.add_re, Complex.sub_re, Complex.zero_re, h₀₀, h₀₁, h₁₀, h₁₁]
      ring
    · simpa only [Complex.add_im, Complex.sub_im, Complex.zero_im] using him₀

/-- If each swap exchanges unequal values in both spectra and no pair sum
vanishes, the four matching products have common support height only at zero. -/
theorem matchingProduct_disjoint_swaps_common_height_eq_zero_of_unequal_pairs
    (a b : ι → ℂ) (σ : Equiv.Perm ι) (i j k l : ι)
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l)
    (haij : a (σ i) ≠ a (σ j)) (hakl : a (σ k) ≠ a (σ l))
    (hbij : b i ≠ b j) (hbkl : b k ≠ b l) (hnz : ∀ r s, a r + b s ≠ 0)
    {η : ℂ} (hη : η ≠ 0) {H : ℝ}
    (h₀₀ : (η * matchingProduct a b σ).re = H)
    (h₀₁ : (η * matchingProduct a b (σ * Equiv.swap i j)).re = H)
    (h₁₀ : (η * matchingProduct a b (σ * Equiv.swap k l)).re = H)
    (h₁₁ : (η * matchingProduct a b (σ * Equiv.swap i j * Equiv.swap k l)).re = H) :
    H = 0 := by
  let z₀₀ := matchingProduct a b σ
  let z₀₁ := matchingProduct a b (σ * Equiv.swap i j)
  let z₁₀ := matchingProduct a b (σ * Equiv.swap k l)
  let z₁₁ := matchingProduct a b (σ * Equiv.swap i j * Equiv.swap k l)
  have hdiag : z₀₀ * z₁₁ = z₀₁ * z₁₀ :=
    matchingProduct_disjoint_swaps_identity a b σ i j k l hij hik hil hjk hjl hkl
  have hΓ : z₀₀ + z₁₁ - z₀₁ - z₁₀ ≠ 0 :=
    matchingProduct_disjoint_swaps_alternating_sum_ne_zero_of_unequal_pairs
      a b σ i j k l hij hik hil hjk hjl hkl haij hakl hbij hbkl hnz
  have hdiag' : (η * z₀₀) * (η * z₁₁) = (η * z₀₁) * (η * z₁₀) := calc
    _ = η ^ 2 * (z₀₀ * z₁₁) := by ring
    _ = η ^ 2 * (z₀₁ * z₁₀) := by rw [hdiag]
    _ = _ := by ring
  have hΓ' : η * z₀₀ + η * z₁₁ - η * z₀₁ - η * z₁₀ ≠ 0 := by
    rw [show η * z₀₀ + η * z₁₁ - η * z₀₁ - η * z₁₀ =
      η * (z₀₀ + z₁₁ - z₀₁ - z₁₀) by ring]
    exact mul_ne_zero hη hΓ
  exact quartet_common_height_eq_zero hdiag' hΓ' h₀₀ h₀₁ h₁₀ h₁₁

/-- For simple spectra with no opposite pairs, four matchings formed by disjoint swaps
can share a common support height only when it is zero. -/
theorem matchingProduct_disjoint_swaps_common_height_eq_zero
    (a b : ι → ℂ) (σ : Equiv.Perm ι) (i j k l : ι)
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l)
    (ha : Function.Injective a) (hb : Function.Injective b) (hnz : ∀ r s, a r + b s ≠ 0)
    {η : ℂ} (hη : η ≠ 0) {H : ℝ}
    (h₀₀ : (η * matchingProduct a b σ).re = H)
    (h₀₁ : (η * matchingProduct a b (σ * Equiv.swap i j)).re = H)
    (h₁₀ : (η * matchingProduct a b (σ * Equiv.swap k l)).re = H)
    (h₁₁ : (η * matchingProduct a b (σ * Equiv.swap i j * Equiv.swap k l)).re = H) :
    H = 0 :=
  matchingProduct_disjoint_swaps_common_height_eq_zero_of_unequal_pairs
    a b σ i j k l hij hik hil hjk hjl hkl
    (ha.ne (σ.injective.ne hij)) (ha.ne (σ.injective.ne hkl)) (hb.ne hij) (hb.ne hkl)
    hnz hη h₀₀ h₀₁ h₁₀ h₁₁

end MOC
