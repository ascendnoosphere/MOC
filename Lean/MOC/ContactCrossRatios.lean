import MOC.DisjointContactRectangle

/-! Cross-ratio constraints on the local contact graph. A pair of active
disjoint exchanges has a real signed phase product; comparing two such
pairs cancels all base matching factors. -/

open BigOperators

namespace MOC
noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A single exchange divides the 2×2 additive-kernel minor by the two
base matching entries. -/
theorem matchingProduct_right_swap_gap_ratio (a b : ι → ℂ) (r : Equiv.Perm ι)
    (hr : matchingProduct a b r ≠ 0) (i j : ι) (hij : i ≠ j) :
    matchingProduct a b r - matchingProduct a b (r * Equiv.swap i j) =
      matchingProduct a b r *
        (((a (r i) - a (r j)) * (b j - b i)) /
          ((a (r i) + b i) * (a (r j) + b j))) := by
  let S : Finset ι := Finset.univ.erase i
  have hj := Finset.mem_erase.mpr ⟨Ne.symm hij, Finset.mem_univ j⟩
  have hsplit (τ : Equiv.Perm ι) :
      matchingProduct a b τ =
        (a (τ i) + b i) * ((a (τ j) + b j) * ∏ k ∈ S.erase j, (a (τ k) + b k)) := by
    unfold matchingProduct
    rw [← Finset.mul_prod_erase Finset.univ (fun k => a (τ k) + b k) (Finset.mem_univ i),
      ← Finset.mul_prod_erase S (fun k => a (τ k) + b k) hj]
  have he : (∏ k ∈ S.erase j, (a ((r * Equiv.swap i j) k) + b k)) =
      ∏ k ∈ S.erase j, (a (r k) + b k) := by
    apply Finset.prod_congr rfl
    intro k hk
    rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne
      (Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).1 (Finset.mem_erase.mp hk).1]
  have hn (k : ι) : a (r k) + b k ≠ 0 :=
    Finset.prod_ne_zero_iff.mp hr k (Finset.mem_univ k)
  rw [hsplit r, hsplit (r * Equiv.swap i j), he, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply,
    Equiv.swap_apply_left, Equiv.swap_apply_right]
  field_simp [hn i, hn j]
  ring

/-- A complex phase gap is nonzero for a single exchange of simple spectra
at a nonzero base matching. Only one nonzero matching is needed. -/
theorem matchingProduct_swap_gap_ne_of_simple (a b : ι → ℂ)
    (ha : Function.Injective a) (hb : Function.Injective b)
    (r : Equiv.Perm ι) (hr : matchingProduct a b r ≠ 0) (i j : ι) (hij : i ≠ j) :
    matchingProduct a b r - matchingProduct a b (r * Equiv.swap i j) ≠ 0 := by
  rw [matchingProduct_right_swap_gap_ratio a b r hr i j hij]
  apply mul_ne_zero hr
  apply div_ne_zero
  · exact mul_ne_zero (sub_ne_zero.mpr (ha.ne (r.injective.ne hij)))
      (sub_ne_zero.mpr (hb.ne (Ne.symm hij)))
  · exact mul_ne_zero
      (Finset.prod_ne_zero_iff.mp hr i (Finset.mem_univ i))
      (Finset.prod_ne_zero_iff.mp hr j (Finset.mem_univ j))

/-- Four active single swaps forming a cycle on four labels constrain the
product of the two spectral cross ratios: it must be strictly positive
real. This test is geometric and needs no product-injectivity or assumption
on otherwise inactive matching values. -/
theorem active_swap_cycle_cross_ratio_positive (a b : ι → ℂ)
    (ha : Function.Injective a) (hb : Function.Injective b)
    (r : Equiv.Perm ι) (η : ℂ) (H : ℝ) (hH : H ≠ 0)
    (hbase : (η * matchingProduct a b r).re = H)
    (hsup : ∀ τ, (η * matchingProduct a b τ).re ≤ H)
    (i j k l : ι) (hij : i ≠ j) (hkl : k ≠ l) (hik : i ≠ k) (hjl : j ≠ l)
    (hd₁ : ∀ m, Equiv.swap i j m = m ∨ Equiv.swap k l m = m)
    (hd₂ : ∀ m, Equiv.swap i k m = m ∨ Equiv.swap j l m = m)
    (hij' : (η * matchingProduct a b (r * Equiv.swap i j)).re = H)
    (hkl' : (η * matchingProduct a b (r * Equiv.swap k l)).re = H)
    (hik' : (η * matchingProduct a b (r * Equiv.swap i k)).re = H)
    (hjl' : (η * matchingProduct a b (r * Equiv.swap j l)).re = H) :
    let D (u v : ι) := (a (r u) - a (r v)) * (b v - b u)
    ∃ t : ℝ, 0 < t ∧ D i j * D k l / (D i k * D j l) = (t : ℂ) := by
  intro D
  let z (τ : Equiv.Perm ι) := η * matchingProduct a b τ
  let G (u v : ι) := z r - z (r * Equiv.swap u v)
  let c (u : ι) := a (r u) + b u
  change (z r).re = H at hbase
  have hz : z r ≠ 0 := by
    intro h
    exact hH (by simpa [h] using hbase.symm)
  have hr : matchingProduct a b r ≠ 0 := fun h => hz (by simp [z, h])
  have hη : η ≠ 0 := fun h => hz (by simp [z, h])
  have hc (u : ι) : c u ≠ 0 :=
    Finset.prod_ne_zero_iff.mp hr u (Finset.mem_univ u)
  have hGne (u v : ι) (huv : u ≠ v) : G u v ≠ 0 := by
    unfold G z
    rw [← mul_sub]
    exact mul_ne_zero hη (matchingProduct_swap_gap_ne_of_simple a b ha hb r hr u v huv)
  have hreal (u v : ι) (h : (z (r * Equiv.swap u v)).re = H) : (G u v).re = 0 := by
    simp only [G, Complex.sub_re, hbase, h, sub_self]
  have hsign (u v x y : ι) (huv : u ≠ v) (hxy : x ≠ y)
      (hd : ∀ m, Equiv.swap u v m = m ∨ Equiv.swap x y m = m)
      (h₁ : (z (r * Equiv.swap u v)).re = H) (h₂ : (z (r * Equiv.swap x y)).re = H) :
      0 < H * ((G u v).im * (G x y).im) := by
    have him {u v : ι} (hne : u ≠ v) (he : (z (r * Equiv.swap u v)).re = H) :
        (G u v).im ≠ 0 := fun h =>
      hGne u v hne (Complex.ext (by simpa using hreal u v he) (by simpa using h))
    have he := matchingProduct_disjoint_perms_fourth_gap a b r
      (Equiv.swap u v) (Equiv.swap x y) hd η H hbase h₁ h₂
    change (H - (z (r * Equiv.swap u v * Equiv.swap x y)).re) *
        (H ^ 2 + (z r).im ^ 2) =
        H * ((z (r * Equiv.swap u v)).im - (z r).im) *
          ((z (r * Equiv.swap x y)).im - (z r).im) at he
    have hf : (H - (z (r * Equiv.swap u v * Equiv.swap x y)).re) *
        (H ^ 2 + (z r).im ^ 2) = H * ((G u v).im * (G x y).im) := by
      rw [he]
      simp only [G, Complex.sub_im]
      ring
    rw [← hf]
    have hnonneg : 0 ≤ (H - (z (r * Equiv.swap u v * Equiv.swap x y)).re) *
        (H ^ 2 + (z r).im ^ 2) :=
      mul_nonneg (sub_nonneg.mpr (hsup _)) (by positivity)
    have hnonzero : (H - (z (r * Equiv.swap u v * Equiv.swap x y)).re) *
        (H ^ 2 + (z r).im ^ 2) ≠ 0 := by
      rw [hf]
      exact mul_ne_zero hH
        (mul_ne_zero (him huv h₁) (him hxy h₂))
    exact lt_of_le_of_ne hnonneg hnonzero.symm
  let P : ℝ := (G i j).im * (G k l).im
  let Q : ℝ := (G i k).im * (G j l).im
  have hP : 0 < H * P := hsign i j k l hij hkl hd₁ hij' hkl'
  have hQ : 0 < H * Q := hsign i k j l hik hjl hd₂ hik' hjl'
  have hpos : 0 < P / Q := by
    have hg : P / Q = (H * P) / (H * Q) := (mul_div_mul_left P Q hH).symm
    rw [hg]
    exact div_pos hP hQ
  have hx (u v : ι) (hne : u ≠ v) : G u v = z r * (D u v / (c u * c v)) := by
    unfold G z
    rw [← mul_sub, matchingProduct_right_swap_gap_ratio a b r hr u v hne]
    ring
  have hpair (u v x y : ι)
      (huv : (z (r * Equiv.swap u v)).re = H) (hxy : (z (r * Equiv.swap x y)).re = H) :
      G u v * G x y = (-((G u v).im * (G x y).im) : ℝ) := by
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im, hreal u v huv, hreal x y hxy]
  have hratio : D i j * D k l / (D i k * D j l) =
      (G i j * G k l) / (G i k * G j l) := by
    let common := (z r * z r) / ((c i * c j) * (c k * c l))
    have hcommon : common ≠ 0 := div_ne_zero (mul_ne_zero hz hz)
      (mul_ne_zero (mul_ne_zero (hc i) (hc j)) (mul_ne_zero (hc k) (hc l)))
    have he : (c i * c k) * (c j * c l) = (c i * c j) * (c k * c l) := by ring
    have hmul (u v x y : ι) (hu : u ≠ v) (hv : x ≠ y)
        (hcEq : (c u * c v) * (c x * c y) = (c i * c j) * (c k * c l)) :
        G u v * G x y = common * (D u v * D x y) := by
      rw [hx u v hu, hx x y hv, mul_mul_mul_comm, div_mul_div_comm, hcEq]
      simp only [common, div_eq_mul_inv]
      ring
    rw [hmul i j k l hij hkl rfl, hmul i k j l hik hjl he, mul_div_mul_left _ _ hcommon]
  refine ⟨P / Q, hpos, ?_⟩
  rw [hratio, hpair i j k l hij' hkl', hpair i k j l hik' hjl']
  change ((-P : ℝ) : ℂ) / ((-Q : ℝ) : ℂ) = ((P / Q : ℝ) : ℂ)
  simp only [Complex.ofReal_neg, neg_div_neg_eq, Complex.ofReal_div]

end
end MOC
