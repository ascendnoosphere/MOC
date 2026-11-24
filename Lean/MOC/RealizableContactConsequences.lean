import MOC.RealizableContactKernels
import MOC.ContactRectangle

/-! Support restrictions from the multiplicative rectangles of realizable
matching profiles. Strict inequalities outside the face are not assumed. -/

open BigOperators Matrix

namespace MOC
noncomputable section

/-- Multiplying two numbers in the closed left half-plane gives a strictly
negative real number only if both belong to the imaginary axis. -/
theorem real_zero_of_negative_product {u v : ℂ} {t : ℝ}
    (ht : 0 < t) (hu : u.re ≤ 0) (hv : v.re ≤ 0)
    (hp : u * v = -(t : ℂ)) : u.re = 0 ∧ v.re = 0 := by
  have haux (x y : ℂ) (hx : x.re ≤ 0) (hy : y.re ≤ 0)
      (h : x * y = -(t : ℂ)) : x.re = 0 := by
    have hre := congrArg Complex.re h
    have him := congrArg Complex.im h
    simp only [Complex.mul_re, Complex.neg_re, Complex.ofReal_re] at hre
    simp only [Complex.mul_im, Complex.neg_im, Complex.ofReal_im, neg_zero] at him
    have he : (x.re ^ 2 + x.im ^ 2) * y.re = -t * x.re := by
      linear_combination x.re * hre + x.im * him
    by_contra hn
    have hpos := mul_pos_of_neg_of_neg (neg_neg_of_pos ht) (lt_of_le_of_ne hx hn)
    have hneg : (x.re ^ 2 + x.im ^ 2) * y.re ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) hy
    rw [he] at hneg
    exact (not_lt_of_ge hneg) hpos
  exact ⟨haux u v hu hv hp, haux v u hv hu (by rwa [mul_comm])⟩

/-- At height zero, opposite-corner contacts on the same open imaginary ray
force both other corners to contact. This excludes a strict missing contact,
even when the two known corner products are distinct. -/
theorem rectangle_complete_of_same_imaginary_ray {z₀₀ z₀₁ z₁₀ z₁₁ : ℂ}
    (hdiag : z₀₀ * z₁₁ = z₀₁ * z₁₀)
    (h₀₀ : z₀₀.re = 0) (h₁₁ : z₁₁.re = 0)
    (hray : 0 < z₀₀.im * z₁₁.im) (h₀₁ : z₀₁.re ≤ 0) (h₁₀ : z₁₀.re ≤ 0) :
    z₀₁.re = 0 ∧ z₁₀.re = 0 := by
  refine real_zero_of_negative_product hray h₀₁ h₁₀ (hdiag.symm.trans ?_)
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im, h₀₀, h₁₁]

/-- If three adjacent corners touch a zero-height line and the common
corner has nonzero value, the fourth corner must touch the same line. -/
theorem rectangle_complete_of_three_zero_height {z₀₀ z₀₁ z₁₀ z₁₁ : ℂ}
    (hdiag : z₀₀ * z₁₁ = z₀₁ * z₁₀) (hbase : z₀₀ ≠ 0)
    (h₀₀ : z₀₀.re = 0) (h₀₁ : z₀₁.re = 0) (h₁₀ : z₁₀.re = 0) : z₁₁.re = 0 := by
  have hm : z₀₀.im ≠ 0 := by
    intro him
    exact hbase (Complex.ext (by simpa using h₀₀) (by simpa using him))
  have h := rectangle_fourth_gap hdiag h₀₀ h₀₁ h₁₀
  simp only [zero_pow (by decide : 2 ≠ 0), zero_add, zero_sub, zero_mul] at h
  have he := (mul_eq_zero.mp h).resolve_right (pow_ne_zero _ hm)
  exact neg_eq_zero.mp he

/-- At a positive maximal support height, two distinct phase changes from the
common contact must move together. If neither phase change vanishes, the
composite corner is strictly below the support. This requires no assumption
of global injectivity of the matching products. -/
theorem rectangle_positive_support_phases {z₀₀ z₀₁ z₁₀ z₁₁ : ℂ} {H : ℝ}
    (hdiag : z₀₀ * z₁₁ = z₀₁ * z₁₀) (hH : 0 < H)
    (h₀₀ : z₀₀.re = H) (h₀₁ : z₀₁.re = H) (h₁₀ : z₁₀.re = H)
    (h₁₁ : z₁₁.re ≤ H) :
    0 ≤ (z₀₁.im - z₀₀.im) * (z₁₀.im - z₀₀.im) ∧
    (z₁₁.re = H ↔ z₀₁ = z₀₀ ∨ z₁₀ = z₀₀) := by
  have he := rectangle_fourth_gap hdiag h₀₀ h₀₁ h₁₀
  rw [mul_assoc] at he
  have hnorm : 0 < H ^ 2 + z₀₀.im ^ 2 :=
    add_pos_of_pos_of_nonneg (pow_pos hH _) (sq_nonneg _)
  constructor
  · apply nonneg_of_mul_nonneg_right ?_ hH
    rw [← he]
    exact mul_nonneg (sub_nonneg.mpr h₁₁) hnorm.le
  · have hz : z₁₁.re = H ↔ (H - z₁₁.re) * (H ^ 2 + z₀₀.im ^ 2) = 0 := by
      rw [mul_eq_zero, or_iff_left hnorm.ne', sub_eq_zero, eq_comm]
    have hleft : z₀₁.im - z₀₀.im = 0 ↔ z₀₁ = z₀₀ :=
      ⟨fun h => Complex.ext (h₀₁.trans h₀₀.symm) (sub_eq_zero.mp h), fun h => by simp [h]⟩
    have hright : z₁₀.im - z₀₀.im = 0 ↔ z₁₀ = z₀₀ :=
      ⟨fun h => Complex.ext (h₁₀.trans h₀₀.symm) (sub_eq_zero.mp h), fun h => by simp [h]⟩
    rw [hz, he, mul_eq_zero, or_iff_right hH.ne', mul_eq_zero, hleft, hright]

variable {ι : Type*} [Fintype ι]

/-- Disjoint changes give a multiplicative rectangle even in a general
pivot kernel, so the argument includes profiles with zero coordinates. -/
theorem kernel_matching_disjoint_rectangle (K : Matrix ι ι ℂ) (d : ℂ)
    (r s t : Equiv.Perm ι) (hst : ∀ i, s i = i ∨ t i = i) :
    let z (q : Equiv.Perm ι) := d * kernelMatchingProduct K q
    z r * z (r * s * t) = z (r * s) * z (r * t) := by
  intro z
  have h : kernelMatchingProduct K r * kernelMatchingProduct K (r * s * t) =
      kernelMatchingProduct K (r * s) * kernelMatchingProduct K (r * t) := by
    simp only [kernelMatchingProduct, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    rcases hst i with hs | ht
    · simp only [Equiv.Perm.mul_apply, hs]
      rcases hst (t i) with hst' | ht'
      · rw [hst', mul_comm]
      · have he : t i = i := t.injective ht'
        simp [he, hs]
    · simp [Equiv.Perm.mul_apply, ht, mul_comm]
  dsimp only [z]
  linear_combination d ^ 2 * h

/-- A missing corner of a zero-height support face rules out opposite
same-ray contacts in any disjoint rectangle of its kernel. -/
theorem kernel_contacts_same_ray_complete (K : Matrix ι ι ℂ) (d : ℂ)
    (r s t : Equiv.Perm ι) (hst : ∀ i, s i = i ∨ t i = i)
    (hsupport : ∀ q, (d * kernelMatchingProduct K q).re ≤ 0)
    (hbase : (d * kernelMatchingProduct K r).re = 0)
    (hopp : (d * kernelMatchingProduct K (r * s * t)).re = 0)
    (hray : 0 < (d * kernelMatchingProduct K r).im *
      (d * kernelMatchingProduct K (r * s * t)).im) :
    (d * kernelMatchingProduct K (r * s)).re = 0 ∧
      (d * kernelMatchingProduct K (r * t)).re = 0 :=
  rectangle_complete_of_same_imaginary_ray
    (kernel_matching_disjoint_rectangle K d r s t hst) hbase hopp hray
    (hsupport _) (hsupport _)

variable [DecidableEq ι]

/-- For simple spectra and nonzero matching coordinates, a single transposition
always changes the complex product. Global injectivity is not required. -/
theorem matchingProduct_right_swap_ne_of_simple
    (a b : ι → ℂ) (ha : Function.Injective a) (hb : Function.Injective b)
    (hn : ∀ σ, matchingProduct a b σ ≠ 0) (r : Equiv.Perm ι) (i j : ι)
    (hij : i ≠ j) : matchingProduct a b r ≠ matchingProduct a b (r * Equiv.swap i j) := by
  let S : Finset ι := Finset.univ.erase i
  have hj : j ∈ S := Finset.mem_erase.mpr ⟨Ne.symm hij, Finset.mem_univ j⟩
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
  have htail : (∏ k ∈ S.erase j, (a (r k) + b k)) ≠ 0 := by
    intro hz
    apply hn r
    rw [hsplit r, hz, mul_zero, mul_zero]
  intro h
  rw [hsplit r, hsplit (r * Equiv.swap i j), he, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply,
    Equiv.swap_apply_left, Equiv.swap_apply_right, ← mul_assoc, ← mul_assoc] at h
  have hpair := mul_right_cancel₀ htail h
  have hzero : (a (r i) - a (r j)) * (b j - b i) = 0 := by
    rw [← matching_pair_sub_swap]
    convert sub_eq_zero.mpr hpair using 1
    ring
  exact mul_ne_zero (sub_ne_zero.mpr (ha.ne (r.injective.ne hij)))
    (sub_ne_zero.mpr (hb.ne (Ne.symm hij))) hzero

/-- In the simple, all-nonzero stratum, a full disjoint-transposition contact
rectangle can only occur at height zero. This holds in any order, including
order five, and does not require pairwise distinct values of all matchings. -/
theorem matchingProduct_disjoint_swap_rectangle_height_zero_of_simple
    (a b : ι → ℂ) (ha : Function.Injective a) (hb : Function.Injective b)
    (hn : ∀ σ, matchingProduct a b σ ≠ 0) (r : Equiv.Perm ι) (i j k l : ι)
    (hij : i ≠ j) (hkl : k ≠ l)
    (hd : ∀ m, Equiv.swap i j m = m ∨ Equiv.swap k l m = m)
    (η : ℂ) (hη : η ≠ 0) (H : ℝ)
    (h₀₀ : (η * matchingProduct a b r).re = H)
    (h₀₁ : (η * matchingProduct a b (r * Equiv.swap i j)).re = H)
    (h₁₀ : (η * matchingProduct a b (r * Equiv.swap k l)).re = H)
    (h₁₁ : (η * matchingProduct a b (r * Equiv.swap i j * Equiv.swap k l)).re = H) :
    H = 0 := by
  let z (q : Equiv.Perm ι) := η * matchingProduct a b q
  let s := Equiv.swap i j
  let t := Equiv.swap k l
  have hrect : z r * z (r * s * t) = z (r * s) * z (r * t) := by
    simpa only [z, kernelMatchingProduct, Matrix.of_apply, matchingProduct] using
      kernel_matching_disjoint_rectangle (Matrix.of fun i j => a i + b j) η r s t hd
  have hphase {q : Equiv.Perm ι} (hre : (z q).re = H)
      (hne : matchingProduct a b r ≠ matchingProduct a b q) :
      (z q).im - (z r).im ≠ 0 := by
    intro h
    apply hne
    apply mul_left_cancel₀ hη
    exact Complex.ext (h₀₀.trans hre.symm) (sub_eq_zero.mp h).symm
  have hs := hphase h₀₁ (matchingProduct_right_swap_ne_of_simple a b ha hb hn r i j hij)
  have ht := hphase h₁₀ (matchingProduct_right_swap_ne_of_simple a b ha hb hn r k l hkl)
  have hg := rectangle_fourth_gap hrect h₀₀ h₀₁ h₁₀
  change (z (r * s * t)).re = H at h₁₁
  rw [h₁₁, sub_self, zero_mul] at hg
  exact (mul_eq_zero.mp ((mul_eq_zero.mp hg.symm).resolve_right ht)).resolve_right hs

end
end MOC
