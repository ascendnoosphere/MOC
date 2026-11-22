import MOC.UnitaryCircleHessian
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card

/-! Testing within each of the two relative eigenspaces and transferring
trace between them eliminates the two-branch case. -/

open BigOperators

namespace MOC

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The diagonal trace-zero Hessian tests force all relative phase
coefficients to agree when the order exceeds two. -/
theorem constant_phase_of_two_branches_and_compressed_hessian
    (t : ℝ) (ht : 0 < t) (hlt : t < 1) (ω : ℂ) (hω : ω ≠ 0) (p : ι → ℂ)
    (hcard : 2 < Fintype.card ι)
    (hp : ∀ i, Complex.normSq (p i) = t ^ 2 * Complex.normSq (1 - p i))
    (hstationary : ∀ i j, (ω * p i).im = (ω * p j).im)
    (htwo : ∀ i j k, p i = p j ∨ p i = p k ∨ p j = p k)
    (hhess : ∀ v : ι → ℝ, (∑ i, v i) = 0 →
      0 ≤ (∑ i, (v i) ^ 2 * (ω * (p i * (1 - p i))).re) +
        (ω * (∑ i, (v i : ℂ) * p i) ^ 2).re) :
    ∀ i j, p i = p j := by
  classical
  let f (z : ℂ) := (ω * (z * (1 - z))).re
  have hsplit (z : ℂ) (k l : ι) (hk : p k = z) (hl : p l = z) (hne : k ≠ l) : 0 ≤ f z := by
    let v (i : ι) : ℝ := (if i = k then 1 else 0) - (if i = l then 1 else 0)
    have hv : ∑ i, v i = 0 := by simp [v, Finset.sum_sub_distrib]
    have hlin (i : ι) : (v i : ℂ) * p i =
        (if i = k then p k else 0) - (if i = l then p l else 0) := by
      by_cases hik : i = k
      · subst i
        simp [v, hne]
      · by_cases hil : i = l
        · subst i
          simp [v, Ne.symm hne]
        · simp [v, hik, hil]
    have hvlin : ∑ i, (v i : ℂ) * p i = 0 := by
      simp [hlin, Finset.sum_sub_distrib, hk, hl]
    have hquad (i : ι) : (v i) ^ 2 * f (p i) =
        (if i = k then f (p k) else 0) + (if i = l then f (p l) else 0) := by
      by_cases hik : i = k
      · subst i
        simp [v, hne]
      · by_cases hil : i = l
        · subst i
          simp [v, Ne.symm hne]
        · simp [v, hik, hil]
    have hs := hhess v hv
    change 0 ≤ (∑ i, (v i) ^ 2 * f (p i)) + _ at hs
    simp only [hquad, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true,
      hk, hl, hvlin, zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero, Complex.zero_re, add_zero] at hs
    linarith only [hs]
  intro i j
  apply Classical.byContradiction
  intro hne
  let a := p i
  let b := p j
  let I := Finset.univ.filter fun k => p k = a
  let J := Finset.univ.filter fun k => p k = b
  have hI (k : ι) : k ∈ I ↔ p k = a := by simp [I]
  have hJ (k : ι) : k ∈ J ↔ p k = b := by simp [J]
  have hdisj : Disjoint I J := Finset.disjoint_left.mpr fun k hk hl =>
    hne (((hI k).mp hk).symm.trans ((hJ k).mp hl))
  have hunion : I ∪ J = Finset.univ := by
    ext k
    simp only [Finset.mem_union, hI, hJ, Finset.mem_univ, iff_true]
    rcases (htwo i j k).resolve_left hne with h | h
    · exact Or.inl h.symm
    · exact Or.inr h.symm
  let m : ℝ := I.card
  let n : ℝ := J.card
  have hm : 1 ≤ m := by
    dsimp only [m]
    exact_mod_cast (Finset.one_le_card.mpr ⟨i, (hI i).mpr rfl⟩)
  have hn : 1 ≤ n := by
    dsimp only [n]
    exact_mod_cast (Finset.one_le_card.mpr ⟨j, (hJ j).mpr rfl⟩)
  have hN : 2 < m + n := by
    have he := Finset.card_union_of_disjoint hdisj
    rw [hunion, Finset.card_univ] at he
    have hn' : 2 < I.card + J.card := he ▸ hcard
    dsimp only [m, n]
    exact_mod_cast hn'
  have hm₀ : m ≠ 0 := (zero_lt_one.trans_le hm).ne'
  have hn₀ : n ≠ 0 := (zero_lt_one.trans_le hn).ne'
  have hsum {R : Type} [AddCommMonoid R] (g : ι → R) (x y : R)
      (hleft : ∀ k ∈ I, g k = x) (hright : ∀ k ∈ J, g k = y) :
      ∑ k, g k = I.card • x + J.card • y := by
    rw [← hunion, Finset.sum_union hdisj]
    congr 1
    · rw [← Finset.sum_const]
      exact Finset.sum_congr rfl hleft
    · rw [← Finset.sum_const]
      exact Finset.sum_congr rfl hright
  have hsI (h : 1 < m) : 0 ≤ f a := by
    dsimp only [m] at h
    have hh : 1 < I.card := by exact_mod_cast h
    obtain ⟨k, hk, l, hl, hnkl⟩ := Finset.one_lt_card.mp hh
    exact hsplit a k l ((hI k).mp hk) ((hI l).mp hl) hnkl
  have hsJ (h : 1 < n) : 0 ≤ f b := by
    dsimp only [n] at h
    have hh : 1 < J.card := by exact_mod_cast h
    obtain ⟨k, hk, l, hl, hnkl⟩ := Finset.one_lt_card.mp hh
    exact hsplit b k l ((hJ k).mp hk) ((hJ l).mp hl) hnkl
  let v (k : ι) := if p k = a then m⁻¹ else -n⁻¹
  have hvI (k : ι) (hk : k ∈ I) : v k = m⁻¹ := by simp only [v, if_pos ((hI k).mp hk)]
  have hvJ (k : ι) (hk : k ∈ J) : v k = -n⁻¹ := by
    have hz : p k ≠ a := fun he => hne (he.symm.trans ((hJ k).mp hk))
    exact if_neg hz
  have hv : ∑ k, v k = 0 := by
    rw [hsum v m⁻¹ (-n⁻¹) hvI hvJ, nsmul_eq_mul, nsmul_eq_mul]
    change m * m⁻¹ + n * -n⁻¹ = 0
    rw [mul_neg, mul_inv_cancel₀ hm₀, mul_inv_cancel₀ hn₀, add_neg_cancel]
  have hlin : ∑ k, (v k : ℂ) * p k = a - b := by
    rw [hsum (fun k => (v k : ℂ) * p k) ((m⁻¹ : ℝ) * a) ((-n⁻¹ : ℝ) * b)
      (fun k hk => by simp only [hvI k hk, (hI k).mp hk])
      (fun k hk => by simp only [hvJ k hk, (hJ k).mp hk]), nsmul_eq_mul, nsmul_eq_mul]
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_natCast]
    change (m : ℂ) * ((m⁻¹ : ℝ) * a) + (n : ℂ) * ((-n⁻¹ : ℝ) * b) = a - b
    rw [← mul_assoc, ← mul_assoc, ← Complex.ofReal_mul, ← Complex.ofReal_mul,
      mul_inv_cancel₀ hm₀, mul_neg, mul_inv_cancel₀ hn₀, Complex.ofReal_one,
      Complex.ofReal_neg, Complex.ofReal_one, one_mul, neg_one_mul, sub_eq_add_neg]
  have hquad : ∑ k, (v k) ^ 2 * f (p k) = f a / m + f b / n := by
    rw [hsum (fun k => (v k) ^ 2 * f (p k)) (m⁻¹ ^ 2 * f a) ((-n⁻¹) ^ 2 * f b)
      (fun k hk => by simp only [hvI k hk, (hI k).mp hk])
      (fun k hk => by simp only [hvJ k hk, (hJ k).mp hk]), nsmul_eq_mul, nsmul_eq_mul]
    change m * (m⁻¹ ^ 2 * f a) + n * ((-n⁻¹) ^ 2 * f b) = _
    field_simp [hm₀, hn₀] <;> ring
  have htr := hhess v hv
  change 0 ≤ (∑ k, (v k) ^ 2 * f (p k)) + _ at htr
  rw [hquad, hlin] at htr
  have hre (z : ℂ) (r : ℝ) : (ω * (z / (r : ℂ))).re = (ω * z).re / r := by
    rw [← mul_div_assoc, div_eq_mul_inv, ← Complex.ofReal_inv, Complex.re_mul_ofReal, div_eq_mul_inv]
  apply two_phase_quadratic_obstruction t ht hlt a b ω hne hω (hp i) (hp j)
    (hstationary i j) m n hm hn hN hsI hsJ
  rw [mul_add, mul_add, Complex.add_re, Complex.add_re, hre, hre]
  exact htr

end MOC
