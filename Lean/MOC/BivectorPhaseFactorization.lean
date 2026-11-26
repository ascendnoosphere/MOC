import MOC.GrassmannianBivectorLift
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Real.Sqrt

/-! A symmetric array of phases factors into phases on its labels
when the products on opposite edges agree on every four labels. -/

open BigOperators Matrix

namespace MOC

variable {ι : Type*}

/-- The four-label equations on an array of off-diagonal phases give
one phase per label. Three distinct labels suffice as references. -/
theorem exists_label_phases_of_four_label_products [DecidableEq ι]
    (v : ι → ι → ℂ) (a b c : ι) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hsymm : ∀ i j, v j i = v i j)
    (hunit : ∀ i j, i ≠ j → Complex.normSq (v i j) = 1)
    (hfour : ∀ i j k l, i ≠ j → i ≠ k → i ≠ l → j ≠ k → j ≠ l → k ≠ l →
      v i j * v k l = v i l * v k j) :
    ∃ t : ι → ℂ, (∀ i, Complex.normSq (t i) = 1) ∧
      ∀ i j, i ≠ j → v i j = t i * t j := by
  have hne (i j : ι) (h : i ≠ j) : v i j ≠ 0 := by
    intro hz
    simpa only [hz, map_zero, zero_ne_one] using hunit i j h
  have hedge (k : ι) (hka : k ≠ a) (hkb : k ≠ b) : v b k * v a c = v b c * v a k := by
    by_cases hkc : k = c
    · rw [hkc]
    · exact hfour b k a c hkb.symm hab.symm hbc hka hkc hac
  have hratio (i j : ι) (hia : i ≠ a) (hja : j ≠ a) (hij : i ≠ j) :
      v i j * (v a b * v a c) = v b c * (v a i * v a j) := by
    by_cases hib : i = b
    · subst i
      calc
        _ = v a b * (v b j * v a c) := by ring
        _ = _ := by rw [hedge j hja hij.symm]; ring
    by_cases hjb : j = b
    · subst j
      calc
        _ = v a b * (v b i * v a c) := by rw [hsymm i b]; ring
        _ = _ := by rw [hedge i hia hib]; ring
    calc
      _ = (v i j * v a b) * v a c := by ring
      _ = (v i b * v a j) * v a c := by rw [hfour i j a b hij hia hib hja hjb hab]
      _ = (v b i * v a c) * v a j := by rw [hsymm i b]; ring
      _ = _ := by rw [hedge i hia hib]; ring
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (v a b * v a c / v b c) zero_lt_two
  have hsnorm : Complex.normSq s = 1 := by
    have h := congrArg Complex.normSq hs
    rw [map_pow, Complex.normSq_div, map_mul, hunit a b hab, hunit a c hac,
      hunit b c hbc, mul_one, div_one] at h
    exact (sq_eq_sq₀ (Complex.normSq_nonneg s) zero_le_one).mp (by simpa only [one_pow] using h)
  have hsne : s ≠ 0 := by
    intro hz
    simpa only [hz, map_zero, zero_ne_one] using hsnorm
  let t (i : ι) : ℂ := if i = a then s else v a i / s
  refine ⟨t, ?_, ?_⟩
  · intro i
    by_cases h : i = a
    · simpa only [t, if_pos h] using hsnorm
    · simp only [t, if_neg h, Complex.normSq_div, hunit a i h.symm, hsnorm, div_one]
  · intro i j hij
    by_cases hia : i = a
    · subst i
      simp only [t, if_pos rfl, if_neg hij.symm, mul_comm s, div_mul_cancel₀ _ hsne]
    by_cases hja : j = a
    · subst j
      simp only [t, if_pos rfl, if_neg hia, div_mul_cancel₀ _ hsne, hsymm i a]
    simp only [t, if_neg hia, if_neg hja, div_mul_div_comm, ← pow_two]
    apply (eq_div_iff (pow_ne_zero _ hsne)).mpr
    apply mul_right_cancel₀ (hne b c hbc)
    calc
      _ = v i j * (s ^ 2 * v b c) := by ring
      _ = v b c * (v a i * v a j) := by
        rw [(eq_div_iff (hne b c hbc)).mp hs, hratio i j hia hja hij]
      _ = _ := by ring

variable {K : Type*} [CommRing K] [Fintype ι] [DecidableEq ι]

/-- A change of coordinates on vectors acts on bivectors by congruence. -/
theorem bivectorMatrix_congr (U : Matrix ι ι K) (x y : ι → K) :
    U * bivectorMatrix x y * Uᵀ = bivectorMatrix (U *ᵥ x) (U *ᵥ y) := by
  have hleft (v w : ι → K) :
      U * Matrix.vecMulVec v w = Matrix.vecMulVec (U *ᵥ v) w := by
    ext i j : 1
    simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.mulVec, dotProduct, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hright (v w : ι → K) :
      Matrix.vecMulVec v w * Uᵀ = Matrix.vecMulVec v (U *ᵥ w) := by
    ext i j : 1
    simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.transpose_apply, Matrix.mulVec,
      dotProduct, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  change U * (Matrix.vecMulVec x y - Matrix.vecMulVec y x) * Uᵀ = _
  rw [Matrix.mul_sub, Matrix.sub_mul, hleft, hleft, hright, hright] <;> rfl

end MOC
