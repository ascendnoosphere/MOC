import MOC.FourSupportConeClassification
import MOC.RealMatchingSquares

/-! A matching-square certificate for the order-four family with ordinary
ray indices 7, 13, 23, 30 and 31. The positive budgets are a, b, c, d
and e in that order, and the mixed ray has coefficient one. -/

namespace MOC

open BigOperators

noncomputable section

private def affineFactorBody (s p c e : ℝ) : ℝ :=
  (1 + c * (1 - e)) * s ^ 2 + (2 - e + c * (1 - e)) * (s * p) +
    (1 - e) * p ^ 2 + (c * e * (1 - e) + 2 * c + 2 * e + 2) * s +
    (c * (e + 1) ^ 2 + (2 - e) * (e + 1)) * p

private def affineFactorIntercept (s p c e : ℝ) : ℝ :=
  (e + 1) * (c ^ 2 * e + (e + 1) * (c + 1)) +
    affineFactorBody s p c e + c ^ 2 * (e * s + e * (1 - e) * p)

private def affineFactorSlope (s p c e : ℝ) : ℝ :=
  (e + 1) * ((1 - 2 * e) * c ^ 2 + (e + 1) * (c + 1)) +
    affineFactorBody s p c e + c ^ 2 * ((e ^ 2 + (1 - e)) * s + (1 - e) * p)

/-- The mixed-sign scalar factor in the five budgets. -/
def fourEightContactAffineFactor (a b c d e : ℝ) : ℝ :=
  affineFactorIntercept (a + b) (a * b) c e +
    d * affineFactorSlope (a + b) (a * b) c e

private theorem affineFactorBody_nonneg {s p c e : ℝ}
    (hs : 0 ≤ s) (hp : 0 ≤ p) (hc : 0 ≤ c) (he : 0 ≤ e) (hle : e ≤ 1) :
    0 ≤ affineFactorBody s p c e := by
  have h₁ : 0 ≤ 1 - e := sub_nonneg.mpr hle
  have h₂ : 0 ≤ 2 - e := by linarith only [hle]
  unfold affineFactorBody
  positivity

/-- A root with fifth budget at most one supplies the ray-23
compensation inequality. -/
theorem fourEightContactAffine_budget {a b c d e : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 < c) (hd : 0 < d) (he : 0 < e)
    (he₁ : e ≤ 1) (hfactor : fourEightContactAffineFactor a b c d e = 0) :
    1 + 1 / d + 1 / e < 4 * c := by
  let s := a + b
  let p := a * b
  let body := affineFactorBody s p c e
  let interceptTail := body + c ^ 2 * (e * s + e * (1 - e) * p)
  let slopeTail := body + c ^ 2 * ((e ^ 2 + (1 - e)) * s + (1 - e) * p)
  let intercept := affineFactorIntercept s p c e
  let slope := affineFactorSlope s p c e
  let gap := 4 * c * e - e - 1
  have hs : 0 ≤ s := add_nonneg ha hb
  have hp : 0 ≤ p := mul_nonneg ha hb
  have h₁ : 0 ≤ 1 - e := sub_nonneg.mpr he₁
  have hbody : 0 ≤ body := affineFactorBody_nonneg hs hp hc.le he.le he₁
  have hI : 0 ≤ interceptTail := by
    dsimp only [interceptTail]
    positivity
  have hK : 0 ≤ slopeTail := by
    dsimp only [slopeTail]
    positivity
  have hIntercept : intercept =
      (e + 1) * (c ^ 2 * e + (e + 1) * (c + 1)) + interceptTail := by
    dsimp [intercept, affineFactorIntercept, interceptTail, body]
    ring
  have hSlope : slope =
      (e + 1) * ((1 - 2 * e) * c ^ 2 + (e + 1) * (c + 1)) + slopeTail := by
    dsimp [slope, affineFactorSlope, slopeTail, body]
    ring
  have hi : 0 < intercept := by rw [hIntercept]; positivity
  change intercept + d * slope = 0 at hfactor
  have hgap : 0 < gap := by
    by_contra! hgap
    have hh : 4 * c * e ≤ e + 1 := by dsimp [gap] at hgap; linarith only [hgap]
    have hhc := mul_le_mul_of_nonneg_right hh hc.le
    have hslack : 0 ≤ (e + 1) * c - 4 * c * e * c := sub_nonneg.mpr hhc
    have hbase : 0 < (1 - 2 * e) * c ^ 2 + (e + 1) * (c + 1) := by
      have heq : (1 - 2 * e) * c ^ 2 + (e + 1) * (c + 1) =
          c ^ 2 + (e + 1) * (c / 2 + 1) + ((e + 1) * c - 4 * c * e * c) / 2 := by
        ring
      rw [heq]
      positivity
    have hsl : 0 < slope := by rw [hSlope]; positivity
    linarith only [hfactor, hi, mul_pos hd hsl]
  have hpair : gap * intercept + e * slope =
      (e + 1) * (gap * (e * c ^ 2 + c + 1) + e * c ^ 2 * (1 + 2 * e) +
        4 * c * e ^ 2) + gap * interceptTail + e * slopeTail := by
    rw [hIntercept, hSlope]
    dsimp only [gap]
    ring
  have hpos : 0 < gap * intercept + e * slope := by rw [hpair]; positivity
  have hprod : 0 < (d * gap - e) * intercept := by
    calc
      0 < d * (gap * intercept + e * slope) := mul_pos hd hpos
      _ = (d * gap - e) * intercept := by linear_combination e * hfactor
  have hlt : e < d * gap :=
    sub_pos.mp ((mul_pos_iff_of_pos_right hi).mp hprod)
  have hdiv : 0 < (4 * c - (1 + 1 / d + 1 / e)) * (d * e) := by
    have hid : (4 * c - (1 + 1 / d + 1 / e)) * (d * e) = d * gap - e := by
      dsimp only [gap]
      field_simp [hd.ne', he.ne'] <;> ring
    rw [hid]
    exact sub_pos.mpr hlt
  exact sub_pos.mp ((mul_pos_iff_of_pos_right (mul_pos hd he)).mp hdiv)

private abbrev ray (i : Fin 34) : Fin 24 → ℝ := ordinaryCostRay i

private def mixed : Fin 24 → ℝ := fun p => (mixedCostSeedInt p : ℝ)

private theorem ray_mem (i : Fin 34) : ray i ∈ realMatchingFunctionSpace := by
  change ordinaryCostRay i ∈ Set.range
    (fourMatchingEvaluation : (Fin 14 → ℝ) → (Fin 24 → ℝ))
  rw [four_matching_space_eq_ordinary_span]
  exact Submodule.subset_span ⟨i, rfl⟩

private theorem mixed_mem : mixed ∈ realMatchingFunctionSpace := by
  have heq : mixed = ray 10 + ray 7 + ray 17 - ray 25 := by
    funext p
    simp [mixed, mixedCostSeedInt, ray, ordinaryCostRay, Pi.add_apply, Pi.sub_apply]
  rw [heq]
  exact realMatchingFunctionSpace.sub_mem
    (realMatchingFunctionSpace.add_mem
      (realMatchingFunctionSpace.add_mem (ray_mem 10) (ray_mem 7)) (ray_mem 17))
    (ray_mem 25)

private theorem ray_square (i : Fin 34) (p : Fin 24) : ray i p ^ 2 = ray i p := by
  have h : ∀ i : Fin 34, ∀ p : Fin 24,
      ordinaryCostRayInt i p ^ 2 = ordinaryCostRayInt i p := by decide +kernel
  change (ordinaryCostRayInt i p : ℝ) ^ 2 = (ordinaryCostRayInt i p : ℝ)
  exact_mod_cast h i p

private theorem mixed_square_difference (p : Fin 24) :
    mixed p ^ 2 - mixed p = ray 23 p * (mixed p - ray 30 p - ray 31 p) := by
  have h : ∀ p : Fin 24, mixedCostSeedInt p ^ 2 - mixedCostSeedInt p =
      ordinaryCostRayInt 23 p *
        (mixedCostSeedInt p - ordinaryCostRayInt 30 p - ordinaryCostRayInt 31 p) := by
    decide +kernel
  unfold mixed ray ordinaryCostRay
  exact_mod_cast h p

private theorem weighted_matching_squares {n : ℕ} (w : Fin n → ℝ)
    (f : Fin n → Fin 24 → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hf : ∀ i, f i ∈ realMatchingFunctionSpace) :
    IsRealMatchingSOS (fun p => ∑ i, w i * f i p ^ 2) := by
  have hx (i : Fin n) : ∃ x : Fin 14 → ℝ, fourMatchingEvaluation x = f i := hf i
  choose x hxe using hx
  refine ⟨n, fun i => Real.sqrt (w i) • x i, fun p => ?_⟩
  apply Finset.sum_congr rfl
  intro i _
  have he : fourMatchingEvaluation (Real.sqrt (w i) • x i) p =
      Real.sqrt (w i) * fourMatchingEvaluation (x i) p := by
    fin_cases p <;> simp [fourMatchingEvaluation, Pi.smul_apply, smul_eq_mul] <;> ring
  rw [he, hxe i, mul_pow, Real.sq_sqrt (hw i)]

/-- The compensation inequality gives an explicit matching sum of squares. -/
theorem fourEightContactAffine_sos_of_budget {a b c d e : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hd : 0 < d) (he : 0 < e)
    (hbudget : 1 + 1 / d + 1 / e ≤ 4 * c) :
    IsRealMatchingSOS (fun p =>
      (mixedCostSeedInt p : ℝ) + a * ordinaryCostRay 7 p + b * ordinaryCostRay 13 p +
        c * ordinaryCostRay 23 p + d * ordinaryCostRay 30 p + e * ordinaryCostRay 31 p) := by
  let remainder := c - (1 + 1 / d + 1 / e) / 4
  let w : Fin 6 → ℝ := ![1, d, e, remainder, a, b]
  let f : Fin 6 → Fin 24 → ℝ :=
    ![mixed - (1 / 2 : ℝ) • ray 23, ray 30 + (1 / (2 * d)) • ray 23,
      ray 31 + (1 / (2 * e)) • ray 23, ray 23, ray 7, ray 13]
  have hrem : 0 ≤ remainder := by dsimp [remainder]; linarith only [hbudget]
  have hw : ∀ i, 0 ≤ w i := by
    intro i
    fin_cases i
    · norm_num [w]
    · exact hd.le
    · exact he.le
    · exact hrem
    · exact ha
    · exact hb
  have hf : ∀ i, f i ∈ realMatchingFunctionSpace := by
    intro i
    fin_cases i
    · exact realMatchingFunctionSpace.sub_mem mixed_mem
        (realMatchingFunctionSpace.smul_mem _ (ray_mem 23))
    · exact realMatchingFunctionSpace.add_mem (ray_mem 30)
        (realMatchingFunctionSpace.smul_mem _ (ray_mem 23))
    · exact realMatchingFunctionSpace.add_mem (ray_mem 31)
        (realMatchingFunctionSpace.smul_mem _ (ray_mem 23))
    · exact ray_mem 23
    · exact ray_mem 7
    · exact ray_mem 13
  have heq : (fun p =>
      mixed p + a * ray 7 p + b * ray 13 p + c * ray 23 p +
        d * ray 30 p + e * ray 31 p) = (fun p => ∑ i, w i * f i p ^ 2) := by
    funext p
    have hmixed : mixed p = mixed p ^ 2 -
        ray 23 p * (mixed p - ray 30 p - ray 31 p) := by
      linarith only [mixed_square_difference p]
    have hsq (m x y z : ℝ) : (m - x / 2) ^ 2 + d * (y + x / (2 * d)) ^ 2 +
          e * (z + x / (2 * e)) ^ 2 + remainder * x ^ 2 =
        m ^ 2 + c * x ^ 2 + d * y ^ 2 + e * z ^ 2 - x * (m - y - z) := by
      dsimp only [remainder]
      field_simp [hd.ne', he.ne'] <;> ring
    simp only [w, f, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
      Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, one_mul, add_zero,
      one_div, div_eq_mul_inv, ray_square]
    have hcomp := hsq (mixed p) (ray 23 p) (ray 30 p) (ray 31 p)
    simp only [ray_square, div_eq_mul_inv] at hcomp
    linear_combination hmixed - hcomp
  change IsRealMatchingSOS (fun p =>
    mixed p + a * ray 7 p + b * ray 13 p + c * ray 23 p +
      d * ray 30 p + e * ray 31 p)
  rw [heq]
  exact weighted_matching_squares w f hw hf

/-- Every root in the stated budget range has a matching sum of squares. -/
theorem fourEightContactAffine_sos_of_factor {a b c d e : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 < c) (hd : 0 < d) (he : 0 < e)
    (he₁ : e ≤ 1) (hfactor : fourEightContactAffineFactor a b c d e = 0) :
    IsRealMatchingSOS (fun p =>
      (mixedCostSeedInt p : ℝ) + a * ordinaryCostRay 7 p + b * ordinaryCostRay 13 p +
        c * ordinaryCostRay 23 p + d * ordinaryCostRay 30 p + e * ordinaryCostRay 31 p) :=
  fourEightContactAffine_sos_of_budget ha hb hd he
    (fourEightContactAffine_budget ha hb hc hd he he₁ hfactor).le

end

end MOC
