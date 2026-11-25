import MOC.FourSupportConeClassification
import MOC.RealMatchingSquares
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-! Two positive-height eight-contact families. Each determinant
factor implies a weighted sum of matching squares. -/

open BigOperators

namespace MOC

private theorem ordered_pair_margin {x y z t : ℝ}
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (ht : 0 < t)
    (hxy : x + y < 1) (hzx : z ≤ x) (hzy : z ≤ y)
    (hts : t ^ 2 = x * y * z) : 0 < 1 - x - y - z + 2 * t := by
  by_cases hsum : x + y + z ≤ 1
  · linarith only [hsum, ht]
  have hbound : z ≤ 4 * x * y := by
    by_cases hx4 : 1 ≤ 4 * x
    · exact hzy.trans (by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hx4 hy.le)
    · have hy4 : 1 ≤ 4 * y := by
        by_contra! hn
        linarith only [not_le.mp hx4, hn, hzx, lt_of_not_ge hsum]
      have hprod := mul_le_mul_of_nonneg_left hy4 hx.le
      nlinarith only [hzx, hprod]
  have hsq : z ^ 2 ≤ 4 * t ^ 2 := by
    have hprod := mul_le_mul_of_nonneg_right hbound hz.le
    nlinarith only [hprod, hts]
  have hzt : z ≤ 2 * t := by
    by_contra! hn
    have hprod := mul_pos (sub_pos.mpr hn) (show 0 < z + 2 * t by positivity)
    nlinarith only [hprod, hsq]
  linarith only [hxy, hzt]

private theorem pair_margin {x y z t : ℝ}
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (ht : 0 < t)
    (hxy : x + y < 1) (hxz : x + z < 1) (hyz : y + z < 1)
    (hts : t ^ 2 = x * y * z) : 0 < 1 - x - y - z + 2 * t := by
  by_cases hzx : z ≤ x
  · by_cases hzy : z ≤ y
    · exact ordered_pair_margin hx hy hz ht hxy hzx hzy hts
    · have ht' : t ^ 2 = x * z * y := by rw [hts]; ring
      have h := ordered_pair_margin hx hz hy ht hxz
        ((le_of_not_ge hzy).trans hzx) (le_of_not_ge hzy) ht'
      linarith only [h]
  · by_cases hxy' : x ≤ y
    · have ht' : t ^ 2 = y * z * x := by rw [hts]; ring
      have h := ordered_pair_margin hy hz hx ht hyz
        hxy' (le_of_not_ge hzx) ht'
      linarith only [h]
    · have ht' : t ^ 2 = x * z * y := by rw [hts]; ring
      have h := ordered_pair_margin hx hz hy ht hxz
        (le_of_not_ge hxy') ((le_of_not_ge hxy').trans (le_of_not_ge hzx)) ht'
      linarith only [h]

private def quadraticCoefficient (b c d : ℝ) : ℝ :=
  let x := b * c
  let y := b * d
  let z := c * d
  3 * (b + c + d + 1) + 2 * (x + y + z) -
    (x * (x + y) + y * (y + z) + z * (z + x) +
      b * (x + y) + c * (x + z) + d * (y + z))

/-- The mixed-sign factor of the scaled inverse-pencil determinant. -/
def fourEightContactTriangleFactor (a b c d e : ℝ) : ℝ :=
  let x := b * c
  let y := b * d
  let z := c * d
  let s := x + y + z
  let t := b * c * d
  let k := 1 + b + c + d + s
  let u := (b + 1) * (d + 1)
  let v := u * (c + 1)
  let q := quadraticCoefficient b c d
  a ^ 3 * (1 + e) * k +
    a ^ 2 * (q + e * (q + (x + z + c) ^ 2)) +
    a * (v * (3 - 2 * s + 3 * t) +
      e * u * (3 - 2 * s + 3 * c + 2 * c ^ 2 + t - x * z)) +
    v * (1 - s + 2 * t) + e * u * (1 - s + c + c ^ 2 + t - x * z)

private theorem triangle_bounds {b c d : ℝ} (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hB : b * (c + d) < 1) (hC : c * (b + d) < 1) (hD : d * (b + c) < 1) :
    let x := b * c
    let y := b * d
    let z := c * d
    let s := x + y + z
    0 < 1 - s + 2 * (b * c * d) ∧ 0 < 3 - 2 * s ∧
      0 < 1 - s + c ∧ x * z ≤ c ^ 2 ∧ 0 < quadraticCoefficient b c d := by
  let x := b * c
  let y := b * d
  let z := c * d
  let t := b * c * d
  have hx : 0 < x := mul_pos hb hc
  have hy : 0 < y := mul_pos hb hd
  have hz : 0 < z := mul_pos hc hd
  have ht : 0 < t := mul_pos hx hd
  have hxy : x + y < 1 := by dsimp [x, y]; nlinarith only [hB]
  have hxz : x + z < 1 := by
    dsimp [x, z]
    nlinarith only [hC]
  have hyz : y + z < 1 := by
    dsimp [y, z]
    nlinarith only [hD]
  have hts : t ^ 2 = x * y * z := by dsimp [t, x, y, z]; ring
  have h0 : 0 < 1 - (x + y + z) + 2 * t := by
    linarith only [pair_margin hx hy hz ht hxy hxz hyz hts]
  have hs : 0 < 3 - 2 * (x + y + z) := by linarith only [hxy, hxz, hyz]
  have hy1 : y < 1 := by linarith only [hx, hxy]
  have hxzC : x * z ≤ c ^ 2 := by
    have hprod := mul_le_mul_of_nonneg_right hy1.le (sq_nonneg c)
    dsimp [x, z, y] at hprod ⊢
    nlinarith only [hprod]
  have hcMargin : 0 < 1 - (x + y + z) + c := by
    by_cases hb1 : b ≤ 1
    · have hx1 : x ≤ c := by
        simpa only [x, one_mul] using mul_le_mul_of_nonneg_right hb1 hc.le
      linarith only [hx1, hyz]
    · have hd1 : d ≤ 1 := by
        have hbd : d ≤ y := by
          simpa only [y, one_mul] using
            mul_le_mul_of_nonneg_right (le_of_not_ge hb1) hd.le
        exact (hbd.trans_lt hy1).le
      have hz1 : z ≤ c := by
        simpa only [z, mul_one] using mul_le_mul_of_nonneg_left hd1 hc.le
      linarith only [hz1, hxy]
  have hq : 0 < quadraticCoefficient b c d := by
    have hX := mul_le_mul_of_nonneg_left hxy.le hx.le
    have hY := mul_le_mul_of_nonneg_left hyz.le hy.le
    have hZ := mul_le_mul_of_nonneg_left (by linarith only [hxz] : z + x ≤ 1) hz.le
    have hb' := mul_le_mul_of_nonneg_left hxy.le hb.le
    have hc' := mul_le_mul_of_nonneg_left hxz.le hc.le
    have hd' := mul_le_mul_of_nonneg_left hyz.le hd.le
    change 0 < 3 * (b + c + d + 1) + 2 * (x + y + z) -
      (x * (x + y) + y * (y + z) + z * (z + x) +
        b * (x + y) + c * (x + z) + d * (y + z))
    nlinarith only [hX, hY, hZ, hb', hc', hd', hx, hy, hz, hb, hc, hd]
  exact ⟨h0, hs, hcMargin, hxzC, hq⟩

/-- A zero of the factor forces one of the three Gram bounds. -/
theorem fourEightContactTriangleFactor_forces_budget {a b c d e : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (he : 0 < e)
    (hzero : fourEightContactTriangleFactor a b c d e = 0) :
    1 ≤ b * (c + d) ∨ 1 ≤ c * (b + d) ∨ 1 ≤ d * (b + c) := by
  by_contra! h
  obtain ⟨hB, hC, hD⟩ := h
  let x := b * c
  let y := b * d
  let z := c * d
  let t := b * c * d
  have hx : 0 < x := mul_pos hb hc
  have hy : 0 < y := mul_pos hb hd
  have hz : 0 < z := mul_pos hc hd
  have ht : 0 < t := mul_pos hx hd
  obtain ⟨h0, hs, hcMargin, hxzC, hq⟩ := triangle_bounds hb hc hd hB hC hD
  change 0 < 1 - (x + y + z) + 2 * t at h0
  change 0 < 3 - 2 * (x + y + z) at hs
  change 0 < 1 - (x + y + z) + c at hcMargin
  change x * z ≤ c ^ 2 at hxzC
  have h1 : 0 < 1 - (x + y + z) + c + c ^ 2 + t - x * z := by
    linarith only [hcMargin, hxzC, ht]
  have h2 : 0 < 3 - 2 * (x + y + z) + 3 * c + 2 * c ^ 2 + t - x * z := by
    linarith only [hs, hc, sq_nonneg c, hxzC, ht]
  have hpos : 0 < fourEightContactTriangleFactor a b c d e := by
    unfold fourEightContactTriangleFactor
    change 0 < a ^ 3 * (1 + e) * (1 + b + c + d + (x + y + z)) +
      a ^ 2 * (quadraticCoefficient b c d +
        e * (quadraticCoefficient b c d + (x + z + c) ^ 2)) +
      a * ((b + 1) * (d + 1) * (c + 1) * (3 - 2 * (x + y + z) + 3 * t) +
        e * ((b + 1) * (d + 1)) * (3 - 2 * (x + y + z) + 3 * c + 2 * c ^ 2 + t - x * z)) +
      (b + 1) * (d + 1) * (c + 1) * (1 - (x + y + z) + 2 * t) +
      e * ((b + 1) * (d + 1)) * (1 - (x + y + z) + c + c ^ 2 + t - x * z)
    have h3 : 0 < 3 - 2 * (x + y + z) + 3 * t := by linarith only [hs, ht]
    positivity
  exact hpos.ne' hzero

/-- The mixed-sign factor for the ordinary rays `7, 18, 20, 23, 28`. -/
def fourEightContactExtendedTriangleFactor (a b c d e : ℝ) : ℝ :=
  let x := b * e
  let y := b * d
  let z := e * d
  let s := x + y + z
  let t := b * e * d
  let k := b + e + d + s
  let u := (b + 1) * (d + 1)
  let v := u * (e + 1)
  let q := quadraticCoefficient b e d
  let r := 2 * y + b * e ^ 2 + x + 2 * b + d * e ^ 2 + z + 2 * d + e ^ 2
  a * (a + c) * (a + c - e * a * c) +
    a ^ 3 * k + a ^ 2 * (q + c * r) +
    a * (v * (3 - 2 * s + 3 * t) +
      c * u * (4 - 2 * s + 3 * e + 2 * e ^ 2 + t - e * (x + z)) +
      c ^ 2 * (u * (e ^ 2 + 1) - 1)) +
    v * (1 - s + 2 * t) +
    c * u * (2 - 2 * s + 2 * t + 2 * e + e ^ 2 + x * z - e * (x + z)) +
    c ^ 2 * u * (1 - s + e + e ^ 2 + t - x * z)

/-- A zero of the factor forces a triangle or signed star Gram bound. -/
theorem fourEightContactExtendedTriangleFactor_forces_budget {a b c d e : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (he : 0 < e)
    (hzero : fourEightContactExtendedTriangleFactor a b c d e = 0) :
    (1 ≤ b * (e + d) ∨ 1 ≤ e * (b + d) ∨ 1 ≤ d * (b + e)) ∨
      a + c ≤ e * a * c := by
  by_contra! h
  obtain ⟨⟨hB, hE, hD⟩, hA⟩ := h
  let x := b * e
  let y := b * d
  let z := e * d
  let t := b * e * d
  have hx : 0 < x := mul_pos hb he
  have hy : 0 < y := mul_pos hb hd
  have hz : 0 < z := mul_pos he hd
  have ht : 0 < t := mul_pos hx hd
  obtain ⟨h0, hs, heMargin, hxzE, hq⟩ := triangle_bounds hb he hd hB hE hD
  change 0 < 1 - (x + y + z) + 2 * t at h0
  change 0 < 3 - 2 * (x + y + z) at hs
  change 0 < 1 - (x + y + z) + e at heMargin
  change x * z ≤ e ^ 2 at hxzE
  have hxz : x + z < 1 := by dsimp [x, z]; nlinarith only [hE]
  have heBound : e * (x + z) ≤ e := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hxz.le he.le
  have h1 : 0 < 1 - (x + y + z) + e + e ^ 2 + t - x * z := by
    linarith only [heMargin, hxzE, ht]
  have h2 : 0 < 4 - 2 * (x + y + z) + 3 * e + 2 * e ^ 2 + t - e * (x + z) := by
    linarith only [hs, he, sq_nonneg e, heBound, ht]
  have h3 :
      0 < 2 - 2 * (x + y + z) + 2 * t + 2 * e + e ^ 2 + x * z - e * (x + z) := by
    linarith only [h0, heMargin, heBound, sq_nonneg e, (mul_pos hx hz).le]
  have h4 : 0 < (b + 1) * (d + 1) * (e ^ 2 + 1) - 1 := by
    have heq : (b + 1) * (d + 1) * (e ^ 2 + 1) - 1 =
      (b + d + b * d) * (e ^ 2 + 1) + e ^ 2 := by ring
    rw [heq]
    positivity
  have hpos : 0 < fourEightContactExtendedTriangleFactor a b c d e := by
    unfold fourEightContactExtendedTriangleFactor
    change 0 < a * (a + c) * (a + c - e * a * c) +
      a ^ 3 * (b + e + d + (x + y + z)) +
      a ^ 2 * (quadraticCoefficient b e d +
        c * (2 * y + b * e ^ 2 + x + 2 * b + d * e ^ 2 + z + 2 * d + e ^ 2)) +
      a * ((b + 1) * (d + 1) * (e + 1) * (3 - 2 * (x + y + z) + 3 * t) +
        c * ((b + 1) * (d + 1)) *
          (4 - 2 * (x + y + z) + 3 * e + 2 * e ^ 2 + t - e * (x + z)) +
        c ^ 2 * ((b + 1) * (d + 1) * (e ^ 2 + 1) - 1)) +
      (b + 1) * (d + 1) * (e + 1) * (1 - (x + y + z) + 2 * t) +
      c * ((b + 1) * (d + 1)) *
        (2 - 2 * (x + y + z) + 2 * t + 2 * e + e ^ 2 + x * z - e * (x + z)) +
      c ^ 2 * ((b + 1) * (d + 1)) * (1 - (x + y + z) + e + e ^ 2 + t - x * z)
    have h5 : 0 < 3 - 2 * (x + y + z) + 3 * t := by linarith only [hs, ht]
    have h6 : 0 < a + c - e * a * c := sub_pos.mpr hA
    positivity
  exact hpos.ne' hzero

private abbrev ray (i : Fin 34) := ordinaryCostRay i

private def seed (p : Fin 24) : ℝ := mixedCostSeedInt p

private theorem mixed_eq_seed (p : Fin 24) : mixedCostRay 0 p = seed p := by
  have h : ∀ p : Fin 24, mixedCostRayInt 0 p = mixedCostSeedInt p := by decide +kernel
  exact_mod_cast h p

private def exceptional (p : Fin 24) : ℝ := if p = 5 then 1 else 0

private theorem ray_mem (i : Fin 34) : ray i ∈ realMatchingFunctionSpace := by
  change ordinaryCostRay i ∈ Set.range
    (fourMatchingEvaluation : (Fin 14 → ℝ) → (Fin 24 → ℝ))
  rw [four_matching_space_eq_ordinary_span]
  exact Submodule.subset_span ⟨i, rfl⟩

private theorem seed_mem : seed ∈ realMatchingFunctionSpace := by
  have h : seed = ray 10 + ray 7 + ray 17 - ray 25 := by
    funext p
    simp [seed, mixedCostSeedInt, ray, ordinaryCostRay, Pi.add_apply, Pi.sub_apply]
  rw [h]
  exact realMatchingFunctionSpace.sub_mem (realMatchingFunctionSpace.add_mem
    (realMatchingFunctionSpace.add_mem (ray_mem 10) (ray_mem 7)) (ray_mem 17)) (ray_mem 25)

private theorem ray_sq (i : Fin 34) (p : Fin 24) : ray i p ^ 2 = ray i p := by
  have h : ∀ i : Fin 34, ∀ p : Fin 24,
      ordinaryCostRayInt i p ^ 2 = ordinaryCostRayInt i p := by decide +kernel
  change (ordinaryCostRayInt i p : ℝ)^2 = ordinaryCostRayInt i p
  exact_mod_cast h i p

private theorem seed_sq (p : Fin 24) : seed p ^ 2 - seed p = 2 * exceptional p := by
  have h : ∀ p : Fin 24, mixedCostSeedInt p ^ 2 - mixedCostSeedInt p =
      2 * (if p = 5 then (1 : ℤ) else 0) := by decide +kernel
  by_cases hp : p = 5
  · have he := h p
    rw [if_pos hp] at he
    unfold seed exceptional
    rw [if_pos hp]
    exact_mod_cast he
  · have he := h p
    rw [if_neg hp] at he
    unfold seed exceptional
    rw [if_neg hp]
    exact_mod_cast he

private theorem weighted_squares {n : ℕ} (w : Fin n → ℝ) (f : Fin n → Fin 24 → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hf : ∀ i, f i ∈ realMatchingFunctionSpace) :
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

private theorem star_sos (r s i j k : Fin 34) {a e x y z u v : ℝ}
    (ha : 0 ≤ a) (he : 0 ≤ e) (hy : 0 < y) (hz : 0 < z)
    (hbudget : u ^ 2 / y + v ^ 2 / z ≤ x)
    (hcross : ∀ p, u * (ray i p * ray j p) + v * (ray i p * ray k p) = exceptional p) :
    IsRealMatchingSOS
      (fun p => seed p + a * ray r p + e * ray s p + x * ray i p + y * ray j p + z * ray k p) := by
  let weights : Fin 6 → ℝ := ![1, a, e, x - (u ^ 2 / y + v ^ 2 / z), y, z]
  let factors : Fin 6 → Fin 24 → ℝ :=
    ![seed, ray r, ray s, ray i, ray j - (u / y) • ray i, ray k - (v / z) • ray i]
  have hw (l : Fin 6) : 0 ≤ weights l := by
    fin_cases l <;> simp [weights, ha, he, hy.le, hz.le, sub_nonneg.mpr hbudget]
  have hf (l : Fin 6) : factors l ∈ realMatchingFunctionSpace := by
    fin_cases l
    · exact seed_mem
    · exact ray_mem r
    · exact ray_mem s
    · exact ray_mem i
    · exact realMatchingFunctionSpace.sub_mem (ray_mem j)
        (realMatchingFunctionSpace.smul_mem _ (ray_mem i))
    · exact realMatchingFunctionSpace.sub_mem (ray_mem k)
        (realMatchingFunctionSpace.smul_mem _ (ray_mem i))
  have hform (p : Fin 24) : ∑ l, weights l * factors l p ^ 2 =
      seed p + a * ray r p + e * ray s p + x * ray i p + y * ray j p + z * ray k p := by
    calc
      _ = seed p ^ 2 + a * ray r p ^ 2 + e * ray s p ^ 2 +
          x * ray i p ^ 2 + y * ray j p ^ 2 + z * ray k p ^ 2 -
          2 * (u * (ray i p * ray j p) + v * (ray i p * ray k p)) := by
        simp [weights, factors, Fin.sum_univ_succ, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        field_simp [hy.ne', hz.ne'] <;> ring
      _ = _ := by
        rw [ray_sq r, ray_sq s, ray_sq i, ray_sq j, ray_sq k, hcross p]
        linarith only [seed_sq p]
  have h := weighted_squares weights factors hw hf
  exact (funext hform) ▸ h

private def triangleRay (i : Fin 3) : Fin 34 := ![18, 23, 28] i

private theorem triangle_cross (i j : Fin 3) (hij : i ≠ j) (p : Fin 24) :
    ray (triangleRay i) p * ray (triangleRay j) p = exceptional p := by
  have h : ∀ i j : Fin 3, ∀ p : Fin 24, i ≠ j →
      ordinaryCostRayInt (triangleRay i) p * ordinaryCostRayInt (triangleRay j) p =
        (if p = 5 then (1 : ℤ) else 0) := by decide +kernel
  have he := h i j p hij
  by_cases hp : p = 5
  · rw [if_pos hp] at he
    unfold ray ordinaryCostRay exceptional
    rw [if_pos hp]
    exact_mod_cast he
  · rw [if_neg hp] at he
    unfold ray ordinaryCostRay exceptional
    rw [if_neg hp]
    exact_mod_cast he

private theorem triangle_star_sos (r s : Fin 34) (i j k : Fin 3)
    (hij : i ≠ j) (hik : i ≠ k) {a e x y z : ℝ}
    (ha : 0 ≤ a) (he : 0 ≤ e) (hy : 0 < y) (hz : 0 < z)
    (hbudget : 1 ≤ x * (y + z)) :
    IsRealMatchingSOS (fun p => seed p + a * ray r p + e * ray s p +
      x * ray (triangleRay i) p + y * ray (triangleRay j) p + z * ray (triangleRay k) p) := by
  have hs : 0 < y + z := add_pos hy hz
  have hcapacity : (y / (y + z)) ^ 2 / y + (z / (y + z)) ^ 2 / z ≤ x := by
    have hidentity : (y / (y + z)) ^ 2 / y + (z / (y + z)) ^ 2 / z = 1 / (y + z) := by
      field_simp [hy.ne', hz.ne', hs.ne'] <;> ring
    rw [hidentity, div_le_iff₀ hs]
    exact hbudget
  apply star_sos r s (triangleRay i) (triangleRay j) (triangleRay k) ha he hy hz hcapacity
  intro p
  rw [triangle_cross i j hij p, triangle_cross i k hik p]
  field_simp [hs.ne'] <;> ring

private theorem triangle_sos (r s : Fin 34) {a e x y z : ℝ}
    (ha : 0 ≤ a) (he : 0 ≤ e) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hbudget : 1 ≤ x * (y + z) ∨ 1 ≤ y * (x + z) ∨ 1 ≤ z * (x + y)) :
    IsRealMatchingSOS (fun p => seed p + a * ray r p + e * ray s p +
      x * ray 18 p + y * ray 23 p + z * ray 28 p) := by
  rcases hbudget with h | h | h
  · exact triangle_star_sos r s 0 1 2 (by decide) (by decide) ha he hy hz h
  · convert triangle_star_sos r s 1 0 2 (by decide) (by decide) ha he hx hz h using 1
    funext p
    simp [triangleRay] <;> ring
  · convert triangle_star_sos r s 2 0 1 (by decide) (by decide) ha he hx hy h using 1
    funext p
    simp [triangleRay] <;> ring

/-- The triangle factor gives matching squares for the five indicated rays. -/
theorem fourEightContactTriangle_matching_sos {a b c d e : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (he : 0 < e)
    (hzero : fourEightContactTriangleFactor a b c d e = 0) :
    IsRealMatchingSOS (fun p => mixedCostRay 0 p + a * ordinaryCostRay 13 p +
      e * ordinaryCostRay 30 p + b * ordinaryCostRay 18 p +
      c * ordinaryCostRay 23 p + d * ordinaryCostRay 28 p) := by
  simpa only [mixed_eq_seed] using triangle_sos 13 30 ha.le he.le hb hc hd
    (fourEightContactTriangleFactor_forces_budget ha hb hc hd he hzero)

private theorem signed_cross (p : Fin 24) :
    ray 28 p * ray 7 p - ray 28 p * ray 20 p = exceptional p := by
  have h : ∀ p : Fin 24, ordinaryCostRayInt 28 p * ordinaryCostRayInt 7 p -
      ordinaryCostRayInt 28 p * ordinaryCostRayInt 20 p =
        (if p = 5 then (1 : ℤ) else 0) := by decide +kernel
  have he := h p
  by_cases hp : p = 5
  · rw [if_pos hp] at he
    unfold ray ordinaryCostRay exceptional
    rw [if_pos hp]
    exact_mod_cast he
  · rw [if_neg hp] at he
    unfold ray ordinaryCostRay exceptional
    rw [if_neg hp]
    exact_mod_cast he

/-- The extended factor gives matching squares by a triangle or a signed star. -/
theorem fourEightContactExtendedTriangle_matching_sos {a b c d e : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (he : 0 < e)
    (hzero : fourEightContactExtendedTriangleFactor a b c d e = 0) :
    IsRealMatchingSOS (fun p => mixedCostRay 0 p + a * ordinaryCostRay 7 p +
      c * ordinaryCostRay 20 p + b * ordinaryCostRay 18 p +
      d * ordinaryCostRay 23 p + e * ordinaryCostRay 28 p) := by
  simp only [mixed_eq_seed]
  rcases fourEightContactExtendedTriangleFactor_forces_budget ha hb hc hd he hzero with ht | hs
  · have ht' : 1 ≤ b * (d + e) ∨ 1 ≤ d * (b + e) ∨ 1 ≤ e * (b + d) := by
      rcases ht with h | h | h
      · exact Or.inl (by simpa only [add_comm e d] using h)
      · exact Or.inr (Or.inr h)
      · exact Or.inr (Or.inl h)
    exact triangle_sos 7 20 ha.le hc.le hb hd he ht'
  · have hbudget : (1 : ℝ) ^ 2 / a + (-1) ^ 2 / c ≤ e := by
      apply (le_of_mul_le_mul_right ?_ (mul_pos ha hc))
      have heq : ((1 : ℝ) ^ 2 / a + (-1) ^ 2 / c) * (a * c) = a + c := by
        field_simp [ha.ne', hc.ne'] <;> ring
      rw [heq]
      nlinarith only [hs]
    have hcross (p : Fin 24) :
        1 * (ray 28 p * ray 7 p) + (-1) * (ray 28 p * ray 20 p) = exceptional p := by
      linarith only [signed_cross p]
    convert star_sos 18 23 28 7 20 hb.le hd.le ha hc hbudget hcross using 1
    funext p
    ring

end MOC
