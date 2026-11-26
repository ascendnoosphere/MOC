import MOC.FourMixedRayCancellation
import MOC.FourSevenContactAffineElimination
import Mathlib.Tactic

/-! Matching sums of squares with one central feature and several leaves.
The order-four wall and a canonical seven-contact family give two instances. -/

open BigOperators Matrix

namespace MOC

noncomputable section

/-- A central matching function can compensate all leaves when its weight
covers the sum of the squared couplings divided by their leaf weights. -/
theorem fourMatchingSOS_of_star {n : ℕ} (b : ℝ) (x : Fin 24 → ℝ)
    (d e : Fin n → ℝ) (f : Fin n → Fin 24 → ℝ)
    (hx : x ∈ realMatchingFunctionSpace) (hf : ∀ i, f i ∈ realMatchingFunctionSpace)
    (hd : ∀ i, 0 < d i) (hb : (∑ i, (e i)^2 / d i) ≤ b) :
    IsRealMatchingSOS (fun p =>
      b * (x p)^2 + (∑ i, d i * (f i p)^2) - 2 * x p * (∑ i, e i * f i p)) := by
  let weights : Fin (n + 1) → ℝ := Fin.cons (b - ∑ i, (e i)^2 / d i) d
  let features : Fin (n + 1) → Fin 24 → ℝ :=
    Fin.cons x (fun i => f i - (e i / d i) • x)
  have hw (i : Fin (n + 1)) : 0 ≤ weights i := by
    refine Fin.cases ?_ (fun j => (hd j).le) i
    exact sub_nonneg.mpr hb
  have hg (i : Fin (n + 1)) : features i ∈ realMatchingFunctionSpace := by
    refine Fin.cases hx (fun j => ?_) i
    exact realMatchingFunctionSpace.sub_mem (hf j) (realMatchingFunctionSpace.smul_mem _ hx)
  have heq (p : Fin 24) :
      (∑ i, weights i * (features i p)^2) =
        b * (x p)^2 + (∑ i, d i * (f i p)^2) - 2 * x p * (∑ i, e i * f i p) := by
    have hleaf (i : Fin n) :
        d i * (f i p - (e i / d i) * x p)^2 =
          (d i * (f i p)^2 - (2 * x p) * (e i * f i p)) + (e i)^2 / d i * (x p)^2 := by
      field_simp [(hd i).ne'] <;> ring
    simp only [Fin.sum_univ_succ, weights, features, Fin.cons_zero, Fin.cons_succ,
      Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hleaf, Finset.sum_add_distrib,
      Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
    ring
  simpa only [heq] using isRealMatchingSOS_weighted weights features hw hg

private abbrev ray (r : Fin 34) : Fin 24 → ℝ := ordinaryCostRay r

private theorem ray_mem (r : Fin 34) : ray r ∈ realMatchingFunctionSpace :=
  ordinaryCostRay_mem_realMatchingFunctionSpace r

private theorem one_mem : (1 : Fin 24 → ℝ) ∈ realMatchingFunctionSpace := by
  have h : ∀ p : Fin 24, ordinaryCostRayInt 0 p + ordinaryCostRayInt 1 p +
      ordinaryCostRayInt 2 p + ordinaryCostRayInt 3 p = 1 := by decide +kernel
  have he : (1 : Fin 24 → ℝ) = ray 0 + ray 1 + ray 2 + ray 3 := by
    funext p
    change (1 : ℝ) = (ordinaryCostRayInt 0 p : ℝ) + (ordinaryCostRayInt 1 p : ℝ) +
      (ordinaryCostRayInt 2 p : ℝ) + (ordinaryCostRayInt 3 p : ℝ)
    exact_mod_cast (h p).symm
  rw [he]
  exact realMatchingFunctionSpace.add_mem
    (realMatchingFunctionSpace.add_mem
      (realMatchingFunctionSpace.add_mem (ray_mem 0) (ray_mem 1)) (ray_mem 2)) (ray_mem 3)

private def wallInt (p : Fin 24) : ℤ :=
  1 - ordinaryCostRayInt 0 p - ordinaryCostRayInt 1 p - ordinaryCostRayInt 4 p +
    ordinaryCostRayInt 10 p + ordinaryCostRayInt 16 p - ordinaryCostRayInt 23 p

/-- The base cost in the order-four wall test. The indices use the ordinary
matching rays, starting at zero. -/
def fourWallCost : Fin 24 → ℝ := fun p => wallInt p

theorem fourWallCost_mem : fourWallCost ∈ realMatchingFunctionSpace := by
  have he : fourWallCost = 1 - ray 0 - ray 1 - ray 4 + ray 10 + ray 16 - ray 23 := by
    funext p
    simp only [fourWallCost, wallInt, ordinaryCostRay, Int.cast_sub, Int.cast_add, Int.cast_one,
      Pi.add_apply, Pi.sub_apply, Pi.one_apply]
  rw [he]
  exact realMatchingFunctionSpace.sub_mem
    (realMatchingFunctionSpace.add_mem
      (realMatchingFunctionSpace.add_mem
        (realMatchingFunctionSpace.sub_mem
          (realMatchingFunctionSpace.sub_mem
            (realMatchingFunctionSpace.sub_mem one_mem (ray_mem 0)) (ray_mem 1)) (ray_mem 4))
        (ray_mem 10)) (ray_mem 16)) (ray_mem 23)

private theorem wallCancellation (p : Fin 24) :
    (fourWallCost p)^2 + 2 * ray 27 p * (ray 29 p - ray 5 p) = fourWallCost p := by
  have h : ∀ p : Fin 24, wallInt p ^ 2 + 2 * ordinaryCostRayInt 27 p *
      (ordinaryCostRayInt 29 p - ordinaryCostRayInt 5 p) = wallInt p := by decide +kernel
  change (wallInt p : ℝ)^2 + 2 * (ordinaryCostRayInt 27 p : ℝ) *
    ((ordinaryCostRayInt 29 p : ℝ) - (ordinaryCostRayInt 5 p : ℝ)) = (wallInt p : ℝ)
  exact_mod_cast h p

/-- The wall budget gives a matching sum of squares for all positive leaf
weights, including equality in the budget. -/
theorem fourWallCost_sos (a c q : ℝ) (hc : 0 < c) (hq : 0 < q)
    (ha : 1 / c + 1 / q ≤ a) :
    IsRealMatchingSOS (fourWallCost + a • ray 27 + c • ray 29 + q • ray 5) := by
  let d : Fin 3 → ℝ := ![c, q, 1]
  let e : Fin 3 → ℝ := ![-1, 1, 0]
  let f : Fin 3 → Fin 24 → ℝ := ![ray 29, ray 5, fourWallCost]
  have hd (i : Fin 3) : 0 < d i := by
    fin_cases i
    · exact hc
    · exact hq
    · exact zero_lt_one
  have hf (i : Fin 3) : f i ∈ realMatchingFunctionSpace := by
    fin_cases i
    · exact ray_mem 29
    · exact ray_mem 5
    · exact fourWallCost_mem
  have hweights : (∑ i, (e i)^2 / d i) = 1 / c + 1 / q := by
    norm_num [d, e, Fin.sum_univ_succ]
  have he : fourWallCost + a • ray 27 + c • ray 29 + q • ray 5 =
      (fun p => a * (ray 27 p)^2 + (∑ i, d i * (f i p)^2) -
        2 * ray 27 p * (∑ i, e i * f i p)) := by
    funext p
    simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul, d, e, f, Fin.sum_univ_succ, ordinaryCostRay_sq]
    linear_combination -(wallCancellation p)
  rw [he]
  exact fourMatchingSOS_of_star a (ray 27) d e f (ray_mem 27) hf hd (hweights.trans_le ha)

private theorem wall_amplitude_bound (h A B C : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hcert : ∀ c q : ℝ, 0 < c → 0 < q →
      0 ≤ h + A^2 / c + c * B^2 + A^2 / q + q * C^2) :
    0 ≤ h + 2 * A * (B + C) := by
  by_contra! hn
  let gap := -(h + 2 * A * (B + C))
  let K := 4 * A + 2 * B + 2 * C + 4
  have hg : 0 < gap := neg_pos.mpr hn
  have hK : 0 < K := by dsimp [K]; positivity
  let t := min 1 (gap / (2 * K))
  have ht : 0 < t := lt_min zero_lt_one (div_pos hg (by positivity))
  have ht1 : t ≤ 1 := min_le_left _ _
  have ht2 : t * (2 * K) ≤ gap :=
    (le_div_iff₀ (show 0 < 2 * K by positivity)).mp (min_le_right _ _)
  have hA' : 0 < A + t := add_pos_of_nonneg_of_pos hA ht
  have hB' : 0 < B + t := add_pos_of_nonneg_of_pos hB ht
  have hC' : 0 < C + t := add_pos_of_nonneg_of_pos hC ht
  let c := (A + t) / (B + t)
  let q := (A + t) / (C + t)
  have hc : 0 < c := div_pos hA' hB'
  have hq : 0 < q := div_pos hA' hC'
  have hs (X : ℝ) (hX : 0 ≤ X) : X^2 ≤ (X + t)^2 := by
    nlinarith only [mul_nonneg hX ht.le, sq_nonneg t]
  have hc_eq : (A + t)^2 / c + c * (B + t)^2 = 2 * (A + t) * (B + t) := by
    dsimp [c]
    field_simp [hA'.ne', hB'.ne'] <;> ring
  have hq_eq : (A + t)^2 / q + q * (C + t)^2 = 2 * (A + t) * (C + t) := by
    dsimp [q]
    field_simp [hA'.ne', hC'.ne'] <;> ring
  have hnew : 0 ≤ h + 2 * (A + t) * (B + C + 2 * t) := by
    have hca := div_le_div_of_nonneg_right (hs A hA) hc.le
    have hcb := mul_le_mul_of_nonneg_left (hs B hB) hc.le
    have hqa := div_le_div_of_nonneg_right (hs A hA) hq.le
    have hqc := mul_le_mul_of_nonneg_left (hs C hC) hq.le
    linarith only [hcert c q hc hq, hca, hcb, hqa, hqc, hc_eq, hq_eq,
      (show 2 * (A + t) * (B + C + 2 * t) =
        2 * (A + t) * (B + t) + 2 * (A + t) * (C + t) by ring)]
  have ht_sq : t * t ≤ t := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left ht1 ht.le
  have hdiff : h + 2 * (A + t) * (B + C + 2 * t) ≤ -gap + K * t := by
    dsimp [gap, K]
    nlinarith only [ht_sq]
  have hKt : K * t ≤ gap / 2 := (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).2 (by
    calc
      K * t * 2 = t * (2 * K) := by ring
      _ ≤ gap := ht2)
  have hbound : gap ≤ K * t :=
    sub_nonneg.mp (by simpa only [sub_eq_add_neg, add_comm] using hnew.trans hdiff)
  exact (not_lt_of_ge (hbound.trans hKt)) (half_lt_self hg)

/-- The wall bound for the three minor amplitudes, including zero amplitudes,
under the alternating correction hypothesis on the signed moment. -/
theorem fourWallCost_amplitude_nonneg (U : Matrix (Fin 4) (Fin 4) ℂ) (hU : IsUnitary U)
    (t : ℝ) (hm : (realMatchingMoment (fun p =>
      realSignedWeight U (fourPerm p).symm + t * matchingSign p)).PosSemidef) :
    let amplitude (r : Fin 34) := Real.sqrt (fourSupportCostValue U (ray r))
    0 ≤ fourSupportCostValue U fourWallCost + 2 * amplitude 27 * (amplitude 29 + amplitude 5) := by
  intro amplitude
  have hs (r : Fin 34) : (amplitude r)^2 = fourSupportCostValue U (ray r) := by
    apply Real.sq_sqrt
    rw [fourSupportCostValue_ordinaryRay U hU]
    exact subsetMinorSq_nonneg _ _ _
  apply wall_amplitude_bound _ _ _ _ (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  intro c q hc hq
  let a := 1 / c + 1 / q
  let g := fourWallCost + a • ray 27 + c • ray 29 + q • ray 5
  have hg : g ∈ realMatchingFunctionSpace :=
    realMatchingFunctionSpace.add_mem
      (realMatchingFunctionSpace.add_mem
        (realMatchingFunctionSpace.add_mem fourWallCost_mem
          (realMatchingFunctionSpace.smul_mem a (ray_mem 27)))
        (realMatchingFunctionSpace.smul_mem c (ray_mem 29)))
      (realMatchingFunctionSpace.smul_mem q (ray_mem 5))
  have h : 0 ≤ fourSupportCostValue U g :=
    realMatchingSOS_pairing_nonneg_of_positiveMoment _ t hg
      (fourWallCost_sos a c q hc hq le_rfl) hm
  rw [hs 27, hs 29, hs 5]
  dsimp only [g, a] at h
  simp only [map_add, map_smul, smul_eq_mul] at h
  linarith only [h, (show (1 / c + 1 / q) * fourSupportCostValue U (ray 27) =
    fourSupportCostValue U (ray 27) / c + fourSupportCostValue U (ray 27) / q by
      simp only [div_eq_mul_inv, one_mul]
      ring)]

private def seed (p : Fin 24) : ℝ := mixedCostSeedInt p

private theorem seed_mem : seed ∈ realMatchingFunctionSpace := by
  have he : seed = ray 10 + ray 7 + ray 17 - ray 25 := by
    funext p
    simp only [seed, mixedCostSeedInt, ordinaryCostRay, Pi.add_apply, Pi.sub_apply,
      Int.cast_add, Int.cast_sub]
  rw [he]
  exact realMatchingFunctionSpace.sub_mem
    (realMatchingFunctionSpace.add_mem
      (realMatchingFunctionSpace.add_mem (ray_mem 10) (ray_mem 7)) (ray_mem 17)) (ray_mem 25)

private theorem seedCancellation (p : Fin 24) :
    (seed p)^2 - 2 * ray 18 p * (ray 13 p - ray 27 p) = seed p := by
  have h : ∀ p : Fin 24, mixedCostSeedInt p ^ 2 - 2 * ordinaryCostRayInt 18 p *
      (ordinaryCostRayInt 13 p - ordinaryCostRayInt 27 p) = mixedCostSeedInt p := by
    decide +kernel
  change (mixedCostSeedInt p : ℝ)^2 - 2 * (ordinaryCostRayInt 18 p : ℝ) *
    ((ordinaryCostRayInt 13 p : ℝ) - (ordinaryCostRayInt 27 p : ℝ)) = (mixedCostSeedInt p : ℝ)
  exact_mod_cast h p

/-- The mixed factor for the seven-contact support with ordinary ray
indices 7, 13, 18, 20, 27 and 30. It is independent of the weights on 20 and 30. -/
def fourSevenContactStarFactor (a b c e : ℝ) : ℝ :=
  (1 + c + c*e + c^2*e + b*c + a + a*e + a*c + a*c*e + a*b + a*b*c) +
    (e + b - b*c*e)

/-- A nonpositive value of the mixed factor supplies the two-leaf budget.
The determinant identity for this factor is a separate premise when
applying the result to a spectral gap. -/
theorem fourSevenContactStarFactor_budget {a b c e : ℝ}
    (ha : 0 ≤ a) (hb : 0 < b) (hc : 0 ≤ c) (he : 0 < e)
    (hfactor : fourSevenContactStarFactor a b c e ≤ 0) :
    1 / b + 1 / e ≤ c := by
  have hrest : 0 ≤ 1 + c + c*e + c^2*e + b*c + a + a*e + a*c + a*c*e + a*b + a*b*c :=
    by positivity
  have hcross : e + b ≤ b*c*e := by
    unfold fourSevenContactStarFactor at hfactor
    linarith only [hrest, hfactor]
  refine le_of_mul_le_mul_right ?_ (mul_pos hb he)
  calc
    (1 / b + 1 / e) * (b * e) = e + b := by field_simp [hb.ne', he.ne'] <;> ring
    _ ≤ b * c * e := hcross
    _ = c * (b * e) := by ring

/-- Closure in the matching-square cone for this factor branch, including
arbitrary nonnegative coefficients on the other two rays. -/
theorem fourSevenContactStarCost_sos {a b c d e f : ℝ}
    (ha : 0 ≤ a) (hb : 0 < b) (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 < e) (hf : 0 ≤ f)
    (hfactor : fourSevenContactStarFactor a b c e ≤ 0) :
    IsRealMatchingSOS (fun p => seed p + a * ray 7 p + b * ray 13 p + c * ray 18 p +
      d * ray 20 p + e * ray 27 p + f * ray 30 p) := by
  let w : Fin 3 → ℝ := ![b, e, 1]
  let coupling : Fin 3 → ℝ := ![1, -1, 0]
  let features : Fin 3 → Fin 24 → ℝ := ![ray 13, ray 27, seed]
  have hw (i : Fin 3) : 0 < w i := by
    fin_cases i
    · exact hb
    · exact he
    · exact zero_lt_one
  have hfeatures (i : Fin 3) : features i ∈ realMatchingFunctionSpace := by
    fin_cases i
    · exact ray_mem 13
    · exact ray_mem 27
    · exact seed_mem
  have hbudget : (∑ i, (coupling i)^2 / w i) ≤ c := by
    have hweights : (∑ i, (coupling i)^2 / w i) = 1 / b + 1 / e := by
      norm_num [w, coupling, Fin.sum_univ_succ]
    exact hweights.trans_le (fourSevenContactStarFactor_budget ha hb hc he hfactor)
  have hbase : IsRealMatchingSOS (fun p => seed p + b * ray 13 p + c * ray 18 p + e * ray 27 p) := by
    have heq :
        (fun p => seed p + b * ray 13 p + c * ray 18 p + e * ray 27 p) =
          (fun p => c * (ray 18 p)^2 + (∑ i, w i * (features i p)^2) -
            2 * ray 18 p * (∑ i, coupling i * features i p)) := by
      funext p
      simp [w, features, coupling, Fin.sum_univ_succ, ordinaryCostRay_sq]
      linear_combination -(seedCancellation p)
    rw [heq]
    exact fourMatchingSOS_of_star c (ray 18) w coupling features (ray_mem 18) hfeatures hw hbudget
  have h₁ := realMatchingSOS_add_ordinaryCostRay hbase 7 a ha
  have h₂ := realMatchingSOS_add_ordinaryCostRay h₁ 20 d hd
  have h₃ := realMatchingSOS_add_ordinaryCostRay h₂ 30 f hf
  convert h₃ using 1
  funext p
  ring

end

end MOC
