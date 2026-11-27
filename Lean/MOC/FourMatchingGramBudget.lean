import MOC.FourSevenContactAffineElimination
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-! The four-function Gram budget, independent of the inverse determinant.
The square identity uses only injectivity of the underlying permutation. -/

open BigOperators
namespace MOC
noncomputable section

private def gramA (π : Equiv.Perm (Fin 4)) : Prop := π 2 = 2
private def gramB (π : Equiv.Perm (Fin 4)) : Prop := π 1 = 3
private def gramC (π : Equiv.Perm (Fin 4)) : Prop :=
  (π 0 = 0 ∧ π 1 = 2) ∨ (π 0 = 2 ∧ π 1 = 0)
private def gramD (π : Equiv.Perm (Fin 4)) : Prop :=
  (π 0 = 1 ∧ π 2 = 2) ∨ (π 0 = 2 ∧ π 2 = 1)
private def gramY (π : Equiv.Perm (Fin 4)) : Prop := π 3 = 1
private def gramW (π : Equiv.Perm (Fin 4)) : Prop :=
  (π 0 = 1 ∧ π 3 = 2) ∨ (π 0 = 2 ∧ π 3 = 1)

private def gramIndicator (P : Prop) : ℝ := by
  classical
  exact if P then 1 else 0

private def gramSeed (π : Equiv.Perm (Fin 4)) : ℝ :=
  gramIndicator (gramA π) + gramIndicator (gramB π) +
    gramIndicator (gramC π) - gramIndicator (gramD π)

-- Each implication is a statement about four distinct symbolic images in Fin 4.
-- No enumeration of permutations or ray profiles enters this proof.
private theorem gramEventGeometry (π : Equiv.Perm (Fin 4)) :
    ¬ (gramC π ∧ gramA π) ∧ ¬ (gramC π ∧ gramB π) ∧
    (gramD π → gramA π ∨ gramB π ∨ gramC π) ∧
    (gramW π → ¬ gramA π) ∧ (gramW π → ¬ gramD π) ∧
    (gramW π → gramY π → (gramB π ↔ ¬ gramC π)) ∧
    (gramW π → ¬ gramY π → ¬ gramC π) ∧
    (¬ gramW π → ((gramB π ∧ gramY π) ↔ (gramA π ∧ gramB π ∧ ¬ gramD π))) := by
  have h01 : π 0 ≠ π 1 := π.injective.ne (by decide)
  have h02 : π 0 ≠ π 2 := π.injective.ne (by decide)
  have h03 : π 0 ≠ π 3 := π.injective.ne (by decide)
  have h12 : π 1 ≠ π 2 := π.injective.ne (by decide)
  have h13 : π 1 ≠ π 3 := π.injective.ne (by decide)
  have h23 : π 2 ≠ π 3 := π.injective.ne (by decide)
  have b0 := (π 0).isLt
  have b1 := (π 1).isLt
  have b2 := (π 2).isLt
  have b3 := (π 3).isLt
  simp only [Fin.ext_iff] at h01 h02 h03 h12 h13 h23
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [gramA, gramB, gramC, gramD, gramY, gramW, Fin.ext_iff] <;> omega

private theorem gramSeed_square_symbolic (π : Equiv.Perm (Fin 4)) :
    gramSeed π ^ 2 = gramSeed π +
      2 * gramIndicator (gramA π ∧ gramB π ∧ ¬ gramD π) := by
  obtain ⟨hCA, hCB, hD, _, _, _, _, _⟩ := gramEventGeometry π
  by_cases ha : gramA π <;> by_cases hb : gramB π <;>
    by_cases hc : gramC π <;> by_cases hd : gramD π <;>
    simp_all [gramSeed, gramIndicator] <;> norm_num

private theorem gramCross_symbolic (π : Equiv.Perm (Fin 4)) :
    gramSeed π * gramIndicator (gramW π) +
      gramIndicator (gramB π) * gramIndicator (gramY π) -
      gramIndicator (gramB π) * gramIndicator (gramW π) -
      gramIndicator (gramY π) * gramIndicator (gramW π) =
    gramIndicator (gramA π ∧ gramB π ∧ ¬ gramD π) := by
  obtain ⟨_, _, _, hA, hD, hBC, hC, hOut⟩ := gramEventGeometry π
  by_cases hw : gramW π
  · have ha := hA hw
    have hd := hD hw
    by_cases hy : gramY π
    · have hbc := hBC hw hy
      by_cases hb : gramB π
      · have hc := hbc.mp hb
        simp [gramSeed, gramIndicator, hw, ha, hd, hy, hb, hc] <;> norm_num
      · have hc : gramC π := by
          by_contra hnc
          exact hb (hbc.mpr hnc)
        simp [gramSeed, gramIndicator, hw, ha, hd, hy, hb, hc] <;> norm_num
    · have hc := hC hw hy
      simp [gramSeed, gramIndicator, hw, ha, hd, hy, hc] <;> norm_num
  · have he := hOut hw
    rw [← he]
    by_cases hb : gramB π <;> by_cases hy : gramY π <;>
      simp [gramIndicator, hw, hb, hy]

private theorem gramIntIndicator (P : Prop) [Decidable P] :
    (Int.cast (ite (P) (1 : ℤ) 0) : ℝ) = gramIndicator P := by
  by_cases h : P <;> simp [gramIndicator, h]

private abbrev ray (i : Fin 34) : Fin 24 → ℝ := ordinaryCostRay i

private def seed (p : Fin 24) : ℝ := mixedCostSeedInt p

private theorem ray_10 (p : Fin 24) : ray 10 p = gramIndicator (gramA (fourPerm p)) := by
  change (ordinaryCostRayInt 10 p : ℝ) = _
  rw [ordinaryCostRayInt, if_pos (show (((10 : Fin 34).val) < 16) by omega)]
  change (Int.cast (ite (fourPerm p 2 = 2) (1 : ℤ) 0) : ℝ) = _
  exact gramIntIndicator _

private theorem ray_7 (p : Fin 24) : ray 7 p = gramIndicator (gramB (fourPerm p)) := by
  change (ordinaryCostRayInt 7 p : ℝ) = _
  rw [ordinaryCostRayInt, if_pos (show (((7 : Fin 34).val) < 16) by omega)]
  change (Int.cast (ite (fourPerm p 1 = 3) (1 : ℤ) 0) : ℝ) = _
  exact gramIntIndicator _

private theorem ray_17 (p : Fin 24) : ray 17 p = gramIndicator (gramC (fourPerm p)) := by
  let π := fourPerm p
  change (ordinaryCostRayInt 17 p : ℝ) = _
  rw [ordinaryCostRayInt, if_neg (show ¬ ((17 : Fin 34).val < 16) by omega)]
  change (Int.cast (ite ((π 0 = 0 ∧ π 1 = 2) ∨ (π 0 = 2 ∧ π 1 = 0)) (1 : ℤ) 0) : ℝ) = _
  exact gramIntIndicator _

private theorem ray_25 (p : Fin 24) : ray 25 p = gramIndicator (gramD (fourPerm p)) := by
  let π := fourPerm p
  change (ordinaryCostRayInt 25 p : ℝ) = _
  rw [ordinaryCostRayInt, if_neg (show ¬ ((25 : Fin 34).val < 16) by omega)]
  change (Int.cast (ite ((π 0 = 1 ∧ π 2 = 2) ∨ (π 0 = 2 ∧ π 2 = 1)) (1 : ℤ) 0) : ℝ) = _
  exact gramIntIndicator _

private theorem ray_13 (p : Fin 24) : ray 13 p = gramIndicator (gramY (fourPerm p)) := by
  change (ordinaryCostRayInt 13 p : ℝ) = _
  rw [ordinaryCostRayInt, if_pos (show (((13 : Fin 34).val) < 16) by omega)]
  change (Int.cast (ite (fourPerm p 3 = 1) (1 : ℤ) 0) : ℝ) = _
  exact gramIntIndicator _

private theorem ray_31 (p : Fin 24) : ray 31 p = gramIndicator (gramW (fourPerm p)) := by
  let π := fourPerm p
  change (ordinaryCostRayInt 31 p : ℝ) = _
  rw [ordinaryCostRayInt, if_neg (show ¬ ((31 : Fin 34).val < 16) by omega)]
  change (Int.cast (ite ((π 0 = 1 ∧ π 3 = 2) ∨ (π 0 = 2 ∧ π 3 = 1)) (1 : ℤ) 0) : ℝ) = _
  exact gramIntIndicator _

private theorem seed_eq_rays (p : Fin 24) :
    seed p = ray 10 p + ray 7 p + ray 17 p - ray 25 p := by
  simp only [seed, mixedCostSeedInt, Int.cast_add, Int.cast_sub, ordinaryCostRay]

private theorem gramSeed_eq (p : Fin 24) : seed p = gramSeed (fourPerm p) := by
  rw [seed_eq_rays, ray_10, ray_7, ray_17, ray_25] <;> rfl

private theorem mixed_seed (p : Fin 24) : mixedCostRay 0 p = seed p := by
  change (mixedCostSeedInt (fourPermIndex (1 * fourPerm p * 1)) : ℝ) = seed p
  rw [one_mul, mul_one, fourPermIndex_fourPerm] <;> rfl

private theorem seed_mem : seed ∈ realMatchingFunctionSpace := by
  have h : seed = ray 10 + ray 7 + ray 17 - ray 25 := funext seed_eq_rays
  rw [h]
  exact realMatchingFunctionSpace.sub_mem
    (realMatchingFunctionSpace.add_mem
      (realMatchingFunctionSpace.add_mem (ordinaryCostRay_mem_realMatchingFunctionSpace 10)
        (ordinaryCostRay_mem_realMatchingFunctionSpace 7))
      (ordinaryCostRay_mem_realMatchingFunctionSpace 17))
    (ordinaryCostRay_mem_realMatchingFunctionSpace 25)

private theorem gram_seed_square_identity (p : Fin 24) :
    seed p ^ 2 = seed p + 2 * (seed p * ray 31 p + ray 7 p * ray 13 p -
      ray 7 p * ray 31 p - ray 13 p * ray 31 p) := by
  rw [gramSeed_eq, ray_31, ray_7, ray_13, gramCross_symbolic]
  exact gramSeed_square_symbolic _

private theorem gram_square_completion (a b e m x y w : ℝ)
    (ha : a ≠ 0) (hab : a * b - 1 ≠ 0) :
    m^2 + a*x^2 + b*y^2 + e*w^2 - 2*(m*w+x*y-x*w-y*w) =
      (m-w)^2 + a*(x+(w-y)/a)^2 +
      (b-1/a)*(y+(a+1)/(a*b-1)*w)^2 +
      (e-(a+1)*(b+1)/(a*b-1))*w^2 := by
  field_simp [ha, hab] <;> ring

/-- Under the Gram budget, four matching functions give a sum of squares. -/
theorem fourMatchingSOS_of_gram_budget {a b e : ℝ}
    (ha : 0 < a) (hab : 1 < a*b) (he : (a+1)*(b+1) ≤ e*(a*b-1)) :
    IsRealMatchingSOS (fun p =>
      mixedCostRay 0 p + a*ordinaryCostRay 7 p + b*ordinaryCostRay 13 p +
        e*ordinaryCostRay 31 p) := by
  have hbcomp : 0 ≤ b-1/a :=
    sub_nonneg.mpr ((div_le_iff₀ ha).2 (by simpa only [mul_comm b a] using hab.le))
  have hecomp : 0 ≤ e-(a+1)*(b+1)/(a*b-1) :=
    sub_nonneg.mpr ((div_le_iff₀ (sub_pos.mpr hab)).2 he)
  let w : Fin 4 → ℝ := ![1, a, b-1/a, e-(a+1)*(b+1)/(a*b-1)]
  let features : Fin 4 → Fin 24 → ℝ := ![seed-ray 31, ray 7 + a⁻¹ • (ray 31-ray 13),
    ray 13 + ((a+1)/(a*b-1)) • ray 31, ray 31]
  have hw : ∀ i, 0 ≤ w i := by
    intro i
    fin_cases i
    · norm_num [w]
    · exact ha.le
    · exact hbcomp
    · exact hecomp
  have hfeat : ∀ i, features i ∈ realMatchingFunctionSpace := by
    intro i
    fin_cases i
    · exact realMatchingFunctionSpace.sub_mem seed_mem (ordinaryCostRay_mem_realMatchingFunctionSpace 31)
    · exact realMatchingFunctionSpace.add_mem (ordinaryCostRay_mem_realMatchingFunctionSpace 7) (realMatchingFunctionSpace.smul_mem _
        (realMatchingFunctionSpace.sub_mem (ordinaryCostRay_mem_realMatchingFunctionSpace 31) (ordinaryCostRay_mem_realMatchingFunctionSpace 13)))
    · exact realMatchingFunctionSpace.add_mem (ordinaryCostRay_mem_realMatchingFunctionSpace 13)
        (realMatchingFunctionSpace.smul_mem _ (ordinaryCostRay_mem_realMatchingFunctionSpace 31))
    · exact ordinaryCostRay_mem_realMatchingFunctionSpace 31
  have hcost : (fun p => mixedCostRay 0 p + a * ray 7 p + b * ray 13 p + e * ray 31 p) =
      (fun p => ∑ i, w i * features i p ^ 2) := by
    funext p
    calc
      mixedCostRay 0 p + a * ray 7 p + b * ray 13 p + e * ray 31 p =
          seed p^2 + a*(ray 7 p)^2 + b*(ray 13 p)^2 + e*(ray 31 p)^2 -
            2*(seed p*ray 31 p+ray 7 p*ray 13 p-ray 7 p*ray 31 p-ray 13 p*ray 31 p) := by
        rw [mixed_seed, gram_seed_square_identity, ordinaryCostRay_sq, ordinaryCostRay_sq,
          ordinaryCostRay_sq]
        ring
      _ = _ := by
        rw [gram_square_completion a b e (seed p) (ray 7 p) (ray 13 p) (ray 31 p)
          ha.ne' (sub_pos.mpr hab).ne']
        simp [w,features,Fin.sum_univ_succ,Pi.add_apply,Pi.sub_apply,Pi.smul_apply,
          smul_eq_mul,one_div,div_eq_mul_inv]
        <;> ring
  rw [hcost]
  exact isRealMatchingSOS_weighted w features hw hfeat

/-- A nonnegative ordinary coefficient adds one square to a certificate. -/
theorem fourMatchingSOS_add_ordinaryRay {g : Fin 24 → ℝ} (hs : IsRealMatchingSOS g)
    (r : Fin 34) {c : ℝ} (hc : 0 ≤ c) :
    IsRealMatchingSOS (fun p => g p + c * ordinaryCostRay r p) :=
  realMatchingSOS_add_ordinaryCostRay hs r c hc

end
end MOC
