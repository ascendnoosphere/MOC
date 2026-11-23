import MOC.WeightedDiamondHardFacets

/-! An order-four squared-minor inequality for a pair of homothetic antipodal spectra. -/

open BigOperators Matrix

namespace MOC

private def minorFacet {M : Type*} [AddCommGroup M]
    (m : Finset (Fin 4) → Finset (Fin 4) → M) : M :=
  m {2} {0} + m {3} {1} + m {0,2} {0,3} + m {0,2} {1,3} -
    m {0,3} {1,2} + m {0,3} {1,3}

private theorem vec0 {α : Type*} (a b c d : α) : ![a,b,c,d] 0 = a := rfl
private theorem vec1 {α : Type*} (a b c d : α) : ![a,b,c,d] 1 = b := rfl
private theorem vec2 {α : Type*} (a b c d : α) : ![a,b,c,d] 2 = c := rfl
private theorem vec3 {α : Type*} (a b c d : α) : ![a,b,c,d] 3 = d := rfl

set_option maxHeartbeats 24000000 in
set_option maxRecDepth 16000 in
private theorem minorFacet_quaternion (p q : Fin 4 → ℝ)
    (hp : (∑ i, p i ^ 2) = 1) (hq : (∑ i, q i ^ 2) = 1) :
    let B := quaternionRotation p q
    0 ≤ B 2 0 ^ 2 + B 3 1 ^ 2 + (B 0 0 * B 2 3 - B 0 3 * B 2 0) ^ 2 + (B 0 1 * B 2 3 - B 0 3 * B 2 1) ^ 2 - (B 0 1 * B 3 2 - B 0 2 * B 3 1) ^ 2 + (B 0 1 * B 3 3 - B 0 3 * B 3 1) ^ 2 := by
  let B := quaternionRotation p q
  change 0 ≤ B 2 0 ^ 2 + B 3 1 ^ 2 + (B 0 0 * B 2 3 - B 0 3 * B 2 0) ^ 2 + (B 0 1 * B 2 3 - B 0 3 * B 2 1) ^ 2 - (B 0 1 * B 3 2 - B 0 2 * B 3 1) ^ 2 + (B 0 1 * B 3 3 - B 0 3 * B 3 1) ^ 2
  have h : 72 * (B 2 0 ^ 2 + B 3 1 ^ 2) * (∑ i, p i ^ 2) * (∑ i, q i ^ 2) +
      72 * ((B 0 0 * B 2 3 - B 0 3 * B 2 0) ^ 2 + (B 0 1 * B 2 3 - B 0 3 * B 2 1) ^ 2 - (B 0 1 * B 3 2 - B 0 2 * B 3 1) ^ 2 + (B 0 1 * B 3 3 - B 0 3 * B 3 1) ^ 2) =
    9 * (2 * B 0 0 * B 1 0 + 2 * B 0 2 * B 1 2) ^ 2 +
      9 * (2 * B 0 0 * B 0 1 + 2 * B 2 0 * B 2 1) ^ 2 +
      9 * (2 * B 2 0 * B 3 0 + 2 * B 2 2 * B 3 2) ^ 2 +
      9 * (2 * B 0 2 * B 0 3 + 2 * B 2 2 * B 2 3) ^ 2 +
      8 * (B 0 0 * B 1 1 + 2 * B 0 1 * B 1 0 - B 2 2 * B 3 3 - 2 * B 2 3 * B 3 2) ^ 2 +
      24 * (B 0 0 * B 1 3 - 2 * B 0 3 * B 1 0 - B 2 1 * B 3 2) ^ 2 +
      12 * (B 0 0 * B 1 3 - B 2 1 * B 3 2 + 2 * B 2 2 * B 3 1) ^ 2 +
      12 * (B 0 2 * B 1 1 + 2 * B 2 0 * B 3 3 - B 2 3 * B 3 0) ^ 2 +
      24 * (2 * B 0 1 * B 1 2 - B 0 2 * B 1 1 + B 2 3 * B 3 0) ^ 2 +
      42 * (B 0 2 * B 1 3 - 2 * B 0 3 * B 1 2 + B 2 1 * B 3 0) ^ 2 +
      30 * (B 0 2 * B 1 3 - 2 * B 2 0 * B 3 1 + B 2 1 * B 3 0) ^ 2 +
      36 * (B 0 0 * B 3 1 + B 1 2 * B 2 3) ^ 2 +
      36 * (B 0 3 * B 3 2 + B 1 1 * B 2 0) ^ 2 := by
    simp only [B, quaternionRotation, Matrix.mul_apply, Fin.sum_univ_four, Matrix.of_apply,
      vec0, vec1, vec2, vec3]
    ring
  rw [hp, hq, mul_one, mul_one] at h
  have hs : 0 ≤ 9 * (2 * B 0 0 * B 1 0 + 2 * B 0 2 * B 1 2) ^ 2 +
      9 * (2 * B 0 0 * B 0 1 + 2 * B 2 0 * B 2 1) ^ 2 +
      9 * (2 * B 2 0 * B 3 0 + 2 * B 2 2 * B 3 2) ^ 2 +
      9 * (2 * B 0 2 * B 0 3 + 2 * B 2 2 * B 2 3) ^ 2 +
      8 * (B 0 0 * B 1 1 + 2 * B 0 1 * B 1 0 - B 2 2 * B 3 3 - 2 * B 2 3 * B 3 2) ^ 2 +
      24 * (B 0 0 * B 1 3 - 2 * B 0 3 * B 1 0 - B 2 1 * B 3 2) ^ 2 +
      12 * (B 0 0 * B 1 3 - B 2 1 * B 3 2 + 2 * B 2 2 * B 3 1) ^ 2 +
      12 * (B 0 2 * B 1 1 + 2 * B 2 0 * B 3 3 - B 2 3 * B 3 0) ^ 2 +
      24 * (2 * B 0 1 * B 1 2 - B 0 2 * B 1 1 + B 2 3 * B 3 0) ^ 2 +
      42 * (B 0 2 * B 1 3 - 2 * B 0 3 * B 1 2 + B 2 1 * B 3 0) ^ 2 +
      30 * (B 0 2 * B 1 3 - 2 * B 2 0 * B 3 1 + B 2 1 * B 3 0) ^ 2 +
      36 * (B 0 0 * B 3 1 + B 1 2 * B 2 3) ^ 2 +
      36 * (B 0 3 * B 3 2 + B 1 1 * B 2 0) ^ 2 := by positivity
  linarith only [h, hs]

private theorem minorFacet_real (O : Matrix.orthogonalGroup (Fin 4) ℝ) :
    0 ≤ minorFacet (subsetMinorSq (Complex.ofRealHom.mapMatrix O.val)) := by
  obtain ⟨p,q,hp,hq,hs,hd⟩ := exists_quaternionRotation_same_squaredMinors O
  unfold minorFacet
  rw [hs 2 0, hs 3 1, hd 0 2 0 3 (by decide) (by decide),
    hd 0 2 1 3 (by decide) (by decide), hd 0 3 1 2 (by decide) (by decide),
    hd 0 3 1 3 (by decide) (by decide)]
  exact minorFacet_quaternion p q hp hq

/-- One pair minor is bounded by two entry squares and three other pair minors. -/
theorem homothetic_minor_facet_nonneg (U : Matrix (Fin 4) (Fin 4) ℂ) (hU : IsUnitary U) :
    0 ≤ subsetMinorSq U {2} {0} + subsetMinorSq U {3} {1} +
      subsetMinorSq U {0,2} {0,3} + subsetMinorSq U {0,2} {1,3} -
      subsetMinorSq U {0,3} {1,2} + subsetMinorSq U {0,3} {1,3} := by
  obtain ⟨κ,inst,w,O,hw,_,hm⟩ := four_minor_mixture U hU
  letI := inst
  let m (k : κ) := subsetMinorSq (Complex.ofRealHom.mapMatrix (O k).val)
  have hprofile : subsetMinorSq U = ∑ k : κ, w k • m k := by
    funext I J
    simpa only [m, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using hm I J
  let L := minorFacet diamondEvaluate
  have hL (v : Finset (Fin 4) → Finset (Fin 4) → ℝ) : L v = minorFacet v := by
    rfl
  change 0 ≤ minorFacet (subsetMinorSq U)
  rw [← hL, hprofile, map_sum]
  apply Finset.sum_nonneg
  intro i _
  rw [map_smul, hL, smul_eq_mul]
  exact mul_nonneg (hw i) (minorFacet_real (O i))

end MOC
