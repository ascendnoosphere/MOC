import MOC.FourMinorCertificate

/-! An order-four spectrum paired with its negative has a support gap that
is a nonnegative combination of ordinary squared-minor profiles. -/

open BigOperators Matrix

namespace MOC

private def negativeCopyScore {R : Type*} [CommRing R] (A B C : R) : Fin 24 → R :=
  ![0, 0, 0, 0, 0, 0, 0, A, 0, -B, A + B, 0, 0, A + B, 0, 0,
    A + 2 * B + C, B + C, -B, 0, 0, 0, B + C, C]

private def negativeCopyRays (k : Fin 7) : Fin 4 → ℤ :=
  ![![0, -1, 0, 0], ![0, -1, 1, -1], ![0, 0, 0, -1], ![1, 0, 0, 1],
    ![1, 1, -1, 1], ![1, 1, 0, 0], ![2, 2, -1, 2]] k

private def negativeCopyRows : Fin 16 → Finset (Fin 4) :=
  ![{0}, {0}, {1}, {2}, {2}, {3}, {0, 1}, {0, 1}, {0, 1}, {0, 1},
    {0, 2}, {0, 2}, {0, 2}, {0, 2}, {0, 3}, {0, 3}]

private def negativeCopyCols : Fin 16 → Finset (Fin 4) :=
  ![{0}, {1}, {3}, {1}, {2}, {3}, {0, 3}, {1, 2}, {1, 3}, {2, 3},
    {0, 3}, {1, 2}, {1, 3}, {2, 3}, {1, 2}, {2, 3}]

private def negativeCopySupports : Fin 7 → Finset (Fin 16) :=
  ![{14}, {12}, {9}, {0, 1, 13, 15}, {2, 5, 10, 13}, {3, 4, 7, 10},
    {0, 5, 6, 7, 8, 10, 11, 13}]

private def negativeCopyMinorEvent (i : Fin 24) (j : Fin 16) : Prop :=
  (negativeCopyCols j).map (fourPerm i).symm.toEmbedding = negativeCopyRows j

private instance (i : Fin 24) (j : Fin 16) : Decidable (negativeCopyMinorEvent i j) :=
  inferInstanceAs (Decidable ((negativeCopyCols j).map (fourPerm i).symm.toEmbedding = negativeCopyRows j))

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem negativeCopyRay_int_certificate : ∀ (k : Fin 7) (i : Fin 24),
    let q := negativeCopyRays k
    q 0 - negativeCopyScore (q 1) (q 2) (q 3) i =
      ∑ j : Fin 16, if j ∈ negativeCopySupports k ∧ negativeCopyMinorEvent i j then 1 else 0 := by
  decide +kernel

private theorem negativeCopyRay_certificate (k : Fin 7) (i : Fin 24) :
    let q (j : Fin 4) := (negativeCopyRays k j : ℝ)
    q 0 - negativeCopyScore (q 1) (q 2) (q 3) i =
      ∑ j : Fin 16, if j ∈ negativeCopySupports k ∧ negativeCopyMinorEvent i j then 1 else 0 := by
  have h := congrArg (Int.cast : ℤ → ℝ) (negativeCopyRay_int_certificate k i)
  fin_cases i <;>
    simpa [negativeCopyScore, Int.cast_sum, apply_ite] using h

set_option maxHeartbeats 1800000 in
private theorem negativeCopy_matching (a : Fin 4 → ℂ) (i : Fin 24) :
    let x := (a 0 - a 1) * (a 2 - a 3)
    let z := (a 0 - a 3) * (a 1 - a 2)
    matchingProduct a (fun j => -a j) (fourPerm i).symm =
      negativeCopyScore (x * x) (x * z) (z * z) i := by
  intro x z
  rw [matchingProduct_inverse]
  fin_cases i <;>
    simp (config := { decide := true }) [x, z, negativeCopyScore, Fin.prod_univ_four,
      fourPerm, Equiv.Perm.mul_apply, Equiv.swap_apply_def] <;> ring

private theorem negativeCopy_projected (a : Fin 4 → ℂ) (η : ℂ) (i : Fin 24) :
    let x := (a 0 - a 1) * (a 2 - a 3)
    let z := (a 0 - a 3) * (a 1 - a 2)
    (η * matchingProduct a (fun j => -a j) (fourPerm i).symm).re =
      negativeCopyScore (η * (x * x)).re (η * (x * z)).re (η * (z * z)).re i := by
  intro x z
  have hm := negativeCopy_matching a i
  change matchingProduct a (fun j => -a j) (fourPerm i).symm =
    negativeCopyScore (x * x) (x * z) (z * z) i at hm
  rw [hm]
  fin_cases i <;>
    simp [negativeCopyScore, two_mul, mul_add, mul_neg, Complex.add_re, Complex.neg_re]

set_option maxHeartbeats 1000000 in
private theorem negativeCopy_ray_expansion (H A B C : ℝ)
    (hs : ∀ i, negativeCopyScore A B C i ≤ H) :
    ∃ w : Fin 7 → ℝ, (∀ k, 0 ≤ w k) ∧ ∀ i,
      H - negativeCopyScore A B C i = ∑ k : Fin 7, w k *
        ((negativeCopyRays k 0 : ℝ) - negativeCopyScore (negativeCopyRays k 1 : ℝ)
          (negativeCopyRays k 2 : ℝ) (negativeCopyRays k 3 : ℝ) i) := by
  have hH : 0 ≤ H := hs 0
  have hA : A ≤ H := hs 7
  have hC : C ≤ H := hs 23
  have hB : -B ≤ H := hs 9
  have hAB : A + B ≤ H := hs 10
  have hBC : B + C ≤ H := hs 17
  have htotal : A + 2 * B + C ≤ H := hs 16
  let p := max B 0
  let k := max (-B) 0
  let m := min H (2 * k)
  have hp : 0 ≤ p := le_max_right _ _
  have hk : 0 ≤ k := le_max_right _ _
  have hkH : k ≤ H := max_le hB hH
  have hkm : k ≤ m := le_min hkH (by linarith)
  have hmH : m ≤ H := min_le_left _ _
  have hm2 : m ≤ 2 * k := min_le_right _ _
  have hpB : p - k = B := by
    rcases le_total 0 B with h | h
    · simp [p, k, max_eq_left h, max_eq_right (neg_nonpos.mpr h)]
    · simp [p, k, max_eq_right h, max_eq_left (neg_nonneg.mpr h)]
  have hap : A + p ≤ H := by
    change A + max B 0 ≤ H
    rw [add_max]
    exact max_le hAB (by simpa using hA)
  have hcp : C + p ≤ H := by
    change C + max B 0 ≤ H
    rw [add_max]
    exact max_le (by simpa only [add_comm B C] using hBC) (by simpa using hC)
  have htotal' : A + C + 2 * p - m ≤ H := by
    rcases le_total H (2 * k) with h | h
    · rw [show m = H from min_eq_left h]
      linarith only [hap, hcp]
    · rw [show m = 2 * k from min_eq_right h]
      linarith only [htotal, hpB]
  let u := max 0 (A + p - m)
  let v := H - m - u
  have hu : 0 ≤ u := le_max_left _ _
  have hua : A + p - m ≤ u := le_max_right _ _
  have huv : u ≤ H - m := max_le (sub_nonneg.mpr hmH) (by linarith only [hap])
  have hv : 0 ≤ v := sub_nonneg.mpr huv
  have hvc : C + p - m ≤ v := by
    change C + p - m ≤ H - m - max 0 (A + p - m)
    rw [le_sub_iff_add_le, add_max]
    exact max_le (by linarith only [hcp]) (by linarith only [htotal'])
  let w : Fin 7 → ℝ := ![u - (A + p - m), p, v - (C + p - m), v,
    2 * k - m, u, m - k]
  refine ⟨w, ?_, ?_⟩
  · intro j
    fin_cases j
    · exact sub_nonneg.mpr hua
    · exact hp
    · exact sub_nonneg.mpr hvc
    · exact hv
    · exact sub_nonneg.mpr hm2
    · exact hu
    · exact sub_nonneg.mpr hkm
  · intro i
    fin_cases i <;>
      simp [w, v, negativeCopyRays, negativeCopyScore, Fin.sum_univ_succ] <;>
      linarith only [hpB]

/-- In order four, an arbitrary complex spectrum and its negative satisfy
the determinant hull inclusion for every relative unitary. -/
theorem holds_four_negative_copy (a : Fin 4 → ℂ) (U : Matrix (Fin 4) (Fin 4) ℂ)
    (hU : IsUnitary U) : Holds a (fun j => -a j) U := by
  classical
  apply (holds_iff_directional _ _ _).mpr
  intro η
  let b (j : Fin 4) := -a j
  let f (i : Fin 24) := (η * matchingProduct a b (fourPerm i).symm).re
  let H := Finset.univ.sup' (Finset.univ_nonempty : (Finset.univ : Finset (Fin 24)).Nonempty) f
  obtain ⟨r, _, hr⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty f
  have hr' : H = f r := hr
  refine ⟨(fourPerm r).symm, ?_⟩
  change (η * determinantValue a b U).re ≤ f r
  rw [← hr']
  let x := (a 0 - a 1) * (a 2 - a 3)
  let z := (a 0 - a 3) * (a 1 - a 2)
  let A := (η * (x * x)).re
  let B := (η * (x * z)).re
  let C := (η * (z * z)).re
  have hf (i : Fin 24) : f i = negativeCopyScore A B C i := negativeCopy_projected a η i
  obtain ⟨w, hwn, hw⟩ := negativeCopy_ray_expansion H A B C (fun i => by
    rw [← hf i]
    exact Finset.le_sup' f (Finset.mem_univ i))
  let t (j : Fin 16) := ∑ k : Fin 7, if j ∈ negativeCopySupports k then w k else 0
  have htn (j : Fin 16) : 0 ≤ t j :=
    Finset.sum_nonneg (fun k _ => by split_ifs <;> simp [hwn k])
  have hdecomp (i : Fin 24) : H - f i =
      ∑ j : Fin 16, if negativeCopyMinorEvent i j then t j else 0 := by
    rw [hf, hw]
    simp_rw [negativeCopyRay_certificate, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : negativeCopyMinorEvent i j
    · simp only [hj, and_true, if_true, t]
      apply Finset.sum_congr rfl
      intro k _
      by_cases hk : j ∈ negativeCopySupports k <;> simp [hk]
    · simp [hj]
  have hs : -H ≤ ((-η) * determinantValue a b U).re := by
    refine four_support_of_minor_gap_decomposition a b (-η) (-H) U hU r ?_
      negativeCopyRows negativeCopyCols t htn ?_
    · change ((-η) * matchingProduct a b (fourPerm r).symm).re = -H
      simpa only [neg_mul, Complex.neg_re] using congrArg Neg.neg hr'.symm
    · intro i
      change ((-η) * matchingProduct a b (fourPerm i).symm).re - -H = _
      rw [neg_mul, Complex.neg_re, sub_neg_eq_add, add_comm]
      simpa only [sub_eq_add_neg] using hdecomp i
  simpa only [neg_mul, Complex.neg_re, neg_le_neg_iff] using hs

end MOC
