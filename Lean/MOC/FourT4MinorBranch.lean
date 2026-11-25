import MOC.FourMatchingRelations
import MOC.TwoValues
import MOC.Support

/-! The ordinary squared-minor branch of Zheng's six-contact case T4.
The replacement for a nonpositive mixed coefficient is checked directly
on the fourteen matching coordinates. -/

open BigOperators Matrix

namespace MOC

noncomputable section

/-- The six prescribed contacts of paper case T4. -/
def fourT4ContactIndices : Finset (Fin 24) := {0, 1, 4, 5, 7, 8}

private def t4MinorRows : Fin 9 → Finset (Fin 4) :=
  ![{0}, {0, 1}, {0, 2}, {0, 3}, {0}, {0, 1}, {3}, {0, 2}, {0, 1}]

private def t4MinorColumns : Fin 9 → Finset (Fin 4) :=
  ![{3}, {2, 3}, {2, 3}, {2, 3}, {2}, {1, 3}, {0}, {1, 2}, {0, 2}]

private def t4MinorCoordinates : Fin 9 → Fin 14 → ℤ :=
  ![![0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 1],
    ![0, 1, 0, -1, 0, 0, -1, 0, 0, 1, 0, -1, 0, 0],
    ![0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
    ![0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 1, -1, -1, 0, 1, -1, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1],
    ![-1, 0, 1, 0, 0, 1, 0, -1, 1, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0]]

private def t4HeightLift (b k e c a j l d H : ℝ) : Fin 14 → ℝ :=
  ![-j, -d - e, -b - d + j, d, 0, c + d + j + l, -c + k - l, -c - j,
    j, c - d - k, -c, d + e, -a - d, H + a + b + 2 * d + k]

private def t4LinearEvaluation : (Fin 14 → ℝ) →ₗ[ℝ] Fin 24 → ℝ where
  toFun := fourMatchingEvaluation
  map_add' m n := by
    funext i
    fin_cases i <;> simp [fourMatchingEvaluation, Pi.add_apply] <;> ring
  map_smul' r m := by
    funext i
    fin_cases i <;> simp [fourMatchingEvaluation, Pi.smul_apply, smul_eq_mul] <;> ring

set_option maxHeartbeats 2000000 in
private theorem t4HeightLift_of_contacts (m : Fin 14 → ℝ) (H : ℝ)
    (hc : ∀ i ∈ fourT4ContactIndices, fourMatchingEvaluation m i = H) :
    let g := fun i => fourMatchingEvaluation m i - H
    m = t4HeightLift (g 19) (g 16) (g 14) (g 10) (g 15) (g 6) (g 13) (g 2 - g 13) H := by
  have h0 := hc 0 (by decide)
  have h1 := hc 1 (by decide)
  have h4 := hc 4 (by decide)
  have h5 := hc 5 (by decide)
  have h7 := hc 7 (by decide)
  have h8 := hc 8 (by decide)
  simp [fourMatchingEvaluation] at h0 h1 h4 h5 h7 h8
  dsimp only
  funext i
  fin_cases i <;> simp [t4HeightLift, fourMatchingEvaluation] <;>
    linarith only [h0, h1, h4, h5, h7, h8]

private def t4MinorWeights (b k e c a j l d τ : ℝ) : Fin 9 → ℝ :=
  ![b + d + τ, k - τ, -d - τ, e - τ, τ, c, a + d, j, l + d]

set_option maxHeartbeats 2000000 in
private theorem t4HeightLift_eq_minor_sum (b k e c a j l d H τ : ℝ) :
    t4HeightLift b k e c a j l d H =
      t4HeightLift 0 0 0 0 0 0 0 0 H + ∑ n, t4MinorWeights b k e c a j l d τ n •
        (fun i => (t4MinorCoordinates n i : ℝ)) := by
  funext i
  fin_cases i <;>
    norm_num [Fin.sum_univ_succ, Finset.sum_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      t4HeightLift, t4MinorWeights, t4MinorCoordinates] <;> ring

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem t4Minor_evaluation (k : Fin 9) (i : Fin 24) :
    t4LinearEvaluation (fun j => (t4MinorCoordinates k j : ℝ)) i =
      if (t4MinorColumns k).map (fourPerm i).symm.toEmbedding = t4MinorRows k then 1 else 0 := by
  have hf : ∀ (x : Fin 9) (y : Fin 24), fourMatchingEvaluation (t4MinorCoordinates x) y =
      (if (t4MinorColumns x).map (fourPerm y).symm.toEmbedding = t4MinorRows x then 1 else 0) := by
    decide +kernel
  have h (v : Fin 14 → ℤ) :
      t4LinearEvaluation (fun j => (v j : ℝ)) i = ((fourMatchingEvaluation v i : ℤ) : ℝ) := by
    fin_cases i <;> simp [t4LinearEvaluation, fourMatchingEvaluation]
  rw [h, hf]
  split_ifs <;> simp only [Int.cast_one, Int.cast_zero]

private theorem t4HeightLift_constant (H : ℝ) :
    t4LinearEvaluation (t4HeightLift 0 0 0 0 0 0 0 0 H) = fun _ => H := by
  funext i
  fin_cases i <;> simp [t4HeightLift, t4LinearEvaluation, fourMatchingEvaluation]

private theorem t4Minor_response (U : Matrix (Fin 4) (Fin 4) ℂ) (hU : IsUnitary U)
    (k : Fin 9) :
    (∑ σ : FourPerm, if (t4MinorColumns k).map σ.toEmbedding = t4MinorRows k then
      realSignedWeight U σ else 0) = subsetMinorSq U (t4MinorRows k) (t4MinorColumns k) := by
  have hminor := congrArg Complex.re
    (sum_signedWeight_image_eq_subsetMinorSq U hU (t4MinorRows k) (t4MinorColumns k))
  simp only [Finset.sum_filter, Complex.re_sum, apply_ite, Complex.zero_re, Complex.ofReal_re] at hminor
  exact hminor

private theorem t4SpectralLift (α β : Fin 4 → ℂ) (η : ℂ) (H : ℝ)
    (hc : ∀ i ∈ fourT4ContactIndices, (η * matchingProduct α β (fourPerm i).symm).re = H) :
    let m : Fin 14 → ℝ := fun i => (η * fourNoncrossingCoordinates (fourSpectralPoints α β) i).re
    let g (i : Fin 24) := (η * matchingProduct α β (fourPerm i).symm).re - H
    m = t4HeightLift (g 19) (g 16) (g 14) (g 10) (g 15) (g 6) (g 13) (g 2 - g 13) H := by
  intro m g
  have heval (i : Fin 24) : fourMatchingEvaluation m i =
      (η * matchingProduct α β (fourPerm i).symm).re :=
    fourMatchingEvaluation_spectral_real_part α β η i
  have h := t4HeightLift_of_contacts m H (fun i hi => (heval i).trans (hc i hi))
  dsimp only at h
  simpa only [heval] using h

set_option maxHeartbeats 2000000 in
private theorem t4Support_minor_response (α β : Fin 4 → ℂ) (η : ℂ) (H : ℝ)
    (hc : ∀ i ∈ fourT4ContactIndices, (η * matchingProduct α β (fourPerm i).symm).re = H)
    (U : Matrix (Fin 4) (Fin 4) ℂ) (hU : IsUnitary U) (τ : ℝ) :
    let g (i : Fin 24) := (η * matchingProduct α β (fourPerm i).symm).re - H
    let w := t4MinorWeights (g 19) (g 16) (g 14) (g 10) (g 15) (g 6) (g 13) (g 2 - g 13) τ
    (η * determinantValue α β U).re - H =
      ∑ k, w k * subsetMinorSq U (t4MinorRows k) (t4MinorColumns k) := by
  classical
  intro g w
  let m : Fin 14 → ℝ := fun i => (η * fourNoncrossingCoordinates (fourSpectralPoints α β) i).re
  have hm : m = t4HeightLift 0 0 0 0 0 0 0 0 H + ∑ k, w k •
      (fun i => (t4MinorCoordinates k i : ℝ)) :=
    (t4SpectralLift α β η H hc).trans (t4HeightLift_eq_minor_sum _ _ _ _ _ _ _ _ _ _)
  have hsum (i : Fin 24) : g i = ∑ k, w k *
      (if (t4MinorColumns k).map (fourPerm i).symm.toEmbedding = t4MinorRows k then 1 else 0) := by
    have hi : g i = t4LinearEvaluation m i - H :=
      congrArg (fun x : ℝ => x - H) (fourMatchingEvaluation_spectral_real_part α β η i).symm
    rw [hi, hm, map_add, map_sum, t4HeightLift_constant]
    simp only [Pi.add_apply, Finset.sum_apply, map_smul, Pi.smul_apply, smul_eq_mul,
      t4Minor_evaluation, add_sub_cancel_left]
  have hgap := support_gap_eq α β U hU (-η) (fourPerm 0).symm
  have h0 := hc 0 (by decide)
  simp only [matchingGap, neg_mul, Complex.neg_re, h0] at hgap
  have hneg (x y : ℝ) : -x - -y = y - x := by ring
  simp only [hneg] at hgap
  rw [hgap]
  let e : Fin 24 ≃ FourPerm := fourPermEquiv.trans (Equiv.inv FourPerm)
  rw [← Equiv.sum_comp e]
  change (∑ i : Fin 24, realSignedWeight U (fourPerm i).symm * g i) = _
  simp_rw [hsum, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  have hprod (i : Fin 24) :
      realSignedWeight U (fourPerm i).symm *
          (w k * (if (t4MinorColumns k).map (fourPerm i).symm.toEmbedding = t4MinorRows k
            then 1 else 0)) =
        w k * (if (t4MinorColumns k).map (fourPerm i).symm.toEmbedding = t4MinorRows k
          then realSignedWeight U (fourPerm i).symm else 0) := by
    split_ifs <;> simp [mul_comm]
  simp_rw [hprod, ← Finset.mul_sum]
  have he (i : Fin 24) : e i = (fourPerm i).symm := rfl
  have hfilter := Equiv.sum_comp e (fun σ =>
    if (t4MinorColumns k).map σ.toEmbedding = t4MinorRows k then realSignedWeight U σ else 0)
  simp only [he] at hfilter
  rw [hfilter, t4Minor_response U hU k]

/-- Linear matching relations on the T4 contacts express gap 9 by
the gap at index 15 and the mixed coefficient. -/
theorem fourT4_gap_nine (α β : Fin 4 → ℂ) (η : ℂ) (H : ℝ)
    (hc : ∀ i ∈ fourT4ContactIndices, (η * matchingProduct α β (fourPerm i).symm).re = H) :
    let g (i : Fin 24) := (η * matchingProduct α β (fourPerm i).symm).re - H
    g 9 = g 15 + (g 2 - g 13) := by
  intro g
  let m : Fin 14 → ℝ := fun i => (η * fourNoncrossingCoordinates (fourSpectralPoints α β) i).re
  have hh : g 9 = fourMatchingEvaluation m 9 - H :=
    congrArg (fun x : ℝ => x - H) (fourMatchingEvaluation_spectral_real_part α β η 9).symm
  have hrep : m = t4HeightLift (g 19) (g 16) (g 14) (g 10) (g 15) (g 6) (g 13) (g 2 - g 13) H :=
    t4SpectralLift α β η H hc
  rw [hh, hrep]
  simp [t4HeightLift, fourMatchingEvaluation] <;> ring

/-- The exact T4 response as an ordinary minor sum plus the four-budget
form. This decomposition is valid at every height. -/
theorem fourT4_gap_eq_budget (α β : Fin 4 → ℂ) (η : ℂ) (H : ℝ)
    (hc : ∀ i ∈ fourT4ContactIndices, (η * matchingProduct α β (fourPerm i).symm).re = H)
    (U : Matrix (Fin 4) (Fin 4) ℂ) (hU : IsUnitary U) :
    let g (i : Fin 24) := (η * matchingProduct α β (fourPerm i).symm).re - H
    let d := g 2 - g 13
    let m := subsetMinorSq U
    (η * determinantValue α β U).re - H =
      (g 16 * m {0, 1} {2, 3} + g 14 * m {0, 3} {2, 3} + g 6 * m {0, 2} {1, 2} +
        g 13 * m {0, 1} {0, 2}) +
      (g 15 * m {3} {0} + g 19 * m {0} {3} + g 10 * m {0, 1} {1, 3} +
        d * (m {0} {3} - m {0, 2} {2, 3} + m {3} {0} + m {0, 1} {0, 2})) := by
  dsimp only
  rw [t4Support_minor_response α β η H hc U hU 0]
  simp [Fin.sum_univ_succ, t4MinorWeights, t4MinorRows, t4MinorColumns] <;> ring

set_option maxHeartbeats 1500000 in
/-- The T4 support inequality when the gap at index 2 is at most the gap
at index 13. All spectra and unitary eigenbases are allowed on this branch. -/
theorem fourT4_support_of_nonpositive_mixed (α β : Fin 4 → ℂ) (η : ℂ) (H : ℝ)
    (hn : ∀ i, H ≤ (η * matchingProduct α β (fourPerm i).symm).re)
    (hc : ∀ i ∈ fourT4ContactIndices, (η * matchingProduct α β (fourPerm i).symm).re = H)
    (hmixed : (η * matchingProduct α β (fourPerm 2).symm).re ≤
      (η * matchingProduct α β (fourPerm 13).symm).re)
    (U : Matrix (Fin 4) (Fin 4) ℂ) (hU : IsUnitary U) :
    H ≤ (η * determinantValue α β U).re := by
  classical
  let m : Fin 14 → ℝ := fun i => (η * fourNoncrossingCoordinates (fourSpectralPoints α β) i).re
  let g (i : Fin 24) := (η * matchingProduct α β (fourPerm i).symm).re - H
  let d := g 2 - g 13
  let τ := max 0 (-d - g 19)
  let w := t4MinorWeights (g 19) (g 16) (g 14) (g 10) (g 15) (g 6) (g 13) d τ
  have heval (i : Fin 24) : g i = fourMatchingEvaluation m i - H :=
    congrArg (fun x : ℝ => x - H) (fourMatchingEvaluation_spectral_real_part α β η i).symm
  have hrep : m = t4HeightLift (g 19) (g 16) (g 14) (g 10) (g 15) (g 6) (g 13) d H :=
    t4SpectralLift α β η H hc
  have hg (i : Fin 24) : 0 ≤ g i := sub_nonneg.mpr (hn i)
  have hd : d ≤ 0 := by
    dsimp only [d, g]
    linarith only [hmixed]
  have h22 : g 22 = g 16 + g 19 + d := by
    rw [heval 22, hrep]
    simp [t4HeightLift, fourMatchingEvaluation] <;> ring
  have h18 : g 18 = g 14 + g 19 + d := by
    rw [heval 18, hrep]
    simp [t4HeightLift, fourMatchingEvaluation] <;> ring
  have h9 : g 9 = g 15 + d := fourT4_gap_nine α β η H hc
  have hw (k : Fin 9) : 0 ≤ w k := by
    have hτ : 0 ≤ τ := le_max_left _ _
    have hτb : -d - g 19 ≤ τ := le_max_right _ _
    have hτk : τ ≤ g 16 := max_le (hg 16) (by linarith only [h22, hg 22])
    have hτe : τ ≤ g 14 := max_le (hg 14) (by linarith only [h18, hg 18])
    have hτd : τ ≤ -d := max_le (neg_nonneg.mpr hd) (by linarith only [hg 19])
    have ha : 0 ≤ g 15 + d := h9 ▸ hg 9
    have hl : 0 ≤ g 13 + d := by dsimp only [d]; linarith only [hg 2]
    fin_cases k
    · change 0 ≤ g 19 + d + τ
      linarith only [hτb]
    · exact sub_nonneg.mpr hτk
    · exact sub_nonneg.mpr hτd
    · exact sub_nonneg.mpr hτe
    · exact hτ
    · exact hg 10
    · exact ha
    · exact hg 6
    · exact hl
  apply sub_nonneg.mp
  rw [t4Support_minor_response α β η H hc U hU τ]
  exact Finset.sum_nonneg (fun k _ => mul_nonneg (hw k) (subsetMinorSq_nonneg U _ _))

end

end MOC
