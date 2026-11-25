import MOC.FourMatchingRelations
import MOC.FourMinorCertificate

/-! The ordinary-minor part of the T6 support certificate. -/

open BigOperators

namespace MOC

noncomputable section

/-- The six prescribed contacts of paper case T6. -/
def fourT6ContactIndices : Finset (Fin 24) := {0, 1, 2, 4, 6, 8}

/-- First extra linear inequality of the T6 ordinary minor cone. -/
def fourT6DefectA (g : Fin 24 → ℝ) : ℝ := -g 3 - 2 * g 7 + g 9 + g 10 - g 12 + g 16 + g 18

/-- Second extra linear inequality of the T6 ordinary minor cone. -/
def fourT6DefectB (g : Fin 24 → ℝ) : ℝ := -g 3 - g 7 + g 9 - g 12 + g 13 + g 18

/-- Reconstruction of a T6 gap profile from its eight free entries. -/
def t6GapProfile (g : Fin 24 → ℝ) : Fin 24 → ℝ :=
  ![0, 0, 0, g 3, 0, g 3, 0, g 7, 0, g 9, g 10, -g 7 + g 9 + g 10, g 12, g 13,
    g 12, -g 3 - g 7 + g 9 + g 13, g 16, -g 3 - g 7 + g 9 + g 16, g 18,
    -g 7 - g 12 + g 13 + g 18, -g 7 + g 10 + g 18,
    -g 3 - 2 * g 7 + g 9 + g 10 - g 12 + g 13 + g 18,
    -g 7 - g 12 + g 16 + g 18, -g 3 - g 7 + g 9 - g 12 + g 16 + g 18]

set_option maxHeartbeats 2000000 in
private theorem t6GapProfile_of_contacts (m : Fin 14 → ℝ) (H : ℝ)
    (hc : ∀ i ∈ fourT6ContactIndices, fourMatchingEvaluation m i = H) :
    let g := fun i => fourMatchingEvaluation m i - H
    ∀ i, g i = t6GapProfile g i := by
  have h0 := hc 0 (by decide)
  have h1 := hc 1 (by decide)
  have h2 := hc 2 (by decide)
  have h4 := hc 4 (by decide)
  have h6 := hc 6 (by decide)
  have h8 := hc 8 (by decide)
  simp [fourMatchingEvaluation] at h0 h1 h2 h4 h6 h8
  dsimp only
  intro i
  fin_cases i <;> simp [t6GapProfile, fourMatchingEvaluation] <;>
    linarith only [h0, h1, h2, h4, h6, h8]

/-- The eight free entries recover the spectral gap profile at T6 contacts. -/
theorem fourT6_spectral_gap_profile (a b : Fin 4 → ℂ) (η : ℂ) (H : ℝ)
    (hc : ∀ i ∈ fourT6ContactIndices, (η * matchingProduct a b (fourPerm i).symm).re = H) :
    let g : Fin 24 → ℝ := fun i => (η * matchingProduct a b (fourPerm i).symm).re - H
    ∀ i, g i = t6GapProfile g i := by
  let m : Fin 14 → ℝ := fun j => (η * fourNoncrossingCoordinates (fourSpectralPoints a b) j).re
  have hm (i : Fin 24) : fourMatchingEvaluation m i =
      (η * matchingProduct a b (fourPerm i).symm).re :=
    fourMatchingEvaluation_spectral_real_part a b η i
  have h := t6GapProfile_of_contacts m H (fun i hi => (hm i).trans (hc i hi))
  dsimp only at h
  simpa only [hm] using h

/-- The remaining projected gaps are explicit linear combinations of the
eight coordinates of the T6 contact face. -/
theorem fourT6_gap_relations (a b : Fin 4 → ℂ) (η : ℂ) (H : ℝ)
    (hc : ∀ i ∈ fourT6ContactIndices, (η * matchingProduct a b (fourPerm i).symm).re = H) :
    let g : Fin 24 → ℝ := fun i => (η * matchingProduct a b (fourPerm i).symm).re - H
    g 11 = -g 7 + g 9 + g 10 ∧ g 15 = -g 3 - g 7 + g 9 + g 13 ∧
    g 17 = -g 3 - g 7 + g 9 + g 16 ∧ g 19 = -g 7 - g 12 + g 13 + g 18 ∧
    g 20 = -g 7 + g 10 + g 18 ∧ g 21 = -g 3 - 2 * g 7 + g 9 + g 10 - g 12 + g 13 + g 18 ∧
    g 22 = -g 7 - g 12 + g 16 + g 18 ∧ g 23 = -g 3 - g 7 + g 9 - g 12 + g 16 + g 18 := by
  have h := fourT6_spectral_gap_profile a b η H hc
  exact ⟨h 11, h 15, h 17, h 19, h 20, h 21, h 22, h 23⟩

private def t6MinorRows : Fin 11 → Finset (Fin 4) :=
  ![{0}, {0, 1}, {0, 2}, {0, 3}, {0}, {0, 1}, {3}, {0, 3}, {0, 2}, {3}, {0, 3}]

private def t6MinorColumns : Fin 11 → Finset (Fin 4) :=
  ![{3}, {2, 3}, {2, 3}, {2, 3}, {2}, {1, 3}, {0}, {1, 2}, {1, 3}, {1}, {0, 1}]

private def t6MinorSupports : Fin 11 → Finset (Fin 24) :=
  ![{18, 19, 20, 21, 22, 23}, {16, 17, 22, 23}, {13, 15, 19, 21}, {12, 14, 18, 20},
    {12, 13, 14, 15, 16, 17}, {10, 11, 20, 21}, {9, 11, 15, 17, 21, 23}, {7, 10, 13, 16},
    {7, 9, 18, 23}, {3, 5, 13, 16, 19, 22}, {3, 5, 9, 11}]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem t6MinorSupports_spec : ∀ (k : Fin 11) (i : Fin 24),
    i ∈ t6MinorSupports k ↔ (t6MinorColumns k).map (fourPerm i).symm.toEmbedding = t6MinorRows k := by
  decide +kernel

private def t6MinorWeights (g : Fin 24 → ℝ) (u v z : ℝ) : Fin 11 → ℝ :=
  ![-g 12 + g 18 + u - v, -g 3 - g 7 + g 16 - u + v + z, -g 3 - g 7 + g 13 - u + v + z,
    g 12 - u, u, -g 7 + g 10 + v, g 9 - v - z, g 7 - v, v, g 3 - z, z]

set_option maxHeartbeats 2000000 in
private theorem t6GapProfile_eq_minorSum (g : Fin 24 → ℝ) (u v z : ℝ) (i : Fin 24) :
    t6GapProfile g i = ∑ k, if i ∈ t6MinorSupports k then t6MinorWeights g u v z k else 0 := by
  fin_cases i <;>
    simp (config := { decide := true }) [t6GapProfile, t6MinorSupports, t6MinorWeights,
      Fin.sum_univ_succ, Matrix.cons_val] <;> ring

private theorem t6_exists_nonnegative_weights (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i)
    (hprofile : ∀ i, g i = t6GapProfile g i) (hA : 0 ≤ fourT6DefectA g) (hB : 0 ≤ fourT6DefectB g) :
    ∃ u v z, ∀ k, 0 ≤ t6MinorWeights g u v z k := by
  let m := min (g 13) (g 16)
  let w := g 3 + g 7 - m + g 12 - g 18
  let v := max 0 (max (g 7 - g 10) (g 7 - m))
  let z := min (g 3) (g 9 - v)
  let u := max 0 (g 12 - g 18 + v)
  have hp (i : Fin 24) : 0 ≤ t6GapProfile g i := (hprofile i) ▸ hg i
  have h11 : 0 ≤ -g 7 + g 9 + g 10 := hp 11
  have h15 : 0 ≤ -g 3 - g 7 + g 9 + g 13 := hp 15
  have h17 : 0 ≤ -g 3 - g 7 + g 9 + g 16 := hp 17
  have h19 : 0 ≤ -g 7 - g 12 + g 13 + g 18 := hp 19
  have h20 : 0 ≤ -g 7 + g 10 + g 18 := hp 20
  have h21 : 0 ≤ -g 3 - 2 * g 7 + g 9 + g 10 - g 12 + g 13 + g 18 := hp 21
  have h22 : 0 ≤ -g 7 - g 12 + g 16 + g 18 := hp 22
  have h23 : 0 ≤ -g 3 - g 7 + g 9 - g 12 + g 16 + g 18 := hp 23
  dsimp only [fourT6DefectA] at hA
  dsimp only [fourT6DefectB] at hB
  have hm : 0 ≤ m := le_min (hg 13) (hg 16)
  have hmc : g 3 + g 7 - g 9 ≤ m := le_min (by linarith only [h15]) (by linarith only [h17])
  have hme : g 7 + g 12 - g 18 ≤ m := le_min (by linarith only [h19]) (by linarith only [h22])
  have hmw : g 3 + g 7 + g 12 - g 18 - g 9 ≤ m :=
    le_min (by linarith only [hB]) (by linarith only [h23])
  have hmcd : g 3 + 2 * g 7 + g 12 - g 18 - g 9 - g 10 ≤ m :=
    le_min (by linarith only [h21]) (by linarith only [hA])
  have hv₀ : 0 ≤ v := le_max_left _ _
  have hv₁ : g 7 - g 10 ≤ v := (le_max_left _ _).trans (le_max_right _ _)
  have hv₂ : g 7 - m ≤ v := (le_max_right _ _).trans (le_max_right _ _)
  have hv7 : v ≤ g 7 := max_le (hg 7) (max_le (sub_le_self _ (hg 10)) (sub_le_self _ hm))
  have hv9 : v ≤ g 9 := max_le (hg 9) (max_le (by linarith only [h11])
    (by linarith only [hmc, hg 3]))
  have hv18 : v ≤ g 18 := max_le (hg 18) (max_le (by linarith only [h20])
    (by linarith only [hme, hg 12]))
  have hw3 : w ≤ g 3 := by dsimp only [w]; linarith only [hme]
  have hvw : v ≤ g 9 - w := max_le (by dsimp only [w]; linarith only [hmw])
    (max_le (by dsimp only [w]; linarith only [hmcd]) (by linarith only [hmc, hw3]))
  have hz₀ : 0 ≤ z := le_min (hg 3) (sub_nonneg.mpr hv9)
  have hz3 : z ≤ g 3 := min_le_left _ _
  have hz9 : z ≤ g 9 - v := min_le_right _ _
  have hzw : w ≤ z := le_min hw3 (by linarith only [hvw])
  have hzmin : g 3 + g 7 - m - v ≤ z :=
    le_min (by linarith only [hv₂]) (by linarith only [hmc])
  have hu₀ : 0 ≤ u := le_max_left _ _
  have hu₁ : g 12 - g 18 + v ≤ u := le_max_right _ _
  have hu12 : u ≤ g 12 := max_le (hg 12) (by linarith only [hv18])
  have hub : u ≤ m - g 3 - g 7 + v + z := max_le (by linarith only [hzmin])
    (by dsimp only [w] at hzw; linarith only [hzw])
  have hm13 : m ≤ g 13 := min_le_left _ _
  have hm16 : m ≤ g 16 := min_le_right _ _
  refine ⟨u, v, z, fun k => ?_⟩
  fin_cases k <;> norm_num [t6MinorWeights]
  · linarith only [hu₁]
  · linarith only [hub, hm16]
  · linarith only [hub, hm13]
  · exact hu12
  · exact hu₀
  · linarith only [hv₁]
  · exact hz9
  · exact hv7
  · exact hv₀
  · exact hz3
  · exact hz₀

/-- Nonnegative T6 defects give an explicit decomposition into eleven
nonnegative ordinary minor costs. -/
theorem fourT6_support_of_nonnegative_defects (a b : Fin 4 → ℂ) (η : ℂ) (H : ℝ)
    (hn : ∀ i, H ≤ (η * matchingProduct a b (fourPerm i).symm).re)
    (hc : ∀ i ∈ fourT6ContactIndices, (η * matchingProduct a b (fourPerm i).symm).re = H)
    (U : Matrix (Fin 4) (Fin 4) ℂ) (hU : IsUnitary U)
    (hdef : let g (i : Fin 24) := (η * matchingProduct a b (fourPerm i).symm).re - H
      0 ≤ fourT6DefectA g ∧ 0 ≤ fourT6DefectB g) : H ≤ (η * determinantValue a b U).re := by
  let g (i : Fin 24) := (η * matchingProduct a b (fourPerm i).symm).re - H
  have hp' (i : Fin 24) : g i = t6GapProfile g i := fourT6_spectral_gap_profile a b η H hc i
  obtain ⟨u, v, z, hw⟩ := t6_exists_nonnegative_weights g (fun i => sub_nonneg.mpr (hn i)) hp' hdef.1 hdef.2
  refine four_support_of_minor_gap_decomposition a b η H U hU 0 (hc 0 (by decide))
    t6MinorRows t6MinorColumns (t6MinorWeights g u v z) hw (fun i => ?_)
  simp_rw [← t6MinorSupports_spec]
  exact (hp' i).trans (t6GapProfile_eq_minorSum g u v z i)

end

end MOC
